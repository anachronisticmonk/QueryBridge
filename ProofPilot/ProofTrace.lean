-- =====================================================
-- ProofTrace — verified-proof inspector
-- =====================================================
-- IO binary that:
--   1. Loads the `Main` module's environment at runtime via
--      `Lean.importModules` (Lean acts as a server here — we ask
--      it to type-check and hand back the kernel-checked env).
--   2. For each named theorem, looks up its `ConstantInfo`,
--      pretty-prints the theorem statement using `Meta.ppExpr`,
--      and walks the proof term's transitive constants with
--      `Lean.collectAxioms` to enumerate the axioms it ultimately
--      relies on.
--   3. Marks the theorem `verified` iff its axiom set does not
--      contain `sorryAx` — i.e. Lean's kernel accepted a complete
--      proof. The set of remaining axioms (typically just the three
--      Lean foundational axioms: `propext`, `Classical.choice`,
--      `Quot.sound`) is reported alongside as a transparency claim.
--   4. Emits a JSON array of the per-theorem reports for the
--      QueryBridge backend to surface in the UI.
--
-- This is the dual of PropRunner.lean: PropRunner shows what
-- Plausible *fails* to prove on the buggy `Error.lean` evaluator;
-- ProofTrace shows what Lean's kernel *accepts* on the correct
-- `Main.lean` formalization.

import Lean
import Main

open Lean Meta

/-- Pretty-print an `Expr` to a single string under the given env. -/
def ppExprIn (env : Environment) (e : Expr) : IO String := do
  let coreCtx : Core.Context := { fileName := "<proofTrace>", fileMap := default }
  let coreSt  : Core.State   := { env := env }
  let action : MetaM Format := Meta.ppExpr e
  let ((fmt, _), _) ← (action.run {} {}).toIO coreCtx coreSt
  return fmt.pretty (width := 100)

/-- Run `Lean.collectAxioms` against the given env. -/
def axiomsIn (env : Environment) (n : Name) : IO (Array Name) := do
  let coreCtx : Core.Context := { fileName := "<proofTrace>", fileMap := default }
  let coreSt  : Core.State   := { env := env }
  let action : CoreM (Array Name) := collectAxioms n
  let (axs, _) ← action.toIO coreCtx coreSt
  return axs

structure ThmSpec where
  name        : Name
  title       : String
  description : String

def thmSpecs : List ThmSpec := [
  { name := `query_equiv
    title := "Headline equivalence theorem"
    description :=
      "For every JSON database `jd`, every SQL database `sd` that is " ++
      "multiset-equivalent to it (`equiv jd sd`, defined as " ++
      "`List.Perm (jd.map toS) sd.toRows`), and every supported jq query, " ++
      "evaluating the jq query and evaluating its translated SQL query " ++
      "produce equivalent results — multiplicities agree on database " ++
      "results, counts agree on scalar results." },
  { name := `eval_bridgeJ
    title := "Cond.evalJ bridges through toS"
    description :=
      "Evaluating a `Cond` on a JSON record agrees with evaluating it on " ++
      "the SQL row produced by `toS`. Foundational lemma used by every " ++
      "predicate-bearing arm of `query_equiv` (find / drop / modify)." },
  { name := `eval_bridgeS
    title := "Cond.evalS bridges through toJ"
    description :=
      "The dual of `eval_bridgeJ`: evaluating a `Cond` on a SQL row " ++
      "agrees with evaluating it on the JSON record produced by `toJ`." },
  { name := `toRows_filter_reconstruct
    title := "Columnar SDB filter ↔ row-wise filter"
    description :=
      "Filtering an SDB row-by-row and reconstructing it from the " ++
      "surviving columns is the same as filtering `sd.toRows` directly. " ++
      "The find- and drop-case proofs of `query_equiv` use this as the " ++
      "structural bridge between the per-column and the per-row views." },
  { name := `toRows_insert
    title := "Columnar SDB insert ↔ row-wise prepend"
    description :=
      "Inserting a value into each of an SDB's column lists corresponds " ++
      "exactly to prepending the assembled row to `sd.toRows`. Used by the " ++
      "prepend-case (`JQuery.prepend ↦ SQuery.insert`) of `query_equiv`." },
  { name := `toRows_map_reconstruct
    title := "Columnar SDB map ↔ row-wise map"
    description :=
      "Mapping each column of an SDB and reconstructing the SDB equals " ++
      "mapping `sd.toRows` directly. Used by the modify-case " ++
      "(`JQuery.modify ↦ SQuery.update`) of `query_equiv`." },
  { name := `applyUpdateIf_bridge
    title := "Per-row conditional UPDATE preserves the JSON ↔ SQL bridge"
    description :=
      "Applying a conditional UPDATE to a JSON record and then converting " ++
      "to SQL produces the same row as applying the SQL UPDATE to the " ++
      "already-converted row." },
  { name := `toJ_toS
    title := "toJ ∘ toS is identity (round-trip lemma 1)"
    description := "Converting a JSON user to a SQL row and back yields the same record." },
  { name := `toS_toJ
    title := "toS ∘ toJ is identity (round-trip lemma 2)"
    description := "Converting a SQL row to a JSON user and back yields the same record." }
]

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules #[{module := `Main}] {} 0
  let mut results : Array Json := #[]
  for spec in thmSpecs do
    match env.find? spec.name with
    | none =>
      results := results.push (Json.mkObj [
        ("name",        .str spec.name.toString),
        ("title",       .str spec.title),
        ("description", .str spec.description),
        ("status",      .str "missing")
      ])
    | some info =>
      let typeStr ← ppExprIn env info.type
      let axs ← axiomsIn env spec.name
      let usesSorry := axs.any (· == ``sorryAx)
      let isThm := info matches ConstantInfo.thmInfo _
      let proofTermSize : Nat :=
        match info.value? with
        | some v => v.approxDepth.toNat
        | none   => 0
      results := results.push (Json.mkObj [
        ("name",          .str spec.name.toString),
        ("title",         .str spec.title),
        ("description",   .str spec.description),
        ("kind",          .str (if isThm then "theorem" else "definition")),
        ("type",          .str typeStr),
        ("status",        .str (if usesSorry then "sorry" else "verified")),
        ("axioms",        Json.arr ((axs.map (fun a => Json.str a.toString))) ),
        ("proofTermDepth", Json.num proofTermSize)
      ])
  IO.println (Json.arr results).compress
