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
      "For every JSON database, every SQL database that's permutation-equivalent " ++
      "to it, and every supported jq query, evaluating the jq query and evaluating " ++
      "its translated SQL query produce equivalent results." },
  { name := `permEquiv_implies_equiv
    title := "Permutation equivalence implies set equivalence"
    description :=
      "If two databases are permutation-equivalent (multiset equal) then they " ++
      "are also set-equivalent. Used as a stepping stone in the find/drop arms " ++
      "of query_equiv." },
  { name := `db_equiv_bridge
    title := "JDB ↔ SDB structural bridge"
    description :=
      "Two databases are equivalent iff every JSON record is in the column-form " ++
      "rows and vice-versa." },
  { name := `eval_bridgeJ
    title := "Cond.evalJ bridges through toS"
    description :=
      "Evaluating a Cond on the JSON record agrees with evaluating it on the " ++
      "SQL row produced by `toS`." },
  { name := `applyUpdateIf_bridge
    title := "Per-row UPDATE preserves the JSON ↔ SQL bridge"
    description :=
      "Applying a conditional UPDATE to a JSON record and converting to SQL " ++
      "produces the same row as applying the SQL UPDATE to the converted row." },
  { name := `toJ_toS
    title := "toS ∘ toJ is identity (round-trip lemma 1)"
    description := "Converting a JSON user to a SQL row and back yields the same record." },
  { name := `toS_toJ
    title := "toJ ∘ toS is identity (round-trip lemma 2)"
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
