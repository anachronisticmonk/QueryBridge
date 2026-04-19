import ProofPilot.Basic
/-!
# QueryEquiv — jq ↔ SQL Equivalence

## Core idea

`JDB` is a list of typed records (`Juser`).
`SDB` is a list of untyped row tuples (`String × Nat`).
`equiv jd sd` means the two stores are roundtrips of each other.

The central theorem `query_equiv` says: if `jd ≡ sd` before a query,
they are still `≡` after running a `JQuery` on the JSON side and its
translated `SQuery` on the SQL side.

Adding a new operation to `JQuery`/`SQuery` without extending
`query_equiv` will cause `lake build` to fail — that failure is the
verification signal.
-/

-- ── Types ─────────────────────────────────────────────────────────────────

structure Juser where
  name : String
  age  : Nat

def JDB : Type := List Juser
def Suser : Type := String × Nat
def SDB : Type := List Suser

-- ── Roundtrip conversions ─────────────────────────────────────────────────

def jdbToSdb (jd : JDB) : SDB :=
  match jd with
  | []              => []
  | {name, age} :: xs => (name, age) :: jdbToSdb xs

def sdbToJdb (sd : SDB) : JDB :=
  match sd with
  | []              => []
  | (name, age) :: xs => {name, age} :: sdbToJdb xs

def equiv (jd : JDB) (sd : SDB) : Prop :=
  (jdbToSdb jd = sd) ∧ (sdbToJdb sd = jd)

-- ── Query languages ───────────────────────────────────────────────────────

inductive JQuery where
  | find   : (Juser → Bool) → JQuery
  | delete : (Juser → Bool) → JQuery

inductive SQuery where
  | select : (Suser → Bool) → SQuery
  | drop   : (Suser → Bool) → SQuery

-- ── Query translation ─────────────────────────────────────────────────────

def jpred_to_spred (p : Juser → Bool) : Suser → Bool :=
  fun r => p { name := r.1, age := r.2 }

def jqueryToSquery : JQuery → SQuery
  | .find   p => .select (jpred_to_spred p)
  | .delete p => .drop   (jpred_to_spred p)

-- ── Semantics ─────────────────────────────────────────────────────────────

def eval_jquery (jd : JDB) : JQuery → JDB
  | .find   p => jd.filter p
  | .delete p => jd.filter (fun u => !p u)

def eval_squery (sd : SDB) : SQuery → SDB
  | .select p => sd.filter p
  | .drop   p => sd.filter (fun r => !p r)

-- ── Helper lemmas ─────────────────────────────────────────────────────────

@[simp]
theorem jdbToSdb_filter (jd : JDB) (p : Juser → Bool) :
    jdbToSdb (jd.filter p) =
    (jdbToSdb jd).filter (fun r => p { name := r.1, age := r.2 }) := by
  induction jd with
  | nil => simp [jdbToSdb, List.filter]
  | cons u us ih =>
    simp [List.filter, jdbToSdb]
    split
    · rename_i h; simp [jdbToSdb, h, ih]
    · rename_i h; simp [h, ih]

@[simp]
theorem sdbToJdb_filter (sd : SDB) (p : Juser → Bool) :
    sdbToJdb (sd.filter (fun r => p { name := r.1, age := r.2 })) =
    (sdbToJdb sd).filter p := by
  induction sd with
  | nil => simp [sdbToJdb, List.filter]
  | cons r rs ih =>
    match r with
    | (n, a) =>
      simp [List.filter, sdbToJdb]
      split
      · rename_i h_true; simp [sdbToJdb]; rw [ih]
      · rename_i h_false; exact ih

@[simp]
theorem jpred_to_spred_apply (p : Juser → Bool) (r : Suser) :
    jpred_to_spred p r = p { name := r.1, age := r.2 } := rfl

-- ── Equivalence theorems ──────────────────────────────────────────────────

theorem query_equiv1 (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    jdbToSdb (eval_jquery jd jq) = eval_squery sd (jqueryToSquery jq) := by
  rcases h with ⟨h_to_sdb, _⟩
  cases jq with
  | find p =>
    simp [eval_jquery, eval_squery, jqueryToSquery, jpred_to_spred]
    grind
  | delete p =>
    simp [eval_jquery, eval_squery, jqueryToSquery]
    rw [h_to_sdb]

theorem query_equiv2 (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    sdbToJdb (eval_squery sd (jqueryToSquery jq)) = eval_jquery jd jq := by
  rcases h with ⟨_, h_to_jdb⟩
  cases jq with
  | find p =>
    simp [eval_jquery, eval_squery, jqueryToSquery, jpred_to_spred]
    rw [h_to_jdb]
  | delete p =>
    simp [eval_jquery, eval_squery, jqueryToSquery]
    rw [sdbToJdb_filter sd (fun r => !(p { name := r.1, age := r.2 }))]
    rw [h_to_jdb]

/-- Master theorem: equivalence is preserved across any JQuery/SQuery pair. -/
theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jqueryToSquery jq)) :=
  ⟨query_equiv1 jd sd jq h, query_equiv2 jd sd jq h⟩

-- ── Structured predicates (for CLI serialisation) ─────────────────────────
-- These let Main.lean build JQuery values from JSON without using
-- function closures, while still instantiating the general theorem above.

namespace Concrete

inductive CompOp | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

def CompOp.eval : CompOp → Nat → Nat → Bool
  | .lt, a, b => a < b  | .le, a, b => a ≤ b
  | .gt, a, b => a > b  | .ge, a, b => a ≥ b
  | .eq, a, b => a == b | .ne, a, b => a != b

structure Pred where
  field : String
  op    : CompOp
  value : Nat
  deriving Repr

def evalJPred (p : Pred) : Juser → Bool
  | u => match p.field with
    | "age"  => CompOp.eval p.op u.age p.value
    | "name" => false   -- name comparisons not yet in scope
    | _      => false

/-- Wraps a structured predicate into a JQuery — covered by query_equiv. -/
def toJQuery (kind : String) (p : Pred) : Option JQuery :=
  match kind with
  | "find"   => some (.find   (evalJPred p))
  | "delete" => some (.delete (evalJPred p))
  | _        => none   -- unknown kind = not in proof scope

end Concrete
