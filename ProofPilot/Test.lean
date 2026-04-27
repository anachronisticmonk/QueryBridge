-- =====================================================
-- Tests.lean — Property-Based Testing for the formalization
-- =====================================================
-- This file uses Plausible to randomly stress-test the eval_jquery /
-- eval_squery / jquery_to_squery functions. The theorem `query_equiv`
-- *proves* correctness, but random testing is still useful for:
--   - bugs in untested helpers (e.g. parser, applyUpdate)
--   - regressions during refactoring
--   - issues in code paths the proofs don't directly cover
--
-- If the implementation is correct, every #test passes silently.
-- If something is wrong, Plausible prints a minimal counterexample.

-- IMPORT NOTE
-- -----------
-- Both Main.lean and Tests.lean live inside the ProofPilot/ directory,
-- so they're sibling modules under the ProofPilot library namespace.
-- The import path mirrors the file path: ProofPilot/Main.lean is
-- imported as ProofPilot.Main.

import Error
import Plausible

open Plausible

-- =====================================================
-- 1. Arbitrary + Shrinkable instances
-- =====================================================
-- Plausible's modern API: provide an `Arbitrary` (generator) and a
-- `Shrinkable` (counterexample minimizer); the default `SampleableExt`
-- instance is then derived automatically.
--
-- For our schema types, shrinking is mostly a no-op — finite enums
-- (Role, Col, Op) have nothing to shrink, and the recursive types
-- (Cond, JQuery) shrink trivially to leaf constructors. This is fine:
-- without shrinking, Plausible still finds counterexamples; it just
-- doesn't minimize them. The starting samples are already small.

instance : Shrinkable Role := ⟨fun _ => []⟩
instance : Arbitrary Role where
  arbitrary := do
    let n ← Arbitrary.arbitrary (α := Fin 3)
    return match n.val with
    | 0 => Role.student
    | 1 => Role.employee
    | _ => Role.retired

instance : Shrinkable Juser where
  shrink u :=
    -- Shrink toward smaller ages and the empty name; preserve role.
    (if u.age = 0 then [] else [{ u with age := 0 }]) ++
    (if u.name = "" then [] else [{ u with name := "" }])
instance : Arbitrary Juser where
  arbitrary := do
    let n ← Arbitrary.arbitrary (α := String)
    let a ← Arbitrary.arbitrary (α := Nat)
    let r ← Arbitrary.arbitrary (α := Role)
    return { name := n, age := a, role := r }

instance : Shrinkable Col := ⟨fun _ => []⟩
instance : Arbitrary Col where
  arbitrary := do
    let n ← Arbitrary.arbitrary (α := Fin 4)
    return match n.val with
    | 0 => Col.name
    | 1 => Col.age
    | 2 => Col.role
    | _ => Col.all

instance : Shrinkable Op := ⟨fun _ => []⟩
instance : Arbitrary Op where
  arbitrary := do
    let n ← Arbitrary.arbitrary (α := Fin 5)
    return match n.val with
    | 0 => Op.eq
    | 1 => Op.gt
    | 2 => Op.lt
    | 3 => Op.ge
    | _ => Op.le

instance : Shrinkable Value := ⟨fun _ => []⟩
instance : Arbitrary Value where
  arbitrary := do
    let n ← Arbitrary.arbitrary (α := Fin 3)
    match n.val with
    | 0 => return Value.nat (← Arbitrary.arbitrary)
    | 1 => return Value.str (← Arbitrary.arbitrary)
    | _ => return Value.role (← Arbitrary.arbitrary)

/-- Generate a flat (no nested and/or) Cond. Plausible struggles with
    deeply-recursive samplers; flat conditions still exercise every
    code path in `eval_bridge` because the recursion is structural. -/
instance : Shrinkable Cond := ⟨fun _ => [Cond.always]⟩
instance : Arbitrary Cond where
  arbitrary := do
    let kind ← Arbitrary.arbitrary (α := Fin 3)
    match kind.val with
    | 0 => return Cond.always
    | 1 =>
      let c ← Arbitrary.arbitrary (α := Col)
      let o ← Arbitrary.arbitrary (α := Op)
      let v ← Arbitrary.arbitrary (α := Value)
      return Cond.cmp c o v
    | _ =>
      let c1 ← Arbitrary.arbitrary (α := Col)
      let o1 ← Arbitrary.arbitrary (α := Op)
      let v1 ← Arbitrary.arbitrary (α := Value)
      let c2 ← Arbitrary.arbitrary (α := Col)
      let o2 ← Arbitrary.arbitrary (α := Op)
      let v2 ← Arbitrary.arbitrary (α := Value)
      return Cond.and (Cond.cmp c1 o1 v1) (Cond.cmp c2 o2 v2)

instance : Shrinkable JQuery := ⟨fun _ => [JQuery.clear]⟩
instance : Arbitrary JQuery where
  arbitrary := do
    let kind ← Arbitrary.arbitrary (α := Fin 6)
    match kind.val with
    | 0 => return JQuery.find (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)
    | 1 => return JQuery.drop (← Arbitrary.arbitrary)
    | 2 => return JQuery.prepend (← Arbitrary.arbitrary)
    | 3 => return JQuery.clear
    | 4 => return JQuery.count
    | _ =>
      return JQuery.modify
        (← Arbitrary.arbitrary)
        (← Arbitrary.arbitrary)
        (← Arbitrary.arbitrary)

-- =====================================================
-- 2. Building an SDB that's permEquiv to a given JDB
-- =====================================================
-- Plausible can generate a random JDB but not a "JDB and an SDB that
-- are permEquiv" pair — independent random sampling almost never
-- produces such a pair. So we derive the SDB directly. The result is
-- definitionally permEquiv to the input JDB, so the precondition of
-- query_equiv holds for free.

def jdbToSdb (jd : JDB) : SDB :=
  { names := jd.map (·.name)
    ages  := jd.map (·.age)
    roles := jd.map (·.role) }

-- =====================================================
-- 3. Decidable result equivalence (for use as a Testable property)
-- =====================================================
-- The `equiv` Prop is a ∀-statement that isn't decidable in general.
-- For testing we use a stronger but decidable equivalent: check that
-- the row projections of both sides are exact list equals (since for
-- our `jdbToSdb` construction the order is preserved, no permutation
-- slack is needed).

def result_equiv_bool : JResult → SResult → Bool
  | JResult.db jd,  SResult.db sd  => jd.map toS = sd.toRows
  | JResult.num n₁, SResult.num n₂ => n₁ = n₂
  | _, _ => false

-- =====================================================
-- 4. Properties
-- =====================================================

/-- The headline property: for any JDB and any JQuery, evaluating the
    query directly on jd should produce a result equivalent (after
    the toS bridge) to evaluating the translated SQuery on the
    derived SDB. This is what `query_equiv` proves; `#test` checks
    it on random samples and reports a minimal counterexample if
    something breaks. -/
def prop_translation_correct (jd : JDB) (jq : JQuery) : Bool :=
  result_equiv_bool
    (eval_jquery jd jq)
    (eval_squery (jdbToSdb jd) (jquery_to_squery jq))

/-- A simpler structural property: the row projection of (jdbToSdb jd)
    is exactly jd.map toS. Catches bugs in jdbToSdb, toS, or zip3. -/
def prop_jdbToSdb_roundtrip (jd : JDB) : Bool :=
  (jdbToSdb jd).toRows = jd.map toS

/-- count is map-invariant (not just under filter): modifying every
    row preserves row-count. -/
def prop_modify_preserves_count
    (jd : JDB) (col : Col) (v : Value) (c : Cond) : Bool :=
  match eval_jquery jd JQuery.count,
        eval_jquery (match eval_jquery jd (JQuery.modify col v c) with
                     | JResult.db jd' => jd'
                     | _              => []) JQuery.count with
  | JResult.num n₁, JResult.num n₂ => n₁ = n₂
  | _, _ => false

/-- find with Cond.always returns the whole database. -/
def prop_find_always_is_identity (jd : JDB) : Bool :=
  match eval_jquery jd (JQuery.find Col.all Cond.always) with
  | JResult.db jd' => jd' = jd
  | _              => false

-- =====================================================
-- 5. Run the tests
-- =====================================================
-- `#test` runs the property; on failure it shrinks and prints a
-- minimal counterexample. On success it's silent.

#test ∀ jd jq, prop_translation_correct jd jq = true
#test ∀ jd, prop_jdbToSdb_roundtrip jd = true
#test ∀ jd col v c, prop_modify_preserves_count jd col v c = true
#test ∀ jd, prop_find_always_is_identity jd = true
