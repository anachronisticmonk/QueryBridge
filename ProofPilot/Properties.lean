-- =====================================================
-- Properties.lean — Plausible test definitions
-- =====================================================
-- Holds the Arbitrary / Shrinkable instances and the property
-- definitions used by both:
--   * Test.lean      — top-level `#test` directives (editor view)
--   * PropRunner.lean — programmatic IO binary that runs Plausible
--                       and serializes the TestResult as JSON
--
-- This file imports `Error.lean` (the deliberately buggy variant
-- of the eval_jquery semantics). Plausible discovers counter-
-- examples for the bugs seeded there.

import Error
import Plausible
open Plausible

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
    | 4 => return JQuery.length
    | _ =>
      return JQuery.modify
        (← Arbitrary.arbitrary)
        (← Arbitrary.arbitrary)
        (← Arbitrary.arbitrary)

def jdbToSdb (jd : JDB) : SDB :=
  { names := jd.map (·.name)
    ages  := jd.map (·.age)
    roles := jd.map (·.role) }

def result_equiv_bool : JResult → SResult → Bool
  | JResult.db jd,  SResult.db sd  => jd.map toS = sd.toRows
  | JResult.num n₁, SResult.num n₂ => n₁ = n₂
  | _, _ => false


/--
  For any database, modifying the values of a user doesn't change the
  number of rows in the database.
  --/
def prop_modify_preserves_count
    (jd : JDB) (col : Col) (v : Value) (c : Cond) : Bool :=
  match eval_jquery jd (JQuery.modify col v c) with
  | JResult.db jd' => jd'.length = jd.length
  | JResult.num _  => false

/--
  For any database, length should return the actual number of rows in
  the database.
  --/
def prop_length_returns_count (jd : JDB) : Bool :=
  match eval_jquery jd JQuery.length with
  | JResult.num n => n = jd.length
  | JResult.db _  => false

/--
  For any database and jq query, evaluating directly on JSON should
  agree with translating to SQL via jquery_to_squery and evaluating on
  the columnar projection.
  --/
def prop_translation_correct (jd : JDB) (jq : JQuery) : Bool :=
  result_equiv_bool
    (eval_jquery jd jq)
    (eval_squery (jdbToSdb jd) (jquery_to_squery jq))

/--
  For any database, selecting all rows returns an identical database.
  --/
def prop_find_always_is_identity (jd : JDB) : Bool :=
  match eval_jquery jd (JQuery.find Col.all Cond.always) with
  | JResult.db jd' => jd' = jd
  | _              => false
