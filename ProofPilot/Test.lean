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

def prop_translation_correct (jd : JDB) (jq : JQuery) : Bool :=
  result_equiv_bool
    (eval_jquery jd jq)
    (eval_squery (jdbToSdb jd) (jquery_to_squery jq))

def prop_jdbToSdb_roundtrip (jd : JDB) : Bool :=
  (jdbToSdb jd).toRows = jd.map toS

def prop_modify_preserves_count
    (jd : JDB) (col : Col) (v : Value) (c : Cond) : Bool :=
  match eval_jquery jd (JQuery.modify col v c) with
  | JResult.db jd' => jd'.length = jd.length
  | JResult.num _  => false

def prop_find_always_is_identity (jd : JDB) : Bool :=
  match eval_jquery jd (JQuery.find Col.all Cond.always) with
  | JResult.db jd' => jd' = jd
  | _              => false


-- Run the tests

#test ∀ jd jq, prop_translation_correct jd jq = true
#test ∀ jd col v c, prop_modify_preserves_count jd col v c = true
#test ∀ jd, prop_find_always_is_identity jd = true
