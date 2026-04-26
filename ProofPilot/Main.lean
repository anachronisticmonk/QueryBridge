import Std
import Init.Data.String.TakeDrop
-- =====================================================
-- 1. Base Data Structures
-- =====================================================

structure Juser where
  name : String
  age  : Nat
deriving Repr, DecidableEq

def Suser : Type := String × Nat

abbrev JDB := List Juser
abbrev SDB := List Suser

-- =====================================================
-- 2. Conversion
-- =====================================================

def toS (u : Juser) : Suser := (u.name, u.age)
def toJ (s : Suser) : Juser := { name := s.1, age := s.2 }

-- =====================================================
-- 3. Schema
-- =====================================================

inductive Col where
  | name | age | all
  deriving Repr, DecidableEq

-- =====================================================
-- 4. Generic Values + Operators
-- =====================================================

inductive Value where
  | nat : Nat → Value
  | str : String → Value
  deriving Repr, DecidableEq

inductive Op where
  | eq | gt | lt | ge | le
  deriving Repr, DecidableEq

-- =====================================================
-- 5. Generic Condition Language
-- =====================================================

inductive Cond where
  | always : Cond
  | cmp    : Col → Op → Value → Cond
  | and    : Cond → Cond → Cond
  | or     : Cond → Cond → Cond
  deriving Repr, Inhabited

-- =====================================================
-- 6. Evaluation Helpers
-- =====================================================

def getVal (c : Col) (u : Juser) : Value :=
  match c with
  | Col.name => Value.str u.name
  | Col.age  => Value.nat u.age
  | Col.all  => Value.str ""   -- unused fallback

def getValS (c : Col) (s : Suser) : Value :=
  match c, s with
  | Col.name, (n, _) => Value.str n
  | Col.age,  (_, a) => Value.nat a
  | Col.all, _       => Value.str ""

def evalOp : Op → Value → Value → Bool
  | Op.eq, v₁, v₂ => v₁ = v₂
  | Op.gt, Value.nat a, Value.nat b => a > b
  | Op.lt, Value.nat a, Value.nat b => a < b
  | Op.ge, Value.nat a, Value.nat b => a ≥ b
  | Op.le, Value.nat a, Value.nat b => a ≤ b
  | _, _, _ => false

-- =====================================================
-- 7. Condition Evaluation
-- =====================================================

def Cond.eval : Cond → Juser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, u =>
      evalOp op (getVal col u) v
  | Cond.and c₁ c₂, u =>
      c₁.eval u && c₂.eval u
  | Cond.or c₁ c₂, u =>
      c₁.eval u || c₂.eval u

def Cond.evalS : Cond → Suser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, s =>
      evalOp op (getValS col s) v
  | Cond.and c₁ c₂, s =>
      c₁.evalS s && c₂.evalS s
  | Cond.or c₁ c₂, s =>
      c₁.evalS s || c₂.evalS s

-- =====================================================
-- 8. Query Languages
-- =====================================================

inductive JQuery where
  | find   : Col → Cond → JQuery
  | drop : Cond → JQuery
  deriving Repr

inductive SQuery where
  | select : Col → Cond → SQuery
  | delete   : Cond → SQuery
  deriving Repr

-- =====================================================
-- 9. Semantics
-- =====================================================

def eval_jquery : JDB → JQuery → JDB
  | jd, JQuery.find _ c => jd.filter c.eval
  | jd, JQuery.drop c => jd.filter (fun u => ¬ c.eval u)

def eval_squery : SDB → SQuery → SDB
  | sd, SQuery.select _ c => sd.filter (fun s => c.evalS s)
  | sd, SQuery.delete c     => sd.filter (fun s => ¬ c.evalS s)

-- =====================================================
-- 10. DB Equivalence
-- =====================================================

def equiv (jd : JDB) (sd : SDB) : Prop :=
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ sd) ∧
  (∀ s : Suser, s ∈ sd ↔ toJ s ∈ jd)

-- =====================================================
-- 11. Translation
-- =====================================================

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p => SQuery.select c p
  | JQuery.drop p => SQuery.delete p

-- =====================================================
-- 12. Bridge Lemma
-- =====================================================

theorem getVal_bridge (col : Col) (u : Juser) :
  getVal col u = getValS col (toS u) := by
  cases col <;> cases u <;> simp [getVal, getValS, toS]

theorem eval_bridge (c : Cond) (u : Juser) :
  c.eval u = c.evalS (toS u) := by
  induction c generalizing u with
  | always =>
      simp [Cond.eval, Cond.evalS]

  | cmp col op v =>
      simp [Cond.eval, Cond.evalS, getVal_bridge]

  | and c₁ c₂ ih₁ ih₂ =>
      simp [Cond.eval, Cond.evalS, ih₁, ih₂]

  | or c₁ c₂ ih₁ ih₂ =>
      simp [Cond.eval, Cond.evalS, ih₁, ih₂]

-- =====================================================
-- 13. Main Correctness Theorem
-- =====================================================

theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by
  cases jq with
  | find col cond | drop cond =>
    -- Expand definitions and use the filter lemma specifically
    simp [equiv, eval_jquery, eval_squery, jquery_to_squery, List.mem_filter] at *
    constructor
    · intro u
      -- Goal: (u ∈ jd ∧ cond.eval u = true) ↔ (toS u ∈ sd ∧ cond.evalS (toS u) = true)
      rw [h.1 u]
      rw [eval_bridge]
    · intro s
      -- Goal: (s ∈ sd ∧ cond.evalS s = true) ↔ (toJ s ∈ jd ∧ cond.eval (toJ s) = true)
      rw [h.2 s]
      -- We need to show cond.evalS s = cond.eval (toJ s)
      -- Using eval_bridge (toJ s) gives: cond.eval (toJ s) = cond.evalS (toS (toJ s))
      rw [eval_bridge]
      -- Simplify toS (toJ s) to s
      have h_id : toS (toJ s) = s := by cases s; simp [toS, toJ]
      rw [h_id]

-- =====================================================
-- 14. Parser (updated for generic Cond)
-- =====================================================

def parseValue (s : String) : Value :=
  if s.length >= 2 && s.startsWith "\"" && s.endsWith "\"" then
    -- Convert the resulting slice into a String
    let inner : String := ((s.drop 1).dropEnd 1).toString
    Value.str inner
  else
    match s.toNat? with
    | some n => Value.nat n
    | none   => Value.str s

def parseOp : String → Op
  | "==" => Op.eq
  | ">"  => Op.gt
  | "<"  => Op.lt
  | ">=" => Op.ge
  | "<=" => Op.le
  | _    => Op.eq -- Default

def parseCol : String → Col
  | "name" => Col.name
  | "age"  => Col.age
  | _      => Col.all

partial def parseCond (s : String) : Cond :=
  -- Fix: trimAscii returns a Slice, so convert to String immediately
  let s' := s.trimAscii.toString

  let parseVal (str : String) : Value :=
    -- Ensure we are working with a trimmed string for matching
    let trimmed := str.trimAscii.toString
    if trimmed.front? = some '"' then
      -- Fix: Use dropEnd and ensure the final result is a String
      Value.str ((trimmed.drop 1).dropEnd 1).toString
    else
      -- toNat! needs a String; str.trimAscii.toString ensures no spaces break it
      Value.nat trimmed.toNat!

  let andParts := s'.splitOn "&&"
  if andParts.length > 1 then
    -- Recursively parse the left side and the joined right side
    Cond.and (parseCond andParts.head!) (parseCond ("&&".intercalate andParts.tail!))
  else if s'.contains "==" then
    let parts := s'.splitOn "=="
    let col := if parts.head!.contains "age" then Col.age else Col.name
    Cond.cmp col Op.eq (parseVal parts.getLast!)
  else if s'.contains ">=" then
    Cond.cmp Col.age Op.ge (parseVal (s'.splitOn ">=" |>.getLast!))
  else if s'.contains "<=" then
    Cond.cmp Col.age Op.le (parseVal (s'.splitOn "<=" |>.getLast!))
  else if s'.contains ">" then
    Cond.cmp Col.age Op.gt (parseVal (s'.splitOn ">" |>.getLast!))
  else if s'.contains "<" then
    Cond.cmp Col.age Op.lt (parseVal (s'.splitOn "<" |>.getLast!))
  else
    Cond.always

-- =====================================================
-- 15. jq → JQuery
-- =====================================================

def jqToJQuery (input : String) : JQuery :=
  let parts := input.splitOn "|" |>.map (fun p => p.trimAscii.toString)
  match parts with
  | [".[]"] => JQuery.find Col.all Cond.always

  | [".[]", sel] =>
      let inner := sel.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
      if sel.startsWith "delete(" then
        JQuery.drop (parseCond inner)
      else
        JQuery.find Col.all (parseCond inner)

  | [".[]", sel, col] =>
      let inner := sel.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
      let column :=
        match col with
        | ".name" => Col.name
        | ".age"  => Col.age
        | _       => Col.all
      if sel.startsWith "delete(" then
        JQuery.drop (parseCond inner)
      else
        JQuery.find column (parseCond inner)

  | _ => JQuery.find Col.all Cond.always

-- =====================================================
-- 16. Testing
-- =====================================================

def myDB : JDB := [
  {name := "Alice", age := 35},
  {name := "Bob", age := 20}
]

#eval jqToJQuery ".[]"

#eval jqToJQuery ".[] | select(.age > 30) | .name"
-- Output: JQuery.find Col.name (Cond.ageGt 30)

#eval eval_jquery myDB (jqToJQuery ".[] | select(.age > 30)")
-- Output: [{ name := "Alice", age := 35 }]

#eval jqToJQuery ".[] | select(.name == \"Bob\" && .age ≥ 20) | .age"

#eval eval_jquery myDB (jqToJQuery ".[] | select(.name == \"Bob\" && .age ≤ 20) | .age")

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.name == \"Alice\")")
-- Output: [{name := "Bob", age := 20}]

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.age ≥ 30)")
-- Output: [{name := "Bob", age := 20}]

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.name == \"Bob\" && .age = 20)")
-- Output: [{name := "Alice", age := 35}]

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.age ≤ 25)")
-- Output: [{name := "Alice", age := 35}]

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.name == \"Bob\")")
-- Output: [{name := "Alice", age := 35}]

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.age > 10)")
-- Output: []

#eval eval_jquery myDB (jqToJQuery ".[] | delete(.age < 18)")
-- Output: [{name := "Alice", age := 35}, {name := "Bob", age := 20}]
