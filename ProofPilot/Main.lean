import Std

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
-- 2. Conversion and Projections
-- =====================================================

def toS (u : Juser) : Suser := (u.name, u.age)
def toJ (s : Suser) : Juser := {name := s.1, age := s.2}

-- =====================================================
-- 3. Schema + Result
-- =====================================================

inductive Col where
  | name | age | all
  deriving Repr, DecidableEq

-- =====================================================
-- 4. Condition Language (shared core)
-- =====================================================

inductive Cond where
  | always : Cond
  | ageGt  : Nat → Cond
  | ageLt  : Nat → Cond
  | ageEq  : Nat → Cond
  | ageGe  : Nat → Cond
  | ageLe  : Nat → Cond
  | nameEq : String → Cond
  | and    : Cond → Cond → Cond
  deriving Repr, Inhabited

def Cond.eval : Cond → Juser → Bool
  | Cond.always, _ => true
  | Cond.ageGt n, u  => u.age > n
  | Cond.ageLt n, u  => u.age < n
  | Cond.ageEq n, u  => u.age = n
  | Cond.ageGe n, u  => u.age ≥ n
  | Cond.ageLe n, u  => u.age ≤ n
  | Cond.nameEq s, u => u.name = s
  | Cond.and c₁ c₂, u => c₁.eval u && c₂.eval u

def Cond.evalS : Cond → Suser → Bool
  | c, (n, a) => c.eval { name := n, age := a }

-- =====================================================
-- 5. Query Languages
-- =====================================================

inductive JQuery where
  | find   : Col → Cond → JQuery
  | delete : Cond → JQuery
  deriving Repr

inductive SQuery where
  | select : Col → Cond → SQuery
  | drop   : Cond → SQuery
  deriving Repr

-- =====================================================
-- 6. Database Semantics
-- =====================================================

def eval_jquery : JDB → JQuery → JDB
  | jd, JQuery.find _ c   => jd.filter c.eval
  | jd, JQuery.delete c   => jd.filter (fun u => ¬ c.eval u)

def eval_squery : SDB → SQuery → SDB
  | sd, SQuery.select _ c => sd.filter (fun s => c.evalS s)
  | sd, SQuery.drop c     => sd.filter (fun s => ¬ c.evalS s)

-- =====================================================
-- 7. Equivalence of DBs
-- =====================================================

def equiv (jd : JDB) (sd : SDB) : Prop :=
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ sd) ∧
  (∀ s : Suser, s ∈ sd ↔ toJ s ∈ jd)

-- =====================================================
-- 8. Translation
-- =====================================================

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p => SQuery.select c p
  | JQuery.delete p => SQuery.drop p

-- =====================================================
-- 9. Key Lemma (filter preservation)
-- =====================================================

theorem eval_bridge (c : Cond) (u : Juser) :
  c.eval u = c.evalS (toS u) := by
  simp [Cond.evalS, toS]

theorem query_equiv (jd: JDB) (sd: SDB) (jq: JQuery) (h: equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by
  -- Deconstruct the equivalence hypothesis
  cases h with | intro h_j_to_s h_s_to_j =>
    constructor
    · -- Direction 1: u ∈ eval_jquery jd jq ↔ toS u ∈ eval_squery sd (jquery_to_squery jq)
      intro u
      cases jq with
      | find col cond =>
          simp [eval_jquery, eval_squery, jquery_to_squery, List.mem_filter]
          rw [h_j_to_s, eval_bridge]
      | delete cond =>
          simp [eval_jquery, eval_squery, jquery_to_squery, List.mem_filter]
          rw [h_j_to_s, eval_bridge]
    · -- Direction 2: s ∈ eval_squery sd (jquery_to_squery jq) ↔ toJ s ∈ eval_jquery jd jq
      intro s
      cases jq with
      | find col cond =>
          simp [eval_jquery, eval_squery, jquery_to_squery, List.mem_filter]
          -- Use eval_bridge but targeting the toJ s conversion
          let u := toJ s
          have hb : cond.evalS s = cond.eval (toJ s) := by
            cases s; simp [Cond.evalS, toJ]
          rw [h_s_to_j, hb]
      | delete cond =>
          simp [eval_jquery, eval_squery, jquery_to_squery, List.mem_filter]
          have hb : cond.evalS s = cond.eval (toJ s) := by
            cases s; simp [Cond.evalS, toJ]
          rw [h_s_to_j, hb]

-- =====================================================
-- 10. String-to-Query Parser (The "jq" Bridge)
-- =====================================================

partial def parseCond (s : String) : Cond :=
  let s' := s.trimAscii.toString

  -- 1. Handle logical AND (Recursive Case)
  -- If splitOn returns more than 1 part, the delimiter exists.
  let andParts := s'.splitOn "&&"
  if andParts.length > 1 then
    let left := andParts.head!.trimAscii.toString
    let right := "&&".intercalate andParts.tail! |>.trimAscii.toString
    Cond.and (parseCond left) (parseCond right)

  -- 2. Handle Comparisons (Base Cases)
  -- We use splitOn for multi-char tokens to ensure they exist.

  else if (s'.splitOn ">=").length > 1 || (s'.splitOn "≥").length > 1 then
    let delim := if (s'.splitOn ">=").length > 1 then ">=" else "≥"
    let val := (s'.splitOn delim |>.getLast!).trimAscii.toString.toNat!
    Cond.ageGe val

  else if (s'.splitOn "<=").length > 1 || (s'.splitOn "≤").length > 1 then
    let delim := if (s'.splitOn "<=").length > 1 then "<=" else "≤"
    let val := (s'.splitOn delim |>.getLast!).trimAscii.toString.toNat!
    Cond.ageLe val

  else if s'.contains '>' then
    let val := (s'.splitOn ">" |>.getLast!).trimAscii.toString.toNat!
    Cond.ageGt val

  else if s'.contains '<' then
    let val := (s'.splitOn "<" |>.getLast!).trimAscii.toString.toNat!
    Cond.ageLt val

  else if (s'.splitOn "==").length > 1 then
    let val := (s'.splitOn "==" |>.getLast!).trimAscii
    let raw := val.toString
    let cleanVal :=
      if raw.startsWith "\"" || raw.startsWith "'" then
        val.drop 1 |>.dropEnd 1 |>.toString
      else raw
    Cond.nameEq cleanVal

  else
    Cond.always

/--
  Converts jq-style pipeline string into JQuery.
  Logic remains the same, ensuring compatibility with standard String functions.
-/
def jqToJQuery (input : String) : JQuery :=
  let parts := input.splitOn "|" |>.map (fun p => p.trimAscii.toString)
  match parts with
  | [".[]"] => JQuery.find Col.all Cond.always

  | [".[]", sel] =>
      let op := sel.trimAscii.toString
      let inner := op.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
                     |>.replace ".age" "" |>.replace ".name" ""
      if op.startsWith "delete(" then
        JQuery.delete (parseCond inner)
      else
        JQuery.find Col.all (parseCond inner)

  | [".[]", sel, col] =>
      let op := sel.trimAscii.toString
      let inner := op.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
                     |>.replace ".age" "" |>.replace ".name" ""
      if op.startsWith "delete(" then
        JQuery.delete (parseCond inner)
      else
        let column := match col.trimAscii.toString with
          | ".name" => Col.name
          | ".age"  => Col.age
          | _       => Col.all
        JQuery.find column (parseCond inner)

  | _ => JQuery.find Col.all Cond.always

-- =====================================================
-- 7. Testing
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
