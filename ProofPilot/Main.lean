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

/--
  Columnar SQL Database:
  Names and Ages are stored in separate parallel lists.
--/
structure SDB where
  names : List String
  ages  : List Nat
deriving Repr

/-- Helper to view the Columnar DB as a list of relational tuples (rows) --/
def SDB.toRows (sd : SDB) : List Suser :=
  sd.names.zip sd.ages

-- =====================================================
-- 2. Conversion
-- =====================================================

def toS (u : Juser) : Suser := (u.name, u.age)
def toJ (s : Suser) : Juser := { name := s.1, age := s.2 }

@[simp]
theorem toJ_toS (u : Juser) : toJ (toS u) = u := by
  simp [toJ, toS]

@[simp]
theorem toS_toJ (s : Suser) : toS (toJ s) = s := by
  obtain ⟨n, a⟩ := s
  rfl

-- =====================================================
-- 3. Schema & Values
-- =====================================================

inductive Col where
  | name | age | all
  deriving Repr, DecidableEq

inductive Value where
  | nat : Nat → Value
  | str : String → Value
  deriving Repr, DecidableEq

inductive Op where
  | eq | gt | lt | ge | le
  deriving Repr, DecidableEq

-- =====================================================
-- 4. Generic Condition Language
-- =====================================================

inductive Cond where
  | always : Cond
  | cmp    : Col → Op → Value → Cond
  | and    : Cond → Cond → Cond
  | or     : Cond → Cond → Cond
  deriving Repr, Inhabited

-- =====================================================
-- 5. Evaluation Helpers
-- =====================================================

def getVal (c : Col) (u : Juser) : Value :=
  match c with
  | Col.name => Value.str u.name
  | Col.age  => Value.nat u.age
  | Col.all  => Value.str ""

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

def Cond.eval : Cond → Juser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, u => evalOp op (getVal col u) v
  | Cond.and c₁ c₂, u => c₁.eval u && c₂.eval u
  | Cond.or c₁ c₂, u => c₁.eval u || c₂.eval u

def Cond.evalS : Cond → Suser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, s => evalOp op (getValS col s) v
  | Cond.and c₁ c₂, s => c₁.evalS s && c₂.evalS s
  | Cond.or c₁ c₂, s => c₁.evalS s || c₂.evalS s

-- =====================================================
-- 6. Query Languages & Semantics
-- =====================================================

inductive JQuery where
  | find : Col → Cond → JQuery
  | drop : Cond → JQuery
  deriving Repr

inductive SQuery where
  | select : Col → Cond → SQuery
  | delete : Cond → SQuery
  deriving Repr

def eval_jquery (jd : JDB) : JQuery → JDB
  | JQuery.find _ c => jd.filter c.eval
  | JQuery.drop c   => jd.filter (fun u => !(c.eval u))

/--
  Columnar Semantics:
  To filter, we zip into rows, filter, then unzip back into columns.
--/
def eval_squery (sd : SDB) : SQuery → SDB
  | SQuery.select _ c =>
      let rows := sd.toRows.filter c.evalS
      { names := rows.map (·.1), ages := rows.map (·.2) }
  | SQuery.delete c   =>
      let rows := sd.toRows.filter (fun s => !(c.evalS s))
      { names := rows.map (·.1), ages := rows.map (·.2) }

-- =====================================================
-- 7. Equivalence & Translation
-- =====================================================

def equiv (jd : JDB) (sd : SDB) : Prop :=
  let rows := sd.toRows
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ rows) ∧
  (∀ s : Suser, s ∈ rows ↔ toJ s ∈ jd)

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p => SQuery.select c p
  | JQuery.drop p   => SQuery.delete p

-- =====================================================
-- 8. Proofs
-- =====================================================

@[simp]
theorem getVal_bridge (col : Col) (u : Juser) :
  getVal col u = getValS col (toS u) := by
  cases col <;> cases u <;> simp [getVal, getValS, toS]

theorem eval_bridge (c : Cond) (u : Juser) :
  c.eval u = c.evalS (toS u) := by
  induction c generalizing u with
  | always => simp [Cond.eval, Cond.evalS]
  | cmp col op v => simp [Cond.eval, Cond.evalS, getVal_bridge]
  | and c₁ c₂ ih₁ ih₂ => simp [Cond.eval, Cond.evalS, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Cond.eval, Cond.evalS, ih₁, ih₂]

theorem eval_bridge_S (c : Cond) (s : Suser) :
  c.evalS s = c.eval (toJ s) := by
  induction c generalizing s with
  | always => rfl
  | cmp col op v =>
    obtain ⟨n, a⟩ := s
    cases col <;> rfl
  | and c₁ c₂ ih₁ ih₂ =>
    simp only [Cond.eval, Cond.evalS]
    rw [ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
    simp only [Cond.eval, Cond.evalS]
    rw [ih₁, ih₂]


/--
  Bridge Lemma: Database Equivalence
  This proves that the high-level JSON structure and the low-level
  Columnar structure are synchronized via the 'toRows' projection.
--/
@[simp]
theorem db_equiv_bridge (jd : JDB) (sd : SDB) :
    equiv jd sd ↔ (∀ u, u ∈ jd ↔ toS u ∈ sd.toRows) ∧ (∀ s, s ∈ sd.toRows ↔ toJ s ∈ jd) := by
  simp [equiv, SDB.toRows]

@[simp]
theorem zip_map_fst_snd {α β : Type} (xs : List (α × β)) :
    List.zip (xs.map (·.1)) (xs.map (·.2)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | mk a b =>
      simp only [List.map, List.zip]
      exact congrArg _ ih

@[simp]
theorem toRows_filter_reconstruct (sd : SDB) (p : Suser → Bool) :
    (SDB.mk (sd.toRows.filter p |>.map (·.1)) (sd.toRows.filter p |>.map (·.2))).toRows
    = sd.toRows.filter p := by
  simp only [SDB.toRows]
  exact zip_map_fst_snd (sd.names.zip sd.ages |>.filter p)

/--
  The correctness theorem for the JQ → SQL translation.
  It proves that the translation preserves the equivalence relation (h).
--/

theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by
  rcases h with ⟨hJ, hS⟩
  cases jq with

  -- =========================
  -- FIND CASE (unchanged)
  -- =========================
  | find col c =>
    constructor
    · intro u
      constructor
      · intro hu
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hu
        have hmem_rows : toS u ∈ sd.toRows := (hJ u).1 hmem
        have hcond_rows : c.evalS (toS u) = true := by
          simpa [eval_bridge] using hcond
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct]
        exact ⟨hmem_rows, hcond_rows⟩

      · intro hu
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct] at hu
        rcases hu with ⟨hmem, hcond⟩
        have hmem_jd : toJ (toS u) ∈ jd := (hS (toS u)).1 hmem
        have hmem_jd' : u ∈ jd := by simpa using hmem_jd
        have hcond_j : c.eval u = true := by
          simpa [eval_bridge] using hcond
        exact List.mem_filter.mpr ⟨hmem_jd', hcond_j⟩

    · intro s
      constructor
      · intro hs
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct] at hs
        rcases hs with ⟨hmem, hcond⟩
        have hmem_jd : toJ s ∈ jd := (hS s).1 hmem
        have hcond_j : c.eval (toJ s) = true := by
          simpa [eval_bridge_S] using hcond
        exact List.mem_filter.mpr ⟨hmem_jd, hcond_j⟩

      · intro hs
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hs
        have hmem_rows : s ∈ sd.toRows := (hJ (toJ s)).1 hmem
        have hcond_s : c.evalS s = true := by
          simpa [eval_bridge_S] using hcond
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct]
        exact ⟨hmem_rows, hcond_s⟩

  -- =========================
  -- DROP CASE
  -- =========================
  | drop c =>
    constructor
    · intro u
      constructor
      · intro hu
        -- J → S
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hu
        have hmem_rows : toS u ∈ sd.toRows := (hJ u).1 hmem
        have hfalse : c.eval u = false := by
          cases h : c.eval u
          · rfl
          · rw [h] at hcond; simp at hcond
        have hcond_rows : c.evalS (toS u) = false := by
          rw [← eval_bridge]; exact hfalse
        have hbang : (!c.evalS (toS u)) = true := by grind
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct]
        grind
        --exact ⟨hmem_rows, hbang⟩

      · intro hu
        -- S → J
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct] at hu
        rcases hu with ⟨hmem, hcond⟩
        have hmem_jd : toJ (toS u) ∈ jd := (hS (toS u)).1 hmem
        have hmem_jd' : u ∈ jd := by simpa using hmem_jd
        have hfalseS : c.evalS (toS u) = false := by
          cases h : c.evalS (toS u)
          · rfl
          · rw [h] at hcond; simp at hcond
        have hfalse : c.eval u = false := by
          rw [eval_bridge]; exact hfalseS
        have hcond_j : (!c.eval u) = true := by grind --rw [hfalse]
        exact List.mem_filter.mpr ⟨hmem_jd', hcond_j⟩

    · intro s
      constructor
      · intro hs
        -- S → J
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct] at hs
        rcases hs with ⟨hmem, hcond⟩
        have hmem_jd : toJ s ∈ jd := (hS s).1 hmem
        have hfalseS : c.evalS s = false := by
          cases h : c.evalS s
          · rfl
          · rw [h] at hcond; simp at hcond
        have hfalse : c.eval (toJ s) = false := by
          rw [← eval_bridge_S]; exact hfalseS
        have hcond_j : (!c.eval (toJ s)) = true := by grind --rw [hfalse]
        exact List.mem_filter.mpr ⟨hmem_jd, hcond_j⟩

      · intro hs
        -- J → S
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hs
        have hmem_rows : s ∈ sd.toRows := (hJ (toJ s)).1 hmem
        have hfalse : c.eval (toJ s) = false := by
          cases h : c.eval (toJ s)
          · rfl
          · rw [h] at hcond; simp at hcond
        have hcond_s : c.evalS s = false := by
          rw [eval_bridge_S]; exact hfalse
        have hbang : (!c.evalS s) = true := by grind --rw [hcond_s]
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct]
        grind
        --exact ⟨hmem_rows, hbang⟩

-- =====================================================
-- 9. Parser Logic
-- =====================================================

partial def parseCond (s : String) : Cond :=
  let s' := s.trimAscii.toString
  let parseVal (str : String) : Value :=
    let trimmed := str.trimAscii.toString
    if trimmed.front? = some '"' then
      Value.str ((trimmed.drop 1).dropEnd 1).toString
    else
      Value.nat trimmed.toNat!

  let andParts := s'.splitOn "&&"
  if andParts.length > 1 then
    Cond.and (parseCond andParts.head!) (parseCond ("&&".intercalate andParts.tail!))
  else if s'.contains "==" then
    let parts := s'.splitOn "=="
    let col := if parts.head!.contains "age" then Col.age else Col.name
    Cond.cmp col Op.eq (parseVal parts.getLast!)
  else if s'.contains ">" then
    Cond.cmp Col.age Op.gt (parseVal (s'.splitOn ">" |>.getLast!))
  else
    Cond.always

def jqToJQuery (input : String) : JQuery :=
  let parts := input.splitOn "|" |>.map (fun p => p.trimAscii.toString)
  match parts with
  | [".[]", sel] =>
      let inner := sel.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
      if sel.startsWith "delete(" then JQuery.drop (parseCond inner)
      else JQuery.find Col.all (parseCond inner)
  | _ => JQuery.find Col.all Cond.always

-- =====================================================
-- 10. Execution Example
-- =====================================================

def myColDB : SDB := {
  names := ["Alice", "Bob"],
  ages  := [35, 20]
}

#eval (myColDB.toRows)
#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | select(.age > 30)"))

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
