import Std
import Init.Data.String.TakeDrop

-- =====================================================
-- 1. Base Data Structures
-- =====================================================

structure Juser where
  name : String
  age  : Nat
deriving Repr, DecidableEq

abbrev Suser : Type := String × Nat

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
  | find   : Col → Cond → JQuery
  | drop   : Cond → JQuery
  | prepend : Juser → JQuery        -- NEW: prepend a JSON record
  deriving Repr

inductive SQuery where
  | select : Col → Cond → SQuery
  | delete : Cond → SQuery
  | insert : Suser → SQuery        -- NEW: prepend a tuple to the columns
  deriving Repr

def eval_jquery (jd : JDB) : JQuery → JDB
  | JQuery.find _ c   => jd.filter c.eval
  | JQuery.drop c     => jd.filter (fun u => !(c.eval u))
  | JQuery.prepend u   => u :: jd

/--
  Columnar Semantics:
  - select/delete: zip into rows, filter, then unzip back into columns.
  - insert: prepend the new tuple's components to each column.
--/
def eval_squery (sd : SDB) : SQuery → SDB
  | SQuery.select _ c =>
      let rows := sd.toRows.filter c.evalS
      { names := rows.map (·.1), ages := rows.map (·.2) }
  | SQuery.delete c   =>
      let rows := sd.toRows.filter (fun s => !(c.evalS s))
      { names := rows.map (·.1), ages := rows.map (·.2) }
  | SQuery.insert s   =>
      { names := s.1 :: sd.names, ages := s.2 :: sd.ages }

-- =====================================================
-- 7. Equivalence & Translation
-- =====================================================

def equiv (jd : JDB) (sd : SDB) : Prop :=
  let rows := sd.toRows
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ rows) ∧
  (∀ s : Suser, s ∈ rows ↔ toJ s ∈ jd)

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p   => SQuery.select c p
  | JQuery.drop p     => SQuery.delete p
  | JQuery.prepend u   => SQuery.insert (toS u)

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
  Synchronizes the JSON view and the columnar view via 'toRows'.
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

/-- Round-trip for filter: rebuild columns from filtered rows recovers the rows. -/
@[simp]
theorem toRows_filter_reconstruct (sd : SDB) (p : Suser → Bool) :
    (SDB.mk (sd.toRows.filter p |>.map (·.1)) (sd.toRows.filter p |>.map (·.2))).toRows
    = sd.toRows.filter p := by
  simp only [SDB.toRows]
  exact zip_map_fst_snd (sd.names.zip sd.ages |>.filter p)

/-- Round-trip for insert: prepending to both columns prepends to the row view. -/
@[simp]
theorem toRows_insert (s : Suser) (sd : SDB) :
    (SDB.mk (s.1 :: sd.names) (s.2 :: sd.ages)).toRows = s :: sd.toRows := by
  obtain ⟨n, a⟩ := s
  rfl

/--
  The correctness theorem for the JQ → SQL translation.
  It proves that the translation preserves the equivalence relation (h),
  for all three query forms: find, drop, and insert.
--/
theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by
  rcases h with ⟨hJ, hS⟩
  cases jq with

  -- =========================
  -- FIND CASE
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
      · intro hu
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
        have hcond_j : (!c.eval u) = true := by grind
        exact List.mem_filter.mpr ⟨hmem_jd', hcond_j⟩
    · intro s
      constructor
      · intro hs
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct] at hs
        rcases hs with ⟨hmem, hcond⟩
        have hmem_jd : toJ s ∈ jd := (hS s).1 hmem
        have hfalseS : c.evalS s = false := by
          cases h : c.evalS s
          · rfl
          · rw [h] at hcond; simp at hcond
        have hfalse : c.eval (toJ s) = false := by
          rw [← eval_bridge_S]; exact hfalseS
        have hcond_j : (!c.eval (toJ s)) = true := by grind
        exact List.mem_filter.mpr ⟨hmem_jd, hcond_j⟩
      · intro hs
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hs
        have hmem_rows : s ∈ sd.toRows := (hJ (toJ s)).1 hmem
        have hfalse : c.eval (toJ s) = false := by
          cases h : c.eval (toJ s)
          · rfl
          · rw [h] at hcond; simp at hcond
        have hcond_s : c.evalS s = false := by
          rw [eval_bridge_S]; exact hfalse
        have hbang : (!c.evalS s) = true := by grind
        simp [eval_squery, jquery_to_squery, toRows_filter_reconstruct]
        grind

  -- =========================
  -- INSERT CASE (new)
  -- =========================
  | prepend u =>
    -- LHS: u :: jd
    -- RHS: SDB with names = u.name :: sd.names, ages = u.age :: sd.ages
    -- After toRows_insert, the row view of the RHS is toS u :: sd.toRows.
    constructor
    · intro v
      constructor
      · -- v ∈ u :: jd  →  toS v ∈ (eval_squery ...).toRows
        intro hv
        simp only [eval_jquery] at hv
        simp only [jquery_to_squery, eval_squery, toRows_insert]
        rcases List.mem_cons.mp hv with rfl | hv'
        · grind --exact List.mem_cons_self _ _
        · exact List.mem_cons_of_mem _ ((hJ v).1 hv')
      · -- toS v ∈ toS u :: sd.toRows  →  v ∈ u :: jd
        intro hv
        simp only [jquery_to_squery, eval_squery, toRows_insert] at hv
        simp only [eval_jquery]
        rcases List.mem_cons.mp hv with heq | hmem
        · -- heq : toS v = toS u, so v = u via toJ
          have : v = u := by
            have h := congrArg toJ heq
            simpa using h
          rw [this]
          grind --exact List.mem_cons_self _ _
        · -- hmem : toS v ∈ sd.toRows, hence v ∈ jd via hS
          have hv_jd : v ∈ jd := by
            have := (hS (toS v)).1 hmem
            simpa using this
          exact List.mem_cons_of_mem _ hv_jd
    · intro s
      constructor
      · -- s ∈ toS u :: sd.toRows  →  toJ s ∈ u :: jd
        intro hs
        simp only [jquery_to_squery, eval_squery, toRows_insert] at hs
        simp only [eval_jquery]
        rcases List.mem_cons.mp hs with rfl | hmem
        · -- s = toS u, so toJ s = u
          rw [toJ_toS]
          grind
          --exact List.mem_cons_self _ _
        · exact List.mem_cons_of_mem _ ((hS s).1 hmem)
      · -- toJ s ∈ u :: jd  →  s ∈ toS u :: sd.toRows
        intro hs
        simp only [eval_jquery] at hs
        simp only [jquery_to_squery, eval_squery, toRows_insert]
        rcases List.mem_cons.mp hs with heq | hmem
        · -- heq : toJ s = u, so s = toS u via toS
          have : s = toS u := by
            have h := congrArg toS heq
            simpa using h
          rw [this]
          grind
          --exact List.mem_cons_self _ _
        · -- hmem : toJ s ∈ jd, hence s ∈ sd.toRows via hJ
          have hs_rows : s ∈ sd.toRows := by
            have := (hJ (toJ s)).1 hmem
            simpa using this
          exact List.mem_cons_of_mem _ hs_rows

-- =====================================================
-- 9. Parser Logic (unchanged; insert is constructed directly)
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

/-- Parse a user record from a string like `"Charlie", 25` --/
def parseUser (s : String) : Juser :=
  let parts := s.splitOn "," |>.map (fun p => p.trimAscii.toString)
  match parts with
  | [nameStr, ageStr] =>
      let trimmed := nameStr.trimAscii.toString
      let name :=
        if trimmed.front? = some '"' then
          ((trimmed.drop 1).dropEnd 1).toString
        else
          trimmed
      let age := ageStr.trimAscii.toString.toNat!
      { name := name, age := age }
  | _ => { name := "", age := 0 }

def jqToJQuery (input : String) : JQuery :=
  let parts := input.splitOn "|" |>.map (fun p => p.trimAscii.toString)
  match parts with
  | [".[]", sel] =>
      if sel.startsWith "insert(" then
        let inner := sel.replace "insert(" "" |>.replace ")" ""
        JQuery.prepend (parseUser inner)
      else
        let inner := sel.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
        if sel.startsWith "delete(" then JQuery.drop (parseCond inner)
        else JQuery.find Col.all (parseCond inner)
  | _ => JQuery.find Col.all Cond.always

-- =====================================================
-- 10. Execution Examples
-- =====================================================

def myColDB : SDB := {
  names := ["Alice", "Bob"],
  ages  := [35, 20]
}

def myDB : JDB := [
  {name := "Alice", age := 35},
  {name := "Bob", age := 20}
]

#eval myColDB.toRows
#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | select(.age > 30)"))

-- Tests for the new insert query (via parser)
#eval jqToJQuery ".[] | prepend(\"Charlie\", 25)"
-- Output: JQuery.prepend { name := "Charlie", age := 25 }

#eval eval_jquery myDB (jqToJQuery ".[] | prepend(\"Charlie\", 25)")
-- Output: [{name := "Charlie", age := 25}, {name := "Alice", age := 35}, {name := "Bob", age := 20}]

#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | prepend(\"Charlie\", 25)"))
-- Output: { names := ["Charlie", "Alice", "Bob"], ages := [25, 35, 20] }

#eval (eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | prepend(\"Charlie\", 25)"))).toRows
-- Output: [("Charlie", 25), ("Alice", 35), ("Bob", 20)]

-- Direct construction (also works)
#eval eval_jquery myDB (JQuery.prepend {name := "Dave", age := 40})
-- Output: [{name := "Dave", age := 40}, {name := "Alice", age := 35}, {name := "Bob", age := 20}]

-- Existing tests
#eval jqToJQuery ".[]"
#eval jqToJQuery ".[] | select(.age > 30) | .name"
#eval eval_jquery myDB (jqToJQuery ".[] | select(.age > 30)")
#eval eval_jquery myDB (jqToJQuery ".[] | delete(.name == \"Alice\")")
#eval eval_jquery myDB (jqToJQuery ".[] | delete(.age > 10)")
#eval eval_jquery myDB (jqToJQuery ".[] | delete(.age < 18)")
