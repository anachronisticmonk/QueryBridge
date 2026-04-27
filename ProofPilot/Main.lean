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
-- 6. Query Languages, Result Types & Semantics
-- =====================================================

inductive JQuery where
  | find    : Col → Cond → JQuery
  | drop    : Cond → JQuery
  | prepend : Juser → JQuery        -- prepend a JSON record
  | clear   : JQuery                -- empty the database
  | count   : JQuery                -- AGGREGATE: number of rows
  | project : Col → Cond → JQuery   -- SELECT col FROM ... WHERE cond
  deriving Repr

inductive SQuery where
  | select   : Col → Cond → SQuery
  | delete   : Cond → SQuery
  | insert   : Suser → SQuery       -- prepend a tuple to the columns
  | truncate : SQuery               -- empty all columns
  | count    : SQuery               -- AGGREGATE: COUNT(*) — number of rows
  | project  : Col → Cond → SQuery  -- SELECT col FROM ... WHERE cond
  deriving Repr

/--
  A query result is one of:
  - a database (for transformation queries),
  - a scalar Nat (for aggregate queries like count),
  - a list of values (for column projection: SELECT col FROM ...).
  Both eval functions return these wrappers, so DB-shaped, scalar-shaped,
  and column-shaped queries can coexist in one query language.
--/
inductive JResult where
  | db   : JDB → JResult
  | num  : Nat → JResult
  | vals : List Value → JResult
  deriving Repr

inductive SResult where
  | db   : SDB → SResult
  | num  : Nat → SResult
  | vals : List Value → SResult
  deriving Repr

def eval_jquery (jd : JDB) : JQuery → JResult
  | JQuery.find _ c     => JResult.db (jd.filter c.eval)
  | JQuery.drop c       => JResult.db (jd.filter (fun u => !(c.eval u)))
  | JQuery.prepend u    => JResult.db (u :: jd)
  | JQuery.clear        => JResult.db []
  | JQuery.count        => JResult.num jd.length
  | JQuery.project col c => JResult.vals ((jd.filter c.eval).map (getVal col))

/--
  Columnar Semantics:
  - select/delete: zip into rows, filter, then unzip back into columns.
  - insert: prepend the new tuple's components to each column.
  - truncate: empty both columns.
  - count: number of rows after the columnar discipline (toRows length).
    Using sd.toRows.length rather than sd.names.length / sd.ages.length
    is what makes the aggregate well-defined when the columns differ in
    length — only matched-up tuples count as a "row".
  - project: filter rows then extract the column. Goes through toRows
    so projection respects the columnar discipline (mismatched columns
    contribute no rows to project from).
--/
def eval_squery (sd : SDB) : SQuery → SResult
  | SQuery.select _ c =>
      let rows := sd.toRows.filter c.evalS
      SResult.db { names := rows.map (·.1), ages := rows.map (·.2) }
  | SQuery.delete c   =>
      let rows := sd.toRows.filter (fun s => !(c.evalS s))
      SResult.db { names := rows.map (·.1), ages := rows.map (·.2) }
  | SQuery.insert s   =>
      SResult.db { names := s.1 :: sd.names, ages := s.2 :: sd.ages }
  | SQuery.truncate   =>
      SResult.db { names := [], ages := [] }
  | SQuery.count      =>
      SResult.num sd.toRows.length
  | SQuery.project col c =>
      SResult.vals ((sd.toRows.filter c.evalS).map (getValS col))

-- =====================================================
-- 7. Equivalence Relations & Translation
-- =====================================================

/-- Set-membership equivalence: every JSON record corresponds to a row. --/
def equiv (jd : JDB) (sd : SDB) : Prop :=
  let rows := sd.toRows
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ rows) ∧
  (∀ s : Suser, s ∈ rows ↔ toJ s ∈ jd)

/-- Permutation equivalence: tracks element MULTIPLICITY, not just
    membership. Strictly stronger than `equiv`. Required for any
    aggregate that isn't set-functional (count, sum, average, …). --/
def permEquiv (jd : JDB) (sd : SDB) : Prop :=
  List.Perm (jd.map toS) sd.toRows

/-- Equivalence on query results: dispatch by case.
    - Two `db` results compare under `equiv`.
    - Two `num` results compare with `=`.
    - Two `vals` results compare under `List.Perm` (permutation), since
      projection through a permuted row list yields a permuted value
      list — the multiset of column values is what's preserved across
      representations, not the order.
    - Mismatched constructors are `False`. --/
def result_equiv : JResult → SResult → Prop
  | JResult.db jd,    SResult.db sd    => equiv jd sd
  | JResult.num n₁,   SResult.num n₂   => n₁ = n₂
  | JResult.vals v₁,  SResult.vals v₂  => List.Perm v₁ v₂
  | _, _ => False

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p     => SQuery.select c p
  | JQuery.drop p       => SQuery.delete p
  | JQuery.prepend u    => SQuery.insert (toS u)
  | JQuery.clear        => SQuery.truncate
  | JQuery.count        => SQuery.count
  | JQuery.project c p  => SQuery.project c p

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

@[simp]
theorem toRows_insert (s : Suser) (sd : SDB) :
    (SDB.mk (s.1 :: sd.names) (s.2 :: sd.ages)).toRows = s :: sd.toRows := by
  obtain ⟨n, a⟩ := s
  rfl

/-- Permutation equivalence implies set equivalence. The DB-returning
    cases of `query_equiv` are inherited from this fact. --/
theorem permEquiv_implies_equiv {jd : JDB} {sd : SDB} (h : permEquiv jd sd) :
    equiv jd sd := by
  unfold permEquiv at h
  refine ⟨?_, ?_⟩
  · intro u
    constructor
    · intro hu
      have h1 : toS u ∈ jd.map toS := List.mem_map_of_mem hu
      exact h.mem_iff.mp h1
    · intro hu
      have h1 : toS u ∈ jd.map toS := h.mem_iff.mpr hu
      obtain ⟨v, hv, hvu⟩ := List.mem_map.mp h1
      have heq : v = u := by
        have := congrArg toJ hvu
        simpa using this
      exact heq ▸ hv
  · intro s
    constructor
    · intro hs
      have h1 : s ∈ jd.map toS := h.mem_iff.mpr hs
      obtain ⟨v, hv, hvs⟩ := List.mem_map.mp h1
      have : toJ s = v := by
        have h2 := congrArg toJ hvs
        simpa using h2.symm
      exact this ▸ hv
    · intro hs
      have h1 : toS (toJ s) ∈ jd.map toS := List.mem_map_of_mem hs
      have h2 : toS (toJ s) = s := toS_toJ s
      rw [h2] at h1
      exact h.mem_iff.mp h1

/--
  Unified correctness theorem for the JQ → SQL translation.
  Under permutation equivalence, executing any query (transformation
  or aggregate) on jd and the translated query on sd yields equivalent
  results, where equivalence is dispatched by result kind.
--/
theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : permEquiv jd sd) :
    result_equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by
  -- Existing DB cases need only set equivalence; derive it from permEquiv.
  have hset : equiv jd sd := permEquiv_implies_equiv h
  rcases hset with ⟨hJ, hS⟩
  cases jq with

  -- =========================
  -- FIND CASE
  -- =========================
  | find col c =>
    -- Goal reduces to `equiv (jd.filter c.eval) {…}` after unfolding result_equiv.
    show equiv _ _
    constructor
    · intro u
      constructor
      · intro hu
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hu
        have hmem_rows : toS u ∈ sd.toRows := (hJ u).1 hmem
        have hcond_rows : c.evalS (toS u) = true := by
          simpa [eval_bridge] using hcond
        simp [toRows_filter_reconstruct]
        exact ⟨hmem_rows, hcond_rows⟩
      · intro hu
        simp [toRows_filter_reconstruct] at hu
        rcases hu with ⟨hmem, hcond⟩
        have hmem_jd : toJ (toS u) ∈ jd := (hS (toS u)).1 hmem
        have hmem_jd' : u ∈ jd := by simpa using hmem_jd
        have hcond_j : c.eval u = true := by
          simpa [eval_bridge] using hcond
        exact List.mem_filter.mpr ⟨hmem_jd', hcond_j⟩
    · intro s
      constructor
      · intro hs
        simp [toRows_filter_reconstruct] at hs
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
        simp [toRows_filter_reconstruct]
        exact ⟨hmem_rows, hcond_s⟩

  -- =========================
  -- DROP CASE
  -- =========================
  | drop c =>
    show equiv _ _
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
        simp [toRows_filter_reconstruct]
        grind
      · intro hu
        simp [toRows_filter_reconstruct] at hu
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
        simp [toRows_filter_reconstruct] at hs
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
        simp [toRows_filter_reconstruct]
        grind

  -- =========================
  -- PREPEND CASE
  -- =========================
  | prepend u =>
    show equiv _ _
    constructor
    · intro v
      constructor
      · intro hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · simp [toRows_insert]
        · simp [toRows_insert]
          right; exact (hJ v).1 hv'
      · intro hv
        simp [toRows_insert] at hv
        rcases hv with heq | hmem
        · have : v = u := by
            have h := congrArg toJ heq
            simpa using h
          rw [this]; exact List.mem_cons_self
        · have hv_jd : v ∈ jd := by
            have := (hS (toS v)).1 hmem
            simpa using this
          exact List.mem_cons_of_mem _ hv_jd
    · intro s
      constructor
      · intro hs
        simp [toRows_insert] at hs
        rcases hs with rfl | hmem
        · rw [toJ_toS]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((hS s).1 hmem)
      · intro hs
        rcases List.mem_cons.mp hs with heq | hmem
        · have : s = toS u := by
            have h := congrArg toS heq
            simpa using h
          simp [toRows_insert]; left; exact this
        · simp [toRows_insert]
          right
          have := (hJ (toJ s)).1 hmem
          simpa using this

  -- =========================
  -- CLEAR CASE
  -- =========================
  | clear =>
    show equiv _ _
    refine ⟨?_, ?_⟩
    · intro u; simp [SDB.toRows]
    · intro s; simp [SDB.toRows]

  -- =========================
  -- COUNT CASE (aggregate)
  -- =========================
  | count =>
    -- Goal reduces to a Nat equality after unfolding result_equiv.
    show jd.length = sd.toRows.length
    -- permEquiv gives Perm (jd.map toS) sd.toRows.
    -- Perm preserves length, and map preserves length, so we chain:
    --   jd.length = (jd.map toS).length = sd.toRows.length
    have h1 : (jd.map toS).length = sd.toRows.length := h.length_eq
    rw [List.length_map] at h1
    exact h1

  -- =========================
  -- PROJECT CASE (column projection → List Value)
  -- =========================
  | project col c =>
    -- Goal reduces to:
    --   List.Perm ((jd.filter c.eval).map (getVal col))
    --             ((sd.toRows.filter c.evalS).map (getValS col))
    --
    -- Strategy:
    --   Step 1 — Bridge equality: rewrite the JSON-side filter+map so it
    --     factors through `jd.map toS` and the SQL-side projector. This
    --     lets us state both sides over the same predicate (c.evalS) and
    --     the same projector (getValS col).
    --   Step 2 — Perm transport: permEquiv gives Perm (jd.map toS) sd.toRows,
    --     and Perm is preserved by `.filter p` and `.map f`.
    show List.Perm ((jd.filter c.eval).map (getVal col))
                   ((sd.toRows.filter c.evalS).map (getValS col))
    -- Step 1: Bridge — proven by induction on jd.
    have key : ∀ (l : List Juser),
        (l.filter c.eval).map (getVal col) =
        ((l.map toS).filter c.evalS).map (getValS col) := by
      intro l
      induction l with
      | nil => rfl
      | cons head tail ih =>
        have heq  : c.eval head = c.evalS (toS head)         := eval_bridge c head
        have hgv  : getVal col head = getValS col (toS head) := getVal_bridge col head
        simp only [List.map_cons, List.filter_cons]
        cases hc : c.eval head with
        | true =>
          have hc' : c.evalS (toS head) = true := heq ▸ hc
          simp [hc', List.map_cons, ih]
        | false =>
          have hc' : c.evalS (toS head) = false := heq ▸ hc
          simp [hc', ih]
    rw [key jd]
    -- Step 2: Apply permutation transport — filter and map preserve Perm.
    exact (h.filter c.evalS).map (getValS col)

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
      else if sel == "clear()" || sel == "clear" then
        JQuery.clear
      else if sel == "count()" || sel == "count" || sel == "length" then
        JQuery.count
      else if sel.startsWith "pick(" then
        -- pick(<col>, <cond>) — minimal projection syntax
        -- Examples: pick(name, .age > 30), pick(age, .age == 20)
        let inner := sel.replace "pick(" "" |>.replace ")" ""
        let parts := inner.splitOn "," |>.map (fun p => p.trimAscii.toString)
        match parts with
        | [colStr, condStr] =>
            let col :=
              if colStr == "name" then Col.name
              else if colStr == "age" then Col.age
              else Col.all
            JQuery.project col (parseCond condStr)
        | _ => JQuery.project Col.all Cond.always
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

-- DB-returning queries (results wrapped in JResult.db / SResult.db)
#eval eval_jquery myDB (jqToJQuery ".[] | select(.age > 30)")
-- Output: JResult.db [{ name := "Alice", age := 35 }]

#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | select(.age > 30)"))
-- Output: SResult.db { names := ["Alice"], ages := [35] }

#eval eval_jquery myDB (jqToJQuery ".[] | clear()")
-- Output: JResult.db []

#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | clear()"))
-- Output: SResult.db { names := [], ages := [] }

-- Aggregate queries (results wrapped in JResult.num / SResult.num)
#eval eval_jquery myDB (jqToJQuery ".[] | count")
-- Output: JResult.num 2

#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | count"))
-- Output: SResult.num 2

#eval eval_jquery myDB (jqToJQuery ".[] | length")
-- Output: JResult.num 2  (jq idiom)

#eval eval_jquery myDB JQuery.count
-- Output: JResult.num 2

#eval eval_squery myColDB SQuery.count
-- Output: SResult.num 2

-- Aggregate after a transformation (chain by re-feeding the DB)
#eval eval_jquery (myDB.filter (Cond.cmp Col.age Op.gt (Value.nat 30)).eval) JQuery.count
-- Output: JResult.num 1   (only Alice survives the filter)

-- Count after prepending a row
#eval eval_jquery ({name := "Charlie", age := 25} :: myDB) JQuery.count
-- Output: JResult.num 3

-- Count after clearing
#eval eval_jquery ([] : JDB) JQuery.count
-- Output: JResult.num 0

-- =========================
-- PROJECT (column selection): SELECT col FROM ... WHERE cond
-- =========================
-- These exercise the new JResult.vals constructor: results are lists
-- of Value (mixed strings/numbers depending on which column is picked).

-- SELECT name FROM users WHERE age > 30
#eval eval_jquery myDB (jqToJQuery ".[] | pick(name, .age > 30)")
-- Output: JResult.vals [Value.str "Alice"]

#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | pick(name, .age > 30)"))
-- Output: SResult.vals [Value.str "Alice"]

-- SELECT age FROM users WHERE age > 10  (every row qualifies)
#eval eval_jquery myDB (jqToJQuery ".[] | pick(age, .age > 10)")
-- Output: JResult.vals [Value.nat 35, Value.nat 20]

#eval eval_squery myColDB (jquery_to_squery (jqToJQuery ".[] | pick(age, .age > 10)"))
-- Output: SResult.vals [Value.nat 35, Value.nat 20]

-- SELECT name FROM users   (no filter — Cond.always)
#eval eval_jquery myDB (JQuery.project Col.name Cond.always)
-- Output: JResult.vals [Value.str "Alice", Value.str "Bob"]

#eval eval_squery myColDB (jquery_to_squery (JQuery.project Col.name Cond.always))
-- Output: SResult.vals [Value.str "Alice", Value.str "Bob"]

-- SELECT name FROM users WHERE name == "Bob"
#eval eval_jquery myDB (jqToJQuery ".[] | pick(name, .name == \"Bob\")")
-- Output: JResult.vals [Value.str "Bob"]

-- Project on empty DB → empty vals
#eval eval_jquery ([] : JDB) (JQuery.project Col.name Cond.always)
-- Output: JResult.vals []

-- Project after a filter that excludes everyone
#eval eval_jquery myDB (JQuery.project Col.name (Cond.cmp Col.age Op.gt (Value.nat 100)))
-- Output: JResult.vals []
