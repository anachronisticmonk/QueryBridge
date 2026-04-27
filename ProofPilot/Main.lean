import Std
import Init.Data.String.TakeDrop

-- =====================================================
-- 1. Base Data Structures
-- =====================================================

structure Juser where
  name  : String
  age   : Nat
  email : String
deriving Repr, DecidableEq, BEq

/-- A SQL row. Encoded right-nested so that:
      s.1     = name
      s.2.1   = age
      s.2.2   = email
    This matches `toS`/`toJ` below and keeps destructuring uniform. --/
abbrev Suser : Type := String × Nat × String

abbrev JDB := List Juser

/--
  Columnar SQL Database:
  Names, ages, and emails are stored in separate parallel lists.
--/
structure SDB where
  names  : List String
  ages   : List Nat
  emails : List String
deriving Repr, DecidableEq, BEq

/-- 3-way zip: aligns three parallel columns into a list of triples.
    Length is bounded by the shortest of the three columns. --/
def zip3 {α β γ : Type} : List α → List β → List γ → List (α × β × γ)
  | a :: as, b :: bs, c :: cs => (a, b, c) :: zip3 as bs cs
  | _, _, _ => []

/-- Helper to view the Columnar DB as a list of relational triples (rows) --/
def SDB.toRows (sd : SDB) : List Suser :=
  zip3 sd.names sd.ages sd.emails

-- =====================================================
-- 2. Conversion
-- =====================================================

def toS (u : Juser) : Suser := (u.name, u.age, u.email)
def toJ (s : Suser) : Juser := { name := s.1, age := s.2.1, email := s.2.2 }

theorem toJ_toS (u : Juser) : toJ (toS u) = u := by
  simp [toJ, toS]

theorem toS_toJ (s : Suser) : toS (toJ s) = s := by
  obtain ⟨n, a, e⟩ := s
  rfl

-- =====================================================
-- 3. Schema & Values
-- =====================================================

inductive Col where
  | name | age | email | all
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
  | Col.name  => Value.str u.name
  | Col.age   => Value.nat u.age
  | Col.email => Value.str u.email
  | Col.all   => Value.str ""

def getValS (c : Col) (s : Suser) : Value :=
  match c, s with
  | Col.name,  (n, _, _) => Value.str n
  | Col.age,   (_, a, _) => Value.nat a
  | Col.email, (_, _, e) => Value.str e
  | Col.all,   _         => Value.str ""

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

/--
  Per-row update on a Juser. Replaces the column with the given value;
  type mismatches (e.g. setting `.name` to a Nat) are silently ignored
  and the row passes through unchanged.

  This "permissive" semantics keeps the proofs simple — no need for a
  typing judgment on Value vs Col — and matches how dynamically-typed
  query languages (jq, MongoDB) actually behave.
--/
def applyUpdate (col : Col) (v : Value) (u : Juser) : Juser :=
  match col, v with
  | Col.name,  Value.str s  => { u with name := s }
  | Col.age,   Value.nat n  => { u with age := n }
  | Col.email, Value.str s  => { u with email := s }
  | _, _                    => u   -- type mismatch or Col.all → no-op

/-- Per-row update on an Suser, mirroring `applyUpdate` on the SQL side. --/
def applyUpdateS (col : Col) (v : Value) (s : Suser) : Suser :=
  match col, v with
  | Col.name,  Value.str n => (n, s.2.1, s.2.2)
  | Col.age,   Value.nat a => (s.1, a, s.2.2)
  | Col.email, Value.str e => (s.1, s.2.1, e)
  | _, _                   => s    -- type mismatch or Col.all → no-op

/-- Per-row update gated by a condition. The natural unit for `modify`. --/
def applyUpdateIf (col : Col) (v : Value) (c : Cond) (u : Juser) : Juser :=
  if c.eval u then applyUpdate col v u else u

def applyUpdateIfS (col : Col) (v : Value) (c : Cond) (s : Suser) : Suser :=
  if c.evalS s then applyUpdateS col v s else s

-- =====================================================
-- 6. Query Languages, Result Types & Semantics
-- =====================================================

inductive JQuery where
  | find    : Col → Cond → JQuery
  | drop    : Cond → JQuery
  | prepend : Juser → JQuery               -- prepend a JSON record
  | clear   : JQuery                       -- empty the database
  | count   : JQuery                       -- AGGREGATE: number of rows
  | modify  : Col → Value → Cond → JQuery  -- jq's `map(if cond then .col = v else . end)`
  deriving Repr

inductive SQuery where
  | select   : Col → Cond → SQuery
  | delete   : Cond → SQuery
  | insert   : Suser → SQuery              -- prepend a tuple to the columns
  | truncate : SQuery                      -- empty all columns
  | count    : SQuery                      -- AGGREGATE: COUNT(*) — number of rows
  | update   : Col → Value → Cond → SQuery -- UPDATE … SET col = v WHERE cond
  deriving Repr

/--
  A query result is either a database (for transformation queries)
  or a scalar (for aggregate queries). Both eval functions return
  these wrappers, so DB-shaped queries and scalar-shaped queries
  can coexist in one query language.
--/
inductive JResult where
  | db  : JDB → JResult
  | num : Nat → JResult
deriving Repr, DecidableEq, BEq

inductive SResult where
  | db  : SDB → SResult
  | num : Nat → SResult
deriving Repr, DecidableEq, BEq

def eval_jquery (jd : JDB) : JQuery → JResult
  | JQuery.find _ c       => JResult.db (jd.filter c.eval)
  | JQuery.drop c         => JResult.db (jd.filter (fun u => !(c.eval u)))
  | JQuery.prepend u      => JResult.db (u :: jd)
  | JQuery.clear          => JResult.db []
  | JQuery.count          => JResult.num jd.length
  | JQuery.modify col v c => JResult.db (jd.map (applyUpdateIf col v c))

/--
  Columnar Semantics:
  - select/delete: zip into rows, filter, then unzip back into three columns.
  - insert: prepend the new tuple's components to each column.
  - truncate: empty all three columns.
  - count: number of rows after the columnar discipline (toRows length).
    Using sd.toRows.length rather than the individual column lengths
    is what makes the aggregate well-defined when columns differ in
    length — only matched-up triples count as a "row".
  - update: zip into rows, map per-row update over them, then unzip.
    Like select/delete, but uses `map` instead of `filter` so every row
    is preserved (just possibly modified).
--/
def eval_squery (sd : SDB) : SQuery → SResult
  | SQuery.select _ c =>
      let rows := sd.toRows.filter c.evalS
      SResult.db { names  := rows.map (·.1)
                   ages   := rows.map (·.2.1)
                   emails := rows.map (·.2.2) }
  | SQuery.delete c   =>
      let rows := sd.toRows.filter (fun s => !(c.evalS s))
      SResult.db { names  := rows.map (·.1)
                   ages   := rows.map (·.2.1)
                   emails := rows.map (·.2.2) }
  | SQuery.insert s   =>
      SResult.db { names  := s.1   :: sd.names
                   ages   := s.2.1 :: sd.ages
                   emails := s.2.2 :: sd.emails }
  | SQuery.truncate   =>
      SResult.db { names := [], ages := [], emails := [] }
  | SQuery.count      =>
      SResult.num sd.toRows.length
  | SQuery.update col v c =>
      let rows := sd.toRows.map (applyUpdateIfS col v c)
      SResult.db { names  := rows.map (·.1)
                   ages   := rows.map (·.2.1)
                   emails := rows.map (·.2.2) }

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

/-- Equivalence on query results: dispatch by case. Two `db` results
    compare under `equiv`; two `num` results compare with `=`;
    a mismatch (one db, one num) is `False`. --/
def result_equiv : JResult → SResult → Prop
  | JResult.db jd,  SResult.db sd  => equiv jd sd
  | JResult.num n₁, SResult.num n₂ => n₁ = n₂
  | _, _ => False

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p       => SQuery.select c p
  | JQuery.drop p         => SQuery.delete p
  | JQuery.prepend u      => SQuery.insert (toS u)
  | JQuery.clear          => SQuery.truncate
  | JQuery.count          => SQuery.count
  | JQuery.modify col v c => SQuery.update col v c

-- =====================================================
-- 8. Proofs
-- =====================================================

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
    obtain ⟨n, a, e⟩ := s
    cases col <;> rfl
  | and c₁ c₂ ih₁ ih₂ =>
    simp only [Cond.eval, Cond.evalS]
    rw [ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
    simp only [Cond.eval, Cond.evalS]
    rw [ih₁, ih₂]

theorem db_equiv_bridge (jd : JDB) (sd : SDB) :
    equiv jd sd ↔ (∀ u, u ∈ jd ↔ toS u ∈ sd.toRows) ∧ (∀ s, s ∈ sd.toRows ↔ toJ s ∈ jd) := by
  simp [equiv, SDB.toRows]

/-- Round-trip for 3-way zip: rebuilding three columns from a list of
    triples and zipping them back recovers the original triple list. --/
theorem zip3_map_components {α β γ : Type} (xs : List (α × β × γ)) :
    zip3 (xs.map (·.1)) (xs.map (·.2.1)) (xs.map (·.2.2)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b, c⟩ := x
    simp only [List.map, zip3]
    exact congrArg _ ih

theorem toRows_filter_reconstruct (sd : SDB) (p : Suser → Bool) :
    (SDB.mk (sd.toRows.filter p |>.map (·.1))
            (sd.toRows.filter p |>.map (·.2.1))
            (sd.toRows.filter p |>.map (·.2.2))).toRows
    = sd.toRows.filter p := by
  simp only [SDB.toRows]
  exact zip3_map_components (zip3 sd.names sd.ages sd.emails |>.filter p)

theorem toRows_insert (s : Suser) (sd : SDB) :
    (SDB.mk (s.1 :: sd.names) (s.2.1 :: sd.ages) (s.2.2 :: sd.emails)).toRows
    = s :: sd.toRows := by
  obtain ⟨n, a, e⟩ := s
  rfl

/-- Per-row update commutes with `toS`. -/
theorem applyUpdate_bridge (col : Col) (v : Value) (u : Juser) :
    applyUpdateS col v (toS u) = toS (applyUpdate col v u) := by
  obtain ⟨n, a, e⟩ := u
  cases col <;> cases v <;> simp [applyUpdate, applyUpdateS, toS]

/-- Conditional update commutes with `toS` (uses eval_bridge for the guard). -/
theorem applyUpdateIf_bridge (col : Col) (v : Value) (c : Cond) (u : Juser) :
    applyUpdateIfS col v c (toS u) = toS (applyUpdateIf col v c u) := by
  unfold applyUpdateIfS applyUpdateIf
  rw [← eval_bridge c u]
  cases h : c.eval u with
  | true  => simp [applyUpdate_bridge]
  | false => simp

/-- Round-trip for map: rebuild columns from a mapped row list recovers
    the rows. The `map` analogue of `toRows_filter_reconstruct`. -/
theorem toRows_map_reconstruct (sd : SDB) (f : Suser → Suser) :
    (SDB.mk ((sd.toRows.map f).map (·.1))
            ((sd.toRows.map f).map (·.2.1))
            ((sd.toRows.map f).map (·.2.2))).toRows
    = sd.toRows.map f := by
  simp only [SDB.toRows]
  exact zip3_map_components (zip3 sd.names sd.ages sd.emails |>.map f)

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
    · intro u; simp [SDB.toRows, zip3]
    · intro s; simp [SDB.toRows, zip3]

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
  -- MODIFY CASE (per-row update)
  -- =========================
  | modify col v c =>
    -- After unfolding result_equiv, the goal is equiv between:
    --   jd.map (applyUpdateIf col v c)                    (jq side)
    --   the SDB returned by eval_squery's `update` branch (SQL side)
    -- The SQL SDB's toRows reduces (via toRows_map_reconstruct) to
    --   sd.toRows.map (applyUpdateIfS col v c).
    --
    -- Strategy:
    --   Step 1 — Build a permEquiv between the two updated row lists,
    --     by chaining: bridge equality (toS commutes with the per-row
    --     updater) + permutation transport (Perm.map applied to h).
    --   Step 2 — Lift that permEquiv to equiv via the existing helper
    --     `permEquiv_implies_equiv`.
    show equiv _ _
    -- The result SDB's toRows is exactly sd.toRows.map (applyUpdateIfS …)
    -- by toRows_map_reconstruct (a simp lemma). Build a permEquiv to it.
    have hPerm : permEquiv (jd.map (applyUpdateIf col v c))
                  (SDB.mk
                    ((sd.toRows.map (applyUpdateIfS col v c)).map (·.1))
                    ((sd.toRows.map (applyUpdateIfS col v c)).map (·.2.1))
                    ((sd.toRows.map (applyUpdateIfS col v c)).map (·.2.2))) := by
      unfold permEquiv
      -- Goal: Perm ((jd.map (applyUpdateIf …)).map toS) (sdb'.toRows)
      -- Step 1a: rewrite the left to factor toS through the updater.
      have hbridge : (jd.map (applyUpdateIf col v c)).map toS
                   = (jd.map toS).map (applyUpdateIfS col v c) := by
        rw [List.map_map, List.map_map]
        congr 1; funext u
        exact (applyUpdateIf_bridge col v c u).symm
      -- Step 1b: rewrite the right via toRows_map_reconstruct.
      rw [hbridge, toRows_map_reconstruct]
      -- Step 1c: now both sides are `_.map (applyUpdateIfS …)` and we
      -- have Perm of the underlying lists from h.
      exact h.map (applyUpdateIfS col v c)
    exact permEquiv_implies_equiv hPerm

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

  -- Detect which column an LHS like `.age` or `.email` refers to.
  let detectCol (lhs : String) : Col :=
    if lhs.contains "email" then Col.email
    else if lhs.contains "age" then Col.age
    else Col.name

  let andParts := s'.splitOn "&&"
  if andParts.length > 1 then
    Cond.and (parseCond andParts.head!) (parseCond ("&&".intercalate andParts.tail!))
  else if s'.contains "==" then
    let parts := s'.splitOn "=="
    Cond.cmp (detectCol parts.head!) Op.eq (parseVal parts.getLast!)
  else if s'.contains ">" then
    Cond.cmp Col.age Op.gt (parseVal (s'.splitOn ">" |>.getLast!))
  else
    Cond.always

/-- Parse a user record from a string like `"Charlie", 25, "c@example.com"` --/
def parseUser (s : String) : Juser :=
  let parts := s.splitOn "," |>.map (fun p => p.trimAscii.toString)
  let stripQuotes (raw : String) : String :=
    let t := raw.trimAscii.toString
    if t.front? = some '"' then ((t.drop 1).dropEnd 1).toString else t
  match parts with
  | [nameStr, ageStr, emailStr] =>
      { name  := stripQuotes nameStr
        age   := ageStr.trimAscii.toString.toNat!
        email := stripQuotes emailStr }
  | _ => { name := "", age := 0, email := "" }

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
      else if sel.startsWith "update(" || sel.startsWith "modify(" then
        -- update(<col>, <value>, <cond>)  — also accepts modify(...)
        -- Examples:
        --   update(.age, 50, .age > 30)
        --   modify(.name, "Anon", .age < 18)
        let inner := (sel.replace "update(" "" |>.replace "modify(" "" |>.replace ")" "")
        let parseVal (str : String) : Value :=
          let trimmed := str.trimAscii.toString
          if trimmed.front? = some '"' then
            Value.str ((trimmed.drop 1).dropEnd 1).toString
          else
            Value.nat trimmed.toNat!
        let detectCol (lhs : String) : Col :=
          if lhs.contains "email" then Col.email
          else if lhs.contains "age" then Col.age
          else Col.name
        -- Split on the first two top-level commas; the rest is the condition
        -- (so the condition can itself contain `&&` etc.).
        let bits := inner.splitOn ","
        match bits with
        | colStr :: valStr :: rest =>
            let condStr := ",".intercalate rest
            JQuery.modify (detectCol colStr) (parseVal valStr) (parseCond condStr)
        | _ => JQuery.modify Col.all (Value.str "") Cond.always
      else
        let inner := sel.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
        if sel.startsWith "delete(" then JQuery.drop (parseCond inner)
        else JQuery.find Col.all (parseCond inner)
  | _ => JQuery.find Col.all Cond.always

-- =====================================================
-- 10. Execution Examples
-- =====================================================

def myColDB : SDB := {
  names  := ["Alice", "Bob"],
  ages   := [35, 20],
  emails := ["alice@example.com", "bob@example.com"]
}

def myDB : JDB := [
  { name := "Alice", age := 35, email := "alice@example.com" },
  { name := "Bob",   age := 20, email := "bob@example.com" }
]

#guard myColDB.toRows =
  [("Alice", 35, "alice@example.com"),
   ("Bob", 20, "bob@example.com")]

#guard eval_jquery myDB (jqToJQuery ".[] | select(.age > 30)")
  = JResult.db [{ name := "Alice", age := 35, email := "alice@example.com" }]

#guard eval_squery myColDB
  (jquery_to_squery (jqToJQuery ".[] | select(.age > 30)")) =
  SResult.db {
    names  := ["Alice"],
    ages   := [35],
    emails := ["alice@example.com"]
  }

#guard eval_jquery myDB
  (jqToJQuery ".[] | select(.email == \"bob@example.com\")") =
  JResult.db [{ name := "Bob", age := 20, email := "bob@example.com" }]

#guard eval_squery myColDB
  (jquery_to_squery
    (jqToJQuery ".[] | select(.email == \"bob@example.com\")")) =
  SResult.db {
    names  := ["Bob"],
    ages   := [20],
    emails := ["bob@example.com"]
  }

  #guard eval_jquery myDB (jqToJQuery ".[] | clear()") =
  JResult.db []

#guard eval_squery myColDB
  (jquery_to_squery (jqToJQuery ".[] | clear()")) =
  SResult.db { names := [], ages := [], emails := [] }

#guard eval_jquery myDB (jqToJQuery ".[] | count") =
  JResult.num 2

#guard eval_squery myColDB
  (jquery_to_squery (jqToJQuery ".[] | count")) =
  SResult.num 2

#guard eval_jquery myDB JQuery.count =
  JResult.num 2

#guard eval_squery myColDB SQuery.count =
  SResult.num 2

#guard eval_jquery myDB
  (jqToJQuery ".[] | insert(\"Charlie\", 25, \"charlie@example.com\")") =
  JResult.db [
    { name := "Charlie", age := 25, email := "charlie@example.com" },
    { name := "Alice",   age := 35, email := "alice@example.com" },
    { name := "Bob",     age := 20, email := "bob@example.com" }
  ]

#guard eval_jquery myDB
  (JQuery.modify Col.age (Value.nat 50)
    (Cond.cmp Col.age Op.gt (Value.nat 30))) =
  JResult.db [
    { name := "Alice", age := 50, email := "alice@example.com" },
    { name := "Bob",   age := 20, email := "bob@example.com" }
  ]

#guard eval_jquery ([] : JDB) JQuery.count =
  JResult.num 0

#guard eval_jquery ([] : JDB)
  (JQuery.modify Col.age (Value.nat 0) Cond.always) =
  JResult.db []
