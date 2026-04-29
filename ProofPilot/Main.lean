import Std
import Init.Data.String.TakeDrop

-- =====================================================
-- 1. Base Data Structures
-- =====================================================

inductive Role where
  | student | employee | retired
  deriving Repr, DecidableEq, BEq

-- JSON user
structure Juser where
  name : String
  age  : Nat
  role : Role
  deriving Repr, DecidableEq, BEq

-- SQL user
abbrev Suser : Type := String × Nat × Role

-- JSON Database
abbrev JDB := List Juser

-- Columnar SQL Database
structure SDB where
  names : List String
  ages  : List Nat
  roles : List Role
  deriving Repr, DecidableEq, BEq

def zip3 {α β γ : Type} : List α → List β → List γ → List (α × β × γ)
  | a :: as, b :: bs, c :: cs => (a, b, c) :: zip3 as bs cs
  | _, _, _ => []

def SDB.toRows (sd : SDB) : List Suser :=
  zip3 sd.names sd.ages sd.roles

-- =====================================================
-- 2. Conversion
-- =====================================================

def toS (u : Juser) : Suser := (u.name, u.age, u.role)
def toJ (s : Suser) : Juser := {name := s.1, age := s.2.1, role := s.2.2}

theorem toJ_toS (u : Juser) : toJ (toS u) = u := by
  simp [toJ, toS]

theorem toS_toJ (s : Suser) : toS (toJ s) = s := by
  obtain ⟨n, a, r⟩ := s
  rfl

-- =====================================================
-- 3. Schema & Values
-- =====================================================

inductive Col where
  | name | age | role | all
  deriving Repr, DecidableEq

inductive Value where
  | nat  : Nat → Value
  | str  : String → Value
  | role : Role → Value
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

def get_valJ (c : Col) (u : Juser) : Value :=
  match c with
  | Col.name => Value.str u.name
  | Col.age  => Value.nat u.age
  | Col.role => Value.role u.role
  | Col.all  => Value.str ""

def get_valS (c : Col) (s : Suser) : Value :=
  match c, s with
  | Col.name, (n, _, _) => Value.str n
  | Col.age,  (_, a, _) => Value.nat a
  | Col.role, (_, _, r) => Value.role r
  | Col.all,  _         => Value.str ""

def eval_op : Op → Value → Value → Bool
  | Op.eq, v1, v2 => v1 = v2
  | Op.gt, Value.nat a, Value.nat b => a > b
  | Op.lt, Value.nat a, Value.nat b => a < b
  | Op.ge, Value.nat a, Value.nat b => a ≥ b
  | Op.le, Value.nat a, Value.nat b => a ≤ b
  | _, _, _ => false

def Cond.evalJ : Cond → Juser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, u => eval_op op (get_valJ col u) v
  | Cond.and c1 c2, u => c1.evalJ u && c2.evalJ u
  | Cond.or c1 c2, u => c1.evalJ u || c2.evalJ u

def Cond.evalS : Cond → Suser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, s => eval_op op (get_valS col s) v
  | Cond.and c1 c2, s => c1.evalS s && c2.evalS s
  | Cond.or c1 c2, s => c1.evalS s || c2.evalS s

-- Per-row update on a Juser.
def apply_updateJ (col : Col) (v : Value) (u : Juser) : Juser :=
  match col, v with
  | Col.name, Value.str s  => {u with name := s}
  | Col.age,  Value.nat n  => {u with age := n}
  | Col.role, Value.role r => {u with role := r}
  | _, _                   => u   -- no-op

-- Per-row update on an Suser
def apply_updateS (col : Col) (v : Value) (s : Suser) : Suser :=
  match col, v with
  | Col.name, Value.str n  => (n, s.2.1, s.2.2)
  | Col.age,  Value.nat a  => (s.1, a, s.2.2)
  | Col.role, Value.role r => (s.1, s.2.1, r)
  | _, _                   => s    -- no-op

-- Per-row update on a Juser by a condition
def apply_update_ifJ (col : Col) (v : Value) (c : Cond) (u : Juser) : Juser :=
  if c.evalJ u then apply_updateJ col v u else u

-- Per-row update on an Suser by a condition
def apply_update_ifS (col : Col) (v : Value) (c : Cond) (s : Suser) : Suser :=
  if c.evalS s then apply_updateS col v s else s

-- =====================================================
-- 6. Query Languages, Result Types & Semantics
-- =====================================================

inductive JQuery where
  | find    : Col → Cond → JQuery          -- jq's `.[] | select(cond)`
  | drop    : Cond → JQuery                -- jq's `.[] | select(cond | not)`
  | prepend : Juser → JQuery               -- jq's `[$u] + .`
  | clear   : JQuery                       -- jq's `[]`
  | length  : JQuery                       -- jq's `length`
  | modify  : Col → Value → Cond → JQuery  -- jq's `map(if cond then .col = v else . end)`
  deriving Repr

inductive SQuery where
  | select   : Col → Cond → SQuery          -- SQL's `SELECT * FROM users WHERE cond`
  | delete   : Cond → SQuery                -- SQL's `DELETE FROM users WHERE cond`
  | insert   : Suser → SQuery               -- SQL's `INSERT INTO users VALUES (n, a, r)`
  | truncate : SQuery                       -- SQL's `TRUNCATE TABLE users`
  | count    : SQuery                       -- SQL's `SELECT COUNT(*) FROM users`
  | update   : Col → Value → Cond → SQuery  -- SQL's `UPDATE users SET col = v WHERE cond`
  deriving Repr

/-- A query result is either a database (for transformation queries)
    or a scalar (for aggregate queries). --/
inductive JResult where
  | db  : JDB → JResult
  | num : Nat → JResult
  deriving Repr, DecidableEq, BEq

inductive SResult where
  | db  : SDB → SResult
  | num : Nat → SResult
  deriving Repr, DecidableEq, BEq

def eval_jquery (jd : JDB) : JQuery → JResult
  | JQuery.find _ c       => JResult.db (jd.filter c.evalJ)
  | JQuery.drop c         => JResult.db (jd.filter (fun u => !(c.evalJ u)))
  | JQuery.prepend u      => JResult.db (u :: jd)
  | JQuery.clear          => JResult.db []
  | JQuery.length         => JResult.num jd.length
  | JQuery.modify col v c => JResult.db (jd.map (apply_update_ifJ col v c))

def eval_squery (sd : SDB) : SQuery → SResult
  | SQuery.select _ c =>
      let rows := sd.toRows.filter c.evalS
      SResult.db { names := rows.map (·.1)
                   ages  := rows.map (·.2.1)
                   roles := rows.map (·.2.2) }
  | SQuery.delete c   =>
      let rows := sd.toRows.filter (fun s => !(c.evalS s))
      SResult.db { names := rows.map (·.1)
                   ages  := rows.map (·.2.1)
                   roles := rows.map (·.2.2) }
  | SQuery.insert s   =>
      SResult.db { names := s.1   :: sd.names
                   ages  := s.2.1 :: sd.ages
                   roles := s.2.2 :: sd.roles }
  | SQuery.truncate   =>
      SResult.db { names := [], ages := [], roles := [] }
  | SQuery.count      =>
      SResult.num sd.toRows.length
  | SQuery.update col v c =>
      let rows := sd.toRows.map (apply_update_ifS col v c)
      SResult.db { names := rows.map (·.1)
                   ages  := rows.map (·.2.1)
                   roles := rows.map (·.2.2) }

-- =====================================================
-- 7. Equivalence Relations & Translation
-- =====================================================

-- Set-membership equivalence: every JSON record corresponds to a row.
def equiv (jd : JDB) (sd : SDB) : Prop :=
  let rows := sd.toRows
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ rows) ∧
  (∀ s : Suser, s ∈ rows ↔ toJ s ∈ jd)

/-- Permutation equivalence: tracks element MULTIPLICITY, not just
    membership. Strictly stronger than `equiv`. Required for any
    aggregate that isn't set-functional (count, sum, average, …). --/
def permEquiv (jd : JDB) (sd : SDB) : Prop :=
  List.Perm (jd.map toS) sd.toRows

def result_equiv : JResult → SResult → Prop
  | JResult.db jd,  SResult.db sd  => equiv jd sd
  | JResult.num n1, SResult.num n2 => n1 = n2
  | _, _ => False

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p       => SQuery.select c p
  | JQuery.drop p         => SQuery.delete p
  | JQuery.prepend u      => SQuery.insert (toS u)
  | JQuery.clear          => SQuery.truncate
  | JQuery.length         => SQuery.count
  | JQuery.modify col v c => SQuery.update col v c

-- =====================================================
-- 8. Proofs
-- =====================================================

theorem getVal_bridge (col : Col) (u : Juser) :
  get_valJ col u = get_valS col (toS u) := by
  cases col <;> cases u <;> simp [get_valJ, get_valS, toS]

theorem eval_bridgeJ (c : Cond) (u : Juser) :
  c.evalJ u = c.evalS (toS u) := by
  induction c generalizing u with
  | always => simp [Cond.evalJ, Cond.evalS]
  | cmp col op v => simp [Cond.evalJ, Cond.evalS, getVal_bridge]
  | and c1 c2 ih1 ih2 => simp [Cond.evalJ, Cond.evalS, ih1, ih2]
  | or c1 c2 ih1 ih2 => simp [Cond.evalJ, Cond.evalS, ih1, ih2]

theorem eval_bridgeS (c : Cond) (s : Suser) :
  c.evalS s = c.evalJ (toJ s) := by
  induction c generalizing s with
  | always => rfl
  | cmp col op v =>
    obtain ⟨n, a, r⟩ := s
    cases col <;> rfl
  | and c1 c2 ih1 ih2 =>
    simp only [Cond.evalJ, Cond.evalS]
    rw [ih1, ih2]
  | or c1 c2 ih1 ih2 =>
    simp only [Cond.evalJ, Cond.evalS]
    rw [ih1, ih2]

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
  exact zip3_map_components (zip3 sd.names sd.ages sd.roles |>.filter p)

theorem toRows_insert (s : Suser) (sd : SDB) :
    (SDB.mk (s.1 :: sd.names) (s.2.1 :: sd.ages) (s.2.2 :: sd.roles)).toRows
    = s :: sd.toRows := by
  obtain ⟨n, a, r⟩ := s
  rfl

-- Per-row update commutes with `toS`.
theorem applyUpdate_bridge (col : Col) (v : Value) (u : Juser) :
    apply_updateS col v (toS u) = toS (apply_updateJ col v u) := by
  obtain ⟨n, a, r⟩ := u
  cases col <;> cases v <;> simp [apply_updateJ, apply_updateS, toS]

-- Conditional update commutes with `toS` (uses eval_bridgeJ for the guard).
theorem applyUpdateIf_bridge (col : Col) (v : Value) (c : Cond) (u : Juser) :
    apply_update_ifS col v c (toS u) = toS (apply_update_ifJ col v c u) := by
  unfold apply_update_ifS apply_update_ifJ
  rw [← eval_bridgeJ c u]
  cases h : c.evalJ u with
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
  exact zip3_map_components (zip3 sd.names sd.ages sd.roles |>.map f)

-- Permutation equivalence implies set equivalence.
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
  Main correctness theorem for the JQ → SQL translation.
  Under permutation equivalence, executing any query on jd
  and the translated query on sd yields equivalent
  results.
--/
theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : permEquiv jd sd) :
    result_equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by

  have hset : equiv jd sd := permEquiv_implies_equiv h
  rcases hset with ⟨hJ, hS⟩
  cases jq with
  | find col c =>
    show equiv _ _
    constructor
    · intro u
      constructor
      · intro hu
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hu
        have hmem_rows : toS u ∈ sd.toRows := (hJ u).1 hmem
        have hcond_rows : c.evalS (toS u) = true := by
          simpa [eval_bridgeJ] using hcond
        simp [toRows_filter_reconstruct]
        exact ⟨hmem_rows, hcond_rows⟩
      · intro hu
        simp [toRows_filter_reconstruct] at hu
        rcases hu with ⟨hmem, hcond⟩
        have hmem_jd : toJ (toS u) ∈ jd := (hS (toS u)).1 hmem
        have hmem_jd' : u ∈ jd := by simpa using hmem_jd
        have hcond_j : c.evalJ u = true := by
          simpa [eval_bridgeJ] using hcond
        exact List.mem_filter.mpr ⟨hmem_jd', hcond_j⟩
    · intro s
      constructor
      · intro hs
        simp [toRows_filter_reconstruct] at hs
        rcases hs with ⟨hmem, hcond⟩
        have hmem_jd : toJ s ∈ jd := (hS s).1 hmem
        have hcond_j : c.evalJ (toJ s) = true := by
          simpa [eval_bridgeS] using hcond
        exact List.mem_filter.mpr ⟨hmem_jd, hcond_j⟩
      · intro hs
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hs
        have hmem_rows : s ∈ sd.toRows := (hJ (toJ s)).1 hmem
        have hcond_s : c.evalS s = true := by
          simpa [eval_bridgeS] using hcond
        simp [toRows_filter_reconstruct]
        exact ⟨hmem_rows, hcond_s⟩

  | drop c =>
    show equiv _ _
    constructor
    · intro u
      constructor
      · intro hu
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hu
        have hmem_rows : toS u ∈ sd.toRows := (hJ u).1 hmem
        have hfalse : c.evalJ u = false := by
          cases h : c.evalJ u
          · rfl
          · rw [h] at hcond; simp at hcond
        have hcond_rows : c.evalS (toS u) = false := by
          rw [← eval_bridgeJ]; exact hfalse
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
        have hfalse : c.evalJ u = false := by
          rw [eval_bridgeJ]; exact hfalseS
        have hcond_j : (!c.evalJ u) = true := by grind
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
        have hfalse : c.evalJ (toJ s) = false := by
          rw [← eval_bridgeS]; exact hfalseS
        have hcond_j : (!c.evalJ (toJ s)) = true := by grind
        exact List.mem_filter.mpr ⟨hmem_jd, hcond_j⟩
      · intro hs
        have ⟨hmem, hcond⟩ := List.mem_filter.mp hs
        have hmem_rows : s ∈ sd.toRows := (hJ (toJ s)).1 hmem
        have hfalse : c.evalJ (toJ s) = false := by
          cases h : c.evalJ (toJ s)
          · rfl
          · rw [h] at hcond; simp at hcond
        have hcond_s : c.evalS s = false := by
          rw [eval_bridgeS]; exact hfalse
        have hbang : (!c.evalS s) = true := by grind
        simp [toRows_filter_reconstruct]
        grind

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

  | clear =>
    show equiv _ _
    refine ⟨?_, ?_⟩
    · intro u; simp [SDB.toRows, zip3]
    · intro s; simp [SDB.toRows, zip3]

  | length =>
    show jd.length = sd.toRows.length
    have h1 : (jd.map toS).length = sd.toRows.length := h.length_eq
    rw [List.length_map] at h1
    exact h1

  | modify col v c =>
    show equiv _ _
    have hPerm : permEquiv (jd.map (apply_update_ifJ col v c))
                  (SDB.mk
                    ((sd.toRows.map (apply_update_ifS col v c)).map (·.1))
                    ((sd.toRows.map (apply_update_ifS col v c)).map (·.2.1))
                    ((sd.toRows.map (apply_update_ifS col v c)).map (·.2.2))) := by
      unfold permEquiv
      have hbridge : (jd.map (apply_update_ifJ col v c)).map toS
                   = (jd.map toS).map (apply_update_ifS col v c) := by
        rw [List.map_map, List.map_map]
        congr 1; funext u
        exact (applyUpdateIf_bridge col v c u).symm
      rw [hbridge, toRows_map_reconstruct]
      exact h.map (apply_update_ifS col v c)
    exact permEquiv_implies_equiv hPerm

