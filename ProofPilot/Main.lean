-- 1. Base Data Structures
structure Juser where
  name : String
  age  : Nat
deriving Repr, DecidableEq

def Suser : Type := String × Nat

abbrev JDB := List Juser
abbrev SDB := List Suser

-- 2. Conversion and Projections
def toS (u : Juser) : Suser := (u.name, u.age)
def toJ (s : Suser) : Juser := {name := s.1, age := s.2}

inductive Col where
  | name | age | all
  deriving Repr, DecidableEq

inductive Result where
  | str  : String → Result
  | num  : Nat → Result
  | user : Juser → Result
  deriving Repr, DecidableEq

-- 3. Equivalence Definition (Set-wise)
def equiv (jd : JDB) (sd : SDB) : Prop :=
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ sd) ∧
  (∀ s : Suser, s ∈ sd ↔ toJ s ∈ jd)

-- 4. Query Definitions
inductive JQuery where
  | find   : Col → (Juser → Bool) → JQuery
  | delete : (Juser → Bool) → JQuery

inductive SQuery where
  | select : Col → (Suser → Bool) → SQuery
  | drop   : (Suser → Bool) → SQuery

def jpred_to_spred (p: Juser → Bool) : Suser → Bool :=
  fun r => p {name := r.1, age := r.2}

def jquery_to_squery : JQuery → SQuery
  | .find c p => .select c (jpred_to_spred p)
  | .delete p => .drop (jpred_to_spred p)

-- 5. Evaluation Logic
def eval_jquery (jd : JDB) : JQuery → JDB
  | .find _ p   => jd.filter p
  | .delete p   => jd.filter (fun u => !(p u))

def eval_squery (sd : SDB) : SQuery → SDB
  | .select _ p => sd.filter p
  | .drop p     => sd.filter (fun s => !(p s))

-- 6. The Equivalence Theorem
theorem query_equiv (jd: JDB) (sd: SDB) (jq: JQuery) (h: equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq)) := by
  constructor
  · intro u
    cases jq <;> {
      simp [eval_jquery, eval_squery, jquery_to_squery, jpred_to_spred, List.mem_filter]
      rw [h.1 u]
      simp [toS]
    }
  · intro s
    cases jq <;> {
      simp [eval_jquery, eval_squery, jquery_to_squery, jpred_to_spred, List.mem_filter]
      rw [h.2 s]
      rfl
    }
