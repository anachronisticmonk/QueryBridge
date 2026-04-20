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

def jProject (c : Col) (u : Juser) : Result :=
  match c with
  | .name => .str u.name
  | .age  => .num u.age
  | .all  => .user u

def sProject (c : Col) (s : Suser) : Result :=
  match c with
  | .name => .str s.1
  | .age  => .num s.2
  | .all  => .user (toJ s)

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

def jqueryToSquery : JQuery → SQuery
  | .find c p => .select c (jpred_to_spred p)
  | .delete p => .drop (jpred_to_spred p)

-- 5. Evaluation Logic
def eval_jquery (jd: JDB) : JQuery → List Result
  | .find c p => (jd.filter p).map (jProject c)
  | .delete p => (jd.filter (fun u => ¬ p u)).map (jProject .all)

def eval_squery (sd: SDB) : SQuery → List Result
  | .select c p => (sd.filter p).map (sProject c)
  | .drop p       => (sd.filter (fun r => ¬ p r)).map (sProject .all)

-- 6. The Equivalence Theorem
theorem query_equiv (jd: JDB) (sd: SDB) (jq: JQuery) (h: equiv jd sd) :
    ∀ res : Result, res ∈ eval_jquery jd jq ↔ res ∈ eval_squery sd (jqueryToSquery jq) := by
  rcases h with ⟨h_js, h_sj⟩
  intro res
  cases jq with
  | find c p =>
      simp [eval_jquery, eval_squery, jqueryToSquery, List.mem_map, List.mem_filter, jpred_to_spred]
      constructor
      · rintro ⟨u, ⟨u_in_jd, p_u⟩, rfl⟩
        refine ⟨toS u, ⟨?_, ?_⟩, ?_⟩
        · exact h_js u |>.mp u_in_jd
        · exact p_u
        · simp [sProject, jProject, toJ, toS]
      · rintro ⟨s, ⟨s_in_sd, p_s⟩, rfl⟩
        refine ⟨toJ s, ⟨?_, ?_⟩, ?_⟩
        · exact h_sj s |>.mp s_in_sd
        · exact p_s
        · simp [sProject, jProject, toJ]
  | delete p =>
      simp [eval_jquery, eval_squery, jqueryToSquery, List.mem_map, List.mem_filter, jpred_to_spred]
      constructor
      · rintro ⟨u, ⟨u_in_jd, not_p_u⟩, rfl⟩
        refine ⟨toS u, ⟨?_, not_p_u⟩, ?_⟩
        · exact h_js u |>.mp u_in_jd
        · simp [sProject, jProject, toJ, toS]
      · rintro ⟨s, ⟨s_in_sd, not_p_s⟩, rfl⟩
        refine ⟨toJ s, ⟨?_, not_p_s⟩, ?_⟩
        · exact h_sj s |>.mp s_in_sd
        · simp [sProject, jProject, toJ]
