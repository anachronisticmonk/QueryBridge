structure Juser where
  name : String
  age  : Nat

def Suser : Type := String × Nat

abbrev JDB := List Juser
abbrev SDB := List Suser

def toS (u : Juser) : Suser := (u.name, u.age)
def toJ (s : Suser) : Juser := {name := s.1, age := s.2}

def equiv (jd : JDB) (sd : SDB) : Prop :=
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ sd) ∧
  (∀ s : Suser, s ∈ sd ↔ toJ s ∈ jd)

inductive JQuery where
  | find : (Juser → Bool) → JQuery
  | delete : (Juser → Bool) → JQuery

inductive SQuery where
  | select : (Suser → Bool) → SQuery
  | drop : (Suser → Bool) → SQuery

def jpred_to_spred (p: Juser → Bool) : Suser → Bool :=
  fun r => p {name := r.1, age := r.2}

def jqueryToSquery : JQuery → SQuery
  | .find p => .select (jpred_to_spred p)
  | .delete p => .drop (jpred_to_spred p)

def eval_jquery (jd: JDB) : JQuery → JDB
  | .find p => jd.filter p
  | .delete p => jd.filter (fun u => ¬ p u)

def eval_squery (sd: SDB) : SQuery → SDB
  | .select p => sd.filter (fun r => p r)
  | .drop p => sd.filter (fun r => ¬ p r)

theorem query_equiv (jd: JDB) (sd: SDB) (jq: JQuery) (h: equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jqueryToSquery jq)) := by
  rcases h with ⟨h_js, h_sj⟩
  cases jq with
  | find p =>
      constructor
      · intro u
        simp [eval_jquery, eval_squery, jqueryToSquery, List.mem_filter, jpred_to_spred]
        rw [h_js]
        rfl
      · intro s
        simp [eval_jquery, eval_squery, jqueryToSquery, List.mem_filter, jpred_to_spred]
        rw [h_sj]
        rfl
  | delete p =>
      constructor
      · intro u
        simp [eval_jquery, eval_squery, jqueryToSquery, List.mem_filter, jpred_to_spred]
        rw [h_js]
        rfl
      · intro s
        simp [eval_jquery, eval_squery, jqueryToSquery, List.mem_filter, jpred_to_spred]
        rw [h_sj]
        rfl
