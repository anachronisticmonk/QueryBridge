structure Juser where
  name : String
  age  : Nat

def JDB : Type := List Juser
def Suser : Type := String × Nat
def SDB : Type := List Suser

def jdbToSdb (jd: JDB) : SDB :=
  match jd with
  | [] => []
  | {name, age} :: xs => (name, age) :: jdbToSdb xs

def sdbToJdb (sd: SDB) : JDB :=
  match sd with
  | [] => []
  | (name, age) :: xs => {name, age} :: sdbToJdb xs

def equiv (jd: JDB) (sd: SDB) : Prop :=
  (jdbToSdb jd = sd) /\ (sdbToJdb sd = jd)

inductive JQuery where
  | find : (Juser → Bool) → JQuery
  | delete : (Juser → Bool) → JQuery

inductive SQuery where
  | select : (Juser → Bool) → SQuery
  | drop : (Juser → Bool) → SQuery

def jqueryToSquery : JQuery → SQuery
  | .find p => .select p
  | .delete p => .drop p

def eval_jquery (jd : JDB) : JQuery → JDB
  | .find p => jd.filter p
  | .delete p => jd.filter (fun u => ¬ p u)

def eval_squery (sd : SDB) : SQuery → SDB
  | .select p => sd.filter (fun r => p {name := r.1, age := r.2})
  | .drop p => sd.filter (fun r => ¬ p {name := r.1, age := r.2})

theorem jdbToSdb_filter (jd: JDB) (p: Juser → Bool) :
    jdbToSdb (jd.filter p) =
    (jdbToSdb jd).filter (fun r => p {name := r.1, age := r.2}) := by
  induction jd with
  | nil => simp [jdbToSdb, List.filter]
  | cons u us ih =>
      simp [List.filter, jdbToSdb]
      split
      · rename_i h
        simp [jdbToSdb, h, ih]
      · rename_i h
        simp [h, ih]

theorem sdbToJdb_filter (sd: SDB) (p: Juser → Bool) :
    sdbToJdb (sd.filter (fun r => p {name := r.1, age := r.2})) =
    (sdbToJdb sd).filter p := by
  induction sd with
  | nil => simp [sdbToJdb, List.filter]
  | cons x xs ih =>
      match x with
      | (n, a) =>
          simp [List.filter, sdbToJdb]
          split
          · rename_i h
            simp [sdbToJdb, ih]
          · rename_i h
            simp [ih]

theorem delete_equiv1 (jd : JDB) (sd : SDB) (p : Juser → Bool) (h : equiv jd sd) :
    jdbToSdb (eval_jquery jd (.delete p)) = eval_squery sd (.drop p) := by
  rcases h with ⟨h_to_sdb, _⟩
  simp [eval_jquery, eval_squery]
  rw [jdbToSdb_filter jd (fun u => !(p u))]
  rw [h_to_sdb]

theorem delete_equiv2 (jd : JDB) (sd : SDB) (p : Juser → Bool) (h : equiv jd sd) :
    sdbToJdb (eval_squery sd (.drop p)) = eval_jquery jd (.delete p) := by
  rcases h with ⟨_, h_to_jdb⟩
  simp [eval_jquery, eval_squery]
  rw [sdbToJdb_filter sd (fun u => !(p u))]
  rw [h_to_jdb]

-- The main result for Delete
theorem delete_equiv (jd : JDB) (sd : SDB) (p : Juser → Bool) (h : equiv jd sd) :
    equiv (eval_jquery jd (.delete p)) (eval_squery sd (.drop p)) := by
  constructor
  · exact delete_equiv1 jd sd p h
  · exact delete_equiv2 jd sd p h

theorem query_equiv1 (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    jdbToSdb (eval_jquery jd jq) = eval_squery sd (jqueryToSquery jq) := by
  rcases h with ⟨h_to_sdb, _⟩
  cases jq with
  | find p =>
      simp [eval_jquery, eval_squery, jqueryToSquery]
      rw [jdbToSdb_filter, h_to_sdb]
  | delete p =>
      simp [eval_jquery, eval_squery, jqueryToSquery]
      rw [jdbToSdb_filter jd (fun u => !(p u))]
      rw [h_to_sdb]

theorem query_equiv2 (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    sdbToJdb (eval_squery sd (jqueryToSquery jq)) = (eval_jquery jd jq) := by
  rcases h with ⟨_, h_to_jdb⟩
  cases jq with
  | find p =>
      simp [eval_jquery, eval_squery, jqueryToSquery]
      -- We use the lemma to show that filtering tuples is same as filtering Users
      rw [sdbToJdb_filter, h_to_jdb]
  | delete p =>
      simp [eval_jquery, eval_squery, jqueryToSquery]
      rw [sdbToJdb_filter sd (fun u => !(p u))]
      rw [h_to_jdb]

theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jqueryToSquery jq)) := by
  constructor
  · exact query_equiv1 jd sd jq h
  · exact query_equiv2 jd sd jq h
