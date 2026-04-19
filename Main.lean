structure Juser where
  name : String
  age  : Nat

def JDB : Type :=
  List Juser

def Suser : Type :=
  String × Nat

def SDB : Type :=
  List Suser

def jdbToSdb (jd: JDB) : SDB :=
  match jd with
  | [] => []
  | {name, age} :: xs =>
      (name, age) :: jdbToSdb xs

def sdbToJdb (sd: SDB) : JDB :=
  match sd with
  | [] => []
  | (name, age) :: xs =>
      {name, age} :: sdbToJdb xs

def equiv (jd: JDB) (sd: SDB) : Prop :=
  (jdbToSdb jd = sd) /\ (sdbToJdb sd = jd)

inductive AgeCond where
  | gt : Nat → AgeCond   -- age > n
  | lt : Nat → AgeCond   -- age < n
  | eq : Nat → AgeCond   -- age = n

inductive SQuery where
  | select : AgeCond → SQuery

inductive JQuery where
  | find : AgeCond → JQuery

def jqueryToSquery (jq: JQuery) : SQuery :=
  match jq with
  | JQuery.find cond => SQuery.select cond

def evalAgeCond (u: Juser) (a: AgeCond) : Bool :=
  match a with
  | .gt n => u.age > n
  | .lt n => u.age < n
  | .eq n => u.age = n

def eval_jquery (jd : JDB) (jq:JQuery) : JDB :=
  match jq with
  | JQuery.find cond =>
      jd.filter (fun u => evalAgeCond u cond)

def eval_squery (sd : SDB) (sq:SQuery) : SDB :=
  match sq with
  | SQuery.select cond =>
      sd.filter (fun u =>
        evalAgeCond {name := u.1, age := u.2} cond)

theorem jdbToSdb_filter (jd: JDB) (p: Juser → Bool) :
    jdbToSdb (jd.filter p) =
    (jdbToSdb jd).filter (fun r => p {name := r.1, age := r.2}) := by
  induction jd with
  | nil =>
      simp [jdbToSdb]
  | cons _ _ ih =>
      simp [List.filter, jdbToSdb]
      split
      . simp [jdbToSdb, ih]
        rename_i h
        simp [h]
      . rename_i h
        simp [h, ih]

theorem sdbToJdb_filter (sd: SDB) (p: Juser → Bool) :
    sdbToJdb (sd.filter (fun r => p {name := r.1, age := r.2})) =
    (sdbToJdb sd).filter p := by
  induction sd with
  | nil =>
      simp [sdbToJdb]
  | cons x _ ih =>
      match x with
      | (n, a) =>
          simp [List.filter, sdbToJdb]
          split
          · simp [sdbToJdb, ih]
          grind

theorem query_equiv1
    (jd : JDB)
    (sd : SDB)
    (jq : JQuery)
    (h : equiv jd sd) :
    jdbToSdb (eval_jquery jd jq) = eval_squery sd (jqueryToSquery jq) := by
  rcases h with ⟨h_to_sdb, _⟩
  cases jq with
  | find cond =>
      simp only [eval_jquery, eval_squery, jqueryToSquery]
      rw [jdbToSdb_filter]
      grind

theorem query_equiv2
    (jdb : JDB)
    (sdb : SDB)
    (jq : JQuery)
    (h : equiv jdb sdb) :
    sdbToJdb (eval_squery sdb (jqueryToSquery jq)) = (eval_jquery jdb jq) := by
  rcases h with ⟨_, h_to_jdb⟩
  cases jq with
  | find cond =>
    simp only [eval_jquery, eval_squery, jqueryToSquery]
    rw [sdbToJdb_filter sdb (fun u => evalAgeCond u cond)]
    grind

-- Main theorem
theorem query_equiv
    (jdb : JDB)
    (sdb : SDB)
    (jq : JQuery)
    (h : equiv jdb sdb) :
    equiv (eval_jquery jdb jq) (eval_squery sdb (jqueryToSquery jq)) := by
    constructor
    . exact query_equiv1 jdb sdb jq h;
    . exact query_equiv2 jdb sdb jq h
