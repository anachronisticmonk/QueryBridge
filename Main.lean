structure User where
  name : String
  age  : Nat

def JDB : Type :=
  List User

def SDB : Type :=
  List (String × Nat)

def jdbToSdb : JDB → SDB
  | [] => []
  | u :: us =>
      (u.name, u.age) :: jdbToSdb us

def sdbToJdb : SDB → JDB
  | [] => []
  | (n, a) :: xs =>
      { name := n, age := a } :: sdbToJdb xs

def equiv (j : JDB) (s : SDB) : Prop :=
  (jdbToSdb j = s) /\ (sdbToJdb s = j)

inductive AgeCond where
  | gt : Nat → AgeCond   -- age > n
  | lt : Nat → AgeCond   -- age < n
  | eq : Nat → AgeCond   -- age = n

inductive SQuery where
  | select : AgeCond → SQuery

inductive JQuery where
  | find : AgeCond → JQuery

def jqueryToSquery : JQuery → SQuery
  | JQuery.find cond => SQuery.select cond

def evalAgeCond (u : User) : AgeCond → Bool
  | AgeCond.gt n => u.age > n
  | AgeCond.lt n => u.age < n
  | AgeCond.eq n => u.age = n

def eval_squery (db : SDB) : SQuery → SDB
  | SQuery.select cond =>
      db.filter (fun r =>
        evalAgeCond { name := r.1, age := r.2 } cond)

def eval_jquery (db : JDB) : JQuery → JDB
  | JQuery.find cond =>
      db.filter (fun u => evalAgeCond u cond)

theorem jdbToSdb_filter (db : JDB) (p : User → Bool) :
    jdbToSdb (db.filter p) =
    (jdbToSdb db).filter (fun r => p { name := r.1, age := r.2 }) := by
  induction db with
  | nil =>
      -- Base case: both sides simplify to []
      simp [List.filter, jdbToSdb]
  | cons u us ih =>
      -- Inductive step: check if u satisfies the predicate
      simp [List.filter, jdbToSdb]
      split
      .
        -- Case where p u is true
        simp [jdbToSdb, ih]
        rename_i h
        simp [h]
      .
        -- Case where p u is false
        rename_i h
        simp [h, ih]

theorem sdbToJdb_filter (db : SDB) (p : User → Bool) :
    sdbToJdb (db.filter (fun r => p { name := r.1, age := r.2 })) =
    (sdbToJdb db).filter p := by
  induction db with
  | nil =>
      -- Base case: [] = []
      simp [List.filter, sdbToJdb]
  | cons r rs ih =>
      -- r is a pair (String × Nat)
      -- Destructure the pair to make the fields explicit
      match r with
      | (n, a) =>
          simp [List.filter, sdbToJdb]
          split
          · -- Case where p { name := n, age := a } is true
            rename_i h
            simp [sdbToJdb, ih]
          · -- Case where p { name := n, age := a } is false
            rename_i h
            simp [ih]

-- Main theorem
theorem query_equiv1
    (jdb : JDB)
    (sdb : SDB)
    (jq : JQuery)
    (h : equiv jdb sdb) :
    jdbToSdb (eval_jquery jdb jq) = eval_squery sdb (jqueryToSquery jq) := by
  -- Destructure the equivalence hypothesis
  obtain ⟨h_to_sdb, _⟩ := h
  -- Case analysis on the query
  cases jq with
  | find cond =>
    -- Unfold definitions
    simp only [eval_jquery, eval_squery, jqueryToSquery]
    -- Apply the distribution lemma
    rw [jdbToSdb_filter]
    -- Use the equivalence to substitute sdb for jdbToSdb jdb
    rw [h_to_sdb]

theorem query_equiv2
    (jdb : JDB)
    (sdb : SDB)
    (jq : JQuery)
    (h : equiv jdb sdb) :
    sdbToJdb (eval_squery sdb (jqueryToSquery jq)) = (eval_jquery jdb jq) := by
  -- 1. Extract the second part of the equivalence: sdbToJdb sdb = jdb
  obtain ⟨_, h_to_jdb⟩ := h

  cases jq with
  | find cond =>
    -- 2. Unfold the definitions
    simp only [eval_jquery, eval_squery, jqueryToSquery]

    -- 3. Use simp to apply the lemma (it's smarter than rw for higher-order functions)
    rw [sdbToJdb_filter sdb (fun u => evalAgeCond u cond)]

    -- 4. Now the goal is: List.filter (...) (sdbToJdb sdb) = List.filter (...) jdb
    -- Use the equivalence hypothesis to replace (sdbToJdb sdb) with jdb
    rw [h_to_jdb]

theorem query_equiv
    (jdb : JDB)
    (sdb : SDB)
    (jq : JQuery)
    (h : equiv jdb sdb) :
    equiv (eval_jquery jdb jq) (eval_squery sdb (jqueryToSquery jq)) := by
    constructor
    . exact query_equiv1 jdb sdb jq h;
    . exact query_equiv2 jdb sdb jq h
