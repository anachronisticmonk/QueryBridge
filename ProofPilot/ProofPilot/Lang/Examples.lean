import ProofPilot.Lang.QueryEquiv
/-! Sanity checks — these also serve as documentation of what is proved. -/

open QueryEquiv

-- Example databases (equiv by construction)
def exJDB : JDB := [{ name := "Alice", age := 8 }, { name := "Bob", age := 12 }, { name := "Charlie", age := 7 }]
def exSDB : SDB := [("Alice", 8), ("Bob", 12), ("Charlie", 7)]

example : equiv exJDB exSDB := by decide

-- find (age < 10)
def q_find : JQuery := .find (fun u => u.age < 10)
#eval eval_jquery exJDB q_find     -- [Alice, Charlie]
#eval eval_squery exSDB (jqueryToSquery q_find)  -- [("Alice",8),("Charlie",7)]

-- The master theorem applied to this concrete pair
example : equiv (eval_jquery exJDB q_find) (eval_squery exSDB (jqueryToSquery q_find)) :=
  query_equiv exJDB exSDB q_find (by decide)
