-- =====================================================
-- SqlGenError — buggy-variant executable
-- =====================================================
-- Same shape as SqlGenMain, but imports `Error` instead of `Main`.
-- Error.lean's eval_jquery has a deliberate bug at the count arm:
--   JQuery.count => JResult.num 1   (Error.lean:205)
-- whereas eval_squery is byte-identical to Main's correct one.
--
-- Running this binary on the seed DB (7 users) with a count query
-- yields jq_result = 1, sq_result = 7, match = false — the
-- counter-example that the Lean proof is designed to rule out.
--
-- INVARIANT: the bug must remain confined to eval_jquery's count
-- arm. If anyone perturbs eval_squery in Error.lean, the demo
-- semantics change. Keep eval_squery in lockstep with Main.lean.

import Error
import Lean.Data.Json

open Lean

-- Same seed as SqlGenMain so jq_result vs sq_result is comparable.
def seedDB : JDB := [
  { name := "Alice",   age := 30, role := Role.student },
  { name := "Bob",     age := 25, role := Role.student },
  { name := "Charlie", age := 35, role := Role.student },
  { name := "Diana",   age := 28, role := Role.student },
  { name := "Eve",     age := 42, role := Role.student },
  { name := "Frank",   age := 19, role := Role.student },
  { name := "Grace",   age := 31, role := Role.student }
]

inductive Source where
  | users : Source

def sourceToSql : Source → String
  | .users => "users"

def colToSql : Col → String
  | .name => "name"
  | .age  => "age"
  | .role => "role"
  | .all  => "*"

def opToSql : Op → String
  | .eq => "="
  | .gt => ">"
  | .lt => "<"
  | .ge => ">="
  | .le => "<="

def roleToSqlLit : Role → String
  | .student  => "'student'"
  | .employee => "'employee'"
  | .retired  => "'retired'"

def valueToSql : Value → String
  | .nat n  => toString n
  | .str s  => "'" ++ s ++ "'"
  | .role r => roleToSqlLit r

partial def condToSql : Cond → String
  | .always       => "TRUE"
  | .cmp col op v => colToSql col ++ " " ++ opToSql op ++ " " ++ valueToSql v
  | .and c₁ c₂    => "(" ++ condToSql c₁ ++ " AND " ++ condToSql c₂ ++ ")"
  | .or  c₁ c₂    => "(" ++ condToSql c₁ ++ " OR "  ++ condToSql c₂ ++ ")"

def insertValuesToSql (s : Suser) : String :=
  "('" ++ s.1 ++ "', " ++ toString s.2.1 ++ ", " ++ roleToSqlLit s.2.2 ++ ")"

def squeryToSql : SQuery → String
  | .select col c   =>
      "SELECT " ++ colToSql col ++ " FROM " ++ sourceToSql .users ++ " WHERE " ++ condToSql c
  | .delete c       =>
      "DELETE FROM " ++ sourceToSql .users ++ " WHERE " ++ condToSql c
  | .insert s       =>
      "INSERT INTO " ++ sourceToSql .users ++ " VALUES " ++ insertValuesToSql s
  | .truncate       =>
      "DELETE FROM " ++ sourceToSql .users
  | .count          =>
      "SELECT COUNT(*) AS count FROM " ++ sourceToSql .users
  | .update col v c =>
      "UPDATE " ++ sourceToSql .users ++
      " SET " ++ colToSql col ++ " = " ++ valueToSql v ++
      " WHERE " ++ condToSql c

def jdbToSdb (jd : JDB) : SDB :=
  { names := jd.map (·.name),
    ages  := jd.map (·.age),
    roles := jd.map (·.role) }

def roleToJson : Role → Json
  | .student  => .str "student"
  | .employee => .str "employee"
  | .retired  => .str "retired"

def juserToJson (u : Juser) : Json :=
  Json.mkObj [("name", .str u.name), ("age", Json.num u.age), ("role", roleToJson u.role)]

def suserToJson (s : Suser) : Json :=
  Json.mkObj [("name", .str s.1), ("age", Json.num s.2.1), ("role", roleToJson s.2.2)]

def jrToJson : JResult → Json
  | .db jd => .arr (jd.map juserToJson).toArray
  | .num n => Json.mkObj [("count", Json.num n)]

def srToJson : SResult → Json
  | .db sd => .arr (sd.toRows.map suserToJson).toArray
  | .num n => Json.mkObj [("count", Json.num n)]

def resultsMatch : JResult → SResult → Bool
  | .db jd,  .db sd  => jd.map toS = sd.toRows
  | .num n,  .num m  => n = m
  | _,       _       => false

def main (args : List String) : IO Unit := do
  let input := args.head?.getD ".[]"
  let jq := jqToJQuery input
  let sq := jquery_to_squery jq
  let sql := squeryToSql sq
  let jr := eval_jquery seedDB jq           -- buggy on count
  let sr := eval_squery (jdbToSdb seedDB) sq -- correct
  let m  := resultsMatch jr sr
  let out := Json.mkObj [
    ("sql",       .str sql),
    ("jq",        .str input),
    ("jq_result", jrToJson jr),
    ("sq_result", srToJson sr),
    ("match",     .bool m)
  ]
  IO.println out.compress
