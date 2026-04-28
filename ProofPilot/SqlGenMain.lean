-- =====================================================
-- SqlGenMain — verified-path executable
-- =====================================================
-- Reads a jq string from argv[0], parses it via Main.jqToJQuery,
-- maps to SQuery via the verified `jquery_to_squery`, prints the
-- SQuery as an SQL string, and emits a JSON document containing
--   sql        — the templatized SQL
--   jq         — the input
--   jq_result  — eval_jquery seedDB <parsed>
--   sq_result  — eval_squery (jdbToSdb seedDB) (translated)
--   match      — true iff the two evaluations agree structurally
--
-- This binary always uses Main's *correct* eval_jquery, so `match`
-- should always be true under the supported subset.

import Main
import JqGenMain
import Lean.Data.Json

open Lean

-- =====================================================
-- Seed: mirrors backend/seed_data.py.
-- Python USERS only carries (name, age); the role column is
-- defaulted to Role.student here. None of the supported queries
-- (find/delete/count over name+age) touch the role column, so
-- this default does not affect result equivalence.
-- =====================================================
def seedDB : JDB := [
  { name := "Alice",   age := 30, role := Role.student },
  { name := "Bob",     age := 25, role := Role.student },
  { name := "Charlie", age := 35, role := Role.student },
  { name := "Diana",   age := 28, role := Role.student },
  { name := "Eve",     age := 42, role := Role.student },
  { name := "Frank",   age := 19, role := Role.student },
  { name := "Grace",   age := 31, role := Role.student }
]

-- =====================================================
-- Source: shaped for forward-compatible composition.
-- Today this is a single-constructor inductive that always
-- resolves to "users". When the AST is later extended with
--   | sub : SQuery → Source
-- the printer recursion plugs in as one extra arm and every
-- existing call site already routes through `sourceToSql`.
-- =====================================================
inductive Source where
  | users : Source

def sourceToSql : Source → String
  | .users => "users"

-- =====================================================
-- SQL printer
-- =====================================================
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

-- Every arm routes its FROM through `sourceToSql`. No hardcoded "users".
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

-- =====================================================
-- jdbToSdb — lifted from Test.lean. Independent copy keeps
-- this binary free of the Test/Plausible dependency.
-- =====================================================
def jdbToSdb (jd : JDB) : SDB :=
  { names := jd.map (·.name),
    ages  := jd.map (·.age),
    roles := jd.map (·.role) }

-- =====================================================
-- JSON encoders
-- =====================================================
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

-- Decidable structural match via the toS bridge (mirrors Test.result_equiv_bool).
def resultsMatch : JResult → SResult → Bool
  | .db jd,  .db sd  => jd.map toS = sd.toRows
  | .num n,  .num m  => n = m
  | _,       _       => false

-- =====================================================
-- Main
-- =====================================================
def main (args : List String) : IO Unit := do
  let input := args.head?.getD ".[]"
  let jq := jqToJQuery input
  let sq := jquery_to_squery jq
  let sql := squeryToSql sq
  let jr := eval_jquery seedDB jq
  let sr := eval_squery (jdbToSdb seedDB) sq
  let m  := resultsMatch jr sr
  let out := Json.mkObj [
    ("sql",       .str sql),
    ("jq",        .str input),
    ("jq_result", jrToJson jr),
    ("sq_result", srToJson sr),
    ("match",     .bool m)
  ]
  IO.println out.compress
