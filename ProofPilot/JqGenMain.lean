import Main
import Lean.Data.Json

open Lean

-- =====================================================
-- 9. Parser Logic
-- =====================================================

partial def parseCond (s : String) : Cond :=
  let s' := s.trimAscii.toString

  -- Try to parse a string as a Role; returns none if it's not a known tag.
  let parseRole? (raw : String) : Option Role :=
    match raw.trimAscii.toString with
    | "student"  => some Role.student
    | "employee" => some Role.employee
    | "retired"  => some Role.retired
    | _          => none

  -- Detect which column an LHS like `.age` or `.role` refers to.
  let detectCol (lhs : String) : Col :=
    if lhs.contains "role" then Col.role
    else if lhs.contains "age" then Col.age
    else Col.name

  -- Parse a value, choosing the right Value variant based on context.
  -- For comparison RHS we know the column from `detectCol`, so role
  -- strings become Value.role rather than Value.str.
  let parseValForCol (col : Col) (str : String) : Value :=
    let trimmed := str.trimAscii.toString
    let unquoted :=
      if trimmed.front? = some '"' then
        ((trimmed.drop 1).dropEnd 1).toString
      else trimmed
    match col with
    | Col.role =>
        match parseRole? unquoted with
        | some r => Value.role r
        | none   => Value.str unquoted
    | Col.age => Value.nat unquoted.toNat!
    | _       => Value.str unquoted

  let andParts := s'.splitOn "&&"
  if andParts.length > 1 then
    Cond.and (parseCond andParts.head!) (parseCond ("&&".intercalate andParts.tail!))
  else if s'.contains "==" then
    let parts := s'.splitOn "=="
    let col := detectCol parts.head!
    Cond.cmp col Op.eq (parseValForCol col parts.getLast!)
  else if s'.contains ">=" then
    let parts := s'.splitOn ">="
    let col := detectCol parts.head!
    Cond.cmp col Op.ge (parseValForCol col parts.getLast!)
  else if s'.contains "<=" then
    let parts := s'.splitOn "<="
    let col := detectCol parts.head!
    Cond.cmp col Op.le (parseValForCol col parts.getLast!)
  else if s'.contains ">" then
    let parts := s'.splitOn ">"
    let col := detectCol parts.head!
    Cond.cmp col Op.gt (parseValForCol col parts.getLast!)
  else if s'.contains "<" then
    let parts := s'.splitOn "<"
    let col := detectCol parts.head!
    Cond.cmp col Op.lt (parseValForCol col parts.getLast!)
  else
    Cond.always

/-- Parse a user record from a string like `"Charlie", 25, "student"` --/
def parseUser (s : String) : Juser :=
  let parts := s.splitOn "," |>.map (fun p => p.trimAscii.toString)
  let stripQuotes (raw : String) : String :=
    let t := raw.trimAscii.toString
    if t.front? = some '"' then ((t.drop 1).dropEnd 1).toString else t
  let parseRole (raw : String) : Role :=
    match stripQuotes raw with
    | "student"  => Role.student
    | "employee" => Role.employee
    | "retired"  => Role.retired
    | _          => Role.student   -- default fallback
  match parts with
  | [nameStr, ageStr, roleStr] =>
      { name := stripQuotes nameStr
        age  := ageStr.trimAscii.toString.toNat!
        role := parseRole roleStr }
  | _ => { name := "", age := 0, role := Role.student }

def jqToJQuery (input : String) : JQuery :=
  let parts := input.splitOn "|" |>.map (fun p => p.trimAscii.toString)
  match parts with
  | ["length"] => JQuery.length
  | [".[]"]    => JQuery.find Col.all Cond.always
  | [".[]", sel] =>
      if sel.startsWith "insert(" then
        let inner := sel.replace "insert(" "" |>.replace ")" ""
        JQuery.prepend (parseUser inner)
      else if sel == "clear()" || sel == "clear" then
        JQuery.clear
      else if sel == "count()" || sel == "count" || sel == "length" then
        JQuery.length
      else if sel.startsWith "update(" || sel.startsWith "modify(" then
        -- update(<col>, <value>, <cond>)  — also accepts modify(...)
        -- Examples:
        --   update(.age, 50, .age > 30)
        --   modify(.role, "retired", .age > 60)
        let inner := (sel.replace "update(" "" |>.replace "modify(" "" |>.replace ")" "")
        let detectCol (lhs : String) : Col :=
          if lhs.contains "role" then Col.role
          else if lhs.contains "age" then Col.age
          else Col.name
        let parseRole? (raw : String) : Option Role :=
          match raw.trimAscii.toString with
          | "student"  => some Role.student
          | "employee" => some Role.employee
          | "retired"  => some Role.retired
          | _          => none
        let parseValForCol (col : Col) (str : String) : Value :=
          let trimmed := str.trimAscii.toString
          let unquoted :=
            if trimmed.front? = some '"' then
              ((trimmed.drop 1).dropEnd 1).toString
            else trimmed
          match col with
          | Col.role =>
              match parseRole? unquoted with
              | some r => Value.role r
              | none   => Value.str unquoted
          | Col.age => Value.nat unquoted.toNat!
          | _       => Value.str unquoted
        -- Split on the first two top-level commas; the rest is the condition.
        let bits := inner.splitOn ","
        match bits with
        | colStr :: valStr :: rest =>
            let condStr := ",".intercalate rest
            let col := detectCol colStr
            JQuery.modify col (parseValForCol col valStr) (parseCond condStr)
        | _ => JQuery.modify Col.all (Value.str "") Cond.always
      else
        let inner := sel.replace "select(" "" |>.replace "delete(" "" |>.replace ")" ""
        if sel.startsWith "delete(" then JQuery.drop (parseCond inner)
        else JQuery.find Col.all (parseCond inner)
  | [".[]", sel, projection] =>
      -- .[] | select(<cond>) | .<col>
      if sel.startsWith "select(" && projection.startsWith "." then
        let inner := sel.replace "select(" "" |>.replace ")" ""
        let colName := projection.drop 1
        let col :=
          if colName.contains "role" then Col.role
          else if colName.contains "age" then Col.age
          else if colName.contains "name" then Col.name
          else Col.all
        JQuery.find col (parseCond inner)
      else
        JQuery.find Col.all Cond.always
  | _ => JQuery.find Col.all Cond.always

-- =====================================================
-- 10. Execution Examples
-- =====================================================

def myColDB : SDB := {
  names := ["Alice", "Bob"],
  ages  := [35, 20],
  roles := [Role.employee, Role.student]
}

def myDB : JDB := [
  { name := "Alice", age := 35, role := Role.employee },
  { name := "Bob",   age := 20, role := Role.student }
]

#guard myColDB.toRows =
  [("Alice", 35, Role.employee),
   ("Bob",   20, Role.student)]

#guard eval_jquery myDB (jqToJQuery ".[] | select(.age > 30)")
  = JResult.db [{ name := "Alice", age := 35, role := Role.employee }]

#guard eval_squery myColDB
  (jquery_to_squery (jqToJQuery ".[] | select(.age > 30)")) =
  SResult.db {
    names := ["Alice"],
    ages  := [35],
    roles := [Role.employee]
  }

-- Filter on the new Role-typed column. Role literals in the surface
-- syntax are quoted strings ("student", "employee", "retired") and
-- the parser routes them to Value.role automatically.
#guard eval_jquery myDB
  (jqToJQuery ".[] | select(.role == \"student\")") =
  JResult.db [{ name := "Bob", age := 20, role := Role.student }]

#guard eval_squery myColDB
  (jquery_to_squery
    (jqToJQuery ".[] | select(.role == \"student\")")) =
  SResult.db {
    names := ["Bob"],
    ages  := [20],
    roles := [Role.student]
  }

-- Direct construction of a role comparison (no parser).
#guard eval_jquery myDB
  (JQuery.find Col.all (Cond.cmp Col.role Op.eq (Value.role Role.employee))) =
  JResult.db [{ name := "Alice", age := 35, role := Role.employee }]

#guard eval_jquery myDB (jqToJQuery ".[] | clear()") =
  JResult.db []

#guard eval_squery myColDB
  (jquery_to_squery (jqToJQuery ".[] | clear()")) =
  SResult.db { names := [], ages := [], roles := [] }

#guard eval_jquery myDB (jqToJQuery ".[] | count") =
  JResult.num 2

#guard eval_squery myColDB
  (jquery_to_squery (jqToJQuery ".[] | count")) =
  SResult.num 2

#guard eval_jquery myDB JQuery.length =
  JResult.num 2

#guard eval_squery myColDB SQuery.count =
  SResult.num 2

-- Insert via parser; third field is now a quoted role tag.
#guard eval_jquery myDB
  (jqToJQuery ".[] | insert(\"Charlie\", 25, \"retired\")") =
  JResult.db [
    { name := "Charlie", age := 25, role := Role.retired },
    { name := "Alice",   age := 35, role := Role.employee },
    { name := "Bob",     age := 20, role := Role.student }
  ]

-- Modify a Nat column.
#guard eval_jquery myDB
  (JQuery.modify Col.age (Value.nat 50)
    (Cond.cmp Col.age Op.gt (Value.nat 30))) =
  JResult.db [
    { name := "Alice", age := 50, role := Role.employee },
    { name := "Bob",   age := 20, role := Role.student }
  ]

-- Modify the Role column: promote everyone over 30 to retired.
#guard eval_jquery myDB
  (JQuery.modify Col.role (Value.role Role.retired)
    (Cond.cmp Col.age Op.gt (Value.nat 30))) =
  JResult.db [
    { name := "Alice", age := 35, role := Role.retired },
    { name := "Bob",   age := 20, role := Role.student }
  ]

-- Modify the Role column via the parser.
#guard eval_jquery myDB
  (jqToJQuery ".[] | update(.role, \"retired\", .age > 30)") =
  JResult.db [
    { name := "Alice", age := 35, role := Role.retired },
    { name := "Bob",   age := 20, role := Role.student }
  ]

#guard eval_jquery ([] : JDB) JQuery.length =
  JResult.num 0

#guard eval_jquery ([] : JDB)
  (JQuery.modify Col.age (Value.nat 0) Cond.always) =
  JResult.db []
