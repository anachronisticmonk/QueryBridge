import Std
import Init.Data.String.TakeDrop

-- =====================================================
-- 1. Base Data Structures
-- =====================================================

inductive Role where
  | student | employee | retired
  deriving Repr, DecidableEq, BEq

-- JSON user
structure Juser where
  name : String
  age  : Nat
  role : Role
  deriving Repr, DecidableEq, BEq

-- SQL user
abbrev Suser : Type := String × Nat × Role

-- JSON Database
abbrev JDB := List Juser

-- Columnar SQL Database
structure SDB where
  names : List String
  ages  : List Nat
  roles : List Role
  deriving Repr, DecidableEq, BEq

def zip3 {α β γ : Type} : List α → List β → List γ → List (α × β × γ)
  | a :: as, b :: bs, c :: cs => (a, b, c) :: zip3 as bs cs
  | _, _, _ => []

def SDB.toRows (sd : SDB) : List Suser :=
  zip3 sd.names sd.ages sd.roles

-- =====================================================
-- 2. Conversion
-- =====================================================

def toS (u : Juser) : Suser := (u.name, u.age, u.role)
def toJ (s : Suser) : Juser := {name := s.1, age := s.2.1, role := s.2.2}

theorem toJ_toS (u : Juser) : toJ (toS u) = u := by
  simp [toJ, toS]

theorem toS_toJ (s : Suser) : toS (toJ s) = s := by
  obtain ⟨n, a, r⟩ := s
  rfl

-- =====================================================
-- 3. Schema & Values
-- =====================================================

inductive Col where
  | name | age | role | all
  deriving Repr, DecidableEq

inductive Value where
  | nat  : Nat → Value
  | str  : String → Value
  | role : Role → Value
  deriving Repr, DecidableEq

inductive Op where
  | eq | gt | lt | ge | le
  deriving Repr, DecidableEq

-- =====================================================
-- 4. Generic Condition Language
-- =====================================================

inductive Cond where
  | always : Cond
  | cmp    : Col → Op → Value → Cond
  | and    : Cond → Cond → Cond
  | or     : Cond → Cond → Cond
  deriving Repr, Inhabited

-- =====================================================
-- 5. Evaluation Helpers
-- =====================================================

def get_valJ (c : Col) (u : Juser) : Value :=
  match c with
  | Col.name => Value.str u.name
  | Col.age  => Value.nat u.age
  | Col.role => Value.role u.role
  | Col.all  => Value.str ""

def get_valS (c : Col) (s : Suser) : Value :=
  match c, s with
  | Col.name, (n, _, _) => Value.str n
  | Col.age,  (_, a, _) => Value.nat a
  | Col.role, (_, _, r) => Value.role r
  | Col.all,  _         => Value.str ""

def eval_op : Op → Value → Value → Bool
  | Op.eq, v1, v2 => v1 = v2
  | Op.gt, Value.nat a, Value.nat b => a > b
  | Op.lt, Value.nat a, Value.nat b => a < b
  | Op.ge, Value.nat a, Value.nat b => a ≥ b
  | Op.le, Value.nat a, Value.nat b => a ≤ b
  | _, _, _ => false

def Cond.evalJ : Cond → Juser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, u => eval_op op (get_valJ col u) v
  | Cond.and c1 c2, u => c1.evalJ u && c2.evalJ u
  | Cond.or c1 c2, u => c1.evalJ u || c2.evalJ u

def Cond.evalS : Cond → Suser → Bool
  | Cond.always, _ => true
  | Cond.cmp col op v, s => eval_op op (get_valS col s) v
  | Cond.and c1 c2, s => c1.evalS s && c2.evalS s
  | Cond.or c1 c2, s => c1.evalS s || c2.evalS s

-- Per-row update on a Juser.
def apply_updateJ (col : Col) (v : Value) (u : Juser) : Juser :=
  match col, v with
  | Col.name, Value.str s  => {u with name := s}
  | Col.age,  Value.nat n  => {u with age := n}
  | Col.role, Value.role r => {u with role := r}
  | _, _                   => u   -- no-op

-- Per-row update on an Suser
def apply_updateS (col : Col) (v : Value) (s : Suser) : Suser :=
  match col, v with
  | Col.name, Value.str n  => (n, s.2.1, s.2.2)
  | Col.age,  Value.nat a  => (s.1, a, s.2.2)
  | Col.role, Value.role r => (s.1, s.2.1, r)
  | _, _                   => s    -- no-op

-- Per-row update on a Juser by a condition
def apply_update_ifJ (col : Col) (v : Value) (c : Cond) (u : Juser) : Juser :=
  if c.evalJ u then apply_updateJ col v u else u

-- Per-row update on an Suser by a condition
def apply_update_ifS (col : Col) (v : Value) (c : Cond) (s : Suser) : Suser :=
  if c.evalS s then apply_updateS col v s else s

-- =====================================================
-- 6. Query Languages, Result Types & Semantics
-- =====================================================

inductive JQuery where
  | find    : Col → Cond → JQuery          -- jq's `.[] | select(cond)`
  | drop    : Cond → JQuery                -- jq's `.[] | select(cond | not)`
  | prepend : Juser → JQuery               -- jq's `[$u] + .`
  | clear   : JQuery                       -- jq's `[]`
  | length  : JQuery                       -- jq's `length`
  | modify  : Col → Value → Cond → JQuery  -- jq's `map(if cond then .col = v else . end)`
  deriving Repr

inductive SQuery where
  | select   : Col → Cond → SQuery          -- SQL's `SELECT * FROM users WHERE cond`
  | delete   : Cond → SQuery                -- SQL's `DELETE FROM users WHERE cond`
  | insert   : Suser → SQuery               -- SQL's `INSERT INTO users VALUES (n, a, r)`
  | truncate : SQuery                       -- SQL's `TRUNCATE TABLE users`
  | count    : SQuery                       -- SQL's `SELECT COUNT(*) FROM users`
  | update   : Col → Value → Cond → SQuery  -- SQL's `UPDATE users SET col = v WHERE cond`
  deriving Repr

/-- A query result is either a database (for transformation queries)
    or a scalar (for aggregate queries). --/
inductive JResult where
  | db  : JDB → JResult
  | num : Nat → JResult
  deriving Repr, DecidableEq, BEq

inductive SResult where
  | db  : SDB → SResult
  | num : Nat → SResult
  deriving Repr, DecidableEq, BEq

def eval_jquery (jd : JDB) : JQuery → JResult
  | JQuery.find _ c       => --JResult.db (jd.filter c.evalJ)
                             JResult.db (jd.filter (fun u => !c.evalJ u)) -- !!BUG!!
  | JQuery.drop c         => JResult.db (jd.filter (fun u => !(c.evalJ u)))
  | JQuery.prepend u      => JResult.db (u :: jd)
  | JQuery.clear          => JResult.db []
  | JQuery.length         => -- JResult.num jd.length
                             JResult.num 1 -- !!BUG!!
  | JQuery.modify _col _v _c => --JResult.db (jd.map (apply_update_ifJ col v c))
                                JResult.db []  -- !!BUG!!

def eval_squery (sd : SDB) : SQuery → SResult
  | SQuery.select _ c =>
      let rows := sd.toRows.filter c.evalS
      SResult.db { names := rows.map (·.1)
                   ages  := rows.map (·.2.1)
                   roles := rows.map (·.2.2) }
  | SQuery.delete c   =>
      let rows := sd.toRows.filter (fun s => !(c.evalS s))
      SResult.db { names := rows.map (·.1)
                   ages  := rows.map (·.2.1)
                   roles := rows.map (·.2.2) }
  | SQuery.insert s   =>
      SResult.db { names := s.1   :: sd.names
                   ages  := s.2.1 :: sd.ages
                   roles := s.2.2 :: sd.roles }
  | SQuery.truncate   =>
      SResult.db { names := [], ages := [], roles := [] }
  | SQuery.count      =>
      SResult.num sd.toRows.length
  | SQuery.update col v c =>
      let rows := sd.toRows.map (apply_update_ifS col v c)
      SResult.db { names := rows.map (·.1)
                   ages  := rows.map (·.2.1)
                   roles := rows.map (·.2.2) }

-- =====================================================
-- 7. Equivalence Relations & Translation
-- =====================================================

-- Set-membership equivalence: every JSON record corresponds to a row.
def equiv (jd : JDB) (sd : SDB) : Prop :=
  let rows := sd.toRows
  (∀ u : Juser, u ∈ jd ↔ toS u ∈ rows) ∧
  (∀ s : Suser, s ∈ rows ↔ toJ s ∈ jd)

/-- Permutation equivalence: tracks element MULTIPLICITY, not just
    membership. Strictly stronger than `equiv`. Required for any
    aggregate that isn't set-functional (count, sum, average, …). --/
def permEquiv (jd : JDB) (sd : SDB) : Prop :=
  List.Perm (jd.map toS) sd.toRows

def result_equiv : JResult → SResult → Prop
  | JResult.db jd,  SResult.db sd  => equiv jd sd
  | JResult.num n1, SResult.num n2 => n1 = n2
  | _, _ => False

def jquery_to_squery : JQuery → SQuery
  | JQuery.find c p       => SQuery.select c p
  | JQuery.drop p         => SQuery.delete p
  | JQuery.prepend u      => SQuery.insert (toS u)
  | JQuery.clear          => SQuery.truncate
  | JQuery.length         => SQuery.count
  | JQuery.modify col v c => SQuery.update col v c

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

  let orParts := s'.splitOn "||"
  if orParts.length > 1 then
    Cond.or (parseCond orParts.head!) (parseCond ("||".intercalate orParts.tail!))
  else
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
  -- Split on " | " (with spaces) so that `||` inside predicates is left intact
  -- for `parseCond`. Our generated jq always uses spaced top-level pipes.
  let parts := input.splitOn " | " |>.map (fun p => p.trimAscii.toString)
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
