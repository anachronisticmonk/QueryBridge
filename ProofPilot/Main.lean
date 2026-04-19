import ProofPilot.Lang.QueryEquiv
/-!
# ProofPilot CLI

Called by lean-server as:
  lake exe proofpilot '<jquery JSON>'

Input JSON shape:
  { "type": "find" | "delete", "pred": { "field": "age", "op": "lt", "value": 10 } }

Exit 0 + stdout "verified"   → query_equiv covers this query.
Exit 0 + stdout "out_of_scope" → query type or field not yet proved.
Exit 1                         → JSON parse error.

The proof (query_equiv) is universal — it holds for ALL JDB/SDB pairs and
ALL JQuery values. So if the query parses into a valid JQuery, it is proved.
If lake build itself fails, lean-server catches the exec error and reports
that the proof is broken.
-/

open QueryEquiv Concrete

-- ── Minimal JSON parser for the fixed CLI schema ──────────────────────────

def extractStr (json key : String) : Option String := do
  let needle := s!"\"{key}\":"
  let i ← json.findSubstr? needle
  let rest := (json.drop (i.2 + 1)).dropWhile (· != '"') |>.drop 1
  return rest.takeWhile (· != '"')

def extractNat (json key : String) : Option Nat := do
  let needle := s!"\"{key}\":"
  let i ← json.findSubstr? needle
  let rest := (json.drop (i.2 + 1)).dropWhile (fun c => !c.isDigit)
  (rest.takeWhile Char.isDigit).toNat?

def parseOp (s : String) : Option CompOp :=
  match s with
  | "lt" => some .lt | "le" => some .le
  | "gt" => some .gt | "ge" => some .ge
  | "eq" => some .eq | "ne" => some .ne
  | _    => none

def parsePred (json : String) : Option Pred := do
  let field ← extractStr json "field"
  let opStr ← extractStr json "op"
  let op    ← parseOp opStr
  let value ← extractNat json "value"
  return { field, op, value }

def parseJQuery (json : String) : Except String (Option JQuery) := do
  let kind ← (extractStr json "type").toExcept "missing \"type\""
  let pred ← (parsePred json).toExcept "could not parse pred"
  return toJQuery kind pred

-- ── Main ──────────────────────────────────────────────────────────────────

def main (args : List String) : IO Unit := do
  let json := args.getD 0 ""
  match parseJQuery json with
  | .error msg =>
    IO.eprintln s!"parse_error: {msg}"
    IO.eprintln s!"input was: {json}"
    IO.Process.exit 1
  | .ok none =>
    -- Parsed fine but query type is not in the current proof scope
    IO.println "out_of_scope"
    IO.println "reason: query type not yet covered by query_equiv"
    IO.println s!"input: {json}"
  | .ok (some _jq) =>
    -- query_equiv : ∀ jd sd jq, equiv jd sd → equiv (eval_jquery jd jq) (eval_squery sd (jqueryToSquery jq))
    -- _jq is a valid JQuery → theorem applies universally
    IO.println "verified"
    IO.println "theorem: QueryEquiv.query_equiv"
    IO.println s!"covers: find | delete over any equiv JDB/SDB pair"
