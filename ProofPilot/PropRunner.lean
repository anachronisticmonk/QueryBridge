-- =====================================================
-- PropRunner — programmatic Plausible runner
-- =====================================================
-- IO binary that runs each property defined in Properties.lean
-- against the *buggy* eval_jquery (Error.lean), capturing the
-- structured TestResult that Plausible returns. The TestResult
-- is then serialized as JSON and printed to stdout so the
-- QueryBridge backend can surface counter-examples in the UI
-- without having to scrape Plausible's text output.
--
-- Each output object carries:
--   id              — stable identifier matching the Lean def name
--   title           — human-readable name
--   prop            — the proposition source as written
--   description     — plain-English meaning of the property
--   bug             — which buggy eval_jquery arm makes this fail
--   status          — "success" | "gaveUp" | "failure"
--   counterExample  — list of binding strings (only on failure)
--   shrinks         — number of shrink steps (only on failure)
--   gaveUpAfter     — number of attempts (only on gaveUp)
--
-- Shape mirrors Plausible.TestResult (see Plausible/Testable.lean).

import Properties
import Lean.Data.Json

open Lean
open Plausible
open Plausible.Decorations

/-- Run one property; return the result as a JSON object. -/
def runOne
    (id : String) (title : String) (prop : String)
    (description : String) (bug : String)
    (cfg : Configuration)
    (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO Json := do
  let common : List (String × Json) := [
    ("id",          .str id),
    ("title",       .str title),
    ("prop",        .str prop),
    ("description", .str description),
    ("bug",         .str bug)
  ]
  match ← Testable.checkIO p' cfg with
  | TestResult.success _ =>
    return Json.mkObj (common ++ [("status", .str "success")])
  | TestResult.gaveUp n =>
    return Json.mkObj (common ++ [
      ("status",      .str "gaveUp"),
      ("gaveUpAfter", Json.num n)
    ])
  | TestResult.failure _ xs n =>
    let arr : Array Json := (xs.map Json.str).toArray
    return Json.mkObj (common ++ [
      ("status",         .str "failure"),
      ("counterExample", Json.arr arr),
      ("shrinks",        Json.num n)
    ])

def main : IO Unit := do
  -- Use Plausible's default Configuration so this binary's output
  -- matches what `#test` shows in the Lean infoview when Test.lean
  -- is opened in an editor. Both paths bottom out in the same
  -- `Testable.checkIO p {}` call.
  let cfg : Configuration := {}
  let r1 ← runOne
    "prop_modify_preserves_count"
    "Modify preserves row count"
    "∀ jd col v c, prop_modify_preserves_count jd col v c = true"
    "Updating field values must never change how many rows the database holds."
    "eval_jquery (JQuery.modify _ _ _) returns JResult.db [] (drops every row)."
    cfg
    (∀ jd col v c, prop_modify_preserves_count jd col v c = true)
  let r2 ← runOne
    "prop_length_returns_count"
    "Length returns the row count"
    "∀ jd, prop_length_returns_count jd = true"
    "JQuery.length must report the actual number of rows in the database."
    "eval_jquery JQuery.length returns the constant JResult.num 1 instead of jd.length."
    cfg
    (∀ jd, prop_length_returns_count jd = true)
  let r3 ← runOne
    "prop_translation_correct"
    "jq ↔ SQL translation correctness"
    "∀ jd jq, prop_translation_correct jd jq = true"
    ("Evaluating any jq query on a JSON database and evaluating the " ++
     "translated SQL on the column-projected database must yield equivalent results.")
    "Multiple arms of eval_jquery diverge from eval_squery (find inverted, length=1, modify=[])."
    cfg
    (∀ jd jq, prop_translation_correct jd jq = true)
  let r4 ← runOne
    "prop_find_always_is_identity"
    "find Col.all Cond.always is the identity"
    "∀ jd, prop_find_always_is_identity jd = true"
    "Selecting every row with an always-true predicate must return the input database unchanged."
    "eval_jquery (JQuery.find _ c) filters by ¬c instead of c — find Cond.always returns []."
    cfg
    (∀ jd, prop_find_always_is_identity jd = true)
  let arr : Array Json := #[r1, r2, r3, r4]
  IO.println (Json.arr arr).compress
