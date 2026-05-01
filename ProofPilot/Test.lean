-- =====================================================
-- Test.lean — Top-level Plausible #test directives
-- =====================================================
-- This file is the editor-visible test runner: opening it in Lean
-- triggers each `#test` and the Plausible counter-examples appear
-- in the infoview / problems pane.
--
-- The same properties are also driven *programmatically* by the
-- `propRunner` binary (see PropRunner.lean), which serializes each
-- TestResult as JSON for the QueryBridge backend to surface in the
-- UI. Test.lean and PropRunner.lean must stay in sync — both pull
-- their definitions from `Properties.lean`.
--
-- The properties are checked against the buggy `eval_jquery` from
-- `Error.lean` (transitively via `Properties.lean`), so failing
-- `#test`s are expected. Building the `propRunner` exe is the
-- production path; running `lake env lean Test.lean` is the
-- developer-visible inspection path.

import Properties

#test ∀ jd col v c, prop_modify_preserves_count jd col v c = true
#test ∀ jd, prop_length_returns_count jd = true
#test ∀ jd jq, prop_translation_correct jd jq = true
#test ∀ jd, prop_find_always_is_identity jd = true
