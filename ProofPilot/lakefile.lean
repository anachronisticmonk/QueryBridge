import Lake
open Lake DSL

package «ProofPilot» where
  -- Per-package options can go here.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "main"

@[default_target]
lean_lib «ProofPilot» where
  roots := #[`Error, `Test]
