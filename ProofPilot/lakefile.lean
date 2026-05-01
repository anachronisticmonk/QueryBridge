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
  roots := #[`Main, `Error, `Bug2, `Bug3, `Properties, `Test, `SqlGenMain, `SqlGenError, `JqGenMain, `PropRunner, `ProofTrace]

lean_exe sqlGenMain where
  root := `SqlGenMain

lean_exe sqlGenError where
  root := `SqlGenError

lean_exe sqlGenBug2 where
  root := `SqlGenBug2

lean_exe sqlGenBug3 where
  root := `SqlGenBug3

lean_exe jqGenMain where
  root := `JqGenMain

lean_exe propRunner where
  root := `PropRunner

lean_exe proofTrace where
  root := `ProofTrace

lean_exe test where
  root := `Test
