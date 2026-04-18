import Mathlib

/-!
# ProofPilot — Basic Setup

Shared imports and utilities used across the library.
-/

macro_rules | `(tactic | decreasing_tactic) => `(tactic | grind)
