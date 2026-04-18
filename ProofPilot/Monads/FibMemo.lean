import Std
/-!
# Fibonacci with Memoization via State Monad

Demonstrates `StateM` for memoized computation. The naive recursive
definition recalculates the same subproblems exponentially; the monadic
version stores results in a `HashMap` carried through the `State`.
-/
namespace ProofPilot.FibMemo

def slowFib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => slowFib (n + 1) + slowFib n

open Std

abbrev FibM := StateM (HashMap Nat Nat)

def fibM (n : Nat) : FibM Nat := do
  let cache ← get
  match cache.get? n with
  | some v => return v
  | none =>
    match n with
    | 0 => modify (·.insert 0 0); return 0
    | 1 => modify (·.insert 1 1); return 1
    | n + 2 =>
      let a ← fibM (n + 1)
      let b ← fibM n
      let r := a + b
      modify (·.insert (n + 2) r)
      return r

#eval fibM 100 |>.run' {}

end ProofPilot.FibMemo
