import ProofPilot.Lang.ImpLang
/-!
# ImpLang Examples

Demonstrates the `#run` command and `eval%` macro.
-/
open ImpLang

-- Conditional
#run
  n := 3; m := 9;
  if (n ≤ 4) { n := 5 + 3 } else { n := 2; m := 7 }
  return

-- Summation loop: sum = 1 + 2 + ... + 10
#run
  n := 10; sum := 0; i := 1;
  while (i ≤ n) { sum := sum + i; i := i + 1 }
  return

-- Primality test as a Lean term
def isPrime57 : String :=
  eval%
    n := 57; i := 2; is_prime := 1;
    while (i < n && is_prime = 1) {
      if (i ∣ n) { is_prime := 0 } else {};
      i := i + 1
    }
    return s!"57 prime? {is_prime == 1}"

#eval isPrime57
