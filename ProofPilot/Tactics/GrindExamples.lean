import ProofPilot.Basic
/-!
# Grind Tactic Showcase

`grind` is Lean 4's powerful ground-truth tactic. It combines:
- E-matching (equational rewriting)
- Congruence closure
- Linear arithmetic (CutSat)
- Case-splits on inductive types

The examples here illustrate how `@[grind .]` annotations on definitions
and theorems feed into the `grind` oracle.
-/
namespace ProofPilot.GrindExamples

-- ─────────────────────────────────────────────
-- 1. Arithmetic
-- ─────────────────────────────────────────────

example (n : Nat) : n + 0 = n := by grind
example (n m : Nat) (h : n ≤ m) : n ≤ m + 1 := by grind

-- ─────────────────────────────────────────────
-- 2. Propositional logic
-- ─────────────────────────────────────────────

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by grind
example (p q : Prop) (h : p ∨ q) (hnp : ¬p) : q := by grind

-- ─────────────────────────────────────────────
-- 3. Inductive types with @[grind cases]
-- ─────────────────────────────────────────────

inductive Color | red | green | blue deriving DecidableEq, Repr

@[grind cases]
def isRed : Color → Bool | .red => true | _ => false

example : isRed .red = true  := by grind
example : isRed .blue = false := by grind

-- ─────────────────────────────────────────────
-- 4. Irrational numbers (classical reasoning)
-- ─────────────────────────────────────────────

noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

theorem sq_sq_sq : (sqrt2 ^ sqrt2) ^ sqrt2 = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt] <;> simp

theorem irrational_power_example :
    ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : Irrational (sqrt2 ^ sqrt2)
  · exact ⟨_, _, h, irrational_sqrt_two, by rw [sq_sq_sq]; norm_cast; simp⟩
  · exact ⟨sqrt2, sqrt2, irrational_sqrt_two, irrational_sqrt_two, h⟩

end ProofPilot.GrindExamples
