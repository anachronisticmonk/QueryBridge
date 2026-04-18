import ProofPilot.Basic
/-!
# Type-Class Polymorphism Patterns

Illustrates the spectrum from explicit type arguments to fully inferred
instances. All examples compile under `grind`-augmented Mathlib.
-/
namespace ProofPilot.TypeClasses

-- ─────────────────────────────────────────────
-- 1. Implicit vs explicit type arguments
-- ─────────────────────────────────────────────

def doubleList  (α : Type)  (l : List α) : List α := l ++ l
def doubleList' {α : Type}  (l : List α) : List α := l ++ l

#eval doubleList  Nat [1, 2, 3]
#eval doubleList'     [1, 2, 3]

-- ─────────────────────────────────────────────
-- 2. Do-notation over List (monad instance)
-- ─────────────────────────────────────────────

def pairs {α β : Type} (l1 : List α) (l2 : List β) : List (α × β) := do
  let x ← l1; let y ← l2; return (x, y)

#eval pairs [1, 2] ["a", "b"]

-- ─────────────────────────────────────────────
-- 3. Structures and inheritance
-- ─────────────────────────────────────────────

structure Person where
  name : String
  age  : Nat
  deriving Repr, DecidableEq

structure Voter extends Person where
  voterId : Nat
  is_eligible : 18 ≤ age
  deriving Repr

def bob : Voter := { name := "Bob", age := 25, voterId := 42, is_eligible := by simp }

-- ─────────────────────────────────────────────
-- 4. Custom type-class instance
-- ─────────────────────────────────────────────

class Printable (α : Type) where
  display : α → String

instance : Printable Nat   where display n := s!"Nat({n})"
instance : Printable Bool  where display b := if b then "true" else "false"
instance [Printable α] [Printable β] : Printable (α × β) where
  display p := s!"({Printable.display p.1}, {Printable.display p.2})"

#eval Printable.display (42, true)

end ProofPilot.TypeClasses
