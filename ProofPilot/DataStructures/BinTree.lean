import ProofPilot.Basic
/-!
# Binary Trees — Membership and Traversal

Defines `BinTree`, converts it to a `List`, and proves that membership
in the tree is equivalent to membership in the flattened list.
All proofs close with `grind` using the annotated lemmas.
-/
namespace ProofPilot.BinTree

variable {α : Type}

inductive BinTree (α : Type) where
  | leaf : α → BinTree α
  | node : BinTree α → BinTree α → BinTree α
  deriving Repr, Inhabited

open BinTree

@[grind .]
def toList : BinTree α → List α
  | leaf x     => [x]
  | node l r   => toList l ++ toList r

def mem : BinTree α → α → Prop
  | leaf x,   y => x = y
  | node l r, y => mem l y ∨ mem r y

@[grind .]
instance : Membership α (BinTree α) where
  mem := mem

@[grind ., simp] theorem mem_leaf (x y : α) : y ∈ leaf x ↔ x = y := by
  simp [mem, Membership.mem]

@[grind ., simp] theorem mem_node (l r : BinTree α) (y : α) :
    y ∈ node l r ↔ y ∈ l ∨ y ∈ r := by
  simp [mem, Membership.mem]

theorem mem_iff_mem_toList (t : BinTree α) (x : α) :
    x ∈ t ↔ x ∈ toList t := by
  induction t with
  | leaf a      => grind
  | node l r ih_l ih_r => grind

end ProofPilot.BinTree
