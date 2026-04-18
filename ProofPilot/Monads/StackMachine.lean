import ProofPilot.Basic
/-!
# Stack Machine with Verified Evaluation

A simple stack-based instruction set. We define an inductive
`ValidProgram` predicate and prove that validity is equivalent to
`eval?` returning `some`. The proofs make heavy use of `grind`.
-/
namespace ProofPilot.StackMachine

inductive Instr
  | push (n : Nat)
  | pop
  | add
  deriving Repr

open Instr

abbrev Stack   := List Nat
abbrev Program := List Instr

def eval? (p : Program) (s : Stack) : Option Stack :=
  match p with
  | []           => some s
  | push n :: p' => eval? p' (n :: s)
  | pop  :: p'   => s.tail?.bind (eval? p')
  | add  :: p'   =>
    match s with
    | x :: y :: zs => eval? p' ((x + y) :: zs)
    | _            => none

@[grind cases]
inductive ValidProgram : Nat → Program → Prop
  | nil  : ValidProgram n []
  | push : ValidProgram (n + 1) p → ValidProgram n (push k :: p)
  | pop  : ValidProgram n p       → ValidProgram (n + 1) (pop :: p)
  | add  : ValidProgram (n + 1) p → ValidProgram (n + 2) (add :: p)

@[simp, grind .] theorem vp_nil  : ValidProgram n [] := ValidProgram.nil
@[simp, grind .] theorem vp_push (h : ValidProgram (n+1) p) : ValidProgram n (push k :: p) := .push h
@[simp, grind .] theorem vp_add  (h : ValidProgram (k+1) p) : ValidProgram (k+2) (add :: p) := .add h
@[simp]          theorem vp_pop  (h : ValidProgram n p)     : ValidProgram (n+1) (pop :: p) := .pop h

example (a b : Nat) : ValidProgram 0 [push a, push b, add] := by grind

end ProofPilot.StackMachine
