import Lean
import Std

open Lean Meta Elab Term

/-!
# ImpLang — A Tiny Imperative DSL

A shallow-embedded imperative language inspired by the IMP language from
Software Foundations. Variables hold `Nat`; expressions are Lean terms
evaluated in a variable-binding context via meta-programming.

Statements:
- `x := expr`       — assignment
- `if (b) { } else { }` — conditional
- `while (b) { }`   — loop
- `print expr`      — IO output
-/

-- ─── Expression helpers ────────────────────────────────────────────────────

private def exprRelVars (vars : List (Name × Nat)) (stx : Syntax.Term) : MetaM Syntax.Term :=
  match vars with
  | [] => return stx
  | (n, v) :: rest => do
    let inner ← exprRelVars rest stx
    `((fun ($(mkIdent n) : $(mkIdent ``Nat)) => $inner) $(Syntax.mkNumLit (toString v)))

private def evalNatM (vars : List (Name × Nat)) (t : Syntax.Term) : TermElabM Nat := do
  let stx ← exprRelVars vars t
  let e ← withoutErrToSorry <| elabTermEnsuringType stx (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Nat (mkConst ``Nat) e

private def evalBoolM (vars : List (Name × Nat)) (t : Syntax.Term) : TermElabM Bool := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Bool)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Bool (mkConst ``Bool) e

private def evalStrM (vars : List (Name × Nat)) (t : Syntax.Term) : TermElabM String := do
  let stx ← exprRelVars vars t
  let e ← withoutErrToSorry <| elabTermEnsuringType stx (mkConst ``String)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr String (mkConst ``String) e

-- ─── Interpreter monad ─────────────────────────────────────────────────────

namespace ImpLang

abbrev ImpState := Std.HashMap Name Nat
abbrev ImpM     := StateT ImpState TermElabM

private def getNat  (t : Syntax.Term) : ImpM Nat    := do evalNatM  (← get).toList t
private def getBool (t : Syntax.Term) : ImpM Bool   := do evalBoolM (← get).toList t
private def getStr  (t : Syntax.Term) : ImpM String := do evalStrM  (← get).toList t
private def setVar  (n : Name) (v : Nat) : ImpM Unit := modify (·.insert n v)

declare_syntax_cat imp_stmt
syntax imp_block   := "{" sepBy(imp_stmt, ";", ";", allowTrailingSep) "}"
syntax imp_program := sepBy(imp_stmt, ";", ";", allowTrailingSep)

syntax imp_block                                        : imp_stmt
syntax ident ":=" term                                  : imp_stmt
syntax "if" "(" term ")" imp_block "else" imp_block     : imp_stmt
syntax "while" "(" term ")" imp_block                   : imp_stmt
syntax "print" term                                     : imp_stmt

private partial def runStmt : TSyntax `imp_stmt → ImpM Unit
  | `(imp_stmt| {$s;*}) => s.getElems.forM runStmt
  | `(imp_stmt| $x:ident := $e) => do setVar x.getId (← getNat e)
  | `(imp_stmt| if ($p) $t else $f) => do
    if ← getBool p then runBlock t else runBlock f
  | `(imp_stmt| while ($p) $b) => do
    let rec loop : ImpM Unit := do
      if ← getBool p then runBlock b; loop
    loop
  | stx@`(imp_stmt| print $s) => do
    logInfoAt stx (← getStr s)
  | _ => throwUnsupportedSyntax
where runBlock : TSyntax ``imp_block → ImpM Unit
  | `(imp_block| {$s;*}) => s.getElems.forM runStmt
  | _ => throwUnsupportedSyntax

private def runProgram (pgm : TSyntax ``imp_program) : ImpM Unit :=
  match pgm with
  | `(imp_program| $s;*) => s.getElems.forM runStmt
  | _ => throwUnsupportedSyntax

-- ─── Surface syntax ────────────────────────────────────────────────────────

elab "#run" ss:imp_program "return" : command =>
  Command.liftTermElabM do
    let (_, m) ← runProgram ss |>.run {}
    logInfo m!"State: {m.toList}"

elab "eval%" ss:imp_program "return" v:term : term => do
  let (_, m) ← runProgram ss |>.run {}
  let t ← exprRelVars m.toList v
  elabTerm t none

end ImpLang
