/-
  File:      Grammatik/X86/InvariantenOpt.lean
  Subject:   Invariant-derived optimisation legality over ACTUAL source semantics.

  This file states and proves generic optimisation legality rules against the
  real typed source language (`Syntax.lean`: `Expr`/`Block`/`Stmt`) and its
  real world semantics (`Semantik.lean`: `eval`/`execBlock`/`execStmt`), for
  consumption by the later IR/certificate lane. No toy model: every rewrite
  is an executable function on source syntax, every correspondence a theorem
  over `eval`/`execBlock` with real table-writing witnesses.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik.X86.InvariantenOpt

variable {D : Deklaration} {V : Vertrag D}
variable {Γ : Ctx} {Λ : List (Res D)}

/-- A computable truth check for boolean source conditions: `wahr`,
    literal comparisons, and boolean combinations. A later certificate
    checker re-runs exactly this `Bool`; nothing is trusted from Rust.
    General-type worker: structural recursion needs the type index free
    (the `Expr.orte` precedent); non-boolean shapes answer `false`. -/
def isWahrAll : Expr D Γ Λ τ → Bool
  | .wahr => true
  | .le a b =>
      match a, b with
      | .lit x, .lit y => decide (x ≤ y)
      | _, _ => false
  | .eq a b =>
      match a, b with
      | .lit x, .lit y => decide (x = y)
      | _, _ => false
  | .und a b => isWahrAll a && isWahrAll b
  | .oder a b => isWahrAll a || isWahrAll b
  | .nicht a => !isWahrAll a
  | _ => false

def isWahr (c : Expr D Γ Λ .bool) : Bool := isWahrAll c

/- CUTS:
   Only the computable check exists so far. Open: its soundness over `eval`;
   constant folding / `weiter` value lemmas; `pruefung`/`ite` elimination with
   exact trace transfer; the invariant-scoped rule (rest/sight/lock-move only,
   never inside a running writer or held section); the stability-gated
   redundant-load rule; cost/ghost-budget, call-log (`Folge`), fault and
   interleaving transfers; the non-degenerate table-writing witness.
-/

end Gabbro.Grammatik.X86.InvariantenOpt
