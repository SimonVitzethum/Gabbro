/-
  File:      Grammatik/KorrespondenzBlockZeuge.lean
  Subject:   PROBES for the BLOCK structure of the correspondence
             certificate (`KorrespondenzAllg.lean`: `blOk`, and the `stOk`
             arms that carry a block).

  WHY THIS FILE EXISTS. The block rows are the first rows of `korrOk` that
  carry OTHER ROWS, and a check over a row list can go wrong in ways a flat
  row cannot: it can take the `else` arm for the `then` arm, it can let an
  arm be SHORTER than the Gabbro block it is supposed to be, and it can
  bind a loop or a call result to a local that the rows after it do not
  read. So every new arm gets BOTH probes:
  * a POSITIVE probe -- the emitted form the arm is meant to accept;
  * a PLANTED DEFECT -- exactly the mistake the arm exists to catch.

  THE FIXTURE is the one of `KorrespondenzWeitZeuge.lean` (`wD`, `wEL`,
  `wK`: one table `T` of four `u32` slots, two `u32` parameters in C locals
  `0` and `1`), so that the probes below add a block structure over a
  statement stock that is already probed. Everything is `decide`.
-/
import Grammatik.KorrespondenzWeitZeuge

namespace Gabbro.Grammatik.BlockZeuge

open Gabbro.Grammatik Gabbro.Grammatik.WeitZeuge

/-! ## 1. The two arms of an `if` -/

/-- The C cell type of the fixture's locals. -/
abbrev bU32c : CTy := .int false .w32

/-- `a = 1;` -- ONE statement, and the `else` arm's is a different one, so
    "the two branches swapped" is a defect the probe can see. -/
def bArmT : Block wD wV false wCtx [] [] :=
  .cons (Stmt.assignVar .hier (.weiter (by decide) (by decide) (Expr.lit 1))) .nil

/-- `a = 2;` -/
def bArmE : Block wD wV false wCtx [] [] :=
  .cons (Stmt.assignVar .hier (.weiter (by decide) (by decide) (Expr.lit 2))) .nil

/-- `if (a < b) { a = 1; } else { a = 2; }` -/
def bIte : Stmt wD wV false wCtx [] [] := .ite (Expr.lt x0 x1) bArmT bArmE

def bRowT : GRow := .setVar 0 bU32c (.lit 1)
def bRowE : GRow := .setVar 0 bU32c (.lit 2)
def bCond : CX := .cmp .lt CIT.u32 (.var 0) (.var 1)

/-- The `if` row, accepted and refused. The PLANTED DEFECTS are the four
    ways a block check can be wrong where a flat one cannot: the two
    branches swapped, a statement DROPPED from one branch (in both
    branches, separately), a statement ADDED to one branch -- and, for
    completeness, the condition read as the opposite comparison. -/
theorem probe_ite :
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowT] [bRowE]) = true ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowE] [bRowT]) = false ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [] [bRowE]) = false ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowT] []) = false ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowT, bRowE] [bRowE]) = false ∧
    stOk wEL wFnum wZert wK bIte
      (.ite (.cmp .ge CIT.u32 (.var 0) (.var 1)) [bRowT] [bRowE]) = false := by
  decide

/-- An `if` row against a statement that is NOT an `if` is refused, and a
    non-`if` row against the `if` statement is refused: the arm reads the
    Gabbro side, not only the C side. -/
theorem probe_ite_fremd :
    stOk wEL wFnum wZert wK bIte bRowT = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.assignVar (V := wV) (l := false) (Λ := []) .hier
        (.weiter (by decide) (by decide) (Expr.lit 1)))
      (.ite bCond [bRowT] [bRowE]) = false := by
  decide

/-! ## 2. The block check itself

    `blOk` walks a `Block` (an arm, later a loop body) against its rows.
    It is the same reading `enOk` gives a terminal block, minus the
    `return` -- a block ENDS, it does not answer. -/

/-- `(void)a; a = 1;` -- the unused-parameter row and a statement. -/
theorem probe_blOk_void :
    blOk wEL wFnum wZert wK bArmT [.void 0, bRowT] = true ∧
    blOk wEL wFnum wZert wK bArmT [.void 7, bRowT] = false ∧
    blOk wEL wFnum wZert wK bArmT [bRowT] = true ∧
    blOk wEL wFnum wZert wK bArmT [] = false ∧
    blOk wEL wFnum wZert wK (Block.nil (D := wD) (V := wV) (l := false)
      (Γ := wCtx) (Λ := [])) [bRowT] = false ∧
    blOk wEL wFnum wZert wK (Block.nil (D := wD) (V := wV) (l := false)
      (Γ := wCtx) (Λ := [])) [] = true := by
  decide

/-- `let t = a; a = t;` inside a block: the `let` binds C local `2`, and the
    row after it must READ that local. PLANTED DEFECTS: the `let` bound to
    a local that is already a parameter (not fresh), and the `let` bound to
    a local the following row does not read. -/
def bLetBlock : Block wD wV false wCtx [] [] :=
  .bind (τ := wU32) x0 (.cons (Stmt.assignVar (.dort .hier) (Expr.var .hier)) .nil)

theorem probe_blOk_let :
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 2 bU32c (.var 0), .setVar 0 bU32c (.var 2)] = true ∧
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 1 bU32c (.var 0), .setVar 0 bU32c (.var 1)] = false ∧
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 3 bU32c (.var 0), .setVar 0 bU32c (.var 2)] = false ∧
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 2 bU32c (.var 1), .setVar 0 bU32c (.var 2)] = false := by
  decide

#print axioms Gabbro.Grammatik.BlockZeuge.probe_ite
#print axioms Gabbro.Grammatik.BlockZeuge.probe_ite_fremd
#print axioms Gabbro.Grammatik.BlockZeuge.probe_blOk_void
#print axioms Gabbro.Grammatik.BlockZeuge.probe_blOk_let

end Gabbro.Grammatik.BlockZeuge
