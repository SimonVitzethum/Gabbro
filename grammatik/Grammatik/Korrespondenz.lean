/-
  File:      Grammatik/Korrespondenz.lean
  Subject:   T2 GENERAL: correspondence certificates as FORM FAMILIES.

  `Korrespondenz104.lean` certifies ONE program: its rows are cut to 104's
  exact shapes. Here a row is a member of a form family over the existing
  T4 judgements (`CFormenI.lean`, `CFormenM.lean`): slot store of any
  expression, plain and compound local assignment, `let`, `if`/`else`,
  direct call of any function with parameter arguments, `return` of an
  expression, `(void)x`, and the `for`-over-`traverse` form
  (`scorr_traverse`). `gbodyOk` is the decidable validity check; the
  flagship soundness theorem `gcert_sound` builds `EndSem` from the T4
  lemmas (nothing re-proved). `Korrespondenz104.lean` keeps building
  unchanged.
-/
import Grammatik.CFormenZeuge

namespace Gabbro.Grammatik

/-- One emitted-C statement as certificate data: a member of a form
    family over the T4 judgements. Expressions ride along as `CX` (plain
    data); their `ExprCorr` (from the T4 expression lemmas) is a premise
    of the row derivation (`RBlock`/`REnd`), not data. -/
inductive GRow where
  | void (x : Nat)
  | storeSlot (kp ip n ss off : Nat) (tc : CTy) (ce : CX)
  | storeGlob (g : Nat) (tc : CTy) (ce : CX)
  | setVar (x : Nat) (tc : CTy) (ce : CX)
  | setOp (x : Nat) (tc : CTy) (op : CBinOp) (t : CIT) (ce : CX)
  | bindLet (x : Nat) (tc : CTy) (ce : CX)
  | ite (cc : CX) (t e : List GRow)
  | call (fc : Nat) (cargs : List CX) (dst : Option (Nat × CTy))
  | ret (cr : Option (CTy × CX))
  | forTrav (x : Nat) (t : CIT) (hi : CX) (body : List GRow) (m : Nat)
  deriving Repr

mutual
/-- Elaboration of one row to its C statement. -/
def growRow : GRow → CS
  | .void x => .expr (.var x)
  | .storeSlot kp ip n ss off tc ce => .store (.slotA (.var kp) (.var ip) n ss off) tc ce
  | .storeGlob g tc ce => .store (.addr (.glob g)) tc ce
  | .setVar x tc ce => .set x tc ce
  | .setOp x tc op t ce => .set x tc (.bin op t (.var x) ce)
  | .bindLet x tc ce => .set x tc ce
  | .ite cc t e => .ite cc (growsCS t .skip) (growsCS e .skip)
  | .call fc cargs dst => .call fc cargs dst
  | .ret cr => .ret cr
  | .forTrav x t hi body m => CS.forUp x t (.lit 0) hi (growsCS body .skip) m
/-- Elaboration of a row list: sequencing, ending in `tl`. -/
def growsCS : List GRow → CS → CS
  | [], tl => tl
  | r :: rs, tl => .seq (growRow r) (growsCS rs tl)
end

end Gabbro.Grammatik
