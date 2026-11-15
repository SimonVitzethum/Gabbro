/-
  File:      stage0/Stage0/Senke/Bild/Mehr/BlindOp.lean
  Subject:   Every instruction of the IR is read-blind (multi-thread image theorem, package MT2): the request tree of
             each opcode (`blind_op`, one arm per opcode as in the runner's `handler_ok`) and so the tree of every
             instruction start (`blind_step`). Its reads all go through `rd8`/`rd32`/`rd64` (`Mehr/Blind.lean`).
-/
module
public import Stage0.Senke.Bild.Mehr.Blind
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR

/-- **The request tree of every opcode is read-blind.** -/
theorem blind_op (o : Nat) (t : T) : Blind (op o t) := by
  match o with
  | 0 => exact Blind.fault
  | 1 =>
    simp only [op]
    apply blind_f2
    intro _
    exact blind_ret1 _ _
  | 2 =>
    simp only [op]
    apply blind_f2
    intro _
    apply blind_ld
    intro _
    exact blind_ret1 _ _
  | 3 => exact blind_bin _ _
  | 4 => exact blind_bin _ _
  | 5 => exact blind_bin _ _
  | 6 => exact blind_bin _ _
  | 7 => exact blind_bin _ _
  | 8 => exact blind_bin _ _
  | 9 => exact blind_bin _ _
  | 10 => exact blind_bin _ _
  | 11 => exact blind_bin _ _
  | 12 => exact blind_bin _ _
  | 13 => exact blind_bin _ _
  | 14 => exact blind_bin _ _
  | 15 =>
    simp only [op]
    apply blind_f2
    intro _
    apply blind_ld
    intro _
    apply blind_rd64
    intro _
    exact blind_ret1 _ _
  | 16 =>
    simp only [op]
    apply blind_f1
    intro _
    apply blind_ld
    intro _
    apply blind_f2
    intro _
    apply blind_ld
    intro _
    exact blind_wr64 _ _ _
  | 17 =>
    simp only [op]
    apply blind_f2
    intro _
    exact blind_ret1 _ _
  | 18 =>
    simp only [op]
    apply blind_f1
    intro _
    exact Blind.next _
  | 19 =>
    simp only [op]
    apply blind_f1
    intro _
    apply blind_ld
    intro _
    apply blind_ite
    · apply blind_f2
      intro _
      exact Blind.next _
    · exact Blind.next _
  | 20 =>
    simp only [op]
    apply blind_f1
    intro _
    apply blind_ld
    intro _
    apply blind_f2
    intro _
    apply blind_wr
    intro r
    apply blind_opt
    intro _
    exact blind_wr64 _ _ _
  | 21 =>
    simp only [op]
    apply blind_rd64
    intro _
    apply blind_rd64
    intro _
    exact Blind.next _
  | 22 =>
    simp only [op]
    apply blind_f2
    intro _
    apply blind_ld
    intro _
    apply blind_f3
    intro _
    apply blind_ld
    intro _
    apply blind_rd64
    intro _
    apply blind_cas
    intro _
    exact blind_ret1 _ _
  | 23 =>
    simp only [op]
    apply blind_f1
    intro _
    apply blind_f2
    intro _
    apply blind_ld
    intro _
    apply blind_rd64
    intro _
    apply blind_rd64
    intro _
    apply blind_rd64
    intro _
    apply blind_rd64
    intro _
    apply blind_rd64
    intro _
    apply blind_rd64
    intro _
    apply blind_sys
    intro r
    apply blind_opt
    intro _
    exact blind_wr64 _ _ _
  | 24 =>
    simp only [op]
    apply blind_f2
    intro _
    apply blind_ld
    intro _
    apply blind_rd64
    intro _
    apply blind_sys
    intro r
    apply blind_opt
    intro _
    apply blind_ite
    · exact Blind.next _
    · exact blind_ret1 _ _
  | 25 => exact blind_bin _ _
  | 26 => exact blind_bin _ _
  | 27 => exact blind_bin _ _
  | 28 => exact blind_fpIR _ _
  | 29 => exact blind_fpIR _ _
  | 30 => exact blind_fpIR _ _
  | 31 => exact blind_fpIR _ _
  | 32 => exact blind_fpIR _ _
  | 33 => exact blind_fpIR _ _
  | 34 => exact blind_fpIR _ _
  | 35 => exact blind_fpIR _ _
  | 36 => exact blind_fpIR _ _
  | 37 => exact blind_fpIR _ _
  | 38 => exact blind_fpIR _ _
  | 39 => exact blind_fpIR _ _
  | 40 => exact blind_fpIR _ _
  | 41 => exact blind_fpIR _ _
  | 42 => exact blind_fpIR _ _
  | 43 => exact blind_fpIR _ _
  | 44 => exact blind_fpIR _ _
  | 45 => exact blind_fpIR _ _
  | 46 => exact blind_fpIR _ _
  | 47 => exact blind_fpIR _ _
  | 48 => exact blind_fpIR _ _
  | 49 => exact blind_fpIR _ _
  | 50 => exact blind_fpIR _ _
  | 51 => exact blind_fpIR _ _
  | 52 => exact blind_fpIR _ _
  | 53 => exact blind_fpIR _ _
  | 54 => exact blind_fpIR _ _
  | 55 => exact blind_fpIR _ _
  | 56 => exact blind_fpIR _ _
  | 57 => exact blind_fpIR _ _
  | 58 => exact blind_fpIR _ _
  | 59 => exact blind_fpIR _ _
  | _ + 60 => exact Blind.fault

/-- **The tree of every instruction start is read-blind.** -/
theorem blind_step (t : T) : Blind (step t) := by
  unfold step
  exact blind_rd8 _ fun _ => blind_op _ _

end Gabbro.Stage0.Senke.BildMehr
