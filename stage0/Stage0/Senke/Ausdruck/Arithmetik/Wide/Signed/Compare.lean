/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Compare.lean
  Subject:   Exact mixed signedness multiword lt, le and eq on complete operand domains.

  Inputs occupy a .. a+k-1 and a+k .. a+2k-1. Each is copied and extended by one limb at
  r = a+2k; the existing comparison then cannot overflow. le compares y < x and complements
  its Boolean word. The result replaces slot a; all other source limbs survive.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.ComparePrep
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

inductive WideCompare where
  | lt | le | eq

def wideMixedC (leftSigned : Bool) (mode : WideCompare) (k a : Nat) : List II :=
  let r := a + 2 * k
  match mode with
  | .lt => wideComparePrep leftSigned (!leftSigned) k r a (a + k) ++ wideLtC k r ++ [ci 2 a r 0]
  | .eq => wideComparePrep leftSigned (!leftSigned) k r a (a + k) ++ wideEqC k r ++ [ci 2 a r 0]
  | .le => wideComparePrep (!leftSigned) leftSigned k r (a + k) a ++ wideLtC k r ++
      [ci 1 (r + 1 : Nat) 1 0, cn 10 a r (r + 1)]

def wideCompareResult (mode : WideCompare) (x y : Int) : Bool :=
  match mode with
  | .lt => decide (x < y)
  | .le => decide (x ≤ y)
  | .eq => decide (x = y)

theorem wideMixed_value (leftSigned : Bool) (mode : WideCompare) (k a : Nat) (x y : Int)
    (hk : 1 ≤ k) (hx : WideFits leftSigned k x) (hy : WideFits (!leftSigned) k y)
    (s : Nat → Runner.W) (hX : ∀ j, j < k → s (a + j) = lmb x j)
    (hY : ∀ j, j < k → s (a + k + j) = lmb y j) :
    aluRun (wideMixedC leftSigned mode k a) s a = Runner.IR.bool (wideCompareResult mode x y) := by
  let r := a + 2 * k
  have diff := wideCompare_difference leftSigned (!leftSigned) k x y hk hx hy
  cases mode with
  | lt =>
    obtain ⟨p1, p2, _⟩ := wideComparePrep_value leftSigned (!leftSigned) k r a (a + k) x y hk
      (by omega) (by omega) hx hy s hX hY
    have cmp := wideLt_value k r _ x y p1 p2 diff.1 diff.2
    simp only [wideMixedC, aluRun_append, aluRun_cons, aluRun_nil, aluStep_mov, slotUpd_same]
    exact cmp
  | eq =>
    obtain ⟨p1, p2, _⟩ := wideComparePrep_value leftSigned (!leftSigned) k r a (a + k) x y hk
      (by omega) (by omega) hx hy s hX hY
    have hp : (2 : Int) ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
      rw [Nat.mul_succ, pow_add, mul_comm]
    have hpos : (0 : Int) < 2 ^ (64 * k) := by positivity
    have cmp := wideEq_value k r _ x y p1 p2 (by rw [hp]; omega) (by rw [hp]; omega)
    simp only [wideMixedC, aluRun_append, aluRun_cons, aluRun_nil, aluStep_mov, slotUpd_same]
    exact cmp
  | le =>
    obtain ⟨p1, p2, _⟩ := wideComparePrep_value (!leftSigned) leftSigned k r (a + k) a y x hk
      (by omega) (by omega) hy hx s hY hX
    have diff' := wideCompare_difference (!leftSigned) leftSigned k y x hk hy hx
    have cmp := wideLt_value k r _ y x p1 p2 diff'.1 diff'.2
    simp only [wideMixedC, aluRun_append, aluRun_cons, aluRun_nil, aluStep_const, aluStep_xor, slotUpd_same]
    rw [slotUpd_other _ _ (by omega : r ≠ r + 1), cmp]
    change Runner.IR.bool (decide (y < x)) ^^^ 1 = Runner.IR.bool (decide (x ≤ y))
    by_cases h : y < x
    · have hn : ¬ x ≤ y := by omega
      simp only [h, hn, decide_true, decide_false, Runner.IR.bool, ite_true, Bool.false_eq_true, ite_false]
      decide
    · have hn : x ≤ y := by omega
      simp only [h, hn, decide_true, decide_false, Runner.IR.bool, ite_true, Bool.false_eq_true, ite_false]
      decide

end Gabbro.Stage0.Senke
