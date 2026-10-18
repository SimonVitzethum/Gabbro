import Grammatik.Code.Refine.Frag

/-
  File:      Grammatik/Code/Refine/Match/Opt.lean
  Subject:   TRACK L, PHASE L1 -- THE EXPRESSIONS OF `opt n` AND `why n`: what the lowered code of
             `none`, `some e`, `istSome e` and `why n r` does.

  An `opt n` is the integer `-1` (absent) or the index `k` in `0 .. n - 1`, a `why n` is the number of
  the reason; both live in `Ar.wid` bits (`encR`, the image of `roh`). So `none` and `why` are
  constants, `some` moves the index to the wider (signed) width, and `istSome` is one signed compare
  with zero (`sge`: `-1` and `0 ..` are told apart by the sign, which is why the range `-1 .. n - 1`
  carries the signed width).
-/

namespace Gabbro.Code.Lower

variable [Conf]

theorem val_icmp_sge (W : Nat) (a b : Int) (hW : 0 < W) (ha : FitS true W a) (hb : FitS true W b) :
    Val.icmp .sge W (Val.ofInt W a) (Val.ofInt W b) = some (Val.bool (decide (b ≤ a))) := by
  obtain ⟨_, a0, a1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ a ∧ a < 2 ^ (W - 1) := by simpa [FitS] using ha
  obtain ⟨_, b0, b1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ b ∧ b < 2 ^ (W - 1) := by simpa [FitS] using hb
  simp [Val.icmp, IPred.ap, Val.ofInt, Ar.sle_ofInt hW b0 b1 a0 a1]

/-- A constant integer operand, as a fragment. -/
theorem frag_intc (m : Mem) (rs : Regs) (r : Nat) (w : Nat) (z : Int) :
    Frag m rs r ([], .int w z, r) (Val.ofInt w z) :=
  frag_const m rs r _ _ rfl (fun x hx => nomatch hx)

/-- The signed width of `-1 .. n - 1` holds `-1`, `0` and every index. -/
theorem optFit {n : Int} (hf : Ar.Fits (-1) (n - 1) 128) (z : Int) (hz : z = -1 ∨ (0 ≤ z ∧ z ≤ n - 1)) :
    FitS true (Ar.wid (-1) (n - 1)) z := by
  have hw := Ar.wid_pos (-1) (n - 1)
  have hF := Ar.wid_fits hf
  unfold Ar.Fits at hF
  rw [if_neg (by omega)] at hF
  have hp : (0 : Int) < 2 ^ (Ar.wid (-1) (n - 1) - 1) := by exact_mod_cast Nat.two_pow_pos _
  simp only [FitS, if_true]
  omega

/-- `istSome`: one signed compare of the `opt` word with zero. -/
theorem istSome_frag {n : Int} (hf : Ar.Fits (-1) (n - 1) 128) (z : Int)
    (hz : z = -1 ∨ (0 ≤ z ∧ z ≤ n - 1))
    (oa : Opd) (r1 : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid (-1) (n - 1)) z)) (hlt : OpdLt oa r1) :
    Frag m rs r1 ([.icmp r1 .sge (Ar.wid (-1) (n - 1)) oa (.int (Ar.wid (-1) (n - 1)) 0)],
      .reg r1, r1 + 1) (Val.bool (decide (0 ≤ z))) := by
  apply frag_one
  have hw := Ar.wid_pos (-1) (n - 1)
  have fz := optFit hf z hz
  have hp : (0 : Int) < 2 ^ (Ar.wid (-1) (n - 1) - 1) := by exact_mod_cast Nat.two_pow_pos _
  have f0 : FitS true (Ar.wid (-1) (n - 1)) 0 := by
    simp only [FitS, if_true]; omega
  have hv := val_icmp_sge (Ar.wid (-1) (n - 1)) z 0 (by omega) fz f0
  have e0 : (Opd.int (Ar.wid (-1) (n - 1)) 0).ev rs = some (Val.ofInt (Ar.wid (-1) (n - 1)) 0) := rfl
  simp only [stepI, hoa, e0, hv, Option.map_some]

end Gabbro.Code.Lower
