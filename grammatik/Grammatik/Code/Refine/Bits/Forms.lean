import Grammatik.Code.Refine.Bits.OpRest

/-
  File:      Grammatik/Code/Refine/Bits/Forms.lean
  Subject:   TRACK L, PHASE L1 -- WHY EACH INSTRUCTION'S PRECONDITION HOLDS: for each of `sdiv`, `srem`,
             `band`, `bor`, `bxor`, `shl`, `shr`, G's ranges give the precondition of the instruction at the
             width the lowering picks (`Ar.wid` of the range `jsdiv`, `jsrem`, `jbit`, `jshl`, `jshr`), and put
             the exact result inside that range.

  The ranges are chosen for exactly this:
    * `sdiv`/`srem`: the range is signed and reaches one below the least number of any operand and of the
      result, so the dividend is never `INT_MIN` (the one dividend/divisor pair whose quotient overflows)
      and every operand and the result is a signed number of the width; the divisor is nonzero by `hb`;
    * `band`/`bor`/`bxor`: unsigned, holds both operands (below `2^w` where the form says so) and the result;
    * `shl`/`shr`: unsigned, holds the operands, the result, and `2 ^ h2`, which forces the width ABOVE the
      largest shift amount `h2` -- the shift amount is a number below the width, whatever `h1` is.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (betragMax tdiv_natAbs_le tmod_natAbs_lt)

theorem fitsS {lo hi : Int} (h : Ar.Fits lo hi 128) (hneg : lo < 0) :
    -(2 ^ (Ar.wid lo hi - 1)) ≤ lo ∧ hi < 2 ^ (Ar.wid lo hi - 1) := by
  have := Ar.wid_fits h
  unfold Ar.Fits at this
  rw [if_neg (by omega)] at this
  exact this

theorem fitsU {lo hi : Int} (h : Ar.Fits lo hi 128) (hnn : 0 ≤ lo) : hi < 2 ^ (Ar.wid lo hi) := by
  have := Ar.wid_fits h
  unfold Ar.Fits at this
  rw [if_pos hnn] at this
  exact this

theorem sdiv_hop (l1 h1 l2 h2 za zb : Int) (hb : 1 ≤ l2 ∨ h2 ≤ -1)
    (hfJ : Ar.Fits (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2 128)
    (e1 : l1 ≤ za) (e2 : za ≤ h1) (e3 : l2 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .sdiv (Ar.wid (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2)
      (Val.ofInt (Ar.wid (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2) za)
      (Val.ofInt (Ar.wid (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2) zb)
      = some (Val.ofInt (Ar.wid (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2) (Int.tdiv za zb)) ∧
    (jsdiv l1 h1 l2 h2).1 ≤ Int.tdiv za zb ∧ Int.tdiv za zb ≤ (jsdiv l1 h1 l2 h2).2 := by
  obtain ⟨hj1, hj2⟩ : (jsdiv l1 h1 l2 h2).1 = min (min l1 l2) (min (-(betragMax l1 h1)) (-1)) - 1 ∧
      (jsdiv l1 h1 l2 h2).2 = max (max h1 h2) (max (betragMax l1 h1) 1) := ⟨rfl, rfl⟩
  have hbm : betragMax l1 h1 = ((max l1.natAbs h1.natAbs : Nat) : Int) := rfl
  have hneg : (jsdiv l1 h1 l2 h2).1 < 0 := by omega
  have hF := fitsS hfJ hneg
  have hw := Ar.wid_pos (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2
  have hq := tdiv_natAbs_le za zb
  refine ⟨val_bin_sdiv _ za zb (by omega) ?_ ?_ ?_ ?_ (by omega), ?_, ?_⟩ <;> omega

theorem srem_hop (l1 h1 l2 h2 za zb : Int) (hb : 1 ≤ l2 ∨ h2 ≤ -1)
    (hfJ : Ar.Fits (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2 128)
    (e1 : l1 ≤ za) (e2 : za ≤ h1) (e3 : l2 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .srem (Ar.wid (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2)
      (Val.ofInt (Ar.wid (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2) za)
      (Val.ofInt (Ar.wid (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2) zb)
      = some (Val.ofInt (Ar.wid (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2) (Int.tmod za zb)) ∧
    (jsrem l1 h1 l2 h2).1 ≤ Int.tmod za zb ∧ Int.tmod za zb ≤ (jsrem l1 h1 l2 h2).2 := by
  obtain ⟨hj1, hj2⟩ : (jsrem l1 h1 l2 h2).1 = min (min l1 l2) (min (-(betragMax l2 h2 - 1)) (-1)) - 1 ∧
      (jsrem l1 h1 l2 h2).2 = max (max h1 h2) (max (betragMax l2 h2 - 1) 1) := ⟨rfl, rfl⟩
  have hbm : betragMax l2 h2 = ((max l2.natAbs h2.natAbs : Nat) : Int) := rfl
  have hneg : (jsrem l1 h1 l2 h2).1 < 0 := by omega
  have hF := fitsS hfJ hneg
  have hw := Ar.wid_pos (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2
  have hq := tmod_natAbs_lt za zb (by omega)
  refine ⟨val_bin_srem _ za zb (by omega) ?_ ?_ ?_ ?_ (by omega), ?_, ?_⟩ <;> omega

theorem band_hop (h1 h2 za zb : Int) (hfJ : Ar.Fits (jbit h1 h2 h1).1 (jbit h1 h2 h1).2 128)
    (e1 : 0 ≤ za) (e2 : za ≤ h1) (e3 : 0 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .and (Ar.wid (jbit h1 h2 h1).1 (jbit h1 h2 h1).2)
      (Val.ofInt (Ar.wid (jbit h1 h2 h1).1 (jbit h1 h2 h1).2) za)
      (Val.ofInt (Ar.wid (jbit h1 h2 h1).1 (jbit h1 h2 h1).2) zb)
      = some (Val.ofInt (Ar.wid (jbit h1 h2 h1).1 (jbit h1 h2 h1).2) ((za.toNat &&& zb.toNat : Nat) : Int)) ∧
    (jbit h1 h2 h1).1 ≤ ((za.toNat &&& zb.toNat : Nat) : Int) ∧
    ((za.toNat &&& zb.toNat : Nat) : Int) ≤ (jbit h1 h2 h1).2 := by
  obtain ⟨hj1, hj2⟩ : (jbit h1 h2 h1).1 = 0 ∧ (jbit h1 h2 h1).2 = max (max h1 h2) h1 := ⟨rfl, rfl⟩
  have hU := fitsU hfJ (by omega)
  have hle := Nat.and_le_left (n := za.toNat) (m := zb.toNat)
  refine ⟨val_bin_andN _ za zb e1 ?_ e3 ?_, ?_, ?_⟩ <;> omega

theorem bor_hop (w : Nat) (h1 h2 za zb : Int) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
    (hfJ : Ar.Fits (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 128)
    (e1 : 0 ≤ za) (e2 : za ≤ h1) (e3 : 0 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .or (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2)
      (Val.ofInt (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2) za)
      (Val.ofInt (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2) zb)
      = some (Val.ofInt (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2)
        ((za.toNat ||| zb.toNat : Nat) : Int)) ∧
    (jbit h1 h2 (2 ^ w - 1)).1 ≤ ((za.toNat ||| zb.toNat : Nat) : Int) ∧
    ((za.toNat ||| zb.toNat : Nat) : Int) ≤ (jbit h1 h2 (2 ^ w - 1)).2 := by
  obtain ⟨hj1, hj2⟩ : (jbit h1 h2 (2 ^ w - 1)).1 = 0 ∧ (jbit h1 h2 (2 ^ w - 1)).2 = max (max h1 h2) (2 ^ w - 1) :=
    ⟨rfl, rfl⟩
  have hU := fitsU hfJ (by omega)
  have hlt := Nat.or_lt_two_pow (x := za.toNat) (y := zb.toNat) (n := w) (toNat_lt_pow e1 (by omega))
    (toNat_lt_pow e3 (by omega))
  have hc : (((za.toNat ||| zb.toNat : Nat)) : Int) < 2 ^ w := by exact_mod_cast hlt
  refine ⟨val_bin_orN _ za zb e1 ?_ e3 ?_, ?_, ?_⟩ <;> omega

theorem bxor_hop (w : Nat) (h1 h2 za zb : Int) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
    (hfJ : Ar.Fits (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 128)
    (e1 : 0 ≤ za) (e2 : za ≤ h1) (e3 : 0 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .xor (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2)
      (Val.ofInt (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2) za)
      (Val.ofInt (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2) zb)
      = some (Val.ofInt (Ar.wid (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2)
        ((za.toNat ^^^ zb.toNat : Nat) : Int)) ∧
    (jbit h1 h2 (2 ^ w - 1)).1 ≤ ((za.toNat ^^^ zb.toNat : Nat) : Int) ∧
    ((za.toNat ^^^ zb.toNat : Nat) : Int) ≤ (jbit h1 h2 (2 ^ w - 1)).2 := by
  obtain ⟨hj1, hj2⟩ : (jbit h1 h2 (2 ^ w - 1)).1 = 0 ∧ (jbit h1 h2 (2 ^ w - 1)).2 = max (max h1 h2) (2 ^ w - 1) :=
    ⟨rfl, rfl⟩
  have hU := fitsU hfJ (by omega)
  have hlt := Nat.xor_lt_two_pow (x := za.toNat) (y := zb.toNat) (n := w) (toNat_lt_pow e1 (by omega))
    (toNat_lt_pow e3 (by omega))
  have hc : (((za.toNat ^^^ zb.toNat : Nat)) : Int) < 2 ^ w := by exact_mod_cast hlt
  refine ⟨val_bin_xorN _ za zb e1 ?_ e3 ?_, ?_, ?_⟩ <;> omega

/-- `2 ^ k < 2 ^ W` gives `k < W`. -/
theorem lt_of_pow_lt {k W : Nat} (h : (2 : Int) ^ k < 2 ^ W) : k < W := by
  have h' : 2 ^ k < 2 ^ W := by exact_mod_cast h
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp h'

theorem shl_hop (h1 h2 za zb : Int) (hfJ : Ar.Fits (jshl h1 h2).1 (jshl h1 h2).2 128)
    (e1 : 0 ≤ za) (e2 : za ≤ h1) (e3 : 0 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .shl (Ar.wid (jshl h1 h2).1 (jshl h1 h2).2)
      (Val.ofInt (Ar.wid (jshl h1 h2).1 (jshl h1 h2).2) za)
      (Val.ofInt (Ar.wid (jshl h1 h2).1 (jshl h1 h2).2) zb)
      = some (Val.ofInt (Ar.wid (jshl h1 h2).1 (jshl h1 h2).2) (za * 2 ^ zb.toNat)) ∧
    (jshl h1 h2).1 ≤ za * 2 ^ zb.toNat ∧ za * 2 ^ zb.toNat ≤ (jshl h1 h2).2 := by
  obtain ⟨hj1, hj2⟩ : (jshl h1 h2).1 = 0 ∧
      (jshl h1 h2).2 = max (max h1 h2) (max (h1 * 2 ^ h2.toNat) (2 ^ h2.toNat)) := ⟨rfl, rfl⟩
  have hU := fitsU hfJ (by omega)
  have hp1 : (2 : Int) ^ zb.toNat ≤ 2 ^ h2.toNat := by
    exact_mod_cast Nat.pow_le_pow_right (by decide) (show zb.toNat ≤ h2.toNat by omega)
  have hpos : (0 : Int) < 2 ^ zb.toNat := by exact_mod_cast Nat.two_pow_pos _
  have hprod : za * 2 ^ zb.toNat ≤ h1 * 2 ^ h2.toNat :=
    Int.mul_le_mul e2 hp1 (Int.le_of_lt hpos) (by omega)
  have hnn : 0 ≤ za * 2 ^ zb.toNat := Int.mul_nonneg e1 (Int.le_of_lt hpos)
  have hh2 : (2 : Int) ^ h2.toNat < 2 ^ (Ar.wid (jshl h1 h2).1 (jshl h1 h2).2) := by omega
  have hbW : zb < (Ar.wid (jshl h1 h2).1 (jshl h1 h2).2 : Int) := by
    have := lt_of_pow_lt hh2
    omega
  refine ⟨val_bin_shl _ za zb e1 ?_ e3 hbW, ?_, ?_⟩ <;> omega

theorem shr_hop (h1 h2 za zb : Int) (hfJ : Ar.Fits (jshr h1 h2).1 (jshr h1 h2).2 128)
    (e1 : 0 ≤ za) (e2 : za ≤ h1) (e3 : 0 ≤ zb) (e4 : zb ≤ h2) :
    Val.bin .lshr (Ar.wid (jshr h1 h2).1 (jshr h1 h2).2)
      (Val.ofInt (Ar.wid (jshr h1 h2).1 (jshr h1 h2).2) za)
      (Val.ofInt (Ar.wid (jshr h1 h2).1 (jshr h1 h2).2) zb)
      = some (Val.ofInt (Ar.wid (jshr h1 h2).1 (jshr h1 h2).2) (za / 2 ^ zb.toNat)) ∧
    (jshr h1 h2).1 ≤ za / 2 ^ zb.toNat ∧ za / 2 ^ zb.toNat ≤ (jshr h1 h2).2 := by
  obtain ⟨hj1, hj2⟩ : (jshr h1 h2).1 = 0 ∧ (jshr h1 h2).2 = max (max h1 h2) (2 ^ h2.toNat) := ⟨rfl, rfl⟩
  have hU := fitsU hfJ (by omega)
  have hpos : (0 : Int) < 2 ^ zb.toNat := by exact_mod_cast Nat.two_pow_pos _
  have hq0 : 0 ≤ za / 2 ^ zb.toNat := Int.ediv_nonneg e1 (Int.le_of_lt hpos)
  have hq1 : za / 2 ^ zb.toNat ≤ za := Int.ediv_le_self _ e1
  have hh2 : (2 : Int) ^ h2.toNat < 2 ^ (Ar.wid (jshr h1 h2).1 (jshr h1 h2).2) := by omega
  have hbW : zb < (Ar.wid (jshr h1 h2).1 (jshr h1 h2).2 : Int) := by
    have := lt_of_pow_lt hh2
    omega
  refine ⟨val_bin_lshr _ za zb e1 ?_ e3 hbW, ?_, ?_⟩ <;> omega

end Gabbro.Code.Lower
