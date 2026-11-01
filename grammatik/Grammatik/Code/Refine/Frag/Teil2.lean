module

public import Grammatik.Code.Lower.Expr
public import Grammatik.Code.Refine.Frag.Teil1

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Wert)
variable {D : Deklaration}

/-- **A comparison**: both operands moved to the width of the joined range, compared. -/
theorem cmpRest_frag (pu ps : IPred) (P : Int → Int → Prop) [DecidableRel P]
    (hic : ∀ (sg : Bool) (W : Nat) (a b : Int), 0 < W → FitS sg W a → FitS sg W b →
      Val.icmp (if sg then ps else pu) W (Val.ofInt W a) (Val.ofInt W b)
        = some (Val.bool (decide (P a b))))
    {la ha lb hb : Int} (za zb : Int) (hfa : Ar.Fits la ha 128) (hfb : Ar.Fits lb hb 128)
    (h1 : la ≤ za) (h2 : za ≤ ha) (h3 : lb ≤ zb) (h4 : zb ≤ hb)
    (oa ob : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid la ha) za))
    (hob : ob.ev rs = some (Val.ofInt (Ar.wid lb hb) zb))
    (hla : OpdLt oa r) (hlb : OpdLt ob r) (c : LR)
    (h : cmpRest pu ps (.int la ha) (.int lb hb) oa ob r = some c) :
    Frag m rs r c (Val.bool (decide (P za zb))) := by
  unfold cmpRest at h
  simp only [joinT, cvtG] at h
  rcases hc1 : cvt (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha)) oa r
    with ⟨c1, oa', r1⟩
  rcases hc2 : cvt (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb)) ob r1
    with ⟨c2, ob', r2⟩
  simp only [hc1, hc2] at h
  split at h
  · rename_i hfit
    obtain rfl := Option.some.inj h
    have hfj : Ar.Fits (min la lb) (max ha hb) 128 := by simpa [fitsT] using hfit
    have hwj := Ar.wid_fits hfj
    have hwp := Ar.wid_pos (min la lb) (max ha hb)
    have f1 := cvt_frag (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha))
      oa r m rs za hoa
      (fitS_of_fits (Ar.wid_fits hfa) (by have := Ar.wid_pos la ha; show 0 < Ar.wid la ha; omega) h1 h2) hla
    rw [hc1] at f1
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := f1
    have hob1 : ob.ev rs1 = some (Val.ofInt (Ar.wid lb hb) zb) := by
      rw [ev_agree hag1 hlb]; exact hob
    have f2 := cvt_frag (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb))
      ob r1 m rs1 zb hob1
      (fitS_of_fits (Ar.wid_fits hfb) (by have := Ar.wid_pos lb hb; show 0 < Ar.wid lb hb; omega) h3 h4)
      (fun x hx => by have h5 : (x : Nat) < r := hlb x hx; have hr1' : r ≤ r1 := hr1; exact Nat.lt_of_lt_of_le h5 hr1')
    rw [hc2] at f2
    obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := f2
    have hev1' : oa'.ev rs2 = some (Val.ofInt (Ar.wid (min la lb) (max ha hb)) za) := by
      rw [ev_agree hag2 hlt1]; exact hev1
    have fa := fitS_of_fits hwj (by omega) (show min la lb ≤ za by omega) (show za ≤ max ha hb by omega)
    have fb := fitS_of_fits hwj (by omega) (show min la lb ≤ zb by omega) (show zb ≤ max ha hb by omega)
    have hstep : stepI (.icmp r2 (if tsgn (.int (min la lb) (max ha hb)) then ps else pu)
        (twid (.int (min la lb) (max ha hb))) oa' ob') m rs2
        = some (m, rs2.set r2 (Val.bool (decide (P za zb)))) := by
      simp only [stepI, hev1', hev2]
      have := hic (tsgn (.int (min la lb) (max ha hb))) (Ar.wid (min la lb) (max ha hb)) za zb
        (by omega) (by simpa [tsgn] using fa) (by simpa [tsgn] using fb)
      simp only [twid] at this ⊢
      simp only [this, Option.map_some]
    have h3' := frag_one m rs2 r2 _ _ hstep
    have t2 := frag_trans (c1 := (c2, ob', r2)) (rs := rs1) (r := r1)
      (c2 := ([.icmp r2 (if tsgn (.int (min la lb) (max ha hb)) then ps else pu)
        (twid (.int (min la lb) (max ha hb))) oa' ob'], .reg r2, r2 + 1)) hs2 hr2 hag2 h3'
    have t1 := frag_trans (c1 := (c1, oa', r1)) (rs := rs) (r := r) hs1 hr1 hag1
      (c2 := (c2 ++ [.icmp r2 (if tsgn (.int (min la lb) (max ha hb)) then ps else pu)
        (twid (.int (min la lb) (max ha hb))) oa' ob'], .reg r2, r2 + 1)) (by simpa using t2)
    rw [List.append_assoc]
    exact t1
  · simp only [reduceCtorEq] at h

theorem val_bin_and (x y : Bool) :
    Val.bin .and 1 (Val.bool x) (Val.bool y) = some (Val.bool (x && y)) := by
  cases x <;> cases y <;> decide

theorem val_bin_or (x y : Bool) :
    Val.bin .or 1 (Val.bool x) (Val.bool y) = some (Val.bool (x || y)) := by
  cases x <;> cases y <;> decide

theorem val_bin_not (x : Bool) :
    Val.bin .xor 1 (Val.bool x) (Val.ofInt 1 1) = some (Val.bool (!x)) := by
  cases x <;> decide

/-- A lowered binary operation always has a result type that fits. -/
theorem binRest_fits {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : binRest op τ σa σb oa ob r = some c) : fitsT τ = true := by
  unfold binRest at h
  split at h
  · split at h
    · split at h
      · rename_i hf; exact hf
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-! ## Division and remainder -/

theorem val_bin_udiv (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 < b) (hb1 : b < 2 ^ W) :
    Val.bin .udiv W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (Int.tdiv a b)) := by
  have hne : BitVec.ofInt W b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [Ar.toNat_ofInt_lt (by omega) hb1] at this
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Int.toNat_eq_zero] at this
    omega
  simp only [Val.bin, BinOp.ap, Val.ofInt, hne, if_false, Option.map_some]
  simp only [dite_true]
  rw [Ar.udiv_ofInt ha0 ha1 (by omega) hb1, Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg ha0]

theorem val_bin_urem (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 < b) (hb1 : b < 2 ^ W) :
    Val.bin .urem W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (Int.tmod a b)) := by
  have hne : BitVec.ofInt W b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [Ar.toNat_ofInt_lt (by omega) hb1] at this
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Int.toNat_eq_zero] at this
    omega
  simp only [Val.bin, BinOp.ap, Val.ofInt, hne, if_false, Option.map_some]
  simp only [dite_true]
  rw [Ar.urem_ofInt ha0 ha1 (by omega) hb1, Int.tmod_eq_emod_of_nonneg ha0]

theorem divRest_fits {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : divRest op τ σa σb oa ob r = some c) : fitsT τ = true := by
  unfold divRest at h
  split at h
  · rename_i la ha lb hb
    simp only at h
    rcases hc1 : cvtG (.int la ha) (joinT (.int la ha) (.int lb hb)) oa r with _ | ⟨c1, oa', r1⟩
    · simp only [hc1, reduceCtorEq] at h
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (joinT (.int la ha) (.int lb hb)) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp only [hc2, reduceCtorEq] at h
    simp only [hc2] at h
    split at h
    · rename_i hf
      exact ((Bool.and_eq_true _ _).mp hf).2
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-- **A division or remainder of non-negative numbers**: both operands at the width of the joined
    range, the instruction (whose precondition, a nonzero divisor, is `1 <= lb`), the result moved to
    its own width. `zf` is the exact result, which is non-negative and below the joined bound. -/
theorem divRest_frag (op : BinOp) (zf : Int → Int → Int)
    (hop : ∀ (W : Nat) (a b : Int), 0 ≤ a → a < 2 ^ W → 0 < b → b < 2 ^ W →
      Val.bin op W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (zf a b)))
    {la ha lb hb lo hi : Int} (za zb : Int) (hla0 : 0 ≤ la) (hlb1 : 1 ≤ lb)
    (hfa : Ar.Fits la ha 128) (hfb : Ar.Fits lb hb 128)
    (h1 : la ≤ za) (h2 : za ≤ ha) (h3 : lb ≤ zb) (h4 : zb ≤ hb) (hz0 : 0 ≤ zf za zb)
    (hz1 : zf za zb ≤ max ha hb)
    (oa ob : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid la ha) za))
    (hob : ob.ev rs = some (Val.ofInt (Ar.wid lb hb) zb))
    (hla : OpdLt oa r) (hlb : OpdLt ob r) (c : LR)
    (h : divRest op (.int lo hi) (.int la ha) (.int lb hb) oa ob r = some c) :
    Frag m rs r c (Val.ofInt (Ar.wid lo hi) (zf za zb)) := by
  unfold divRest at h
  simp only [cvtG, joinT] at h
  rcases hc1 : cvt (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha)) oa r with
    ⟨c1, oa', r1⟩
  rcases hc2 : cvt (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb)) ob r1 with
    ⟨c2, ob', r2⟩
  simp only [hc1, hc2] at h
  split at h
  · rename_i hfit
    have hfj : Ar.Fits (min la lb) (max ha hb) 128 := by
      have := ((Bool.and_eq_true _ _).mp hfit).1
      simpa [fitsT] using this
    have hmin : 0 ≤ min la lb := by omega
    have hWj := Ar.wid_fits hfj
    have hWp : 0 < Ar.wid (min la lb) (max ha hb) := by
      have := Ar.wid_pos (min la lb) (max ha hb); omega
    have hbound : max ha hb < 2 ^ Ar.wid (min la lb) (max ha hb) := by
      have := hWj
      unfold Ar.Fits at this
      rw [if_pos hmin] at this
      exact this
    have f1 := cvt_frag (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha)) oa r m rs za
      hoa (fitS_of_fits (Ar.wid_fits hfa) (by have := Ar.wid_pos la ha; show 0 < Ar.wid la ha; omega) h1 h2) hla
    rw [hc1] at f1
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := f1
    have hob1 : ob.ev rs1 = some (Val.ofInt (Ar.wid lb hb) zb) := by
      rw [ev_agree hag1 hlb]; exact hob
    have f2 := cvt_frag (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb)) ob r1 m rs1 zb
      hob1 (fitS_of_fits (Ar.wid_fits hfb) (by have := Ar.wid_pos lb hb; show 0 < Ar.wid lb hb; omega) h3 h4)
      (fun x hx => by
        have h5 : (x : Nat) < r := hlb x hx
        have hr1' : r ≤ r1 := hr1
        exact Nat.lt_of_lt_of_le h5 hr1')
    rw [hc2] at f2
    obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := f2
    have hev1' : oa'.ev rs2 = some (Val.ofInt (Ar.wid (min la lb) (max ha hb)) za) := by
      rw [ev_agree hag2 hlt1]; exact hev1
    have hstep : stepI (.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob') m rs2
        = some (m, rs2.set r2 (Val.ofInt (Ar.wid (min la lb) (max ha hb)) (zf za zb))) := by
      simp only [stepI, hev1', hev2]
      have := hop (twid (.int (min la lb) (max ha hb))) za zb (by omega)
        (by have : za ≤ max ha hb := by omega
            show za < 2 ^ Ar.wid (min la lb) (max ha hb)
            omega)
        (by omega)
        (by have : zb ≤ max ha hb := by omega
            show zb < 2 ^ Ar.wid (min la lb) (max ha hb)
            omega)
      simp only [twid] at this ⊢
      simp only [this, Option.map_some]
    have tb := frag_one m rs2 r2 _ _ hstep
    rcases hc3 : cvt (twid (.int (min la lb) (max ha hb))) (twid (.int lo hi)) (tsgn (.int (min la lb) (max ha hb)))
      (.reg r2) (r2 + 1) with ⟨c3, o3, r3⟩
    simp only [hc3] at h
    obtain rfl := Option.some.inj h
    have f3 := cvt_frag (twid (.int (min la lb) (max ha hb))) (twid (.int lo hi))
      (tsgn (.int (min la lb) (max ha hb))) (.reg r2) (r2 + 1) m (rs2.set r2 (Val.ofInt
        (Ar.wid (min la lb) (max ha hb)) (zf za zb))) (zf za zb)
      (by simp only [Opd.ev, regs_set_same, twid]) (by
        have hsg : tsgn (.int (min la lb) (max ha hb)) = false := by
          simp only [tsgn]
          simp only [show ¬(min la lb < 0) by omega, decide_false]
        rw [hsg]
        show FitS false (twid (.int (min la lb) (max ha hb))) (zf za zb)
        simp only [FitS, twid, Bool.false_eq_true, if_false]
        exact ⟨hz0, by omega⟩)
      (opdlt_reg r2 (r2 + 1) (by omega))
    rw [hc3] at f3
    -- compose: c1, c2, the instruction, c3
    have t3 := frag_trans (c1 := ([.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob'], .reg r2, r2 + 1))
      (c2 := (c3, o3, r3)) (m := m) (rs := rs2) (rs1 := rs2.set r2 (Val.ofInt (Ar.wid (min la lb) (max ha hb)) (zf za zb)))
      (r := r2) (by simp only [seqI, hstep]) (by simp only [Nat.le_add_right]) (fun x hx => regs_set_ne rs2 r2 x _ (Nat.ne_of_lt hx))
      (by simpa using f3)
    have t2 := frag_trans (c1 := (c2, ob', r2)) (c2 := ([.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob'] ++ c3, o3, r3))
      (rs := rs1) (r := r1) hs2 hr2 hag2 (by simpa using t3)
    have t1 := frag_trans (c1 := (c1, oa', r1)) (c2 := (c2 ++ ([.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob'] ++ c3), o3, r3))
      hs1 hr1 hag1 (by simpa using t2)
    simpa [List.append_assoc, twid] using t1
  · simp only [reduceCtorEq] at h

end Gabbro.Code.Lower
