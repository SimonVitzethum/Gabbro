import Grammatik.Code.Refine.Bits.Ops
import Grammatik.Code.Refine.Mono

/-
  File:      Grammatik/Code/Refine/Bits/OpRest.lean
  Subject:   TRACK L, PHASE L1 -- AN INTEGER OPERATION AT A CHOSEN WIDTH: `opRest`.

  `opRest op (jl, jh) τ σa σb oa ob r` moves both operands to the width of the range `jl .. jh`, runs the
  instruction `op` there and moves the result to the width of its own type `τ`. Which range the
  lowering of a form picks is a choice that makes the instruction's precondition a fact of G's ranges
  (`jsdiv`, `jsrem`, `jbit`, `jshl`, `jshr` in `Lower/Expr.lean`); `opRest_frag` takes that fact as
  `hop`, the behaviour of the instruction on the two encodings at that width, and proves the code
  computes the exact result `zf za zb` when the result lies in the range.
-/

namespace Gabbro.Code.Lower

variable [Conf]

theorem opRest_fits {op : BinOp} {j : Int × Int} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : opRest op j τ σa σb oa ob r = some c) : fitsT (.int j.1 j.2) = true ∧ fitsT τ = true := by
  unfold opRest at h
  split at h
  · rename_i la ha lb hb
    rcases hc1 : cvtG (.int la ha) (.int j.1 j.2) oa r with _ | ⟨c1, oa', r1⟩
    · simp [hc1] at h
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (.int j.1 j.2) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp [hc2] at h
    simp only [hc2] at h
    split at h
    · rename_i hf
      exact (Bool.and_eq_true _ _).mp hf
    · simp at h
  · simp at h

theorem opRest_frag (op : BinOp) (zf : Int → Int → Int) (jl jh : Int)
    {la ha lb hb lo hi : Int} (za zb : Int) (hfa : Ar.Fits la ha 128) (hfb : Ar.Fits lb hb 128)
    (h1 : la ≤ za) (h2 : za ≤ ha) (h3 : lb ≤ zb) (h4 : zb ≤ hb)
    (hop : Val.bin op (Ar.wid jl jh) (Val.ofInt (Ar.wid jl jh) za) (Val.ofInt (Ar.wid jl jh) zb)
      = some (Val.ofInt (Ar.wid jl jh) (zf za zb)))
    (hz1 : jl ≤ zf za zb) (hz2 : zf za zb ≤ jh)
    (oa ob : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid la ha) za))
    (hob : ob.ev rs = some (Val.ofInt (Ar.wid lb hb) zb))
    (hla : OpdLt oa r) (hlb : OpdLt ob r) (c : LR)
    (h : opRest op (jl, jh) (.int lo hi) (.int la ha) (.int lb hb) oa ob r = some c) :
    Frag m rs r c (Val.ofInt (Ar.wid lo hi) (zf za zb)) := by
  have hfit := opRest_fits h
  have hfJ : Ar.Fits jl jh 128 := by simpa [fitsT] using hfit.1
  unfold opRest at h
  obtain ⟨cA, hcA, F1⟩ := cvtG_frag (lb := jl) (hb := jh) (m := m) (rs := rs) hfa h1 h2 hoa hla
  rw [hcA] at h
  rcases cA with ⟨c1, oa', r1⟩
  simp only at h
  have hr1 : r ≤ r1 := by obtain ⟨_, _, h, _⟩ := F1; exact h
  rcases hc2 : cvtG (.int lb hb) (.int jl jh) ob r1 with _ | ⟨c2, ob', r2⟩
  · simp [hc2] at h
  simp only [hc2] at h
  rcases hq : (fitsT (.int jl jh) && fitsT (.int lo hi)) with _ | _
  · simp [hq] at h
  simp only [hq, if_true] at h
  rcases hc3 : cvtG (.int jl jh) (.int lo hi) (.reg r2) (r2 + 1) with _ | ⟨c3, o3, r3⟩
  · simp [hc3] at h
  simp only [hc3] at h
  obtain rfl := Option.some.inj h
  have F12 : Frag m rs r (c1 ++ c2 ++ [Instr.bin r2 op (twid (.int jl jh)) oa' ob'], .reg r2, r2 + 1)
      (Val.ofInt (Ar.wid jl jh) (zf za zb)) := by
    refine frag_three (ob := ob') (r1 := r1) (r2 := r2) (vb := Val.ofInt (Ar.wid jl jh) zb)
      (ct := ([Instr.bin r2 op (twid (.int jl jh)) oa' ob'], .reg r2, r2 + 1)) F1
      (fun rsA hag => ?_) (fun rsB hagB hoa' hob' hla' hlb' => ?_)
    · have hob1 : ob.ev rsA = some (Val.ofInt (Ar.wid lb hb) zb) := by
        rw [ev_agree hag hlb]; exact hob
      obtain ⟨cB, hcB, F2⟩ := cvtG_frag (lb := jl) (hb := jh) (m := m) (rs := rsA) hfb h3 h4 hob1
        (fun x hx => Nat.lt_of_lt_of_le (hlb x hx) hr1)
      rw [hc2] at hcB
      obtain rfl := Option.some.inj hcB
      exact F2
    · apply frag_one
      simp only [stepI, hoa', hob']
      simp only [twid]
      rw [hop]
      rfl
  refine frag_two (ct := (c3, o3, r3)) F12 (fun rsC hag hoc hltc => ?_)
  obtain ⟨cC, hcC, F3⟩ := cvtG_frag (la := jl) (ha := jh) (lb := lo) (hb := hi) (m := m) (rs := rsC) hfJ hz1 hz2
    hoc hltc
  rw [hc3] at hcC
  obtain rfl := Option.some.inj hcC
  exact F3

end Gabbro.Code.Lower
