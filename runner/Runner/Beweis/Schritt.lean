module
public import Runner.Beweis.Handler.Sprung
public import Runner.Beweis.Handler.Floating
public import Runner.Beweis.Handler.FloatingCodec
public import Runner.Beweis.Handler.FloatingUnsigned
@[expose] public section


/-! # One IR instruction: dispatch, then the handler of the opcode byte

`step_ok`: from a dispatch copy related to `t`, the x86 thread makes exactly the requests of `IR.step t` -- the
opcode read, then the handler's -- with one extra read of the dispatch table, answered by the table's word. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

theorem bad_ok {L : Lay} {k : Nat} {y : X} (h : HPre L k y) (hk : handler k = [.ud2]) :
    Match L .fault y := by
  have hc := h.code
  rw [hk] at hc
  exact .fault ((step_code hc).trans rfl)

theorem handler_ok {L : Lay} (k : Nat) {y : X} (h : HPre L k y) : Match L (IR.op k ⟨y.r12, y.r13⟩) y := by
  match k with
  | 0 => exact bad_ok h rfl
  | 1 => exact h1_ok h
  | 2 => exact h2_ok h
  | 3 => exact h3_ok h
  | 4 => exact h4_ok h
  | 5 => exact h5_ok h
  | 6 => exact h6_ok h
  | 7 => exact h7_ok h
  | 8 => exact h8_ok h
  | 9 => exact h9_ok h
  | 10 => exact h10_ok h
  | 11 => exact h11_ok h
  | 12 => exact h12_ok h
  | 13 => exact h13_ok h
  | 14 => exact h14_ok h
  | 15 => exact h15_ok h
  | 16 => exact h16_ok h
  | 17 => exact h17_ok h
  | 18 => exact h18_ok h
  | 19 => exact h19_ok h
  | 20 => exact h20_ok h
  | 21 => exact h21_ok h
  | 22 => exact h22_ok h
  | 23 => exact h23_ok h
  | 24 => exact h24_ok h
  | 25 => exact h25_ok h
  | 26 => exact h26_ok h
  | 27 => exact h27_ok h
  | 28 => exact fp_arith_ok .add .f32 h
  | 29 => exact fp_arith_ok .add .f64 h
  | 30 => exact fp_arith_ok .sub .f32 h
  | 31 => exact fp_arith_ok .sub .f64 h
  | 32 => exact fp_arith_ok .mul .f32 h
  | 33 => exact fp_arith_ok .mul .f64 h
  | 34 => exact fp_arith_ok .div .f32 h
  | 35 => exact fp_arith_ok .div .f64 h
  | 36 => exact fp_neg_ok .f32 h
  | 37 => exact fp_neg_ok .f64 h
  | 38 => exact fp_compare_ok .eq .f32 h
  | 39 => exact fp_compare_ok .eq .f64 h
  | 40 => exact fp_compare_ok .lt .f32 h
  | 41 => exact fp_compare_ok .lt .f64 h
  | 42 => exact fp_compare_ok .le .f32 h
  | 43 => exact fp_compare_ok .le .f64 h
  | 44 => exact fp_finite_ok .f32 h
  | 45 => exact fp_finite_ok .f64 h
  | 46 => exact fp_fromInt_ok .f32 h
  | 47 => exact fp_fromInt_ok .f64 h
  | 48 => by
    simpa only [IR.op, IR.fp, fpSequence] using
      fp_fromUInt64_body (L := L) (y := y) .f32 h.tb h.mode h.code
  | 49 => by
    simpa only [IR.op, IR.fp, fpSequence] using
      fp_fromUInt64_body (L := L) (y := y) .f64 h.tb h.mode h.code
  | 50 => exact bad_ok h rfl
  | 51 => exact bad_ok h rfl
  | 52 => exact bad_ok h rfl
  | 53 => exact bad_ok h rfl
  | 54 => exact fp_widen_ok h
  | 55 => exact fp_narrow_ok h
  | 56 => exact fp_flags_ok .f32 h
  | 57 => exact fp_flags_ok .f64 h
  | 58 => exact fp_truncate_ok .f32 h
  | 59 => exact fp_truncate_ok .f64 h
  | k + 60 => exact bad_ok h rfl

theorem step_ok {L : Lay} (hI : CInv L) {t : IR.T} {x : X} (hD : Disp L t x) : Match L (IR.step t) x := by
  have h1 := step_code hD.code
  have hc2 : Code L.C (x.rip + BitVec.ofNat 64 (enc (.ldzx .rax (mb .r12))).length) [.jmpm (ms .r14 .rax)] :=
    hD.code.2.2
  let x1 (v : W) := ({ x with rip := x.rip + BitVec.ofNat 64 (enc (.ldzx .rax (mb .r12))).length }.set .rax v)
  have he : exec (.ldzx .rax (mb .r12)) (enc (.ldzx .rax (mb .r12))).length x =
      .ask (.rd 1 t.pc) fun r => opt r fun p => .next (x1 ((p.1.setWidth 8).setWidth 64)) := by
    have hea : ea x (mb .r12) = t.pc := by simp [ea, mb, X.get, hD.pc, sx32]
    simp only [exec, rd8, hea]
    rfl
  simp only [IR.step, rd8]
  refine .ask (h1.trans he) fun a => ?_
  cases a with
  | none => exact .kfault
  | some p =>
    simp only [opt_some]
    refine .knext ?_
    have h2 : step L.C (x1 ((p.1.setWidth 8).setWidth 64)) =
        exec (.jmpm (ms .r14 .rax)) (enc (.jmpm (ms .r14 .rax))).length (x1 ((p.1.setWidth 8).setWidth 64)) :=
      step_code (x := x1 _) (by simpa [x1, X.set] using hc2)
    let op := ((p.1.setWidth 8).setWidth 64 : W).toNat
    have hop : op < 256 := by simp only [op, BitVec.toNat_setWidth]; omega
    have hnot : op ≠ 256 := by omega
    have hwid : readOnlyWidth op = 8 := by simp only [readOnlyWidth, if_neg hnot]
    have hval : readOnlyValue L op = L.H op := by simp only [readOnlyValue, if_neg hnot]
    refine .tbl (k := fun r => opt r fun q => .next { x1 ((p.1.setWidth 8).setWidth 64) with rip := q.1 }) op
      (by omega) ?_ fun w => ?_
    · rw [hwid, h2]
      simp only [exec, rd64, ea, ms, X.get, x1, X.set, hD.tb, taddr, op, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    · simp only [hval, opt_some]
      refine .knext ?_
      have hpre : HPre L op { x1 ((p.1.setWidth 8).setWidth 64) with rip := L.H op } :=
        ⟨rfl, by simp [x1, X.set, hD.tb], hI, by simpa [x1, X.set, X.fpReady] using hD.mode⟩
      have := handler_ok op hpre
      have e : (⟨({ x1 ((p.1.setWidth 8).setWidth 64) with rip := L.H op }).r12,
          ({ x1 ((p.1.setWidth 8).setWidth 64) with rip := L.H op }).r13⟩ : IR.T) = t := by
        simp [x1, X.set, hD.pc, hD.fp]
      rw [e] at this
      exact this

end Runner.Beweis
