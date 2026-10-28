import Runner.Beweis.Handler.Sprung

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
  | k + 25 => exact bad_ok h rfl

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
  | none => exact .fault
  | some p =>
    simp only [opt_some]
    refine .next ?_
    have h2 : step L.C (x1 ((p.1.setWidth 8).setWidth 64)) =
        exec (.jmpm (ms .r14 .rax)) (enc (.jmpm (ms .r14 .rax))).length (x1 ((p.1.setWidth 8).setWidth 64)) :=
      step_code (x := x1 _) (by simpa [x1, X.set] using hc2)
    let op := ((p.1.setWidth 8).setWidth 64 : W).toNat
    refine .tbl (k := fun r => opt r fun q => .next { x1 ((p.1.setWidth 8).setWidth 64) with rip := q.1 }) op
      ?_ fun w => ?_
    · rw [h2]
      simp only [exec, rd64, ea, ms, X.get, x1, X.set, hD.tb, taddr, op, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    · simp only [opt_some]
      refine .next ?_
      have hpre : HPre L op { x1 ((p.1.setWidth 8).setWidth 64) with rip := L.H op } :=
        ⟨rfl, by simp [x1, X.set, hD.tb], hI⟩
      have := handler_ok op hpre
      have e : (⟨({ x1 ((p.1.setWidth 8).setWidth 64) with rip := L.H op }).r12,
          ({ x1 ((p.1.setWidth 8).setWidth 64) with rip := L.H op }).r13⟩ : IR.T) = t := by
        simp [x1, X.set, hD.pc, hD.fp]
      rw [e] at this
      exact this

end Runner.Beweis
