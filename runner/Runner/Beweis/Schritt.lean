import Runner.Beweis.Handler.Sys

/-! # One IR step: dispatch, then the handler of the opcode byte

`step_ok`: from related states, the model does what one `S0IR` step does -- with at least one x86 step when the IR
continues, so a run of the model never stalls behind the IR. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-- Opcodes without a handler: `ud2`, a fault, as in the IR. -/
theorem bad_ok {L : Lay} {k : Nat} {y : X} (h : HPre L k y) (hk : handler k = [.ud2]) :
    Reach y .fault := by
  have hc := h.code
  rw [hk] at hc
  exact Reach.here ((step_code hc).trans rfl) (by simp)

theorem handler_ok {L : Lay} (k : Nat) {y : X} (h : HPre L k y) : HSim L (IR.op k ⟨y.r12, y.r13, y.mem⟩) y := by
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
  | k + 24 => exact bad_ok h rfl

/-- The model's side of one IR step. -/
def Sim1 (L : Lay) : Res IR.S → X → Prop
  | .next s', x => ∃ z, Plus x z ∧ R L s' z
  | r, x => HSim L r x

theorem step_ok {L : Lay} {s : IR.S} {x : X} (hR : R L s x) : Sim1 L (IR.step s) x := by
  obtain ⟨hnone, hsome⟩ := dispatch_ok hR
  simp only [IR.step]
  cases hop : s.mem.rd8 s.pc with
  | none => exact hnone hop
  | some op =>
    obtain ⟨y, hxy, hrip, h12, h13, h14, hm⟩ := hsome op hop
    have hpre : HPre L op.toNat y := ⟨hrip, h14.trans hR.tb, hm ▸ hR.img⟩
    have hs : s = ⟨y.r12, y.r13, y.mem⟩ := by
      obtain ⟨pc, fp, mem⟩ := s
      simp only [h12, h13, hm, hR.pc, hR.fp, hR.mem]
    have hh := handler_ok op.toNat hpre
    rw [← hs] at hh
    obtain ⟨y1, hy1, hy⟩ := hxy
    simp only [opt_some]
    cases hr : IR.op op.toNat s with
    | next s' =>
      rw [hr] at hh
      obtain ⟨z, hz, hRz⟩ := hh
      exact ⟨z, ⟨y1, hy1, hy.trans hz⟩, hRz⟩
    | fault | sys | unk =>
      rw [hr] at hh
      exact HSim.prefix (Star.step hy1 hy) hh

end Runner.Beweis
