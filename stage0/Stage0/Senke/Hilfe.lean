/-
  File:      stage0/Stage0/Senke/Hilfe.lean
  Subject:   Tools for `ir_sim`: code split in parts, field values, writing a frame slot, one instruction as a step.
-/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

theorem pc_add (pc : Runner.W) (a b : Nat) :
    pc + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * b) = pc + BitVec.ofNat 64 (16 * (a + b)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem codeAt_left {m : Runner.Mem} {pc : Runner.W} {a b : List II} (h : CodeAt m pc (a ++ b)) : CodeAt m pc a :=
  fun k hk => by
    have := h k (by simp; omega)
    simpa [List.getElem_append_left hk] using this

theorem codeAt_right {m : Runner.Mem} {pc : Runner.W} {a b : List II} (h : CodeAt m pc (a ++ b)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * a.length)) b := fun k hk => by
  have := h (a.length + k) (by simp; omega)
  rw [← pc_add] at this
  simpa [List.getElem_append_right (Nat.le_add_right _ _)] using this

theorem codeFar_left {pc fp : Runner.W} {n k K : Nat} (h : CodeFar pc (n + k) fp K) : CodeFar pc n fp K := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨by omega, h2, by omega⟩

theorem codeFar_right {pc fp : Runner.W} {n k K : Nat} (h : CodeFar pc (n + k) fp K) :
    CodeFar (pc + BitVec.ofNat 64 (16 * n)) k fp K := by
  obtain ⟨h1, h2, h3⟩ := h
  have := pc.isLt
  have hx : (pc + BitVec.ofNat 64 (16 * n)).toNat = pc.toNat + 16 * n := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by rw [hx]; omega, h2, by rw [hx]; omega⟩

/-- A field holding a small natural number. -/
theorem sx_nat {d : Nat} (h : d < 2 ^ 31) : sx (II.f (d : Int)) = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.ofInt 32 (d : Int)).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofInt, decide_eq_false_iff_not]; omega
  simp only [sx, II.f, BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth,
    BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- A field holding a literal of 32 bits. -/
theorem sx_lit {n : Int} (h : lit32 n = true) : sx (II.f n) = BitVec.ofInt 64 n := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at h
  apply BitVec.eq_of_toInt_eq
  simp only [sx, II.f, BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]

/-- Writing slot `d` of a frame. -/
theorem wr_slot {m : Runner.Mem} {fp : Runner.W} {K d : Nat} (hF : FrameOK m fp K) (hd : d < K) (v : Runner.W) :
    m.wr64 (slot fp (BitVec.ofNat 64 d)) v = some (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat) ∧
    (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat).rd64 (slot fp (BitVec.ofNat 64 d)) = some v ∧
    Agree fp d K m (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat) :=
  ⟨wr64_some (hF.wr d hd), rd64_wr64 (wr64_some (hF.wr d hd)) (hF.rd d hd),
   agree_write hF.room (Nat.le_refl d) hd _⟩

/-- One instruction as a step of the machine. -/
theorem star_ins {m m' : Runner.Mem} {pc fp : Runner.W} {i : II} (hc : CodeAt m pc [i]) (ho : i.o < 256)
    (hr : Run (op i.o ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m') :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [i].length), fp⟩ m' :=
  Star.one (run_step (t := ⟨pc, fp⟩) (by simpa using hc 0 (by simp)) ho hr)

theorem vslot_lt {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : vslot x < frei Γ := by
  have : Var.idx x < Γ.length := by
    induction x with
    | here => simp [Var.idx]
    | there x ih => simp [Var.idx]; omega
  unfold vslot frei; omega

theorem envAt_agree {D : Deklaration} {m m' : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {d K : Nat}
    (h : EnvAt m fp ρ) (ha : Agree fp d K m m') (hF : FrameOK m fp K) (hd : frei Γ ≤ d) (hK : d ≤ K) :
    EnvAt m' fp ρ := by
  intro τ x
  obtain ⟨w, hw, he⟩ := h τ x
  refine ⟨w, ?_, he⟩
  rw [agree_rd_low ha hF.room (by have := vslot_lt x; omega) hK]
  exact hw

end Gabbro.Stage0.Senke
