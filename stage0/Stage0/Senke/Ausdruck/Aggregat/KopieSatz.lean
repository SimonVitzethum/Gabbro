/- Compositional execution of contiguous value copies on the actual IR machine. -/
import Stage0.Senke.Ausdruck.Sim
import Stage0.Senke.Ausdruck.Quant.Frame

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The common transport primitive also copies results back down the frame.
    Its footprint is exactly the destination span; neither direction requires
    a source expression or a postulated child run. -/
theorem copyWords_run {fp : Runner.W} {K : Nat} (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {dst src : Nat},
    FrameOK m fp K → K < 2 ^ 31 → dst + words.length ≤ K → src + words.length ≤ K →
    (dst ≤ src ∨ src + words.length ≤ dst) →
    CodeAt m pc (copyWords words.length dst src) → CodeFar pc words.length fp K →
    WordsAt m fp src words →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * words.length), fp⟩ m' ∧
      Agree fp dst (dst + words.length) m m' ∧ WordsAt m' fp dst words := by
  induction words with
  | nil =>
    intro m pc dst src frame small hd hs disjoint code far input
    exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _,
      by intro i hi; simp at hi⟩
  | cons w ws ih =>
    intro m pc dst src frame small hd hs disjoint code far input
    have read : m.rd64 (slot fp (BitVec.ofNat 64 src)) = some w := input 0 (by simp)
    let m1 := write m (slot fp (BitVec.ofNat 64 dst)) 8 w.toNat
    have step := quant_mov frame small (show dst < K by simp at hd; omega)
      (show src < K by simp at hs; omega) (codeAt_left code) read
    have changed : Agree fp dst K m m1 := agree_write frame.room (by omega) (by simp at hd; omega) _
    have tail : WordsAt m1 fp (src + 1) ws := by
      intro i hi
      have ne : dst ≠ src + 1 + i := by simp only [List.length_cons] at disjoint; omega
      rw [rd64_write_far (slot_far frame.room (by simp at hd; omega) (by simp at hs; omega) ne)]
      have h := input (i + 1) (by simp; omega)
      change m.rd64 (slot fp (BitVec.ofNat 64 (src + (i + 1)))) = some ws[i] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have tailFar := codeFar_right (n := 1) (k := ws.length) (by simpa [Nat.add_comm] using far)
    have tailCode : CodeAt m1 (pc + 16) (copyWords ws.length (dst + 1) (src + 1)) :=
      (codeAt_right (a := [ci 2 dst src 0]) code).agree changed (by simpa using tailFar)
    obtain ⟨m2, run, changed2, output⟩ := ih (m := m1) (pc := pc + 16) (dst := dst + 1) (src := src + 1) (frame.agree changed) small
      (by simp at hd; omega) (by simp at hs; omega)
      (by simp only [List.length_cons] at disjoint; omega) tailCode tailFar tail
    have room : fp.toNat + 8 * (dst + (w :: ws).length) ≤ 2 ^ 64 := by have := frame.room; omega
    have first : Agree fp dst (dst + (w :: ws).length) m m1 :=
      agree_write room (by omega) (by simp) _
    have rest : Agree fp dst (dst + (w :: ws).length) m1 m2 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using changed2.mono (Nat.le_succ dst)
    refine ⟨m2, ?_, first.trans rest, ?_⟩
    · have combined := step.trans run
      simpa [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm] using combined
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, agree_rd_low changed2 (by have := frame.room; simp at hd; omega) (by omega) (by omega)]
        exact (wr_slot frame (by simp at hd; omega) w).2.1
      | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using output i (by simp at hi; omega)

/-- One typed copy contract for locals, parameters and results in either direction.
    All limbs and nested elements are copied, with the canonical declared width. -/
theorem copyValue_run {τ : Ty} {v : Wert D τ} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst src : Nat} (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (hd : dst + valueWords τ ≤ K) (hs : src + valueWords τ ≤ K)
    (disjoint : dst ≤ src ∨ src + valueWords τ ≤ dst)
    (code : CodeAt m pc (copyWords (valueWords τ) dst src))
    (far : CodeFar pc (valueWords τ) fp K) (input : ValueAt L m fp src τ v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * valueWords τ), fp⟩ m' ∧
      Agree fp dst (dst + valueWords τ) m m' ∧ ValueAt L m' fp dst τ v := by
  obtain ⟨m', run, changed, output⟩ := copyWords_run (encodeWords L τ v) frame small
    (by simpa only [encodeWords_length] using hd) (by simpa only [encodeWords_length] using hs)
    (by simpa only [encodeWords_length] using disjoint)
    (by simpa only [encodeWords_length] using code) (by simpa only [encodeWords_length] using far) input.2
  exact ⟨m', by simpa only [encodeWords_length] using run,
    by simpa only [encodeWords_length] using changed, input.1, output⟩

/-- Normal results, including the empty result's ABI marker, use the same copy. -/
theorem copyResult_run {e : Option Ty} {v : ErgVal D e} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst src : Nat} (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (hd : dst + resultWords e ≤ K) (hs : src + resultWords e ≤ K)
    (disjoint : dst ≤ src ∨ src + resultWords e ≤ dst)
    (code : CodeAt m pc (copyWords (resultWords e) dst src))
    (far : CodeFar pc (resultWords e) fp K) (input : ResultAt L m fp src e v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * resultWords e), fp⟩ m' ∧
      Agree fp dst (dst + resultWords e) m m' ∧ ResultAt L m' fp dst e v := by
  cases e with
  | none => exact copyWords_run [0] frame small hd hs disjoint code far input
  | some τ => exact copyValue_run frame small hd hs disjoint code far input

/-- The expression emitter's prefix-to-fresh specialization of the shared copy. -/
theorem copyWords_ok {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {fp : Runner.W} {K : Nat} (words : List Runner.W)
    {m : Runner.Mem} {pc : Runner.W} {d s : Nat}
    (hs : s + words.length ≤ d) (hd : d + words.length ≤ K)
    (pre : Pre L m pc fp K d (copyWords words.length d s) ρ W reserved)
    (input : WordsAt m fp s words) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * words.length), fp⟩ m' ∧
      Agree fp d K m m' ∧ WordsAt m' fp d words := by
  obtain ⟨m', run, changed, output⟩ := copyWords_run words pre.frame pre.small hd
    (by omega) (Or.inr hs) pre.code (by simpa only [copyWords_length] using pre.far) input
  exact ⟨m', run, Agree.widen changed hd, output⟩

end Gabbro.Stage0.Senke
