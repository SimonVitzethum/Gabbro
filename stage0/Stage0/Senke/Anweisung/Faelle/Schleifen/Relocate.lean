/- Overlap-safe emitted frame relocation: copy the highest source word first. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter
import Stage0.Senke.Anweisung.PufferTor

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

/-- Actual Runner execution, exact destination frame, and all relocated words.
    No disjointness premise between the source and destination ranges is needed. -/
theorem relocate_run [Kern] {m : Mem} {pc fp : W} {K base shift n : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (bound : base + shift + n ≤ K)
    (code : CodeAt m pc (relocateC base shift n))
    (far : CodeFar pc n fp K) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), fp⟩ m' ∧
      Agree fp (base + shift) (base + shift + n) m m' ∧
      ∀ i, i < n → m'.rd64 (slot fp (BitVec.ofNat 64 (base + shift + i))) =
        m.rd64 (slot fp (BitVec.ofNat 64 (base + i))) := by
  induction n generalizing m pc with
  | zero =>
    exact ⟨m, by simpa using (Star.refl ⟨pc, fp⟩ m), .refl _ _ _ _, by omega⟩
  | succ n ih =>
    let dst := base + shift + n
    let src := base + n
    let v := BitVec.ofNat 64 (le m (slot fp (BitVec.ofNat 64 src)) 8)
    have read : m.rd64 (slot fp (BitVec.ofNat 64 src)) = some v := by
      simp only [Mem.rd64, frame.rd src (by dsimp [src]; omega), ↓reduceIte]
      rfl
    let m1 := write m (slot fp (BitVec.ofNat 64 dst)) 8 v.toNat
    have writeFrame : Agree fp dst K m m1 := agree_write frame.room (by omega) (by dsimp [dst]; omega) _
    have step := quant_mov frame small (show dst < K by dsimp [dst]; omega)
      (show src < K by dsimp [src]; omega) (codeAt_left code) read
    have tailCode : CodeAt m1 (pc + 16) (relocateC base shift n) := by
      exact (codeAt_right code).agree writeFrame (by simpa [relocateC_length, Nat.add_comm] using (codeFar_right (n := 1) (k := n) (by simpa [Nat.add_comm] using far)))
    obtain ⟨m2, rest, tailFrame, moved⟩ := ih (frame.agree writeFrame) (by omega)
      tailCode (by simpa [relocateC_length, Nat.add_comm] using (codeFar_right (n := 1) (k := n) (by simpa [Nat.add_comm] using far)))
    refine ⟨m2, ?_, ?_, ?_⟩
    · have run := step.trans rest
      have eq : pc + 16 + BitVec.ofNat 64 (16 * n) = pc + BitVec.ofNat 64 (16 * (n + 1)) := by
        simpa [Nat.add_comm] using (pc_add pc 1 n)
      rw [eq] at run
      exact run
    · have first : Agree fp (base + shift) (base + shift + (n + 1)) m m1 :=
        agree_write (by have := frame.room; omega) (by dsimp [dst]; omega) (by dsimp [dst]; omega) _
      exact first.trans ⟨tailFrame.rd, tailFrame.wr, fun x hx => tailFrame.b x (by
        unfold inSlots at *; omega)⟩
    · intro i hi
      by_cases top : i = n
      · subst i
        rw [agree_rd_high tailFrame frame.room (by omega) (by omega)]
        rw [read]
        exact rd64_write_same (frame.rd dst (by dsimp [dst]; omega))
      · rw [moved i (by omega)]
        rw [Mem.rd64_write_far (slot_far frame.room (show dst < K by dsimp [dst]; omega)
          (show base + i < K by omega) (by dsimp [dst]; omega))]

/-- Relocate the complete lexical environment, parameters and locals together. -/
theorem relocate_env [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {m : Mem} {pc fp : W} {K reserved extra : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (bound : frei Γ (reserved + extra) ≤ K)
    (env : EnvAt L m fp ρ reserved)
    (code : CodeAt m pc (relocateC (FB + reserved) extra Γ.length))
    (far : CodeFar pc Γ.length fp K) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * Γ.length), fp⟩ m' ∧
      Agree fp (FB + reserved + extra) (frei Γ (reserved + extra)) m m' ∧
      EnvAt L m' fp ρ (reserved + extra) := by
  obtain ⟨m', run, writes, moved⟩ := relocate_run frame small
    (show FB + reserved + extra + Γ.length ≤ K by unfold frei at bound; omega) code far
  refine ⟨m', run, ?_, ?_⟩
  · simpa [frei, Nat.add_assoc] using writes
  · intro τ x
    obtain ⟨w, read, enc⟩ := env τ x
    have ix := idx_lt x
    have h := moved (Γ.length - 1 - Var.idx x) (by omega)
    refine ⟨w, ?_, enc⟩
    simpa [vslot, Nat.add_assoc] using h.trans read

end Gabbro.Stage0.Senke
