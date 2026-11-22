module

public import Stage0.Senke.Bild.ImageAddress
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The last immediate of the child's call tail materializes the actual
    lowered address in its scratch slot, with code and frame rights intact. -/
theorem Emitted.root_call_target [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (bytes : BytesAt (before.ms.1.view (index + 1)) codeBase (output.image.code.flatMap encII)) :
    let entry := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index))
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    let pointer : T := ⟨entry + BitVec.ofNat 64 (16 * 3), fp⟩
    let scratch := FB + FB + contextWords ((declOf output.compiled.unit).params root.1)
    before.ths[index + 1]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view (index + 1)) fp output.image.Ks →
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 5
        ⟨after, before.ths.set (index + 1) (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      after.1.view (index + 1) =
        Mem.write (before.ms.1.view (index + 1)) (slot fp (BitVec.ofNat 64 scratch)) 8 (output.image.A root.1) ∧
      BytesAt (after.1.view (index + 1)) codeBase (output.image.code.flatMap encII) ∧
      FrameOK (after.1.view (index + 1)) fp output.image.Ks ∧
      (after.1.view (index + 1)).rd64 (slot fp (BitVec.ofNat 64 scratch)) =
        some (BitVec.ofNat 64 (output.image.A root.1)) := by
  intro entry fp pointer scratch running frame
  obtain ⟨stub, _, _, exitRoom, signed⟩ := output.root_stub_code bytes declared
  obtain ⟨_, _, _, _, _, targetFits⟩ := output.relocated_function_code bytes root.1
  have callRoom : scratch < output.image.Ks := by
    have margin := startScratch_ge root.1
    dsimp only [scratch]
    omega
  have instruction : InsAt (before.ms.1.view (index + 1)) pointer.pc 1
      (II.f (scratch : Int)) (II.f ((output.image.A root.1 : Nat) : Int)) (II.f 0) := by
    have immediate := stub 3 (by rw [startC_len]; decide)
    simpa only [pointer, entry, scratch, startC, callTail, callTailN, ci, List.singleton_append, List.cons_append,
      List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte] using immediate
  have dest : sx (II.f (scratch : Int)) = BitVec.ofNat 64 scratch := sx_nat (callRoom.trans signed)
  have target : sx (II.f ((output.image.A root.1 : Nat) : Int)) = BitVec.ofNat 64 (output.image.A root.1) :=
    sx_nat targetFits
  have writable : Mem.all before.ms.1.m.wr (slot fp (sx (II.f (scratch : Int)))) 8 = true := by
    rw [dest, ← foldl_wr (before.ms.1.buf (index + 1)) before.ms.1.m]
    exact frame.wr _ callRoom
  obtain ⟨after, run, memory, view, others⟩ :=
    tso_const_prefix (before := imageToTSO before) running instruction writable
  have small := targetFits.trans (by decide : 2 ^ 31 < 2 ^ 64)
  have written : after.1.view (index + 1) =
      Mem.write (before.ms.1.view (index + 1)) (slot fp (BitVec.ofNat 64 scratch)) 8 (output.image.A root.1) := by
    rw [view, dest, target, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] <;> rfl
  refine ⟨after, tso_silent_prefix_image run rfl, memory, others, written, ?_, ?_, ?_⟩ <;> rw [written]
  · apply output.code_survives_writes (write_nurIn _ _ _) _ bytes
    intro byte touched
    have declaredThread := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
    have reserved := imageStackFootprint_slot (output := output) (i := index + 1) declaredThread callRoom touched
    exact (Nat.le_add_right _ _).trans reserved.2.1
  · exact ⟨frame.lt, frame.rd, frame.wr⟩
  · have exactWord := rd64_write_same (w := BitVec.ofNat 64 (output.image.A root.1)) (frame.rd scratch callRoom)
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using exactWord

end Gabbro.Stage0
