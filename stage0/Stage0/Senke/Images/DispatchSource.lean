module

public import Stage0.Senke.Images.Correctness
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- Every continuing step of the mapped loader establishes the precise
    entry stub, including its typed arguments at the serialized frame
    offsets. It takes no step of the source program. -/
theorem MappedImage.dispatched_source [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {machine : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (O : Orakel (declOf output.compiled.unit))
    {after : Cfg imageTSO (Res T)} {events : List Ev}
    (step : ProcessStep imageTSO actI ⟨machine.ms, [some t4]⟩ events after) :
    events = [] ∧ ImageSlotsMatch after (imageSourceStart E) ∧
      ImageRuntimeMatches output E O [] after (imageSourceStart E) := by
  obtain ⟨quiet, rfl⟩ := mapped.dispatch_step step
  obtain ⟨_, _, _, bytes, packed, _, _, _, stackMemory⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll mapped.bytes
  obtain ⟨_, _, _, _, _, _, entryWords, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  obtain ⟨_, entryFrame, entryLoaded⟩ :=
    startStackBytes_frame packed output.image.fp0 stackMemory 0 (Nat.zero_lt_succ _)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero, entryWords] at entryFrame entryLoaded
  have initialFrame := bild_initialized_frames_u output.initialValid output.emission
    output.funktionen_voll mapped.bytes 0 (Nat.zero_le _)
  have view : machine.ms.1.view 0 = machine.ms.1.m := by
    simp only [TSt.view, mapped.emptyBuffers 0, List.foldl_nil]
  have entered : ImageRootPhase output E [] (machine.ms.1.view 0) 0
      (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩) (imageSourceStart E) := by
    rw [view]
    refine Or.inr ⟨⟨output.compiled.main, output.args⟩, by rw [unit.starts]; rfl,
      Or.inl rfl, output.loaded_code mapped.bytes, initialFrame, ?_, ?_⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using startFrameBytes_read entryFrame entryLoaded
    · refine ⟨⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩, ?_, Or.inl rfl⟩
      refine ⟨rfl, 0, Nat.zero_le _, ?_, rfl⟩
      change 0 < 10 * output.starts.length + 8
      omega
  refine ⟨quiet, ⟨?_, ?_⟩, ?_⟩
  · intro i
    cases i <;> simp [imageSourceStart, FadenStart]
  · intro i retired
    cases i <;> simp at retired
  · refine ⟨fun _ _ => False, [none], privateBuffers_empty mapped.emptyBuffers, rfl, Or.inl ⟨?_, ?_⟩, ?_⟩
    · intro i r
      cases i <;> simp
    · change WeltAt (mergedView machine.ms.1 (fun _ _ => False)) _ ((speicherR E.sp0).welt [])
      rw [mergedView_empty _ _ mapped.emptyBuffers, unit.memory]
      exact (output.loaded_initial_world mapped.bytes).withIdle
    · intro i
      cases i with
      | zero => exact Or.inr ⟨_, rfl, rfl, entered⟩
      | succ i => exact Or.inl rfl

end Gabbro.Stage0
