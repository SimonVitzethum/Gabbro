module

public import Stage0.Senke.Images.Correctness
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The concrete successful mmap continuation establishes the runner
    relation from its instruction address and the mapped image base. -/
theorem MappedImage.of_mmap_continuation [Kern] {output : Emitted src reserve options}
    {state : imageTSO.St} {x : Runner.X86.X}
    (payload : BytesAt state.1.m Runner.Prog.IMG output.bytes)
    (buffers : ∀ i, state.1.buf i = [])
    (file : FileInv state.1.m)
    (address : x.rip = BitVec.ofNat 64 (Runner.Prog.BASE + Runner.Prog.find Runner.Prog.tab Runner.Prog.LOADER) +
      BitVec.ofNat 64 (lenOfL (Runner.Prog.ld1 ++ [Runner.Prog.ldj1] ++ Runner.Prog.ld2 ++
        [Runner.Prog.ldj2, Runner.Prog.ldj3] ++ Runner.Prog.ld4 ++ [Runner.Prog.ldj4])))
    (base : x.rcx = BitVec.ofNat 64 Runner.Prog.IMG) :
    MappedImage output ⟨state, [some x]⟩ := by
  obtain ⟨valid, bytes⟩ := Bool.and_eq_true_iff.mp loader_placed
  have code := code_of_image valid bytes
  have suffix := code_append
    (is := Runner.Prog.ld1 ++ [Runner.Prog.ldj1] ++ Runner.Prog.ld2 ++
      [Runner.Prog.ldj2, Runner.Prog.ldj3] ++ Runner.Prog.ld4 ++ [Runner.Prog.ldj4])
    (js := Runner.Prog.ld5 TBL ++ [.ud2])
    (by simpa only [Runner.Prog.loaderI, List.append_assoc] using code)
  refine ⟨payload, buffers, ⟨rfl, ?_⟩, file⟩
  intro i
  cases i with
  | zero => exact seg5 (by rw [address]; exact suffix) base
  | succ i => trivial

/-- Every continuing step of the mapped loader establishes the precise
    entry stub, including its typed arguments at the serialized frame
    offsets. It takes no step of the source program. -/
theorem MappedImage.dispatched_source [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {machine : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (O : Orakel (declOf output.compiled.unit))
    {after : Cfg imageTSO (Res T)} {events : List Ev}
    (step : ProcessStep imageTSO actI ⟨machine.ms, [some t4]⟩ events after) :
    events = [] ∧ ImageSlotsMatch output E O [] after (imageSourceStart E) ∧
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
      simp only [ite_true, Nat.zero_add, startLen]
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

/-- The loader part of the runner refinement is concrete: every
    matched IR prefix through dispatch keeps the declared initial GX
    state, including when x86 has only partially executed the dispatch. -/
theorem MappedImage.loader_prefix_source [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {machine : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (O : Orakel (declOf output.compiled.unit))
    {after : Cfg imageTSO (Res T)} {events : List Ev} {steps : Nat}
    (run : ProcessPrefix imageTSO actI ⟨machine.ms, [some t4]⟩ events steps after)
    (loaderSteps : steps ≤ 1) :
    events = [] ∧ ImageSlotsMatch output E O events after (imageSourceStart E) ∧
      ImageRuntimeMatches output E O events after (imageSourceStart E) := by
  cases run with
  | nil =>
    obtain ⟨_, slots, _, runtime⟩ := mapped.source_start unit O
    exact ⟨rfl, slots, runtime⟩
  | cons step rest =>
    cases rest with
    | nil =>
      obtain ⟨rfl, matched⟩ := mapped.dispatched_source unit O step
      exact ⟨rfl, matched⟩
    | cons next tail => omega

/-- Every concrete x86 prefix that has advanced at most through loader
    dispatch satisfies the complete goal at the declared source start. -/
theorem MappedImage.loader_prefix_goal [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {machine finish : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : NutzerPflichtA E) (calls : CallSitePflicht E) (posts : PostDeckt E)
    (binding : ForeignVertrag E O) (hardware : HardwareAnnahmenHw O E.Q)
    {events : List Ev} {count : Nat} (run : ProcessPrefix imageTSO (actX L0) machine events count finish)
    (inLoader : ∀ ir steps, ProcessPrefix imageTSO actI ⟨machine.ms, [some t4]⟩ events steps ir →
      Rel L0 ir finish → steps ≤ 1) :
    ∃ ir steps, ProcessPrefix imageTSO actI ⟨machine.ms, [some t4]⟩ events steps ir ∧ Rel L0 ir finish ∧
      events = [] ∧ ImageSlotsMatch output E O events ir (imageSourceStart E) ∧
      ImageRuntimeMatches output E O events ir (imageSourceStart E) ∧
      ImageGoalAt output E O (imageSourceStart E) := by
  obtain ⟨ir, steps, trace, related⟩ := mapped.runner_prefix run
  obtain ⟨quiet, slots, runtime⟩ := mapped.loader_prefix_source unit O trace (inLoader ir steps trace related)
  refine ⟨ir, steps, trace, related, quiet, slots, runtime, ?_⟩
  exact gabbro_ziel akzeptiertX_pruefer _ E output.fsA output.lsA output.csA accepted duties calls posts O binding
    hardware output.image.passes _ _ (laufzeit_initRuhe E) _ _ .start

/-- On the domain with a complete current unit export, the actual CLI bytes
    determine the source, checker verdict and full goal through dispatch. -/
theorem irBild_checked_loader_prefix [Kern] {bytes : List B}
    (emitted : irBild src reserve options = .ok bytes) :
    ∃ output : Emitted src reserve options, emit src reserve options = .ok output ∧
      output.bytes = bytes ∧ CanonicalSourceProgram output.compiled ∧
      (output.compiled.unit.axs.length = 0 →
        OldSource.zertifizierbar output.compiled.unit = true → imageAccumulatorItems output = [] →
        let E := output.goalUnit (axWahr _)
        ImageModelUnit output E ∧
        akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true ∧
        ∀ (O : Orakel (declOf output.compiled.unit)), HardwareAnnahmenHw O E.Q →
          ∀ {machine finish : Cfg imageTSO Runner.X86.X} {events : List Ev} {count : Nat},
            MappedImage output machine → ProcessPrefix imageTSO (actX L0) machine events count finish →
            (∀ ir steps, ProcessPrefix imageTSO actI ⟨machine.ms, [some t4]⟩ events steps ir →
              Rel L0 ir finish → steps ≤ 1) →
            ∃ ir steps, ProcessPrefix imageTSO actI ⟨machine.ms, [some t4]⟩ events steps ir ∧
              Rel L0 ir finish ∧ events = [] ∧ ImageSlotsMatch output E O events ir (imageSourceStart E) ∧
              ImageRuntimeMatches output E O events ir (imageSourceStart E) ∧
              ImageGoalAt output E O (imageSourceStart E)) := by
  obtain ⟨output, wrote, payload⟩ := irBild_emitted src reserve bytes emitted
  refine ⟨output, wrote, payload, compile_source_program src output.compiled, ?_⟩
  intro noAxioms noOwnership noAccumulators
  obtain ⟨unit, accepted⟩ := output.checked_image_model_empty noAxioms noOwnership noAccumulators
  refine ⟨unit, accepted, ?_⟩
  intro O hardware machine finish events count mapped run inLoader
  have absent (a : (declOf output.compiled.unit).Ax) :
      (declOf output.compiled.unit).axHerkunft a ≠ some AxOrigin.software :=
    False.elim ((Nat.not_lt_zero a.val) (noAxioms ▸ a.isLt))
  have duties := nutzerPflicht_of_geprueft output.fsA.2 output.lsA.2
    (Bool.and_eq_true_iff.mp (output.goal_axiomFree (axWahr _) noAxioms)).2
  exact mapped.loader_prefix_goal unit accepted duties (callSitePflicht_ohne _ absent) unit.postDeckt
    (foreignVertrag_ohne _ O absent) hardware run inLoader

end Gabbro.Stage0
