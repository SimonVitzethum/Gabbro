module

public import Stage0.Senke.Images.Correctness
import Stage0.Senke.Bild.Mehr.ImageTransition
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- Before allocation, a future stack keeps its loaded bytes and
    permissions along the actual runner prefix. A local write
    classification is sufficient, since allocated slots only grow. -/
theorem image_future_frame_of_prefix [Kern] {output : Emitted src reserve options}
    {θ : Type} {act : θ → Res θ} {initial final : Cfg imageTSO θ}
    {history : List Ev} {count future : Nat}
    (path : ProcessPrefix imageTSO act initial history count final)
    (unallocated : final.ths.length ≤ future)
    (classify : ∀ {before after : Cfg imageTSO θ} {earlier events : List Ev} {steps : Nat},
      ProcessPrefix imageTSO act initial earlier steps before →
      ProcessStep imageTSO act before events after → after.ths.length ≤ future →
      GleichAuf (imageStackFootprint output future) before.ms.1.m after.ms.1.m) :
    GleichAuf (imageStackFootprint output future) initial.ms.1.m final.ms.1.m := by
  induction path with
  | nil => exact fun byte _ => GleichAt.refl _ byte
  | cons step tail ih =>
    have remaining := processPrefix_threadSlots tail
    have stillUnallocated := (Nat.le_add_right _ _).trans (remaining ▸ unallocated)
    have first := classify (.nil _) step stillUnallocated
    have rest := ih unallocated (fun earlier next bound =>
      classify ((ProcessPrefix.ofStep step).trans earlier) next bound)
    exact fun byte inFrame => (first byte inFrame).trans (rest byte inFrame)

/-- Agreement on a startup reservation transports both the frame
    permissions and every serialized argument word to the new memory. -/
theorem image_stack_frame_preserved [Kern] {output : Emitted src reserve options} {thread base : Nat}
    {saved current : Mem} {words : List W} (declared : thread ≤ output.starts.length)
    (equal : GleichAuf (imageStackFootprint output thread) saved current)
    (fits : base + words.length ≤ output.image.Ks) :
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread))
    FrameOK saved fp output.image.Ks → WordsAt saved fp base words →
      FrameOK current fp output.image.Ks ∧ WordsAt current fp base words := by
  intro fp frame arguments
  have slotAgreement (index : Nat) (inside : index < output.image.Ks) :
      GleichAuf (fenster (slot fp (BitVec.ofNat 64 index))) saved current :=
    fun byte touches => equal byte (imageStackFootprint_slot declared inside touches)
  refine ⟨⟨frame.lt, ?_, ?_⟩, ?_⟩
  · intro index inside
    rw [← gleich_rdall (slotAgreement index inside)]
    exact frame.rd index inside
  · intro index inside
    rw [← gleich_wr (slotAgreement index inside)]
    exact frame.wr index inside
  · intro index inside
    have within : base + index < output.image.Ks := by omega
    rw [← gleich_rd64 (slotAgreement (base + index) within)]
    exact arguments index inside

private theorem serializedRoot_slot (start offset : Nat) :
    slot (BitVec.ofNat 64 start) (BitVec.ofNat 64 offset) = BitVec.ofNat 64 (start + 8 * offset) := by
  change BitVec.ofNat 64 start + BitVec.ofNat 64 offset * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm offset 8]

/-- Every serialized root in the actual image has its declared typed
    arguments at the final frame address assigned to that thread. -/
theorem Emitted.loaded_root_frame [Kern] (output : Emitted src reserve options)
    {memory : Mem} (loaded : BytesAt memory Runner.Prog.IMG output.bytes) {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root) :
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    let words := encodeEnv output.image.Y root.2
    (FB + FB + words.length ≤ output.image.Ks) ∧
      FrameOK memory fp output.image.Ks ∧ WordsAt memory fp (FB + FB) words := by
  intro fp words
  obtain ⟨_, _, _, _, packed, _, _, _, stackMemory⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  obtain ⟨_, _, _, _, _, roots, _, rootWords⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  have chosen : (output.image.args :: output.image.rootArgs)[index + 1]? = some words := by
    simp only [List.getElem?_cons_succ, rootWords, List.getElem?_map, declared, Option.map_some, words]
  obtain ⟨within, exactWords⟩ := List.getElem?_eq_some_iff.mp chosen
  obtain ⟨_, frameMade, frameBytes⟩ := startStackBytes_frame packed output.image.fp0 stackMemory (index + 1) within
  rw [exactWords] at frameMade
  have fits : FB + FB + words.length ≤ output.image.Ks := by
    unfold startFrameBytes at frameMade
    split at frameMade
    · assumption
    · cases frameMade
  have bound : index + 1 ≤ output.image.roots.length := by
    rw [roots, List.length_map]
    exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
  have frame := bild_initialized_frames_u output.initialValid output.emission
    output.funktionen_voll loaded (index + 1) bound
  refine ⟨fits, frame, ?_⟩
  intro position present
  simpa only [fp, serializedRoot_slot, Nat.mul_assoc] using
    startFrameBytes_read frameMade frameBytes position present

/-- The serialized frame, preserved up to allocation, establishes the
    exact root-stub phase at the child's emitted entry address. -/
theorem Emitted.fresh_root_phase [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {original memory : Mem} (loaded : BytesAt original Runner.Prog.IMG output.bytes)
    {index : Nat} {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (preserved : GleichAuf (imageStackFootprint output (index + 1)) original memory)
    (code : BytesAt memory codeBase (output.image.code.flatMap encII))
    {history : List Ev} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (head : state.m.faeden (index + 1) = (imageSourceStart E).m.faeden (index + 1)) :
    let pc := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index))
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    ImageRootPhase output E history memory (index + 1) (.next ⟨pc, fp⟩) state := by
  intro pc fp
  have declaredThread := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
  obtain ⟨fits, setup, typed⟩ := output.loaded_root_frame loaded declared
  obtain ⟨frame, words⟩ := image_stack_frame_preserved declaredThread preserved fits setup typed
  refine Or.inr ⟨root, ?_, Or.inl head, code, frame, ?_,
    ⟨⟨pc, fp⟩, ?_, Or.inl rfl⟩⟩
  · rw [unit.starts]
    exact declared
  · intro position present
    have read := words position present
    simpa only [fp, serializedRoot_slot] using read
  · refine ⟨rfl, 10 * output.starts.length + startLen + startLen * index, ?_, ?_, rfl⟩
    all_goals simp only [Nat.succ_ne_zero, ite_false, startLen] <;> omega

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
  · refine ⟨imageStackFootprint output, [none], privateBuffers_empty mapped.emptyBuffers, rfl,
      Or.inl ⟨?_, ?_⟩, ?_⟩
    · intro i r
      cases i <;> simp
    · change WeltAt (mergedView machine.ms.1 (imageStackFootprint output)) _ ((speicherR E.sp0).welt [])
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

private theorem MappedImage.loader_thread [Kern] {output : Emitted src reserve options}
    {before : Cfg imageTSO Runner.X86.X} (mapped : MappedImage output before)
    {i : Nat} {x : Runner.X86.X} (found : before.ths[i]? = some (some x)) :
    i = 0 ∧ Match L0 t4 x := by
  obtain ⟨r, slot, control⟩ := rel_at mapped.loader found
  cases i with
  | zero =>
    have same : r = t4 := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using slot.symm
    exact ⟨rfl, same ▸ control⟩
  | succ i => simp at slot

private theorem loader_not_next (t : T) : t4 ≠ .next t := by intro equal; cases equal

private theorem loader_not_sys {x : Runner.X86.X} {req : Req} {k : Ans → Res Runner.X86.X}
    (matched : Match L0 t4 x) (asked : actX L0 x = .ask (.sys req) k) : False := by
  rcases inv_ask matched asked loader_not_next with ⟨_, _, impossible, _⟩ | ⟨_, impossible, _⟩
  · cases impossible
  · cases impossible

/-- The actual first continuing x86 step from the mapped loader either
    performs runner bookkeeping or reads the serialized frame word. The
    IR prefix through dispatch therefore has length at most one. -/
theorem MappedImage.runner_loader_step [Kern] {output : Emitted src reserve options}
    {before after : Cfg imageTSO Runner.X86.X} {events : List Ev}
    (mapped : MappedImage output before) (step : ProcessStep imageTSO (actX L0) before events after) :
    ∃ ir steps, ProcessPrefix imageTSO actI ⟨before.ms, [some t4]⟩ events steps ir ∧
      steps ≤ 1 ∧ Rel L0 ir after := by
  let initial : Cfg imageTSO (Res T) := ⟨before.ms, [some t4]⟩
  cases step with
  | tau flush =>
    obtain ⟨i, _, _, _, pending, _⟩ := flush
    rw [mapped.emptyBuffers i] at pending
    cases pending
  | priv found continued =>
    obtain ⟨rfl, matched⟩ := mapped.loader_thread found
    exact ⟨initial, 0, .nil _, by decide,
      ⟨mapped.loader.ms, relT_setX mapped.loader.th rfl (inv_next matched continued loader_not_next)⟩⟩
  | @ask i x x' request k answer memory found asked ordinary answered continued =>
    obtain ⟨rfl, matched⟩ := mapped.loader_thread found
    rcases inv_ask matched asked loader_not_next with ⟨op, valid, rfl, resumes⟩ | ⟨resume, exactRequest, resumes⟩
    · obtain ⟨rfl, word, rfl⟩ := imageTSO_fixed _ _ _ _ _ valid answered
      exact ⟨initial, 0, .nil _, by decide,
        ⟨mapped.loader.ms, relT_setX mapped.loader.th rfl (invK_next (continued ▸ resumes word))⟩⟩
    · have ready : actI t4 = .ask request (fun a => .next (resume a)) := by
        rw [exactRequest]
        rfl
      have finished := invK_next (continued ▸ resumes answer)
      have move := ProcessStep.ask (act := actI) (c := initial) (i := 0) rfl ready ordinary answered rfl
      exact ⟨_, 1, ProcessPrefix.ofStep move, Nat.le_refl 1,
        ⟨rfl, relT_set mapped.loader.th (vI := some (resume answer)) (vX := some x') finished⟩⟩
  | exit found asked _ | cloneNo found asked _ _ _ | clone found asked _ _ _ _ =>
    exact (loader_not_sys (mapped.loader_thread found).2 asked).elim

/-- An actual x86 step at the mapped loader cannot terminate the process.
    The dispatch word is readable and is the exact frame address, so the
    loader's only IR request also cannot fault on its answer. -/
theorem MappedImage.loader_step_no_terminal [Kern] {output : Emitted src reserve options}
    {before : Cfg imageTSO Runner.X86.X} {events : List Ev} {ending : Ende}
    (mapped : MappedImage output before) (run : Tr imageTSO (actX L0) before events ending 1) :
    ending = .lauf := by
  cases run with
  | tau _ suffix => cases suffix; rfl
  | priv _ _ suffix => cases suffix; rfl
  | ask _ _ _ _ _ suffix => cases suffix; rfl
  | exit _ _ _ suffix => cases suffix; rfl
  | cloneNo _ _ _ _ _ suffix => cases suffix; rfl
  | clone _ _ _ _ _ _ suffix => cases suffix; rfl
  | exitGroup found asked _ | cloneNoStop found asked _ _ _ =>
    exact (loader_not_sys (mapped.loader_thread found).2 asked).elim
  | @stop _ i x e found stopped =>
    have matched := (mapped.loader_thread found).2
    cases actual : actX L0 x with
    | fault => cases inv_fault matched actual loader_not_next
    | unk => exact (inv_unk matched actual).elim
    | next | ask => simp only [actual, Runner.Mach.Res.ende, reduceCtorEq] at stopped
  | @askStop _ i x request k value memory e found asked _ answered stopped =>
    obtain ⟨rfl, matched⟩ := mapped.loader_thread found
    rcases inv_ask matched asked loader_not_next with ⟨op, valid, rfl, resumed⟩ | ⟨resume, exact, resumed⟩
    · obtain ⟨_, word, rfl⟩ := imageTSO_fixed _ _ _ _ _ valid answered
      cases (invK_ende (resumed word) stopped).1
    · simp only [t4, rd64, Runner.Res.ask.injEq] at exact
      obtain ⟨rfl, rfl⟩ := exact
      obtain ⟨_, extra, read⟩ := answered.1
      have word := output.loader_frame mapped.bytes
      have valueExact : value = some (BitVec.ofNat 64 output.image.fp0, extra) := by
        simpa only [rdN, TSt.view, mapped.emptyBuffers 0, List.foldl_nil, word, Option.map_some] using read
      have failed := (invK_ende (resumed value) stopped).1
      rw [valueExact] at failed
      simp only [opt_some, reduceCtorEq] at failed

/-- An actual loader step is silent and either leaves the same mapped
    phase or establishes the root stub with its initialized arguments.
    The declared source start is valid in both phases. -/
theorem MappedImage.loader_transition [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {before after : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output before) (unit : ImageModelUnit output E)
    (O : Orakel (declOf output.compiled.unit))
    {events : List Ev} (step : ProcessStep imageTSO (actX L0) before events after) :
    events = [] ∧ (MappedImage output after ∨
      ∃ ir, ProcessPrefix imageTSO actI ⟨before.ms, [some t4]⟩ [] 1 ir ∧ Rel L0 ir after ∧
        ImageSlotsMatch output E O [] ir (imageSourceStart E) ∧
        ImageRuntimeMatches output E O [] ir (imageSourceStart E)) := by
  obtain ⟨ir, steps, path, bound, related⟩ := mapped.runner_loader_step step
  cases path with
  | nil =>
    have memory := related.ms.symm
    refine ⟨rfl, Or.inl ⟨?_, ?_, ⟨rfl, related.th⟩, ?_⟩⟩
    · rw [memory]; exact mapped.bytes
    · rw [memory]; exact mapped.emptyBuffers
    · rw [memory]; exact mapped.runnerFile
  | cons read tail =>
    cases tail with
    | nil =>
      obtain ⟨quiet, slots, runtime⟩ := mapped.dispatched_source unit O read
      refine ⟨?_, Or.inr ⟨_, ProcessPrefix.ofStep (quiet ▸ read), related, slots, runtime⟩⟩
      simp only [quiet, List.nil_append]
    | cons _ _ => omega

private theorem MappedImage.source_start_goal [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : NutzerPflichtA E) (calls : CallSitePflicht E) (posts : PostDeckt E)
    (binding : ForeignVertrag E O) (hardware : HardwareAnnahmenHw O E.Q) :
    ImageGoalAt output E O (imageSourceStart E) :=
  gabbro_ziel akzeptiertX_pruefer _ E output.fsA output.lsA output.csA accepted duties calls posts O binding
    hardware output.image.passes _ _ (laufzeit_initRuhe E) _ _ .start

/-- The first actual continuing x86 step already has the full goal at
    the declared source start. The loader bound is a consequence of the
    machine step, so no restriction on candidate IR prefixes is required. -/
theorem MappedImage.first_step_goal [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {machine finish : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : NutzerPflichtA E) (calls : CallSitePflicht E) (posts : PostDeckt E)
    (binding : ForeignVertrag E O) (hardware : HardwareAnnahmenHw O E.Q)
    {events : List Ev} (step : ProcessStep imageTSO (actX L0) machine events finish) :
    ∃ ir steps, ProcessPrefix imageTSO actI ⟨machine.ms, [some t4]⟩ events steps ir ∧ Rel L0 ir finish ∧
      events = [] ∧ ImageSlotsMatch output E O events ir (imageSourceStart E) ∧
      ImageRuntimeMatches output E O events ir (imageSourceStart E) ∧
      ImageGoalAt output E O (imageSourceStart E) := by
  obtain ⟨ir, steps, path, bound, related⟩ := mapped.runner_loader_step step
  obtain ⟨quiet, slots, runtime⟩ := mapped.loader_prefix_source unit O path bound
  exact ⟨ir, steps, path, related, quiet, slots, runtime,
    MappedImage.source_start_goal accepted duties calls posts binding hardware⟩

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
  exact ⟨ir, steps, trace, related, quiet, slots, runtime,
    MappedImage.source_start_goal accepted duties calls posts binding hardware⟩

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
