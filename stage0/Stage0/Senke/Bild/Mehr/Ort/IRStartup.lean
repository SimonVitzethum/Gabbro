module

public import Stage0.Senke.Images.Correctness
public import Stage0.Senke.Bild.Emitted
public import Stage0.Senke.Bild.Mehr.Ort.SpawnReference
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Senke Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options} [Kern]
  {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
  {O : Orakel (declOf output.compiled.unit)} {memory : imageTSO.St}

/-- The exact serialized IR is ready to run in the Lean IR machine. -/
structure LoadedIRImage (output : Emitted src reserve options) (memory : imageTSO.St) : Prop where
  payload : BytesAt memory.1.m Runner.Prog.IMG output.bytes
  emptyBuffers : ∀ thread, memory.1.buf thread = []

def Emitted.irEntry (output : Emitted src reserve options) (memory : imageTSO.St) :
    Cfg imageTSO (Res T) :=
  ⟨memory, [some (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩

/-- Until the first host observation, the loaded image runs on its one
    initial thread. Buffer flushes project away. Every generated memory
    reference ending at a host request contains the projected execution. -/
theorem LoadedIRImage.silentEntry {finish : Cfg imageTSO (Res T)} {count : Nat}
    (loaded : LoadedIRImage output memory)
    (path : ProcessPrefix imageTSO actI (output.irEntry memory) [] count finish) :
    let startSC := BildMehr.singleThreadSC (imageToTSO (output.irEntry memory))
    let finishSC := BildMehr.singleThreadSC (imageToTSO finish)
    ∃ steps, steps ≤ count ∧ finish.ths.length = 1 ∧
      ProcessPrefix (SC L0) actI startSC [] steps finishSC ∧
      startSC.ms.1 = memory.1.m ∧ finishSC.ms.1 = finish.ms.1.view 0 ∧
      ∀ expected available request resume,
        BildMehr.SCMemoryPrefix L0 startSC available expected →
        expected.ths = [some (.ask (.sys request) resume)] →
        steps ≤ available ∧ BildMehr.SCMemoryPrefix L0 finishSC (available - steps) expected ∧
        ∀ {next events}, ProcessStep imageTSO actI finish events next → events ≠ [] →
          steps = available ∧ finishSC = expected := by
  obtain ⟨owned, steps, bound, run⟩ := BildMehr.tso_silent_single_thread
    (image_prefix_tso path) rfl rfl (BildMehr.privateBuffers_empty loaded.emptyBuffers)
  have one : finish.ths.length = 1 := path.silent_slots rfl
  refine ⟨steps, bound, one, run, BildMehr.mergedView_empty _ _ loaded.emptyBuffers,
    BildMehr.singleThreadView _ owned, ?_⟩
  intro expected available request resume reference waiting
  obtain ⟨within, rest⟩ := reference.consume_until_host waiting run rfl (BildMehr.alleBlind_start _)
  refine ⟨within, rest, ?_⟩
  intro next events observed visible
  obtain ⟨empty, same⟩ := rest.at_observation (M := imageTSO) (before := finish) rfl one observed visible
  exact ⟨by omega, same⟩

private theorem LoadedIRImage.firstWorkerReference
    (loaded : LoadedIRImage output memory) (workers : 0 < output.starts.length) :
    let parent : T := ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * output.image.Ks)⟩
    let initial := BildMehr.singleThreadSC (imageToTSO (output.irEntry memory))
    ∃ count expected, BildMehr.SCMemoryPrefix L0 initial count expected ∧
      expected.ths = [some (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)] := by
  intro parent child initial
  let entry := codeBase + 16 * (10 * output.starts.length + startLen)
  let stack := output.image.fp0 + 8 * output.image.Ks
  let scratch := startScratch output.compiled.main
  have firstDeclared : output.starts[0]? = some output.starts[0] := List.getElem?_eq_getElem workers
  obtain ⟨decoded, _, _⟩ := output.loaded_boot_site output.checkedUnit.unit.Q
    (output.loaded_code loaded.payload) firstDeclared
  have code : CodeAt memory.1.m (BitVec.ofNat 64 codeBase) (spawnOne scratch entry stack) := by
    simpa [scratch, entry, stack] using decoded
  obtain ⟨_, body, _, layout, _, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have firstFrame := bild_initialized_frames_u output.initialValid output.emission output.funktionen_voll
    loaded.payload 0 (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.add_zero] at firstFrame
  have imageEnd : output.image.fp0 + 8 * output.image.K < 2 ^ 31 := layout.hfit
  have totalStack : output.image.fp0 + 8 * (output.image.Ks * (output.starts.length + 1)) ≤ output.image.Y.lo := by
    simpa only [Emitted.starts, List.length_map] using layout.hylo
  have worldStart := layout.hyord
  have worldEnd := layout.hyhi
  have singleStack : output.image.Ks ≤ output.image.Ks * (output.starts.length + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have stackFits : stack < 2 ^ 31 := by dsimp only [stack]; omega
  have slotsFit : output.image.Ks < 2 ^ 31 := by dsimp only [stack] at stackFits; omega
  have frameStart : output.image.fp0 = codeBase + 16 * (headLen output.starts.length + body.length) := by
    simpa only [Emitted.starts, List.length_map] using layout.hfp
  have entryFits : entry < 2 ^ 31 := by
    dsimp only [entry]
    simp only [headLen, startLen] at frameStart ⊢
    omega
  have scratchFits : scratch + 8 ≤ output.image.Ks := layout.hex _ (List.mem_cons_self ..)
  have far : CodeFar (BitVec.ofNat 64 codeBase) 10 (BitVec.ofNat 64 output.image.fp0) output.image.Ks := by
    apply codeFar_nat _ (Nat.lt_trans stackFits (by decide))
    simp only [headLen, startLen] at frameStart
    omega
  have startMemory : initial.ms.1 = memory.1.m :=
    BildMehr.mergedView_empty _ _ loaded.emptyBuffers
  have exactStart : initial =
      (⟨⟨memory.1.m, memory.2.1⟩, [some (.next
        ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩ : Cfg (SC L0) (Res T)) := by
    exact congrArg (fun state : (SC L0).St =>
      ⟨state, (output.irEntry memory).ths⟩ : (SC L0).St → Cfg (SC L0) (Res T))
      (Subtype.ext startMemory)
  obtain ⟨referenceSteps, prepared, invariant, reference⟩ := BildMehr.spawnSite_reference (layout := L0)
    memory.2.1 code firstFrame far (by omega) slotsFit entryFits stackFits
  exact ⟨referenceSteps, _, exactStart.symm ▸ reference, rfl⟩

/-- Before the first worker launch, the loaded IR cannot stop silently.
    Any first visible transition is at the generated clone request,
    with the exact relocated worker entry and stack. -/
theorem LoadedIRImage.workerStartup
    (loaded : LoadedIRImage output memory) (workers : 0 < output.starts.length) :
    let parent : T := ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * output.image.Ks)⟩
    (∀ {before after : Cfg imageTSO (Res T)} {event : Ev} {count : Nat},
      ProcessPrefix imageTSO actI (output.irEntry memory) [] count before →
      ProcessStep imageTSO actI before [event] after →
      before.ths = [some (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)]) ∧
    ∀ {ending count}, Tr imageTSO actI (output.irEntry memory) [] ending count → ending = .lauf := by
  intro parent child
  obtain ⟨available, expected, reference, waiting⟩ := loaded.firstWorkerReference workers
  constructor
  · intro before after event count quiet observed
    obtain ⟨_, _, _, _, _, _, covers⟩ := loaded.silentEntry quiet
    obtain ⟨_, _, atHost⟩ := covers expected available cloneReq _ reference waiting
    obtain ⟨_, same⟩ := atHost observed (by simp)
    exact (congrArg Cfg.ths same).trans waiting
  · intro ending count actual
    by_contra stopped
    obtain ⟨_, _, sc⟩ := BildMehr.image_silent_trace_sc actual stopped rfl
      (BildMehr.privateBuffers_empty loaded.emptyBuffers)
    exact stopped (reference.no_silent_stop_until_host waiting sc rfl (BildMehr.alleBlind_start _))

private theorem firstWorker_clone_control
    {before after : Cfg imageTSO (Res T)} {parent child : T} {id extra : W}
    (waiting : before.ths = [some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)])
    (observed : ProcessStep imageTSO actI before [(0, cloneReq, some (id, extra))] after)
    (positive : 0 < id.toInt) :
    after = ⟨before.ms, [some (ret1 parent id), some (.next child)]⟩ := by
  let pending : Res T := .ask (.sys cloneReq) fun answer =>
    opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1
  have issuer {i : Nat} {control : Res T} (found : before.ths[i]? = some (some control)) :
      i = 0 ∧ control = pending := by
    rw [waiting] at found
    cases i <;> simp_all only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ,
      List.getElem?_nil, reduceCtorEq, and_false, true_and, pending]
  have nonzero : id ≠ 0 := by
    rintro rfl
    exact (by decide : ¬ (0 < (0 : W).toInt)) positive
  suffices exactClone : ∀ {labels}, ProcessStep imageTSO actI before labels after →
      labels = [(0, cloneReq, some (id, extra))] →
      after = ⟨before.ms, [some (ret1 parent id), some (.next child)]⟩ from exactClone observed rfl
  intro labels transition logged
  cases transition with
  | tau | priv => cases logged
  | ask found asked ordinary _ _ =>
    obtain ⟨rfl, rfl⟩ := issuer found
    cases asked
    exact ((by decide : ¬ (Op.sys cloneReq).special = false) ordinary).elim
  | exit => cases logged
  | cloneNo _ _ _ refused _ =>
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at logged
    obtain ⟨_, accepted⟩ := logged
    exact (refused id extra accepted positive).elim
  | clone found asked response _ resumed spawned =>
    obtain ⟨rfl, rfl⟩ := issuer found
    simp only [List.cons.injEq, Prod.mk.injEq, Option.some.injEq, true_and, and_true] at logged
    obtain ⟨rfl, rfl⟩ := logged
    cases asked
    have sameMemory := response.2
    change (if cloneReq = cloneReq then _ else _) at sameMemory
    rw [ite_eq_left rfl] at sameMemory
    obtain ⟨rfl, _⟩ := sameMemory
    simp only [pending, opt_some, ite_eq_right nonzero, ite_eq_left rfl, Res.next.injEq] at resumed spawned
    subst_vars
    rw [waiting]
    rfl

/-- The first successful worker activation in the actual Lean IR agrees
    with the declared GX activation, including the source thread's
    original start environment. -/
theorem LoadedIRImage.firstWorkerActivation
    {before after : Cfg imageTSO (Res T)} {id extra : W} {count : Nat}
    (loaded : LoadedIRImage output memory) (unit : ImageModelUnit output E)
    (workers : 0 < output.starts.length)
    (quiet : ProcessPrefix imageTSO actI (output.irEntry memory) [] count before)
    (observed : ProcessStep imageTSO actI before [(0, cloneReq, some (id, extra))] after)
    (positive : 0 < id.toInt) :
    ∃ next : FadenMaschine (declOf output.compiled.unit).mitRuhe,
      ImageSlotsMatch output E O [(0, cloneReq, some (id, extra))] after next ∧
      ImageReach output E O (imageSourceStart E) next ∧ next.m = (imageSourceStart E).m ∧
      E.starts[1]? = output.starts[0]? := by
  let parent : T := ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
  let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen)),
    BitVec.ofNat 64 (output.image.fp0 + 8 * output.image.Ks)⟩
  have pending := (loaded.workerStartup workers).1 quiet observed
  have exactSlots := firstWorker_clone_control pending observed positive
  have ready : before.ths[0]? = some (some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)) := by
    rw [pending]
    rfl
  have slots : ImageSlotsMatch output E O [] before (imageSourceStart E) := by
    refine ⟨?_, ?_⟩
    · intro i
      cases i <;> simp [pending, imageSourceStart, entryStart, FadenStart]
    · intro i retired
      cases i <;> simp [pending] at retired
  have declared : before.ths.length < E.starts.length := by
    rw [pending, unit.starts, List.length_cons, List.length_cons, List.length_nil]
    omega
  obtain ⟨next, _, _, advanced, matched, unchanged, _⟩ :=
    slots.activate_clone (parent := parent) (child := child) (id := id) (extra := extra)
      ready rfl declared
  refine ⟨next, ?_, .schritt _ _ .start advanced, unchanged, ?_⟩
  · rw [pending] at matched
    rw [exactSlots]
    exact matched
  · rw [unit.starts]
    rfl

end Gabbro.Stage0
