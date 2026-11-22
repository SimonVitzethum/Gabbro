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

/-- At any installed spawn site, the exact code and the startup stack
    determine the next host request and both relocated child operands. -/
theorem Emitted.workerReference (output : Emitted src reserve options)
    {view : Mem} (table : TabInv L0 view)
    (code : BytesAt view codeBase (output.image.code.flatMap encII))
    (frame : FrameOK view (BitVec.ofNat 64 output.image.fp0) output.image.Ks)
    {j : Nat} (declared : j < output.starts.length) :
    let pc := BitVec.ofNat 64 (codeBase + 16 * (10 * j))
    let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * j)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (j + 1)))⟩
    ∃ (count : Nat) (expected : Cfg (SC L0) (Res T)),
      BildMehr.SCMemoryPrefix L0 ⟨⟨view, table⟩, [some (.next ⟨pc, parent.fp⟩)]⟩ count expected ∧
      expected.ths = [some (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)] ∧
      ∀ {control : Res T} {actual : Mem}, BildMehr.SoloLauf ⟨pc, parent.fp⟩ view control actual →
        BildMehr.MemoryScopedControl (imageRootReads output 0) (imageStackFootprint output 0) control ∨
          control = .ask (.sys cloneReq) (fun answer =>
            opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1) := by
  intro pc parent child
  let entry := codeBase + 16 * (10 * output.starts.length + startLen + startLen * j)
  let stack := output.image.fp0 + 8 * (output.image.Ks * (j + 1))
  let scratch := startScratch output.compiled.main
  have start := List.getElem?_eq_getElem (l := output.starts) declared
  obtain ⟨decoded, _, _⟩ := output.loaded_boot_site output.checkedUnit.unit.Q code start
  have placed : CodeAt view pc (spawnOne scratch entry stack) := by
    simpa only [pc, BitVec.ofNat_add] using decoded
  obtain ⟨_, body, _, layout, _, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have totalStack : output.image.fp0 + 8 * (output.image.Ks * (output.starts.length + 1)) ≤ output.image.Y.lo := by
    simpa only [Emitted.starts, List.length_map] using layout.hylo
  have imageEnd := layout.hfit
  have worldStart := layout.hyord
  have worldEnd := layout.hyhi
  have stackFits : stack < 2 ^ 31 := by
    have used : output.image.Ks * (j + 1) ≤ output.image.Ks * (output.starts.length + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right declared.le 1)
    dsimp only [stack]
    omega
  have frameStart : output.image.fp0 = codeBase + 16 * (headLen output.starts.length + body.length) := by
    simpa only [Emitted.starts, List.length_map] using layout.hfp
  have entryFits : entry < 2 ^ 31 := by
    dsimp only [entry]
    simp only [headLen, startLen] at frameStart ⊢
    omega
  have scratchFits : scratch + 8 ≤ output.image.Ks := layout.hex _ List.mem_cons_self
  have far : CodeFar pc 10 (BitVec.ofNat 64 output.image.fp0) output.image.Ks := by
    have singleStack : output.image.Ks ≤ output.image.Ks * (j + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos j)
    have room : output.image.fp0 + 8 * output.image.Ks < 2 ^ 64 := by
      dsimp only [stack] at stackFits
      omega
    apply codeFar_nat _ room
    simp only [headLen, startLen] at frameStart
    omega
  obtain ⟨count, prepared, preserved, ran, confined⟩ :=
    BildMehr.spawnSite_reference table placed frame far (by omega) layout.startLimits.2.2 entryFits stackFits
  have fpValue : (BitVec.ofNat 64 output.image.fp0).toNat = output.image.fp0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [stack] at stackFits; omega)]
  have ownFrame : inSlots parent.fp 0 output.image.Ks = imageStackFootprint output 0 := by
    funext byte
    apply propext
    simp only [parent, inSlots, fpValue, imageStackFootprint, Nat.zero_le, true_and,
      Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.mul_one]
  have readFrame : ∀ byte, inSlots parent.fp 0 output.image.Ks byte → imageRootReads output 0 byte :=
    fun byte inside => .inl (ownFrame ▸ inside)
  have readCode : ∀ byte : W, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * 10 →
      imageRootReads output 0 byte := by
    intro byte _ last
    exact .inr (last.trans_le (fpValue ▸ far.2.2))
  refine ⟨count, ⟨⟨prepared, preserved⟩, _⟩, ran, rfl, ?_⟩
  intro control actual solo
  rcases confined (imageRootReads output 0) readFrame readCode solo with inside | pending
  · exact .inl (Eq.mp (congrArg (fun writes => BildMehr.MemoryScopedControl (imageRootReads output 0) writes control)
      ownFrame) inside)
  · exact .inr pending

/-- The active spawn site retains one ordinary IR prefix and a proof
    memory agreeing with the issuer on the code and private frame. -/
def Emitted.SpawnPrefix (output : Emitted src reserve options) (index : Nat)
    (control : Res T) (view : Mem) : Prop :=
  ∃ initial localMemory, TabInv L0 initial ∧
    BytesAt initial codeBase (output.image.code.flatMap encII) ∧
    FrameOK initial (BitVec.ofNat 64 output.image.fp0) output.image.Ks ∧
    BildMehr.SoloLauf ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * index)), BitVec.ofNat 64 output.image.fp0⟩
      initial control localMemory ∧
    BildMehr.GleichAuf (imageRootReads output 0) view localMemory

theorem Emitted.SpawnPrefix.start {view : Mem} {index : Nat} (table : TabInv L0 view)
    (code : BytesAt view codeBase (output.image.code.flatMap encII))
    (frame : FrameOK view (BitVec.ofNat 64 output.image.fp0) output.image.Ks) :
    output.SpawnPrefix index
      (.next ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * index)), BitVec.ofNat 64 output.image.fp0⟩) view :=
  ⟨view, view, table, code, frame, BildMehr.soloLauf_start _ _, fun byte _ => BildMehr.GleichAt.refl _ byte⟩

theorem Emitted.SpawnPrefix.transport {index : Nat} {control : Res T} {view next : Mem}
    (phase : output.SpawnPrefix index control view)
    (unchanged : BildMehr.GleichAuf (imageRootReads output 0) next view) :
    output.SpawnPrefix index control next := by
  obtain ⟨initial, localMemory, table, code, frame, run, agrees⟩ := phase
  exact ⟨initial, localMemory, table, code, frame, run,
    fun byte used => (unchanged byte used).trans (agrees byte used)⟩

theorem Emitted.SpawnPrefix.begin {index : Nat} {view : Mem} {pointer : T}
    (phase : output.SpawnPrefix index (.next pointer) view) :
    output.SpawnPrefix index (step pointer) view := by
  obtain ⟨initial, localMemory, table, code, frame, run, agrees⟩ := phase
  exact ⟨initial, localMemory, table, code, frame, run.priv, agrees⟩

theorem Emitted.SpawnPrefix.answer_memory {index : Nat} (declared : index < output.starts.length)
    {before after : imageTSO.St} {request : Op} {resume : Ans → Res T} {reply : Ans}
    (phase : output.SpawnPrefix index (.ask request resume) (before.1.view 0))
    (ordinary : BildMehr.istSpeicherOp request = true)
    (answered : imageTSO.ans before 0 request reply after) :
    output.SpawnPrefix index (resume reply) (after.1.view 0) := by
  obtain ⟨initial, localMemory, table, code, frame, run, agrees⟩ := phase
  obtain ⟨_, _, _, _, classify⟩ := output.workerReference table code frame declared
  rcases classify run with access | clone
  · obtain ⟨updated, continued, preserved⟩ := run.answer_tso agrees access.2.1 ordinary answered.1
    exact ⟨initial, updated, table, code, frame, continued, preserved⟩
  · cases clone
    cases ordinary

/-- The active startup reference survives a silent process step.
    Changes by another issuer need only preserve the startup read region. -/
theorem Emitted.SpawnPrefix.silent_step {index : Nat} (declared : index < output.starts.length)
    {before after : Cfg imageTSO (Res T)} {previous : Res T} {events : List Ev}
    (phase : output.SpawnPrefix index previous (before.ms.1.view 0))
    (active : before.ths[0]? = some (some previous))
    (step : ProcessStep imageTSO actI before events after) (quiet : events = [])
    (stable : after.ths[0]? = before.ths[0]? →
      BildMehr.GleichAuf (imageRootReads output 0) (after.ms.1.view 0) (before.ms.1.view 0)) :
    ∃ control, after.ths[0]? = some (some control) ∧ output.SpawnPrefix index control (after.ms.1.view 0) := by
  have untouched (same : after.ths[0]? = before.ths[0]?) :
      ∃ control, after.ths[0]? = some (some control) ∧ output.SpawnPrefix index control (after.ms.1.view 0) :=
    ⟨previous, same.trans active, phase.transport (stable same)⟩
  have indexPresent := (List.getElem?_eq_some_iff.mp active).1
  cases step with
  | tau => exact untouched rfl
  | @priv issuer control _ found moved =>
    by_cases own : issuer = 0
    · subst issuer
      have exactControl := Option.some.inj (Option.some.inj (found.symm.trans active))
      subst control
      cases previous with
      | next pointer =>
        cases moved
        exact ⟨_, List.getElem?_set_self indexPresent, phase.begin⟩
      | ask | fault | unk => cases moved
    · exact untouched (List.getElem?_set_ne own)
  | @ask issuer control _ operation continuation reply memory found asked ordinary answered advanced =>
    by_cases own : issuer = 0
    · subst issuer
      have exactControl := Option.some.inj (Option.some.inj (found.symm.trans active))
      subst control
      cases previous with
      | next | fault | unk => cases asked
      | ask request resume =>
        cases asked
        cases advanced
        have permitted : BildMehr.istSpeicherOp operation = true := by
          obtain ⟨_, _, table, code, frame, path, _⟩ := phase
          obtain ⟨_, _, _, _, classify⟩ := output.workerReference table code frame declared
          rcases classify path with access | clone
          · exact access.1
          · cases clone
            exact ((by decide : ¬ (Op.sys cloneReq).special = false) ordinary).elim
        exact ⟨_, List.getElem?_set_self indexPresent, phase.answer_memory declared permitted answered⟩
    · exact untouched (List.getElem?_set_ne own)
  | exit | cloneNo | clone => cases quiet

/-- Select the main thread's actual local controls from an arbitrarily
    interleaved silent path through a single installed spawn site. -/
theorem Emitted.SpawnPrefix.follow_silent {index : Nat} (declared : index < output.starts.length)
    {start finish : Cfg imageTSO (Res T)} {control : Res T} {count : Nat}
    (path : ProcessPrefix imageTSO actI start [] count finish)
    (running : start.ths[0]? = some (some control))
    (phase : output.SpawnPrefix index control (start.ms.1.view 0))
    (stable : ∀ {before after : Cfg imageTSO (Res T)} {steps : Nat},
      ProcessPrefix imageTSO actI start [] steps before →
      ProcessStep imageTSO actI before [] after → after.ths[0]? = before.ths[0]? →
      BildMehr.GleichAuf (imageRootReads output 0) (after.ms.1.view 0) (before.ms.1.view 0)) :
    ∃ residual, finish.ths[0]? = some (some residual) ∧ output.SpawnPrefix index residual (finish.ms.1.view 0) := by
  suffices follow : ∀ {before after : Cfg imageTSO (Res T)} {events : List Ev} {steps : Nat},
      ProcessPrefix imageTSO actI before events steps after → events = [] →
      ∀ {prior current}, ProcessPrefix imageTSO actI start [] prior before →
        before.ths[0]? = some (some current) → output.SpawnPrefix index current (before.ms.1.view 0) →
        ∃ residual, after.ths[0]? = some (some residual) ∧ output.SpawnPrefix index residual (after.ms.1.view 0)
    from follow path rfl (.nil start) running phase
  intro before after events steps execution
  induction execution with
  | nil =>
    intro _ _ _ _ active activePhase
    exact ⟨_, active, activePhase⟩
  | cons step _ ih =>
    intro quiet prior current earlier active activePhase
    obtain ⟨first, rest⟩ := List.append_eq_nil_iff.mp quiet
    have silent := first ▸ step
    obtain ⟨residual, ready, remaining⟩ := activePhase.silent_step declared active step first (stable earlier silent)
    exact ih rest (earlier.trans (.ofStep silent)) ready remaining

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
  have firstFrame := bild_initialized_frames_u output.initialValid output.emission output.funktionen_voll
    loaded.payload 0 (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.add_zero] at firstFrame
  have startMemory : initial.ms.1 = memory.1.m :=
    BildMehr.mergedView_empty _ _ loaded.emptyBuffers
  have exactStart : initial =
      (⟨⟨memory.1.m, memory.2.1⟩, [some (.next
        ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩ : Cfg (SC L0) (Res T)) := by
    exact congrArg (fun state : (SC L0).St =>
      ⟨state, (output.irEntry memory).ths⟩ : (SC L0).St → Cfg (SC L0) (Res T))
      (Subtype.ext startMemory)
  obtain ⟨count, expected, reference, waiting, _⟩ :=
    output.workerReference memory.2.1 (output.loaded_code loaded.payload) firstFrame workers
  refine ⟨count, expected, ?_, ?_⟩
  · rw [exactStart]
    simpa only [Nat.mul_zero, Nat.add_zero] using reference
  · simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one] using waiting

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

/-- Both outcomes of an actual clone response install the exact parent
    continuation. A positive result also appends the decoded child. -/
theorem image_clone_response
    {before after : Cfg imageTSO (Res T)} {parent child : T} {id extra : W}
    (waiting : before.ths[0]? = some (some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)))
    (observed : ProcessStep imageTSO actI before [(0, cloneReq, some (id, extra))] after) :
    id ≠ 0 ∧ after = ⟨before.ms, before.ths.set 0 (some (ret1 parent id)) ++
      (if 0 < id.toInt then [some (.next child)] else [])⟩ := by
  have responseState {issuer : Nat} {memory : imageTSO.St}
      (response : imageTSO.ans before.ms issuer (.sys cloneReq) (some (id, extra)) memory) :
      memory = before.ms ∧ id ≠ 0 := by
    have actual := response.2
    change (if cloneReq = cloneReq then _ else _) at actual
    rw [if_pos rfl] at actual
    obtain ⟨unchanged, result, additional, exactWords, nonzero⟩ := actual
    exact ⟨unchanged, (Prod.mk.inj (Option.some.inj exactWords)).1.symm ▸ nonzero⟩
  suffices exactClone : ∀ {labels}, ProcessStep imageTSO actI before labels after →
      labels = [(0, cloneReq, some (id, extra))] →
      id ≠ 0 ∧ after = ⟨before.ms, before.ths.set 0 (some (ret1 parent id)) ++
        (if 0 < id.toInt then [some (.next child)] else [])⟩
    from exactClone observed rfl
  intro labels transition logged
  cases transition with
  | tau | priv => cases logged
  | @ask _ _ _ request _ _ _ _ _ ordinary _ _ =>
    cases request with
    | sys call =>
      simp only [Mach.lbl, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at logged
      obtain ⟨_, rfl, _⟩ := logged
      exact ((by decide : ¬ (Op.sys cloneReq).special = false) ordinary).elim
    | rd | wr | cas | fp => cases logged
  | exit => cases logged
  | cloneNo found asked response refused resumed =>
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at logged
    obtain ⟨rfl, rfl⟩ := logged
    have exactControl := Option.some.inj (Option.some.inj (found.symm.trans waiting))
    subst_vars
    cases asked
    obtain ⟨rfl, nonzero⟩ := responseState response
    have negative := refused id extra rfl
    simp only [opt_some, ite_eq_right nonzero, Res.next.injEq] at resumed
    subst_vars
    exact ⟨nonzero, by simp only [ite_eq_right negative, List.append_nil]⟩
  | clone found asked response positive resumed spawned =>
    simp only [List.cons.injEq, Prod.mk.injEq, Option.some.injEq, true_and, and_true] at logged
    obtain ⟨rfl, rfl, rfl⟩ := logged
    have same := found.symm.trans waiting
    have exactControl := Option.some.inj (Option.some.inj same)
    subst_vars
    cases asked
    obtain ⟨rfl, nonzero⟩ := responseState response
    simp only [opt_some, ite_eq_right nonzero, Res.next.injEq] at resumed spawned
    subst_vars
    exact ⟨nonzero, by simp only [ite_eq_left positive, ite_true]⟩

/-- Every actual successful startup clone activates the next declared GX
    slot with its exact arguments, even when earlier children have
    already run or retired. -/
theorem ImageSlotsMatch.observed_clone {history : List Ev}
    {before after : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {parent child : T} {id extra : W}
    (slots : ImageSlotsMatch output E O history before state)
    (waiting : before.ths[0]? = some (some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)))
    (notWaiting : state.wartet 0 = [])
    (declared : before.ths.length < E.starts.length)
    (observed : ProcessStep imageTSO actI before [(0, cloneReq, some (id, extra))] after)
    (positive : 0 < id.toInt) :
    ∃ next actualStart, E.starts[before.ths.length]? = some actualStart ∧
      ImageReach output E O state next ∧
      ImageSlotsMatch output E O (history ++ [(0, cloneReq, some (id, extra))]) after next ∧ next.m = state.m ∧
      after = ⟨before.ms, before.ths.set 0 (some (ret1 parent id)) ++ [some (.next child)]⟩ ∧
      ∀ {body : BildMehr.PCfg} {snapshots positions committed},
        BildMehr.MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
          body state snapshots positions committed →
        BildMehr.MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
          ⟨body.m, body.ths ++ [none]⟩ next snapshots positions committed := by
  obtain ⟨next, actualStart, start, step, matched, unchanged, append⟩ :=
    slots.activate_clone (parent := parent) (child := child) (id := id) (extra := extra)
      waiting notWaiting declared
  have control : after = ⟨before.ms, before.ths.set 0 (some (ret1 parent id)) ++ [some (.next child)]⟩ := by
    simpa only [if_pos positive] using (image_clone_response waiting observed).2
  exact ⟨next, actualStart, start, .schritt _ _ .start step, control.symm ▸ matched, unchanged, control, append⟩

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
  obtain ⟨next, _, _, reached, matched, unchanged, _, _⟩ :=
    slots.observed_clone ready rfl declared observed positive
  refine ⟨next, matched, reached, unchanged, ?_⟩
  rw [unit.starts]
  rfl

end Gabbro.Stage0
