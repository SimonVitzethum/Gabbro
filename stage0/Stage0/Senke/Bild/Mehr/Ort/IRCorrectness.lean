module

public import Stage0.Senke.Images.Correctness
public import Stage0.Senke.Bild.Emitted
public import Stage0.Senke.Bild.Mehr.Ort.SilentControl
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

/-- Every function in the actual payload has the ordinary IR semantics
    of its typed model body at every representable depth. The same code
    table is used for all calls, including indirect and recursive calls. -/
def Emitted.IRFunctionSemantics (output : Emitted src reserve options) (memory : Runner.Mem) : Prop :=
  let D := declOf output.compiled.unit
  ∃ (code : D.Fn → List II) (frameWords : Nat),
    FB + (output.image.depth + 1) * frameWords ≤ output.image.Ks ∧
    (∀ fn, ∃ top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y fn =
      some (code fn, top) ∧ top ≤ frameWords ∧
      CodeAt memory (BitVec.ofNat 64 (output.image.A fn)) (code fn) ∧
      output.image.A fn + 16 * (code fn).length ≤ output.image.fp0) ∧
    ∀ (oracle : Orakel D), TorOK output.image.Y oracle → SichtOK oracle →
      ∀ depth, depth < 2 ^ 64 →
        FunSpec output.image.Y output.image.A code
          (rufAt output.compiled.program oracle output.image.passes depth)
          (BitVec.ofNat 64 depth) ((depth + 1) * frameWords)

theorem LoadedIRImage.function_semantics (loaded : LoadedIRImage output memory) :
    output.IRFunctionSemantics memory.1.m := by
  obtain ⟨_, _, _, _, packed, _, _, startup, _⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded.payload
  obtain ⟨functions, body, spawns, layout, code, _, entry, roots⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  have exactBytes : BytesAt memory.1.m codeBase (output.image.code.flatMap encII ++
      ((startStackBytes output.image.Ks (FB + FB) (output.image.args :: output.image.rootArgs)).getD [] ++ [])) := by
    simpa only [packed, Option.getD_some, List.append_nil] using startup
  rw [code, entry, roots] at exactBytes
  obtain ⟨lowered, located, _, _, _⟩ := layout.code exactBytes
  let functionCode (fn : (declOf output.compiled.unit).Fn) :=
    ((functions[fn.val]?).map (·.1)).getD []
  refine ⟨functionCode, maxTop functions, ?_, ?_, ?_⟩
  · have enough : FB ≤ output.image.Ks := Nat.le_trans (Nat.le_add_right _ _) layout.hroom
    have reduced : 0 < output.image.depth := layout.depth_pos
    have quotient : output.image.depth + 1 = (output.image.Ks - FB) / maxTop functions := by
      rw [layout.hdepth, depthOf] at reduced ⊢
      omega
    rw [quotient]
    have used := Nat.div_mul_le_self (output.image.Ks - FB) (maxTop functions)
    omega
  · intro fn
    obtain ⟨top, built, small⟩ := lowered fn
    exact ⟨top, built, small, located fn⟩
  · intro oracle gates visibility depth fitted
    letI := gates
    letI := visibility
    exact layout.funSpec exactBytes depth fitted

/-- The production frontend, executable checker, and sequential
    function lowering agree on a single typed program and image. -/
theorem irBild_function_semantics {bytes : List B} (wrote : irBild src reserve options = .ok bytes) :
    ∃ output : Emitted src reserve options, emit src reserve options = .ok output ∧
      output.bytes = bytes ∧ CanonicalSourceProgram output.compiled ∧
      ImageModelUnit output output.checkedUnit.unit ∧
      akzeptiertX_pruefer.akzeptiert output.checkedUnit.unit output.fsA.1 output.lsA.1 output.csA.1 = true ∧
      ∀ memory : imageTSO.St, LoadedIRImage output memory → output.IRFunctionSemantics memory.1.m := by
  obtain ⟨output, emitted, payload, canonical, unit, accepted, _, _⟩ := irBild_checkImageUnit wrote
  exact ⟨output, emitted, payload, canonical, unit, accepted, fun _ loaded => loaded.function_semantics⟩

/-- An IR segment either stays silent or ends at its first host
    observation. The observed answer is checked at that exact endpoint,
    before any later segment can reuse the result area. -/
inductive ImageIRSegment : Cfg imageTSO (Res T) → List Ev → Cfg imageTSO (Res T) → Prop where
  | silent {before after count} :
    ProcessPrefix imageTSO actI before [] count after → ImageIRSegment before [] after
  | observed {before cut after count event} :
    ProcessPrefix imageTSO actI before [] count cut →
    ProcessStep imageTSO actI cut [event] after → ImageIRSegment before [event] after

/-- Segment refinement at the compiler boundary. The endpoint of a
    silent segment may lie inside any generated block. -/
structure ImageIRRefinement (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (memory : imageTSO.St) where
  related : List Ev → Cfg imageTSO (Res T) → FadenMaschine (declOf output.compiled.unit).mitRuhe → Prop
  initial : related [] (output.irEntry memory) (imageSourceStart E)
  consistent : ∀ history ir state, related history ir state →
    ImageSlotsMatch output E O history ir state ∧ ImageForeignTrace output history state ∧
      ImageRuntimeMatches output E O history ir state
  segment : ∀ {history before state events after}, related history before state →
    ImageIRSegment before events after →
    ∃ next, related (history ++ events) after next ∧ ImageReach output E O state next ∧
      ∀ event ∈ events, imageExternalEvent event = true → ImageGateEvent output E O state next after event
  stop : ∀ {history before state last ending}, related history before state →
    Tr imageTSO actI before last ending 1 → ending ≠ .lauf →
    ∃ next, ImageReach output E O state next ∧ ImageStopMatches output O next history last ending

private theorem processStep_eventCount {M : MemSys} {θ : Type} {act : θ → Res θ}
    {before after : Cfg M θ} {events : List Ev} (step : ProcessStep M act before events after) :
    events.length ≤ 1 := by
  have counted := (step.prepend (.nil after)).events_le_steps
  simpa only [List.append_nil, Nat.zero_add] using counted

private theorem singleObservation {before after : Cfg imageTSO (Res T)} {events : List Ev}
    (step : ProcessStep imageTSO actI before events after) : events = [] ∨ ∃ event, events = [event] := by
  have length := processStep_eventCount step
  cases events with
  | nil => exact .inl rfl
  | cons event rest =>
    have empty : rest = [] := List.length_eq_zero_iff.mp
      (Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ length))
    exact .inr ⟨event, congrArg (event :: ·) empty⟩

/-- Compose entire silent stretches of the IR execution at its
    observations. Only the last stretch can end inside a block without
    reaching another observation. -/
theorem ImageIRRefinement.follow (refinement : ImageIRRefinement output E O memory)
    {history events : List Ev} {before after : Cfg imageTSO (Res T)} {count : Nat}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (run : ProcessPrefix imageTSO actI before events count after)
    (initial : refinement.related history before state) :
    ∃ next, refinement.related (history ++ events) after next ∧ ImageReach output E O state next := by
  suffices follow :
      ∀ {current finish : Cfg imageTSO (Res T)} {future : List Ev} {steps : Nat},
        ProcessPrefix imageTSO actI current future steps finish →
        ∀ {anchor silentSteps previous origin},
          ProcessPrefix imageTSO actI anchor [] silentSteps current →
          refinement.related previous anchor origin →
          ∃ next, refinement.related (previous ++ future) finish next ∧ ImageReach output E O origin next
    from follow run (.nil before) initial
  intro current finish future steps path
  induction path with
  | nil =>
    intro anchor silentSteps previous origin silent matched
    obtain ⟨next, endpoint, reached, _⟩ := refinement.segment matched (.silent silent)
    exact ⟨next, endpoint, reached⟩
  | cons step _ tail =>
    intro anchor silentSteps previous origin silent matched
    rcases singleObservation step with quiet | ⟨event, observed⟩
    · subst_vars
      exact tail (silent.trans (.ofStep step)) matched
    · subst_vars
      obtain ⟨middle, advanced, first, _⟩ := refinement.segment matched (.observed silent step)
      obtain ⟨next, endpoint, rest⟩ := tail (.nil _) advanced
      exact ⟨next, by simpa only [List.append_assoc] using endpoint, imageReach_trans first rest⟩

theorem ImageIRRefinement.terminal (refinement : ImageIRRefinement output E O memory)
    {events : List Ev} {ending : Ende} {count : Nat}
    (run : Tr imageTSO actI (output.irEntry memory) events ending count) (stopped : ending ≠ .lauf) :
    ∃ earlier last state, events = earlier ++ last ∧
      ImageReach output E O (imageSourceStart E) state ∧ ImageStopMatches output O state earlier last ending := by
  obtain ⟨_, earlier, last, _, path, finish, eventsEq, _⟩ := run.split_stop stopped
  obtain ⟨_, matched, reached⟩ := refinement.follow path refinement.initial
  obtain ⟨next, advanced, exactStop⟩ := refinement.stop matched finish stopped
  exact ⟨earlier, last, next, eventsEq, imageReach_trans reached advanced, exactStop⟩

/-- Every successful production compilation exports the model unit
    accepted by the checker and refines every execution of its exact IR.
    The conclusion contains the full GX goal on every matched endpoint. -/
def Stage0Correct : Prop :=
  ∀ (source : String) (reserve : Nat) (options : Profil.Options) (bytes : List B),
    irBild source reserve options = .ok bytes →
    ∃ (output : Emitted source reserve options) (E : Einheit (declOf output.compiled.unit)),
      emit source reserve options = .ok output ∧ output.bytes = bytes ∧
      CanonicalSourceProgram output.compiled ∧ ImageModelUnit output E ∧
      akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true ∧
      ∀ (O : Orakel (declOf output.compiled.unit)),
        CallSitePflicht E → ForeignVertrag E O →
        HardwareAnnahmenHw O E.Q → TorOK output.image.Y O → ImageGateAnswers output.image.Y O →
        ImageFutexAnswers → SichtOK O →
        ∀ (memory : imageTSO.St), LoadedIRImage output memory →
        output.IRFunctionSemantics memory.1.m ∧ ∃ refinement : ImageIRRefinement output E O memory,
          (∀ finish events count, ProcessPrefix imageTSO actI (output.irEntry memory) events count finish →
            ∃ state, refinement.related events finish state ∧
              ImageReach output E O (imageSourceStart E) state ∧ ImageGoalAt output E O state) ∧
          (∀ events ending count, Tr imageTSO actI (output.irEntry memory) events ending count →
            ending ≠ .fault ∧ ending ≠ .unk ∧
            (ending ≠ .lauf → ∃ earlier last state, events = earlier ++ last ∧
              ImageReach output E O (imageSourceStart E) state ∧
              ImageStopMatches output O state earlier last ending ∧ ImageGoalAt output E O state))

/-- The production checker and canonical AST discharge the source side.
    A segment proof over the Lean IR supplies the execution side for the
    same model unit and initialized image. -/
theorem stage0_correct_of_ir_refinement
    (refineIR : ∀ (source : String) (reserve : Nat) (options : Profil.Options)
      (output : Emitted source reserve options), emit source reserve options = .ok output →
      let E := output.checkedUnit.unit
      ∀ (O : Orakel (declOf output.compiled.unit)),
        CallSitePflicht E → ForeignVertrag E O →
        HardwareAnnahmenHw O E.Q → TorOK output.image.Y O → ImageGateAnswers output.image.Y O →
        ImageFutexAnswers → SichtOK O →
        ∀ (memory : imageTSO.St), LoadedIRImage output memory →
          Nonempty (ImageIRRefinement output E O memory)) :
    Stage0Correct := by
  intro source reserve options bytes wrote
  obtain ⟨output, emitted, payload, canonical, model, accepted, posts, duties⟩ := irBild_checkImageUnit wrote
  let E := output.checkedUnit.unit
  refine ⟨output, E, emitted, payload, canonical, model, accepted, ?_⟩
  intro oracle calls foreign hardware gates answers futex visibility memory loaded
  obtain ⟨refinement⟩ := refineIR source reserve options output emitted oracle calls foreign hardware gates
    answers futex visibility memory loaded
  have goal {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
      (reached : ImageReach output E oracle (imageSourceStart E) state) : ImageGoalAt output E oracle state :=
    gabbro_ziel akzeptiertX_pruefer _ E output.fsA output.lsA output.csA accepted duties calls posts oracle
      foreign hardware output.image.passes _ _ (laufzeit_initRuhe E) _ _ reached
  refine ⟨loaded.function_semantics, refinement, ?_, ?_⟩
  · intro finish events count run
    obtain ⟨state, matched, reached⟩ := refinement.follow run refinement.initial
    exact ⟨state, matched, reached, goal reached⟩
  · intro events ending count run
    have stops (stopped : ending ≠ .lauf) := refinement.terminal run stopped
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := stops (by decide)
      cases impossible
    · rintro rfl
      obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := stops (by decide)
      cases impossible
    · intro stopped
      obtain ⟨earlier, last, state, trace, reached, matched⟩ := stops stopped
      exact ⟨earlier, last, state, trace, reached, matched, goal reached⟩

end Gabbro.Stage0
