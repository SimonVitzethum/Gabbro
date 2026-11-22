module

public import Stage0.Senke.Bild.Ruf.PrologueCode
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Senke Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options} [Kern]
  {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
  {O : Orakel (declOf output.compiled.unit)} {memory : imageTSO.St}

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
      ImageRuntimeMatches output E O history ir state (ImagePendingRoot output E history state)
  segment : ∀ {history before state events after}, related history before state →
    ImageIRSegment before events after →
    ∃ next, related (history ++ events) after next ∧ ImageReach output E O state next ∧
      (events = [] → imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents state.m.lauf) ∧
      ∀ event ∈ events, ImageObservation output E O state next after event
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

/-- Silent IR stretches preserve the allocation and retirement of slots.
    An advancing GX segment keeps the retirement evidence for every
    source head it leaves in place. -/
theorem ImageSlotsMatch.follow_silent {history : List Ev}
    {before after : Cfg imageTSO (Res T)} {count : Nat}
    {state next : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (slots : ImageSlotsMatch output E O history before state)
    (execution : ProcessPrefix imageTSO actI before [] count after)
    (advanced : ImageReach output E O state next) (live : next.lebt = state.lebt)
    (heads : ∀ thread, before.ths[thread]? = some none → next.m.faeden thread = state.m.faeden thread) :
    ImageSlotsMatch output E O history after next := by
  have retired_unchanged (thread : Nat) : after.ths[thread]? = some none → before.ths[thread]? = some none := by
    have setPreserves {slots : List (Option (Res T))} {issuer : Nat} {previous control : Res T}
        (active : slots[issuer]? = some (some previous))
        (retired : (slots.set issuer (some control))[thread]? = some none) : slots[thread]? = some none := by
      by_cases owns : thread = issuer
      · subst thread
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp active).1] at retired
        cases retired
      · rwa [List.getElem?_set_ne (Ne.symm owns)] at retired
    have noRetire {a b : Cfg imageTSO (Res T)} {events : List Ev}
        (step : ProcessStep imageTSO actI a events b) (quiet : events = [])
        (retired : b.ths[thread]? = some none) : a.ths[thread]? = some none := by
      cases step with
      | tau => exact retired
      | priv active _ | ask active _ _ _ _ => exact setPreserves active retired
      | exit | cloneNo | clone => cases quiet
    have follow {a b : Cfg imageTSO (Res T)} {events : List Ev} {steps : Nat}
        (path : ProcessPrefix imageTSO actI a events steps b) :
        events = [] → b.ths[thread]? = some none → a.ths[thread]? = some none := by
      induction path with
      | nil => exact fun _ retired => retired
      | cons step _ ih =>
        intro quiet retired
        obtain ⟨first, rest⟩ := List.append_eq_nil_iff.mp quiet
        exact noRetire step first (ih rest retired)
    exact follow execution rfl
  refine ⟨fun thread => by rw [execution.silent_slots rfl, live]; exact slots.1 thread, ?_⟩
  intro thread retired
  have beforeSlot := retired_unchanged thread retired
  rcases slots.2 thread beforeSlot with finished | ⟨atExit, req, earlier, reached, since, head, binding, number, last⟩
  · left
    unfold FertigG at finished ⊢
    rw [heads thread beforeSlot]
    exact finished
  · exact .inr ⟨atExit, req, earlier, reached, imageReach_trans since advanced,
      (heads thread beforeSlot).trans head, binding, number, last⟩

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
    obtain ⟨next, endpoint, reached, _, _⟩ := refinement.segment matched (.silent silent)
    exact ⟨next, endpoint, reached⟩
  | cons step _ tail =>
    intro anchor silentSteps previous origin silent matched
    rcases singleObservation step with quiet | ⟨event, observed⟩
    · subst_vars
      exact tail (silent.trans (.ofStep step)) matched
    · subst_vars
      obtain ⟨middle, advanced, first, _, _⟩ := refinement.segment matched (.observed silent step)
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
    ∃ output : Emitted source reserve options,
      let E := output.checkedUnit.unit
      emit source reserve options = .ok output ∧ output.bytes = bytes ∧
      CanonicalSourceProgram output.compiled ∧ ImageModelUnit output E ∧
      akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true ∧
      ∀ (O : Orakel (declOf output.compiled.unit)),
        CallSitePflicht E → ForeignVertrag E O →
        HardwareAnnahmenHw O E.Q → TorOK output.image.Y O → ImageGateAnswers output.image.Y O →
        ImageFutexAnswers → SichtOK O →
        ∀ (memory : imageTSO.St), LoadedIRImage output memory →
        output.IRFunctionSemantics memory.1.m ∧
          (∀ finish events count, ProcessPrefix imageTSO actI (output.irEntry memory) events count finish →
            ∃ state, ImageReach output E O (imageSourceStart E) state ∧
              ImageSlotsMatch output E O events finish state ∧ ImageForeignTrace output events state ∧
              ImageRuntimeMatches output E O events finish state (ImagePendingRoot output E events state) ∧
              ImageGoalAt output E O state) ∧
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
  refine ⟨output, emitted, payload, canonical, model, accepted, ?_⟩
  intro oracle calls foreign hardware gates answers futex visibility memory loaded
  obtain ⟨refinement⟩ := refineIR source reserve options output emitted oracle calls foreign hardware gates
    answers futex visibility memory loaded
  have goal {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
      (reached : ImageReach output E oracle (imageSourceStart E) state) : ImageGoalAt output E oracle state :=
    gabbro_ziel akzeptiertX_pruefer _ E output.fsA output.lsA output.csA accepted duties calls posts oracle
      foreign hardware output.image.passes _ _ (laufzeit_initRuhe E) _ _ reached
  refine ⟨loaded.function_semantics, ?_, ?_⟩
  · intro finish events count run
    obtain ⟨state, matched, reached⟩ := refinement.follow run refinement.initial
    obtain ⟨slots, observations, runtime⟩ := refinement.consistent events finish state matched
    exact ⟨state, reached, slots, observations, runtime, goal reached⟩
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
