module

public import Stage0.Senke.Images.Correctness
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options} [Kern]
  {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
  {O : Orakel (declOf output.compiled.unit)} {start : Cfg imageTSO X86.X}

/-- The remaining compiler relation is over actual IR steps and the
    declared source machine. The verified native runner projects to it. -/
structure ImageIRSimulation (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (start : Cfg imageTSO X86.X) where
  related : List Ev → Cfg imageTSO (Res T) → FadenMaschine (declOf output.compiled.unit).mitRuhe → Prop
  initial : related [] ⟨start.ms, [some t4]⟩ (imageSourceStart E)
  image : ∀ history ir state, related history ir state →
    FileInv ir.ms.1.m ∧ ImageSlotsMatch output E O history ir state ∧
    ImageForeignTrace output history state ∧ ImageRuntimeMatches output E O history ir state
  step : ∀ history before state events after, related history before state →
    ProcessStep imageTSO actI before events after →
    ∃ next, related (history ++ events) after next ∧ ImageReach output E O state next ∧
      (events = [] → imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents state.m.lauf) ∧
      ∀ event ∈ events, imageExternalEvent event = true → ImageGateEvent output E O state next after event
  stop : ∀ history before state last ending, related history before state →
    Tr imageTSO actI before last ending 1 → ending ≠ .lauf →
    ∃ next, ImageReach output E O state next ∧ ImageStopMatches output O next history last ending

theorem ImageIRSimulation.follow (sim : ImageIRSimulation output E O start)
    {history events : List Ev} {before after : Cfg imageTSO (Res T)} {count : Nat}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (run : ProcessPrefix imageTSO actI before events count after) (related : sim.related history before state) :
    ∃ next, sim.related (history ++ events) after next ∧ ImageReach output E O state next ∧
      (events = [] → imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents state.m.lauf) := by
  induction run generalizing history state with
  | nil => exact ⟨state, by simpa only [List.append_nil] using related, .start _, fun _ => rfl⟩
  | cons head _ ih =>
    obtain ⟨middle, first, advanced, stillForeign, _⟩ := sim.step _ _ _ _ _ related head
    obtain ⟨last, final, continued, finallyForeign⟩ := ih first
    refine ⟨last, by simpa only [List.append_assoc] using final, imageReach_trans advanced continued, ?_⟩
    intro quiet
    obtain ⟨firstQuiet, restQuiet⟩ := List.append_eq_nil_iff.mp quiet
    exact (finallyForeign restQuiet).trans (stillForeign firstQuiet)

private theorem ImageGateEvent.after_silent
    {before middle after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {ir : Cfg imageTSO (Res T)} {event : Ev}
    (prefix : ImageReach output E O before middle)
    (history : imageSourceForeignEvents middle.m.lauf = imageSourceForeignEvents before.m.lauf)
    (matched : ImageGateEvent output E O middle after ir event) :
    ImageGateEvent output E O before after ir event := by
  obtain ⟨site, memory, routine, world, args, first, last, live, call, extended, privateMemory, gate⟩ := matched
  exact ⟨site, memory, routine, world, args, imageReach_trans prefix first, last, live, call,
    extended.trans (congrArg (· ++ [(event.1, routine)]) history), privateMemory, gate⟩

/-- With the IR relation established, the same simulation applies to
    every native scheduler transition, including the exact endpoint and
    foreign answer. Normalization preceding an event stays silent. -/
theorem ImageIRSimulation.toRunner (sim : ImageIRSimulation output E O start)
    (mapped : MappedImage output start) : Nonempty (ImageSimulation output E O start) := by
  refine ⟨{
    related := fun history native ir state => Rel L0 ir native ∧ sim.related history ir state
    initial := ⟨mapped.loader, sim.initial⟩
    image := ?_
    step := ?_
    stop := ?_ }⟩
  · intro history native ir state matching
    refine ⟨matching.1, ?_⟩
    rw [← matching.1.ms]
    exact sim.image history ir state matching.2
  · intro history native ir state native' events matching moved
    obtain ⟨ir', steps, trace, same, silent | ⟨cut, _, prefix, last⟩⟩ :=
      runner_process_step imageTSO_fixed cinv_L0 matching.1 moved
    · subst events
      obtain ⟨next, related, reach, _⟩ := sim.follow trace matching.2
      exact ⟨ir', steps, next, trace, ⟨same, related⟩, reach, fun _ absent => False.elim (List.not_mem_nil absent)⟩
    · obtain ⟨middle, related, reached, unchanged⟩ := sim.follow prefix matching.2
      rw [List.append_nil] at related
      obtain ⟨next, final, advanced, _, observed⟩ := sim.step _ _ _ _ _ related last
      exact ⟨ir', steps, next, trace, ⟨same, final⟩, imageReach_trans reached advanced,
        fun event occurs external => (observed event occurs external).after_silent reached (unchanged rfl)⟩
  · intro history native ir state events ending matching terminal stopped
    obtain ⟨_, _, projected⟩ := runner_mt imageTSO_fixed cinv_L0 1 matching.1 terminal
    obtain ⟨boundary, earlier, last, _, prefix, tail, exactEvents, _⟩ := projected.split_stop stopped
    obtain ⟨middle, related, first, _⟩ := sim.follow prefix matching.2
    obtain ⟨next, continued, matched⟩ := sim.stop _ boundary middle last ending related tail stopped
    have lastLength : last.length = 1 := by
      obtain ⟨_, _, same, _, _, _⟩ := matched
      simp only [same, List.length_cons, List.length_nil]
    have length := terminal.events_le_steps
    rw [exactEvents, List.length_append, lastLength] at length
    have silent : earlier = [] := List.length_eq_zero_iff.mp (by omega)
    subst earlier
    simp only [List.nil_append] at exactEvents
    subst events
    simpa only [List.append_nil] using
      (show ∃ next, ImageReach output E O state next ∧ ImageStopMatches output O next (history ++ []) last ending from
        ⟨next, imageReach_trans first continued, matched⟩)

/-- After constructing the checked semantic export and the IR simulation,
    the goal theorem applies to all native runs of the emitted bytes. -/
theorem stage0_correct_of_ir_simulation
    (prepare : ∀ (source : String) (reserve : Nat) (options : Profil.Options)
        (output : Emitted source reserve options), emit source reserve options = .ok output →
        ∃ E : Einheit (declOf output.compiled.unit), ImageModelUnit output E ∧
          akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true ∧
          ∀ (O : Orakel (declOf output.compiled.unit)),
            CallSitePflicht E → ForeignVertrag E O →
            HardwareAnnahmenHw O E.Q → TorOK output.image.Y O → ImageGateAnswers output.image.Y O →
            ImageFutexAnswers → SichtOK O →
            ∀ (start : Cfg imageTSO X86.X), MappedImage output start →
              Nonempty (ImageIRSimulation output E O start)) :
    Stage0Correct := by
  apply stage0_correct_of_export_simulation
  intro source reserve options output emitted
  obtain ⟨E, model, accepted, simulate⟩ := prepare source reserve options output emitted
  refine ⟨E, model, accepted, ?_⟩
  intro O calls foreign hardware gate answers futex visibility start mapped
  obtain ⟨ir⟩ := simulate O calls foreign hardware gate answers futex visibility start mapped
  exact ir.toRunner mapped

end Gabbro.Stage0
