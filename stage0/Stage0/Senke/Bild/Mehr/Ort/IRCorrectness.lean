module

public import Stage0.Senke.Images.Correctness
public import Stage0.Senke.Bild.Emitted
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
  refine ⟨_, maxTop functions, ?_, ?_, ?_⟩
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

/-- Segment refinement at the compiler boundary. A segment may contain
    an arbitrary number of internal IR steps and at most one host event.
    Its endpoint may lie inside a generated block. -/
structure ImageIRRefinement (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (memory : imageTSO.St) where
  related : List Ev → Cfg imageTSO (Res T) → FadenMaschine (declOf output.compiled.unit).mitRuhe → Prop
  initial : related [] (output.irEntry memory) (imageSourceStart E)
  consistent : ∀ history ir state, related history ir state →
    ImageSlotsMatch output E O history ir state ∧ ImageForeignTrace output history state ∧
      ImageRuntimeMatches output E O history ir state
  segment : ∀ {history before state events count after}, related history before state →
    ProcessPrefix imageTSO actI before events count after → events.length ≤ 1 →
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

/-- The same relation and GX history compose across the whole IR run. -/
theorem ImageIRRefinement.follow (refinement : ImageIRRefinement output E O memory)
    {history events : List Ev} {before after : Cfg imageTSO (Res T)} {count : Nat}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (run : ProcessPrefix imageTSO actI before events count after)
    (initial : refinement.related history before state) :
    ∃ next, refinement.related (history ++ events) after next ∧ ImageReach output E O state next := by
  induction run generalizing history state with
  | nil => exact ⟨state, by simpa only [List.append_nil] using initial, .start⟩
  | cons step _ ih =>
    obtain ⟨middle, matched, first, _⟩ :=
      refinement.segment initial (.ofStep step) (processStep_eventCount step)
    obtain ⟨next, final, reached⟩ := ih matched
    exact ⟨next, by simpa only [List.append_assoc] using final, imageReach_trans first reached⟩

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
