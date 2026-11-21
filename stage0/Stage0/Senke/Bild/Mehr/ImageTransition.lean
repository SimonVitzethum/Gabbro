module

public import Stage0.Senke.Images.Correctness

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildMehr

variable [Kern]

/-- The two process models use exactly the same machine memory and
    controls. Only the permitted answers at the host boundary differ. -/
def imageToTSO {θ : Type} (machine : Cfg imageTSO θ) : Cfg (TSO L0) θ :=
  ⟨machine.ms, machine.ths⟩

def tsoToImage {θ : Type} (machine : Cfg (TSO L0) θ) : Cfg imageTSO θ :=
  ⟨machine.ms, machine.ths⟩

/-- Forget the host restrictions while retaining the actual configuration,
    observation and transition. -/
theorem image_step_tso {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {events : List Ev}
    (step : ProcessStep imageTSO act before events after) :
    ProcessStep (TSO L0) act (imageToTSO before) events (imageToTSO after) := by
  cases step with
  | tau flush => exact .tau flush
  | priv ready move => exact .priv ready move
  | ask ready ask ordinary answer next => exact .ask ready ask ordinary answer.1 next
  | exit ready ask kind => exact .exit ready ask kind
  | cloneNo ready ask answer refusal next => exact .cloneNo ready ask answer.1 refusal next
  | clone ready ask answer success parent child =>
    exact .clone ready ask answer.1 success parent child

/-- The number of steps and the complete observation list survive this
    projection. -/
theorem image_prefix_tso {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {events : List Ev} {count : Nat}
    (run : ProcessPrefix imageTSO act before events count after) :
    ProcessPrefix (TSO L0) act (imageToTSO before) events count (imageToTSO after) := by
  induction run with
  | nil c => exact .nil (imageToTSO c)
  | cons step _ next => exact .cons (image_step_tso step) next

private theorem quiet_answer {before after : (TSO L0).St} {i : Nat} {op : Op} {answer : Ans}
    (quiet : lbl i op answer = []) (accepted : (TSO L0).ans before i op answer after) :
    imageTSO.ans before i op answer after := by
  cases op with
  | rd | wr | cas | fp => exact ⟨accepted, True.intro⟩
  | sys => cases quiet

/-- A silent TSO step cannot use a host answer, so the same step is
    available in the actual image model with its host restrictions. -/
theorem tso_silent_step_image {θ : Type} {act : θ → Res θ}
    {before after : Cfg (TSO L0) θ} {events : List Ev}
    (step : ProcessStep (TSO L0) act before events after) (quiet : events = []) :
    ProcessStep imageTSO act (tsoToImage before) events (tsoToImage after) := by
  cases step with
  | tau flush => exact .tau flush
  | priv ready move => exact .priv ready move
  | ask ready request ordinary answered next =>
    exact .ask ready request ordinary (quiet_answer quiet answered) next
  | exit | cloneNo | clone => cases quiet

/-- Silent prefixes retain the same endpoints in both memory models. -/
theorem tso_silent_prefix_image {θ : Type} {act : θ → Res θ}
    {before after : Cfg (TSO L0) θ} {events : List Ev} {count : Nat}
    (run : ProcessPrefix (TSO L0) act before events count after) (quiet : events = []) :
    ProcessPrefix imageTSO act (tsoToImage before) events count (tsoToImage after) := by
  induction run with
  | nil c => exact .nil (tsoToImage c)
  | cons step _ rest =>
    obtain ⟨head, tail⟩ := List.append_eq_nil_iff.mp quiet
    exact .cons (tso_silent_step_image step head) (rest tail)

/-- The actual host-constrained runner path projects to the SC memory
    steps used by the compiler refinement. Flushes carry no program step.
    The request classifier is the compiler-side obligation. -/
theorem image_memory_prefix_projects {footprint : Nat → W → Prop}
    {initial final : Cfg imageTSO (Res T)} {count : Nat}
    (run : ProcessPrefix imageTSO actI initial [] count final)
    (buffers : PrivateBuffers footprint initial.ms.1)
    (classify : ∀ {c : Cfg imageTSO (Res T)} {n},
      ProcessPrefix imageTSO actI initial [] n c →
      ∀ {i : Nat} {op : Op} {resume : Ans → Res T} {response : Ans} {after : (TSO L0).St},
        c.ths[i]? = some (some (.ask op resume)) → op.special = false → lbl i op response = [] →
        (TSO L0).ans c.ms i op response after → ProjectedRequest footprint i op) :
    PrivateBuffers footprint final.ms.1 ∧
      SCErreichbar L0 ⟨projectSCState footprint initial.ms, initial.ths⟩
        ⟨projectSCState footprint final.ms, final.ths⟩ :=
  tso_memory_process_projects (image_prefix_tso run) buffers
    (fun seen => classify (tso_silent_prefix_image seen rfl))

/-- A declared non-returning thread exit retires just its own slot.
    The source stays at the exact call head, and the exit is entered in
    the history of that thread only. -/
theorem ImageSlotsMatch.retire_never {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {i : Nat} {req : Req} {resume : Ans → Res T}
    (slots : ImageSlotsMatch output E O history before state)
    (reached : ImageReach output E O (imageSourceStart E) state)
    (ready : before.ths[i]? = some (some (.ask (.sys req) resume)))
    (number : req.nr.toNat = NR_EXIT) (matching : ImageNeverRequest output O state i req) :
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i none⟩
    ProcessStep imageTSO actI before [(i, req, none)] after ∧
      ImageSlotsMatch output E O (history ++ [(i, req, none)]) after state := by
  intro after
  refine ⟨.exit ready rfl number, ?_, ?_⟩
  · intro j
    simpa only [after, List.length_set] using slots.1 j
  · intro j retired
    by_cases same : j = i
    · subst j
      refine Or.inr ⟨state, req, history.filter (fun event => event.1 == i),
        reached, .start, rfl, matching, number, ?_⟩
      simp only [List.filter_append, List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil]
    · have unchanged : before.ths[j]? = some none := by
        simpa only [after, List.getElem?_set_ne (Ne.symm same)] using retired
      obtain finished | ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, last⟩ :=
        slots.2 j unchanged
      · exact Or.inl finished
      · refine Or.inr ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, ?_⟩
        simp only [List.filter_append, List.filter_cons, beq_eq_false_iff_ne.mpr (Ne.symm same),
          Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil, last]

end Gabbro.Stage0
