module

public import Stage0.Senke.Images.Correctness

@[expose] public section

namespace Gabbro.Stage0

open Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildMehr

variable [Kern]

/-- The two process models use exactly the same machine memory and
    controls. Only the permitted answers at the host boundary differ. -/
def imageToTSO {θ : Type} (machine : Cfg imageTSO θ) : Cfg (TSO L0) θ :=
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

/-- The actual host-constrained runner path projects to the SC memory
    steps used by the compiler refinement. Flushes carry no program step.
    The request classifier is the compiler-side obligation. -/
theorem image_memory_prefix_projects {footprint : Nat → W → Prop}
    {initial final : Cfg imageTSO (Res T)} {count : Nat}
    (run : ProcessPrefix imageTSO actI initial [] count final)
    (buffers : PrivateBuffers footprint initial.ms.1)
    (classify : ∀ {c : Cfg (TSO L0) (Res T)} {n},
      ProcessPrefix (TSO L0) actI (imageToTSO initial) [] n c →
      ∀ {i : Nat} {op : Op} {resume : Ans → Res T} {response : Ans} {after : (TSO L0).St},
        c.ths[i]? = some (some (.ask op resume)) → op.special = false → lbl i op response = [] →
        (TSO L0).ans c.ms i op response after → ProjectedRequest footprint i op) :
    PrivateBuffers footprint final.ms.1 ∧
      SCErreichbar L0 ⟨projectSCState footprint initial.ms, initial.ths⟩
        ⟨projectSCState footprint final.ms, final.ths⟩ :=
  tso_memory_process_projects (image_prefix_tso run) buffers classify

end Gabbro.Stage0
