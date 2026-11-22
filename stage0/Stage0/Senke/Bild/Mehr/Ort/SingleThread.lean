module

public import Stage0.Senke.Bild.Mehr.ImageTransition
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach

def singleThreadFootprint (thread : Nat) (_ : W) : Prop := thread = 0

/-- For a lone thread the buffer projection is its entire current view. -/
theorem singleThreadView (state : TSt) (buffers : PrivateBuffers singleThreadFootprint state) :
    mergedView state singleThreadFootprint = state.view 0 := by
  apply mem_eq_of_agreement
  intro address
  exact tso_views_merge state singleThreadFootprint buffers.disjoint 0 address rfl

noncomputable def singleThreadSC {layout : Lay} (state : Cfg (TSO layout) θ) : Cfg (SC layout) θ :=
  ⟨projectSCState singleThreadFootprint state.ms, state.ths⟩

private theorem silent_answer_one {layout : Lay} {before after : (TSO layout).St}
    {request : Op} {response : Ans} (quiet : lbl 0 request response = [])
    (answered : (TSO layout).ans before 0 request response after)
    (buffers : PrivateBuffers singleThreadFootprint before.1) :
    PrivateBuffers singleThreadFootprint after.1 ∧
      (SC layout).ans (projectSCState singleThreadFootprint before) 0 request response
        (projectSCState singleThreadFootprint after) := by
  have memory (memoryRequest : istSpeicherOp request = true) :=
    (ProjectedRequest.owned (footprint := singleThreadFootprint) (thread := 0)
      memoryRequest (fun _ _ => rfl) (fun _ _ _ _ owner => owner)).projects buffers answered
  cases request with
  | rd | wr | cas =>
    obtain ⟨owned, _, scAnswer⟩ := memory rfl
    exact ⟨owned, scAnswer⟩
  | fp kind x y =>
    obtain ⟨rfl, unchanged⟩ := answered
    exact ⟨buffers, rfl, unchanged⟩
  | sys => cases quiet

private theorem silent_step_one {layout : Lay} {act : θ → Res θ}
    {before after : Cfg (TSO layout) θ} {events : List Ev}
    (step : ProcessStep (TSO layout) act before events after)
    (quiet : events = []) (one : before.ths.length = 1)
    (buffers : PrivateBuffers singleThreadFootprint before.ms.1) :
    PrivateBuffers singleThreadFootprint after.ms.1 ∧
      ∃ count, count ≤ 1 ∧ ProcessPrefix (SC layout) act (singleThreadSC before) [] count (singleThreadSC after) := by
  cases step with
  | tau flush =>
    refine ⟨buffers.flush flush, 0, by decide, ?_⟩
    unfold singleThreadSC
    rw [projectSCState_flush flush singleThreadFootprint
      (fun thread store pending address touched => (buffers thread store pending address touched).1) buffers.disjoint]
    exact .nil _
  | priv ready move =>
    exact ⟨buffers, 1, by decide, .ofStep (.priv ready move)⟩
  | @ask c i t t' op resume response ms ready asked ordinary answered resumed =>
    have live := List.getElem?_eq_some_iff.mp ready
    have first : i = 0 := by have lt := live.1; omega
    subst i
    obtain ⟨owned, scAnswer⟩ := silent_answer_one quiet answered buffers
    refine ⟨owned, 1, by decide, ?_⟩
    exact quiet ▸ ProcessPrefix.ofStep (.ask ready asked ordinary scAnswer resumed)
  | exit | cloneNo | clone => cases quiet

/-- Every silent prefix of a lone thread has an SC prefix with the same
    instruction and answer history up to erased buffer flushes. No
    memory footprint classifier is needed, including for floating-point
    requests. -/
theorem tso_silent_single_thread {layout : Lay} {act : θ → Res θ}
    {before after : Cfg (TSO layout) θ} {events : List Ev} {count : Nat}
    (run : ProcessPrefix (TSO layout) act before events count after)
    (quiet : events = []) (one : before.ths.length = 1)
    (buffers : PrivateBuffers singleThreadFootprint before.ms.1) :
    PrivateBuffers singleThreadFootprint after.ms.1 ∧
      ∃ steps, steps ≤ count ∧ ProcessPrefix (SC layout) act (singleThreadSC before) [] steps (singleThreadSC after) := by
  induction run with
  | nil => exact ⟨buffers, 0, Nat.le_refl _, .nil _⟩
  | cons step _ ih =>
    obtain ⟨head, tail⟩ := List.append_eq_nil_iff.mp quiet
    obtain ⟨stillOwned, n, small, first⟩ := silent_step_one step head one buffers
    have stillOne := (step.silent_slots head).trans one
    obtain ⟨finallyOwned, m, rest, last⟩ := ih tail stillOne stillOwned
    exact ⟨finallyOwned, m + n, by omega, first.trans last⟩

end Gabbro.Stage0.Senke.BildMehr

namespace Gabbro.Stage0

open Runner Runner.IR Runner.Beweis Runner.Mach Senke.BildMehr

/-- An actual silent x86 prefix from the loaded image has a sequential IR
    prefix from the same loader and initialized bytes, ending in the
    same thread state and the whole visible memory of that thread. -/
theorem MappedImage.single_thread_sc [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options}
    {start finish : Cfg imageTSO Runner.X86.X} (mapped : MappedImage output start)
    {count : Nat} (run : ProcessPrefix imageTSO (actX L0) start [] count finish) :
    ∃ ir irSteps scSteps, ProcessPrefix imageTSO actI ⟨start.ms, [some t4]⟩ [] irSteps ir ∧
      Rel L0 ir finish ∧ scSteps ≤ irSteps ∧ ir.ths.length = 1 ∧
      ProcessPrefix (SC L0) actI (singleThreadSC (imageToTSO ⟨start.ms, [some t4]⟩)) [] scSteps
        (singleThreadSC (imageToTSO ir)) ∧
      (singleThreadSC (imageToTSO ⟨start.ms, [some t4]⟩)).ms.1 = start.ms.1.m ∧
      (singleThreadSC (imageToTSO ir)).ms.1 = ir.ms.1.view 0 := by
  obtain ⟨ir, irSteps, irRun, relation⟩ := mapped.runner_prefix run
  obtain ⟨owned, scSteps, bound, scRun⟩ :=
    tso_silent_single_thread (image_prefix_tso irRun) rfl rfl (privateBuffers_empty mapped.emptyBuffers)
  exact ⟨ir, irSteps, scSteps, irRun, relation, bound, irRun.silent_slots rfl, scRun,
    mergedView_empty _ _ mapped.emptyBuffers, singleThreadView _ owned⟩

end Gabbro.Stage0
