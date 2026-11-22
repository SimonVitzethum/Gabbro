module

public import Stage0.Senke.Bild.Mehr.Ort.SingleThread
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach

private theorem onlySlot {α : Type} {slots : List (Option α)} {i : Nat} {r : α}
    (one : slots.length = 1) (ready : slots[i]? = some (some r)) : i = 0 := by
  have present := (List.getElem?_eq_some_iff.mp ready).1
  omega

/-- A quiet transition in a one-thread process issues the memory
    operation selected by the reference instruction. Floating-point and
    foreign answers cannot be substituted for that memory request. -/
theorem sc_memory_step_selected {layout : Runner.Beweis.Lay} {before expected after : Cfg (SC layout) (Res T)}
    {events : List Ev} (one : before.ths.length = 1)
    (reference : SCSchritt layout 0 before expected)
    (actual : ProcessStep (SC layout) actI before events after) (quiet : events = []) :
    SCSchritt layout 0 before after := by
  cases actual with
  | tau flush => cases flush
  | @priv i r next ready moved =>
    have selected := onlySlot one ready
    subst i
    cases r <;> cases moved
    exact .priv ready
  | @ask i r next request resume response memory ready asked ordinary answered continued =>
    have selected := onlySlot one ready
    subst i
    cases r with
    | next | fault | unk => cases asked
    | ask actualRequest actualResume =>
      cases asked
      cases continued
      cases reference with
      | priv waiting =>
        rw [ready] at waiting
        cases waiting
      | ask waiting operation _ =>
        rw [ready] at waiting
        cases waiting
        exact .ask ready operation answered
  | exit | cloneNo | clone => cases quiet

/-- Read-blind generated code is deterministic at the request boundary
    even though SC allows an arbitrary second word on a read. -/
theorem SCSchritt.deterministic {layout : Runner.Beweis.Lay} {i : Nat}
    {before first second : Cfg (SC layout) (Res T)}
    (blind : AlleBlind before.ths) (left : SCSchritt layout i before first)
    (right : SCSchritt layout i before second) : first = second := by
  have same := MSchritt.deterministic (sc_mSchritt left (blind i)) (sc_mSchritt right (blind i))
  have bytes := congrArg PCfg.m same
  have threads := congrArg PCfg.ths same
  have memory : first.ms = second.ms := Subtype.ext bytes
  cases first
  cases second
  cases memory
  cases threads
  rfl

/-- At a known memory instruction every possible quiet SC transition
    reaches the same concrete endpoint as the generated instruction. -/
theorem sc_memory_step_exact {layout : Runner.Beweis.Lay} {before expected after : Cfg (SC layout) (Res T)}
    {events : List Ev} (one : before.ths.length = 1) (blind : AlleBlind before.ths)
    (reference : SCSchritt layout 0 before expected)
    (actual : ProcessStep (SC layout) actI before events after) (quiet : events = []) :
    after = expected :=
  (sc_memory_step_selected one reference actual quiet).deterministic blind reference

end Gabbro.Stage0.Senke.BildMehr
