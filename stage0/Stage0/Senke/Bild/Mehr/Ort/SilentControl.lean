module

public import Stage0.Senke.Bild.Mehr.Ort.SingleThread
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildLauf

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

/-- A counted SC reference through memory operations of the first thread. -/
inductive SCMemoryPrefix (layout : Runner.Beweis.Lay) :
    Cfg (SC layout) (Res T) → Nat → Cfg (SC layout) (Res T) → Prop where
  | nil (state) : SCMemoryPrefix layout state 0 state
  | cons {before middle after count} :
      SCSchritt layout 0 before middle → SCMemoryPrefix layout middle count after →
      SCMemoryPrefix layout before (count + 1) after

private theorem SCSchritt.slots {layout : Runner.Beweis.Lay} {i : Nat}
    {before after : Cfg (SC layout) (Res T)} (step : SCSchritt layout i before after) :
    after.ths.length = before.ths.length := by
  cases step <;> exact List.length_set

/-- Every silent one-thread execution that stays within the length of
    a memory reference is a prefix of that same reference. The endpoint
    and its remaining memory operations are fixed by the executable
    instruction tree, regardless of the unused read answer word. -/
theorem SCMemoryPrefix.consume {layout : Runner.Beweis.Lay}
    {before expected after : Cfg (SC layout) (Res T)} {taken available : Nat}
    (reference : SCMemoryPrefix layout before available expected)
    (actual : ProcessPrefix (SC layout) actI before [] taken after)
    (one : before.ths.length = 1) (blind : AlleBlind before.ths)
    (within : taken ≤ available) :
    SCMemoryPrefix layout after (available - taken) expected := by
  suffices consume : ∀ {before after : Cfg (SC layout) (Res T)} {events taken},
      ProcessPrefix (SC layout) actI before events taken after →
      events = [] → before.ths.length = 1 → AlleBlind before.ths →
      ∀ {expected available}, SCMemoryPrefix layout before available expected → taken ≤ available →
        SCMemoryPrefix layout after (available - taken) expected from
    consume actual rfl one blind reference within
  intro initial final events taken run
  induction run with
  | nil =>
    intro _ _ _ target available reference _
    simpa only [Nat.sub_zero] using reference
  | cons step _ ih =>
    intro quiet one blind target available reference within
    cases reference with
    | nil => omega
    | cons head tail =>
      obtain ⟨first, remaining⟩ := List.append_eq_nil_iff.mp quiet
      have same := sc_memory_step_exact one blind head step first
      cases same
      have room : _ ≤ _ := Nat.le_of_succ_le_succ within
      simpa only [Nat.succ_sub_succ_eq_sub] using
        ih remaining (head.slots.trans one) (alleBlind_schritt head blind) tail room

theorem SCMemoryPrefix.trans {layout : Runner.Beweis.Lay}
    {before middle after : Cfg (SC layout) (Res T)} {first second : Nat}
    (a : SCMemoryPrefix layout before first middle)
    (b : SCMemoryPrefix layout middle second after) :
    SCMemoryPrefix layout before (second + first) after := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step ih

/-- The sequential correctness proof supplies a memory reference for
    the SC runner, one decoded request at a time. -/
theorem RunM.sc_reference {layout : Runner.Beweis.Lay}
    {control : Res T} {before after : Mem} {next : T}
    (ran : RunM control before next after) (table : TabInv layout before)
    (blind : Blind control) :
    ∃ count (final : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some control]⟩ count ⟨⟨after, final⟩, [some (.next next)]⟩ := by
  induction ran with
  | next => exact ⟨0, table, .nil _⟩
  | @ask request resume before middle after reply next answered _ ih =>
    have kind : istSpeicherOp request = true := by
      cases request <;> first | rfl | cases answered
    have widths (n : Nat) (address : W) (read : request = .rd n address) :
        n = 1 ∨ n = 4 ∨ n = 8 := (blind.lesen read).1
    obtain ⟨preserved, answer⟩ := memAns_sc (L := layout) (i := 0) widths answered
    obtain ⟨count, final, reference⟩ := ih preserved (blind.weiter reply)
    have first : SCSchritt layout 0 ⟨⟨before, table⟩, [some (.ask request resume)]⟩
        ⟨⟨middle, preserved⟩, [some (resume reply)]⟩ := .ask rfl kind answer
    exact ⟨count + 1, final, .cons first reference⟩

/-- A sequence of whole proved memory instructions gives the counted
    reference used to cover all actual one-thread silent prefixes. -/
theorem StarM.sc_reference {layout : Runner.Beweis.Lay}
    {initial final : T} {before after : Mem} {instructions : Nat}
    (ran : StarM instructions initial before final after) (table : TabInv layout before) :
    ∃ count (preserved : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some (.next initial)]⟩ count
        ⟨⟨after, preserved⟩, [some (.next final)]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | next instruction _ ih =>
    obtain ⟨first, middleTable, requests⟩ := RunM.sc_reference instruction table (blind_step _)
    obtain ⟨rest, finalTable, tail⟩ := ih middleTable
    exact ⟨rest + first + 1, finalTable, .cons (.priv rfl) (requests.trans tail)⟩

end Gabbro.Stage0.Senke.BildMehr
