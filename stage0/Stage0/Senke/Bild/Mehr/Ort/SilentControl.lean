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

private theorem SCMemoryPrefix.consume_to_boundary {layout : Runner.Beweis.Lay}
    {before expected after : Cfg (SC layout) (Res T)} {taken available : Nat}
    (reference : SCMemoryPrefix layout before available expected)
    (actual : ProcessPrefix (SC layout) actI before [] taken after)
    (one : before.ths.length = 1) (blind : AlleBlind before.ths)
    (bound : taken ≤ available ∨ ∀ next, ¬ ProcessStep (SC layout) actI expected [] next) :
    taken ≤ available ∧ SCMemoryPrefix layout after (available - taken) expected := by
  suffices consume : ∀ {before after : Cfg (SC layout) (Res T)} {events taken},
      ProcessPrefix (SC layout) actI before events taken after →
      events = [] → before.ths.length = 1 → AlleBlind before.ths →
      ∀ {expected available}, SCMemoryPrefix layout before available expected →
        (taken ≤ available ∨ ∀ next, ¬ ProcessStep (SC layout) actI expected [] next) →
        taken ≤ available ∧ SCMemoryPrefix layout after (available - taken) expected from
    consume actual rfl one blind reference bound
  intro initial final events taken run
  induction run with
  | nil =>
    intro _ _ _ target available reference _
    exact ⟨Nat.zero_le _, by simpa only [Nat.sub_zero] using reference⟩
  | cons step _ ih =>
    intro quiet one blind target available reference bound
    obtain ⟨first, remaining⟩ := List.append_eq_nil_iff.mp quiet
    cases reference with
    | nil =>
      rcases bound with within | blocked
      · omega
      · exact (blocked _ (first ▸ step)).elim
    | cons head tail =>
      have same := sc_memory_step_exact one blind head step first
      cases same
      have room := bound.imp Nat.le_of_succ_le_succ id
      obtain ⟨within, rest⟩ := ih remaining (head.slots.trans one) (alleBlind_schritt head blind) tail room
      exact ⟨Nat.succ_le_succ within, by simpa only [Nat.succ_sub_succ_eq_sub] using rest⟩

/-- A silent one-thread execution within the reference length is a
    prefix of that reference, with a uniquely determined remainder. -/
theorem SCMemoryPrefix.consume {layout : Runner.Beweis.Lay}
    {before expected after : Cfg (SC layout) (Res T)} {taken available : Nat}
    (reference : SCMemoryPrefix layout before available expected)
    (actual : ProcessPrefix (SC layout) actI before [] taken after)
    (one : before.ths.length = 1) (blind : AlleBlind before.ths)
    (within : taken ≤ available) :
    SCMemoryPrefix layout after (available - taken) expected :=
  (reference.consume_to_boundary actual one blind (.inl within)).2

private theorem sc_waiting_host_no_silent {layout : Runner.Beweis.Lay}
    {before after : Cfg (SC layout) (Res T)} {events : List Ev}
    {request : Req} {resume : Ans → Res T}
    (waiting : before.ths = [some (.ask (.sys request) resume)])
    (step : ProcessStep (SC layout) actI before events after) (quiet : events = []) : False := by
  have one : before.ths.length = 1 := by simp only [waiting, List.length_cons, List.length_nil]
  have issuer {i : Nat} {r : Res T} (ready : before.ths[i]? = some (some r)) :
      r = .ask (.sys request) resume := by
    rw [onlySlot one ready, waiting] at ready
    exact (Option.some.inj (Option.some.inj ready)).symm
  cases step with
  | tau impossible => cases impossible
  | priv ready moved =>
    have ready := issuer ready
    cases ready
    cases moved
  | ask ready asked _ _ _ =>
    have ready := issuer ready
    cases ready
    cases asked
    cases quiet
  | exit | cloneNo | clone => cases quiet

/-- A generated memory segment ends at its host request. Every silent
    one-thread execution is within the proved segment, including when
    the scheduler has already reached the host request and cannot
    advance it silently. -/
theorem SCMemoryPrefix.consume_until_host {layout : Runner.Beweis.Lay}
    {before expected after : Cfg (SC layout) (Res T)} {taken available : Nat}
    {request : Req} {resume : Ans → Res T}
    (reference : SCMemoryPrefix layout before available expected)
    (waiting : expected.ths = [some (.ask (.sys request) resume)])
    (actual : ProcessPrefix (SC layout) actI before [] taken after)
    (one : before.ths.length = 1) (blind : AlleBlind before.ths) :
    taken ≤ available ∧ SCMemoryPrefix layout after (available - taken) expected :=
  reference.consume_to_boundary actual one blind (.inr fun _ step => sc_waiting_host_no_silent waiting step rfl)

private theorem SCSchritt.no_host_request {layout : Runner.Beweis.Lay}
    {before after : Cfg (SC layout) (Res T)} {i : Nat}
    (step : SCSchritt layout i before after) {control : Res T} {request : Req}
    {resume : Ans → Res (Res T)} (position : before.ths[i]? = some (some control))
    (asks : actI control = .ask (.sys request) resume) : False := by
  cases step with
  | priv ready =>
    rw [ready] at position
    have same := (Option.some.inj (Option.some.inj position)).symm
    subst control
    cases asks
  | ask ready memory =>
    rw [ready] at position
    have same := (Option.some.inj (Option.some.inj position)).symm
    subst control
    have operation := (Res.ask.inj asks).1
    rw [operation] at memory
    cases memory

/-- An observed event from the only running slot occurs at the end of
    its memory reference. The actual observation can use any memory
    system with the same thread controls at that boundary. -/
theorem SCMemoryPrefix.at_observation {layout : Runner.Beweis.Lay} {M : MemSys}
    {start expected : Cfg (SC layout) (Res T)} {before after : Cfg M (Res T)}
    {remaining : Nat} {events : List Ev}
    (reference : SCMemoryPrefix layout start remaining expected)
    (threads : start.ths = before.ths) (one : before.ths.length = 1)
    (observed : ProcessStep M actI before events after) (visible : events ≠ []) :
    remaining = 0 ∧ start = expected := by
  cases reference with
  | nil => exact ⟨rfl, rfl⟩
  | cons first _ =>
    exfalso
    have impossible {i : Nat} {control : Res T} {request : Req} {resume : Ans → Res (Res T)}
        (ready : before.ths[i]? = some (some control))
        (asks : actI control = .ask (.sys request) resume) : False := by
      have index := onlySlot one ready
      subst i
      exact first.no_host_request (threads.symm ▸ ready) asks
    cases observed with
    | tau | priv => exact visible rfl
    | @ask _ _ _ operation _ _ _ ready asked _ _ _ =>
      cases operation with
      | rd | wr | cas | fp => exact visible rfl
      | sys => exact impossible ready asked
    | exit ready asked _ | cloneNo ready asked _ _ _ | clone ready asked _ _ _ _ =>
      exact impossible ready asked

private theorem actI_ask_no_terminal {control : Res T}
    {request : Op} {resume : Ans → Res (Res T)} {reply : Ans} {ending : Ende}
    (asked : actI control = .ask request resume) (stopped : Res.ende (resume reply) = some ending) : False := by
  cases control with
  | next | fault | unk => cases asked
  | ask _ _ =>
    change Res.ask _ _ = Res.ask request resume at asked
    obtain ⟨_, rfl⟩ := Res.ask.inj asked
    cases stopped

private theorem sc_memory_step_continues {layout : Runner.Beweis.Lay}
    {before expected : Cfg (SC layout) (Res T)} {ending : Ende} {events : List Ev}
    (reference : SCSchritt layout 0 before expected) (one : before.ths.length = 1)
    (actual : Tr (SC layout) actI before events ending 1) (quiet : events = []) :
    ending = .lauf := by
  cases actual with
  | tau invalid _ => cases invalid
  | priv _ _ tail | ask _ _ _ _ _ tail => cases tail; rfl
  | stop found stopped =>
    have issuer := onlySlot one found
    subst issuer
    cases reference with
    | priv ready =>
      rw [ready] at found
      cases found
      cases stopped
    | ask ready _ _ =>
      rw [ready] at found
      cases found
      cases stopped
  | askStop _ asked _ _ stopped => exact (actI_ask_no_terminal asked stopped).elim
  | exit | exitGroup | cloneNo | cloneNoStop | clone => cases quiet

/-- An actual silent SC run cannot stop while its certified memory
    reference has a next step. This excludes both machine faults and
    unknown instructions before the reference boundary. -/
theorem SCMemoryPrefix.no_terminal {layout : Runner.Beweis.Lay}
    {before expected : Cfg (SC layout) (Res T)} {available taken : Nat} {ending : Ende}
    (reference : SCMemoryPrefix layout before available expected)
    (actual : Tr (SC layout) actI before [] ending taken)
    (one : before.ths.length = 1) (blind : AlleBlind before.ths)
    (within : taken ≤ available) : ending = .lauf := by
  by_contra stopped
  obtain ⟨boundary, earlier, last, steps, takenPath, terminal, events, rfl⟩ := actual.split_stop stopped
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp events.symm
  have remaining := reference.consume takenPath one blind (by omega)
  have active : 0 < available - steps := by omega
  generalize available - steps = count at active remaining
  cases count with
  | zero => omega
  | succ count =>
    cases remaining with
    | cons next _ =>
      exact stopped (sc_memory_step_continues next (takenPath.silent_slots rfl |>.trans one) terminal rfl)

theorem SCMemoryPrefix.trans {layout : Runner.Beweis.Lay}
    {before middle after : Cfg (SC layout) (Res T)} {first second : Nat}
    (a : SCMemoryPrefix layout before first middle)
    (b : SCMemoryPrefix layout middle second after) :
    SCMemoryPrefix layout before (second + first) after := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

/-- A memory-only execution of an instruction tree supplies the SC
    reference up to its residual control, including pending host calls. -/
theorem RunP.sc_reference {layout : Runner.Beweis.Lay}
    {control residual : Res T} {before after : Mem}
    (ran : RunP control before residual after) (table : TabInv layout before)
    (blind : Blind control) :
    ∃ (count : Nat) (final : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some control]⟩ count ⟨⟨after, final⟩, [some residual]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | @ask request resume before middle after reply residual answered _ ih =>
    have kind : istSpeicherOp request = true := by
      cases request <;> first | rfl | cases answered
    have widths (n : Nat) (address : W) (read : request = .rd n address) :
        n = 1 ∨ n = 4 ∨ n = 8 := (blind.lesen read).1
    obtain ⟨preserved, answer⟩ := memAns_sc (L := layout) (s := ⟨before, table⟩) (i := 0) widths answered
    obtain ⟨count, final, reference⟩ := ih preserved (blind.weiter reply)
    have first : SCSchritt layout 0 ⟨⟨before, table⟩, [some (.ask request resume)]⟩
        ⟨⟨middle, preserved⟩, [some (resume reply)]⟩ := .ask rfl kind answer
    exact ⟨count + 1, final, .cons first reference⟩

private theorem RunM.partial {control : Res T} {before after : Mem} {next : T}
    (ran : RunM control before next after) : RunP control before (.next next) after := by
  induction ran with
  | next => exact .refl _ _
  | ask answered _ ih => exact .ask answered ih

/-- A sequence of whole proved memory instructions gives the counted
    reference used to cover all actual one-thread silent prefixes. -/
theorem StarM.sc_reference {layout : Runner.Beweis.Lay}
    {initial final : T} {before after : Mem} {instructions : Nat}
    (ran : StarM instructions initial before final after) (table : TabInv layout before) :
    ∃ (count : Nat) (preserved : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some (.next initial)]⟩ count
        ⟨⟨after, preserved⟩, [some (.next final)]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | next instruction _ ih =>
    obtain ⟨first, middleTable, requests⟩ := RunP.sc_reference (RunM.partial instruction) table (blind_step _)
    obtain ⟨rest, finalTable, tail⟩ := ih middleTable
    exact ⟨rest + first + 1, finalTable, .cons (.priv rfl) (requests.trans tail)⟩

/-- Before issuing a syscall or creating another thread, a terminal IR
    observation is the same terminal control in its SC projection. -/
private theorem image_silent_terminal_sc [Kern]
    {before : Cfg imageTSO (Res T)} {events : List Ev} {ending : Ende}
    (terminal : Tr imageTSO actI before events ending 1) (quiet : events = []) (stop : ending ≠ .lauf) :
    Tr (SC L0) actI (singleThreadSC (imageToTSO before)) [] ending 1 := by
  cases terminal with
  | tau _ rest | priv _ _ rest | ask _ _ _ _ _ rest =>
    cases rest
    exact (stop rfl).elim
  | stop found finished => exact .stop found finished
  | askStop _ asked _ _ finished => exact (actI_ask_no_terminal asked finished).elim
  | exit | exitGroup | cloneNo | cloneNoStop | clone => cases quiet

/-- Every terminal observation in a silent one-thread IR execution
    projects to a terminal SC observation of the same kind. Private
    TSO buffer drains can only shorten the projected execution. -/
theorem image_silent_trace_sc [Kern] {before : Cfg imageTSO (Res T)}
    {ending : Ende} {count : Nat}
    (run : Tr imageTSO actI before [] ending count) (stop : ending ≠ .lauf)
    (one : before.ths.length = 1) (buffers : PrivateBuffers singleThreadFootprint before.ms.1) :
    ∃ steps, steps ≤ count ∧ Tr (SC L0) actI (singleThreadSC (imageToTSO before)) [] ending steps := by
  obtain ⟨middle, earlier, last, steps, taken, terminal, labels, rfl⟩ := run.split_stop stop
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp labels.symm
  obtain ⟨_, count, bound, projected⟩ := tso_silent_single_thread (image_prefix_tso taken) rfl one buffers
  exact ⟨1 + count, by omega, projected.prepend (image_silent_terminal_sc terminal rfl stop)⟩

end Gabbro.Stage0.Senke.BildMehr

namespace Gabbro.Stage0

open Runner Runner.IR Runner.Beweis Runner.Mach Senke.BildMehr

/-- Before exhausting a certified memory reference, the mapped native
    image cannot stop in a silent one-thread run. The bound measures
    normalized IR transitions, rather than physical x86 microsteps. -/
theorem MappedImage.no_early_silent_terminal [Kern] {src : String} {reserve : Nat}
    {options : Profil.Options} {output : Emitted src reserve options}
    {start : Cfg imageTSO X86.X} (mapped : MappedImage output start)
    {expected : Cfg (SC L0) (Res T)} {available count : Nat} {ending : Ende}
    (reference : SCMemoryPrefix L0
      (singleThreadSC (imageToTSO (⟨start.ms, [some t4]⟩ : Cfg imageTSO (Res T)))) available expected)
    (run : Tr imageTSO (actX L0) start [] ending count)
    (within : ∀ steps, Tr imageTSO actI ⟨start.ms, [some t4]⟩ [] ending steps → steps ≤ available) :
    ending = .lauf := by
  by_contra stopped
  obtain ⟨_, count, ir⟩ := runner_mt imageTSO_fixed cinv_L0 _ mapped.loader run
  obtain ⟨steps, bound, sc⟩ := image_silent_trace_sc ir stopped rfl (privateBuffers_empty mapped.emptyBuffers)
  have blind : AlleBlind [some t4] := by
    intro thread control found
    have first := onlySlot rfl found
    subst thread
    have same : control = t4 := (Option.some.inj (Option.some.inj found)).symm
    subst control
    exact blind_rd64 _ (fun _ => .next _)
  exact stopped (reference.no_terminal sc rfl blind (bound.trans (within count ir)))

end Gabbro.Stage0
