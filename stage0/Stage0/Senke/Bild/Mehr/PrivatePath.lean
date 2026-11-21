module

public import Stage0.Senke.Bild.Mehr.SCSchritt
public import Stage0.Senke.Bild.Mehr.Schritt
public import Stage0.Senke.Bild.Mehr.StoreBuffer

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach Gabbro.Grammatik

/-- A memory-only SC path with private requests preserves the image relation
    and its thread footprints. Every prefix has the same committed G state. -/
theorem sc_private_runs_refine {D : Deklaration} [Runner.IR.Kern] {hardwareLayout : Runner.Beweis.Lay}
    {c0 c : Cfg (SC hardwareLayout) (Res T)}
    {P : Programm D} {O : Orakel D} {passes : Nat} {layout : Senke.Lay D}
    {K : FadenMaschine D} {initial : Nat → Option Solo} {positions : Nat → MLage D}
    {committed : Mem}
    (relation : MTRel P O passes layout ⟨c0.ms.1, c0.ths⟩ K initial positions committed)
    (blind : AlleBlind c0.ths)
    (access : ∀ {before after i}, SCErreichbar hardwareLayout c0 before →
      SCSchritt hardwareLayout i before after → ∀ {s o k},
      initial i = some s → before.ths[i]? = some (some (.ask o k)) →
      (∀ y, fussOp o y → s.F y) ∧ (schreibtOp o = true → ∀ y, fussOp o y → s.Wr y))
    (reached : SCErreichbar hardwareLayout c0 c) :
    ∃ snapshots, MTRel P O passes layout ⟨c.ms.1, c.ths⟩ K snapshots positions committed ∧
      AlleBlind c.ths ∧ ∀ i s, snapshots i = some s →
        ∃ original, initial i = some original ∧ s.F = original.F ∧ s.Wr = original.Wr := by
  induction reached with
  | start => exact ⟨initial, relation, blind, fun _ s found => ⟨s, found, rfl, rfl⟩⟩
  | @schritt before after i reachedBefore step ih =>
    obtain ⟨snapshots, beforeRelation, beforeBlind, sameSets⟩ := ih
    have live : ∃ result, before.ths[i]? = some (some result) := by
      cases step with
      | priv found => exact ⟨_, found⟩
      | ask found _ _ => exact ⟨_, found⟩
    obtain ⟨result, live⟩ := live
    obtain ⟨s, found⟩ := beforeRelation.lebend i result live
    have privateRequest : ImFuss s := by
      intro o k request
      obtain ⟨original, originalFound, footprint, writes⟩ := sameSets i s found
      have pending := beforeRelation.zustand i s found
      rw [request] at pending
      simpa only [footprint, writes] using access reachedBefore step originalFound pending
    obtain ⟨next, footprint, writes, afterRelation⟩ :=
      mtRel_schritt beforeRelation found privateRequest (sc_mSchritt step (beforeBlind i))
    refine ⟨setzeS snapshots i next, afterRelation, alleBlind_schritt step beforeBlind, ?_⟩
    intro j s' updated
    obtain ⟨beforeSnapshot, beforeFound, sameFootprint, sameWrites⟩ :=
      setzeS_fuss found footprint writes updated
    obtain ⟨original, originalFound, oldFootprint, oldWrites⟩ := sameSets j beforeSnapshot beforeFound
    exact ⟨original, originalFound, sameFootprint.trans oldFootprint, sameWrites.trans oldWrites⟩

/-- Every memory request confined to its private read and write footprints
    preserves its answer in the SC state used by the image relation. -/
theorem project_private_request {layout : Runner.Beweis.Lay} {before after : (TSO layout).St}
    {i : Nat} {request : Op} {answer : Ans}
    (memoryRequest : istSpeicherOp request = true)
    (step : (TSO layout).ans before i request answer after)
    (footprint : Nat → W → Prop)
    (within : ∀ address, fussOp request address → footprint i address)
    (exclusive : schreibtOp request = true →
      ∀ address, fussOp request address → ∀ j, footprint j address → j = i)
    (disjoint : ∀ thread store, store ∈ before.1.buf thread →
      ∀ other, other ≠ thread → ∀ address, footprint other address → ¬ fenster store.1 address) :
    (SC layout).ans (projectSCState footprint before) i request answer
      (projectSCState footprint after) := by
  cases request with
  | rd width base => exact projectSCState_read step footprint within disjoint
  | wr base value =>
    exact projectSCState_store step footprint
      (fun address member => ⟨within address member, exclusive rfl address member⟩)
  | cas base expected value =>
    exact projectSCState_cas step footprint
      (fun address member => ⟨within address member, exclusive rfl address member⟩) disjoint
  | sys _ => cases memoryRequest
  | fp _ _ _ => cases memoryRequest

/-- The pending stores of each thread are confined to its exclusive bytes. -/
def PrivateBuffers (footprint : Nat → W → Prop) (state : TSt) : Prop :=
  ∀ i store, store ∈ state.buf i → ∀ address, fenster store.1 address →
    footprint i address ∧ ∀ j, footprint j address → j = i

theorem privateBuffers_empty {footprint : Nat → W → Prop} {state : TSt}
    (empty : ∀ i, state.buf i = []) : PrivateBuffers footprint state := by
  intro i store pending
  rw [empty i] at pending
  cases pending

private theorem PrivateBuffers.disjoint {footprint : Nat → W → Prop} {state : TSt}
    (owned : PrivateBuffers footprint state) :
    ∀ i store, store ∈ state.buf i → ∀ j, j ≠ i →
      ∀ address, footprint j address → ¬ fenster store.1 address :=
  fun i store pending j different address present touched =>
    different ((owned i store pending address touched).2 j present)

private theorem privateBuffers_set {footprint : Nat → W → Prop} {state : TSt}
    (before : PrivateBuffers footprint state) (i : Nat) (stores : List (W × W))
    (owns : ∀ store, store ∈ stores → ∀ address, fenster store.1 address →
      footprint i address ∧ ∀ j, footprint j address → j = i) :
    PrivateBuffers footprint (state.setBuf i stores) := by
  intro j store pending
  by_cases same : j = i
  · subst j
    exact owns store (by simpa only [TSt.setBuf, if_pos rfl, ↓reduceIte] using pending)
  · exact before j store (by simpa only [TSt.setBuf, if_neg same] using pending)

private theorem privateBuffers_answer {layout : Runner.Beweis.Lay}
    {before after : (TSO layout).St} {i : Nat} {request : Op} {answer : Ans}
    {footprint : Nat → W → Prop} (buffers : PrivateBuffers footprint before.1)
    (memory : istSpeicherOp request = true) (step : (TSO layout).ans before i request answer after)
    (newStore : ∀ {base value}, request = .wr base value → ∀ address, fenster base address →
      footprint i address ∧ ∀ j, footprint j address → j = i) :
    PrivateBuffers footprint after.1 := by
  cases request with
  | rd _ _ => rw [step.1]; exact buffers
  | wr base value =>
    rcases step with ⟨_, _, same⟩ | ⟨_, _, enqueued⟩
    · rw [same]; exact buffers
    · rw [enqueued]
      apply privateBuffers_set buffers
      intro store pending address touched
      rcases List.mem_append.mp pending with earlier | last
      · exact buffers i store earlier address touched
      · have same : store = (base, value) := List.mem_singleton.mp last
        subst store
        exact newStore rfl address touched
  | cas _ _ _ =>
    rcases step.2 with ⟨_, _, same⟩ | ⟨_, _, _, _, updated⟩
    · rw [same]; exact buffers
    · rw [updated]; exact buffers
  | sys _ => cases memory
  | fp _ _ _ => cases memory

private theorem privateBuffers_flush {layout : Runner.Beweis.Lay}
    {before after : (TSO layout).St} {footprint : Nat → W → Prop}
    (buffers : PrivateBuffers footprint before.1) (flush : (TSO layout).tau before after) :
    PrivateBuffers footprint after.1 := by
  obtain ⟨i, base, value, tail, head, drained⟩ := flush
  rw [drained]
  apply privateBuffers_set buffers
  intro store pending
  apply buffers i store
  rw [head]
  exact List.mem_cons_of_mem _ pending

/-- The memory-only fragment of the runner's TSO process. Private reads
    stay inside their footprint and writes require exclusive ownership. -/
inductive TSOPrivateReachable (layout : Runner.Beweis.Lay) (footprint : Nat → W → Prop)
    (initial : Cfg (TSO layout) (Res T)) : Cfg (TSO layout) (Res T) → Prop
  | start : TSOPrivateReachable layout footprint initial initial
  | priv {before : Cfg (TSO layout) (Res T)} {i : Nat} {t : T} :
      TSOPrivateReachable layout footprint initial before →
      before.ths[i]? = some (some (.next t)) →
      TSOPrivateReachable layout footprint initial ⟨before.ms, before.ths.set i (some (step t))⟩
  | ask {before : Cfg (TSO layout) (Res T)} {i : Nat} {request : Op}
      {resume : Ans → Res T} {answer : Ans} {state : (TSO layout).St} :
      TSOPrivateReachable layout footprint initial before →
      before.ths[i]? = some (some (.ask request resume)) →
      istSpeicherOp request = true →
      (TSO layout).ans before.ms i request answer state →
      (∀ address, fussOp request address → footprint i address) →
      (schreibtOp request = true → ∀ address, fussOp request address →
        ∀ j, footprint j address → j = i) →
      TSOPrivateReachable layout footprint initial ⟨state, before.ths.set i (some (resume answer))⟩
  | flush {before : Cfg (TSO layout) (Res T)} {state : (TSO layout).St} :
      TSOPrivateReachable layout footprint initial before →
      (TSO layout).tau before.ms state →
      TSOPrivateReachable layout footprint initial ⟨state, before.ths⟩

/-- Every prefix of a private TSO path retains exclusive pending stores
    and projects to an SC path. Draining a buffer adds no SC step. -/
theorem tso_private_projects {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    {initial final : Cfg (TSO layout) (Res T)} (buffers : PrivateBuffers footprint initial.ms.1)
    (reached : TSOPrivateReachable layout footprint initial final) :
    PrivateBuffers footprint final.ms.1 ∧
      SCErreichbar layout ⟨projectSCState footprint initial.ms, initial.ths⟩
        ⟨projectSCState footprint final.ms, final.ths⟩ := by
  induction reached with
  | start => exact ⟨buffers, .start⟩
  | priv _ ready ih =>
    exact ⟨ih.1, .schritt ih.2 (.priv ready)⟩
  | ask _ ready memory answer within exclusive ih =>
    refine ⟨privateBuffers_answer ih.1 memory answer ?_,
      .schritt ih.2 (.ask ready memory
        (project_private_request memory answer footprint within exclusive ih.1.disjoint))⟩
    rintro _ _ rfl address touched
    exact ⟨within address touched, exclusive rfl address touched⟩
  | flush _ flush ih =>
    refine ⟨privateBuffers_flush ih.1 flush, ?_⟩
    rw [projectSCState_flush flush footprint
      (fun i store pending address touched => (ih.1 i store pending address touched).1) ih.1.disjoint]
    exact ih.2

/-- A private TSO path preserves the source thread machine and its committed
    memory through the SC projection and the per-thread image relation. -/
theorem tso_private_runs_refine {D : Deklaration} [Runner.IR.Kern]
    {hardwareLayout : Runner.Beweis.Lay} {initial final : Cfg (TSO hardwareLayout) (Res T)}
    {P : Programm D} {O : Orakel D} {passes : Nat} {layout : Senke.Lay D}
    {K : FadenMaschine D} {snapshots : Nat → Option Solo} {positions : Nat → MLage D}
    {committed : Mem} {footprint : Nat → W → Prop}
    (relation : MTRel P O passes layout ⟨(projectSCState footprint initial.ms).1, initial.ths⟩
      K snapshots positions committed)
    (blind : AlleBlind initial.ths)
    (access : ∀ {before after i},
      SCErreichbar hardwareLayout ⟨projectSCState footprint initial.ms, initial.ths⟩ before →
      SCSchritt hardwareLayout i before after → ∀ {s o k},
      snapshots i = some s → before.ths[i]? = some (some (.ask o k)) →
      (∀ y, fussOp o y → s.F y) ∧ (schreibtOp o = true → ∀ y, fussOp o y → s.Wr y))
    (buffers : PrivateBuffers footprint initial.ms.1)
    (reached : TSOPrivateReachable hardwareLayout footprint initial final) :
    ∃ updated, MTRel P O passes layout ⟨(projectSCState footprint final.ms).1, final.ths⟩
      K updated positions committed ∧ AlleBlind final.ths ∧
      ∀ i s, updated i = some s →
        ∃ original, snapshots i = some original ∧ s.F = original.F ∧ s.Wr = original.Wr :=
  sc_private_runs_refine relation blind access (tso_private_projects buffers reached).2

/-- A private path is a real silent prefix of the runner's IR process.
    Prepending it preserves the observation and ending of any suffix. -/
theorem TSOPrivateReachable.prepend {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    {initial final : Cfg (TSO layout) (Res T)}
    (path : TSOPrivateReachable layout footprint initial final)
    {events : List Ev} {ending : Ende} {count : Nat}
    (suffix : Tr (TSO layout) actI final events ending count) :
    ∃ steps, Tr (TSO layout) actI initial events ending steps := by
  induction path generalizing count with
  | start => exact ⟨_, suffix⟩
  | priv _ found ih =>
    exact ih (.priv found rfl suffix)
  | @ask before i request resume answer state _ found memory responded _ _ ih =>
    have quiet : request.special = false ∧ lbl i request answer = [] := by
      cases request <;> simp only [istSpeicherOp] at memory <;>
        first | contradiction | exact ⟨rfl, rfl⟩
    obtain ⟨ordinary, silent⟩ := quiet
    have step := Tr.ask (act := actI) found rfl ordinary responded rfl suffix
    rw [silent, List.nil_append] at step
    exact ih step
  | flush _ flushed ih =>
    exact ih (.tau flushed suffix)

/-- The footprint obligation at a real running configuration. Only
    answered requests with no system-call event enter a private segment. -/
def PrivateRequestsAt {layout : Runner.Beweis.Lay} (footprint : Nat → W → Prop)
    (c : Cfg (TSO layout) (Res T)) : Prop :=
  ∀ {i : Nat} {request : Op} {resume : Ans → Res T} {response : Ans} {after : (TSO layout).St},
    c.ths[i]? = some (some (.ask request resume)) →
    request.special = false → lbl i request response = [] →
    (TSO layout).ans c.ms i request response after →
    istSpeicherOp request = true ∧
      (∀ y, fussOp request y → footprint i y) ∧
      (schreibtOp request = true → ∀ y, fussOp request y → ∀ j, footprint j y → j = i)

private theorem private_of_process_step {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    {initial before after : Cfg (TSO layout) (Res T)} {events : List Ev}
    (prior : TSOPrivateReachable layout footprint initial before)
    (checks : PrivateRequestsAt footprint before)
    (step : ProcessStep (TSO layout) actI before events after) (silent : events = []) :
    TSOPrivateReachable layout footprint initial after := by
  cases step with
  | tau flushed => exact .flush prior flushed
  | @priv i r _ ready evaluated =>
    cases r <;> cases evaluated
    exact .priv prior ready
  | @ask i r _ _ _ response _ ready evaluated ordinary answered resumed =>
    cases r with
    | next | fault | unk => cases evaluated
    | ask request resume =>
      cases evaluated
      cases resumed
      obtain ⟨memory, within, exclusive⟩ := checks ready ordinary silent answered
      exact .ask prior ready memory answered within exclusive
  | exit | cloneNo | clone => cases silent

/-- An actual silent runner path becomes a private TSO path from checks
    on requests at its reachable configurations. Endpoints, answers and
    flushes come from the process semantics. -/
theorem TSOPrivateReachable.of_process_prefix {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    {initial final : Cfg (TSO layout) (Res T)} {count : Nat}
    (path : ProcessPrefix (TSO layout) actI initial [] count final)
    (access : ∀ {c : Cfg (TSO layout) (Res T)} {n},
      ProcessPrefix (TSO layout) actI initial [] n c → PrivateRequestsAt footprint c) :
    TSOPrivateReachable layout footprint initial final := by
  have extend {before after : Cfg (TSO layout) (Res T)} {events : List Ev} {steps : Nat}
      (remaining : ProcessPrefix (TSO layout) actI before events steps after) :
      TSOPrivateReachable layout footprint initial before →
      (∃ n, ProcessPrefix (TSO layout) actI initial [] n before) →
      events = [] → TSOPrivateReachable layout footprint initial after := by
    induction remaining with
    | nil => intro prior _ _; exact prior
    | cons step _ ih =>
      intro prior seen silent
      obtain ⟨_, seen⟩ := seen
      obtain ⟨emptyStep, emptyTail⟩ := List.append_eq_nil_iff.mp silent
      have next := private_of_process_step prior (access seen) step emptyStep
      exact ih next ⟨_, seen.trans (ProcessPrefix.ofStep (emptyStep ▸ step))⟩ emptyTail
  exact extend path .start ⟨0, .nil _⟩ rfl

/-- Matching a concrete x86 path retains the actual IR endpoint. The
    request checks classify that same reachable endpoint as private. -/
theorem runner_private_endpoint {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    (fixed : Fixed (TSO layout) layout) (code : CInv layout)
    {initial : Cfg (TSO layout) (Res T)} {before after : Cfg (TSO layout) Runner.X86.X} {count : Nat}
    (related : Rel layout initial before) (path : ProcessPrefix (TSO layout) (actX layout) before [] count after)
    (access : ∀ {c : Cfg (TSO layout) (Res T)} {n},
      ProcessPrefix (TSO layout) actI initial [] n c → PrivateRequestsAt footprint c) :
    ∃ final steps, ProcessPrefix (TSO layout) actI initial [] steps final ∧
      Rel layout final after ∧ TSOPrivateReachable layout footprint initial final := by
  obtain ⟨final, steps, run, same⟩ := runner_process_prefix fixed code related path
  exact ⟨final, steps, run, same, .of_process_prefix run access⟩

/-- Requests whose answers and effects are preserved by the SC projection. -/
inductive ProjectedRequest (footprint : Nat → W → Prop) (thread : Nat) : Op → Prop where
  | owned {request : Op} : istSpeicherOp request = true →
      (∀ y, fussOp request y → footprint thread y) →
      (schreibtOp request = true → ∀ y, fussOp request y → ∀ j, footprint j y → j = thread) →
      ProjectedRequest footprint thread request
  | sharedRead {width : Nat} {address : W} :
      (∀ y, fenster address y → ∀ j, ¬ footprint j y) →
      ProjectedRequest footprint thread (.rd width address)
  | sharedCAS {address expected value : W} :
      (∀ y, fenster address y → ∀ j, ¬ footprint j y) →
      ProjectedRequest footprint thread (.cas address expected value)

private theorem ProjectedRequest.projects {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    {before after : (TSO layout).St} {i : Nat} {request : Op} {response : Ans}
    (accepted : ProjectedRequest footprint i request) (buffers : PrivateBuffers footprint before.1)
    (answered : (TSO layout).ans before i request response after) :
    PrivateBuffers footprint after.1 ∧ istSpeicherOp request = true ∧
      (SC layout).ans (projectSCState footprint before) i request response (projectSCState footprint after) := by
  cases accepted with
  | owned memory within exclusive =>
    refine ⟨privateBuffers_answer buffers memory answered ?_, memory,
      project_private_request memory answered footprint within exclusive buffers.disjoint⟩
    rintro _ _ rfl address touched
    exact ⟨within address touched, exclusive rfl address touched⟩
  | sharedRead outside =>
    refine ⟨privateBuffers_answer buffers rfl answered (by intro _ _ wrong; cases wrong), rfl, ?_⟩
    exact projectSCState_read_shared answered footprint outside
      (fun thread store pending y touched => (buffers thread store pending y touched).1)
  | sharedCAS outside =>
    exact ⟨privateBuffers_answer buffers rfl answered (by intro _ _ wrong; cases wrong), rfl,
      projectSCState_cas_shared answered footprint outside⟩

/-- Every actual silent TSO prefix with classified memory requests projects
    to SC, including shared reads and CAS between private operations. -/
theorem tso_memory_process_projects {layout : Runner.Beweis.Lay} {footprint : Nat → W → Prop}
    {initial final : Cfg (TSO layout) (Res T)} {count : Nat}
    (path : ProcessPrefix (TSO layout) actI initial [] count final)
    (buffers : PrivateBuffers footprint initial.ms.1)
    (classify : ∀ {c : Cfg (TSO layout) (Res T)} {n},
      ProcessPrefix (TSO layout) actI initial [] n c →
      ∀ {i : Nat} {op : Op} {resume : Ans → Res T} {response : Ans} {after : (TSO layout).St},
        c.ths[i]? = some (some (.ask op resume)) → op.special = false → lbl i op response = [] →
        (TSO layout).ans c.ms i op response after → ProjectedRequest footprint i op) :
    PrivateBuffers footprint final.ms.1 ∧
      SCErreichbar layout ⟨projectSCState footprint initial.ms, initial.ths⟩
        ⟨projectSCState footprint final.ms, final.ths⟩ := by
  let projected (c : Cfg (TSO layout) (Res T)) : Cfg (SC layout) (Res T) :=
    ⟨projectSCState footprint c.ms, c.ths⟩
  have advance {before after : Cfg (TSO layout) (Res T)} {n : Nat}
      (seen : ProcessPrefix (TSO layout) actI initial [] n before)
      (step : ProcessStep (TSO layout) actI before [] after)
      (owned : PrivateBuffers footprint before.ms.1)
      (reached : SCErreichbar layout (projected initial) (projected before)) :
      PrivateBuffers footprint after.ms.1 ∧ SCErreichbar layout (projected initial) (projected after) := by
    generalize quiet : ([] : List Ev) = labels at step
    cases step with
    | tau flushed =>
      refine ⟨privateBuffers_flush owned flushed, ?_⟩
      change SCErreichbar layout (projected initial) ⟨projectSCState footprint _, _⟩
      rw [projectSCState_flush flushed footprint
        (fun i store pending y touched => (owned i store pending y touched).1) owned.disjoint]
      exact reached
    | @priv i r _ ready evaluated =>
      cases r <;> cases evaluated
      exact ⟨owned, .schritt reached (.priv ready)⟩
    | @ask i r _ _ _ response _ ready evaluated ordinary answered resumed =>
      cases r with
      | next | fault | unk => cases evaluated
      | ask request resume =>
        cases evaluated
        cases resumed
        obtain ⟨stillOwned, memory, scAnswer⟩ :=
          (classify seen ready ordinary quiet.symm answered).projects owned answered
        exact ⟨stillOwned, .schritt reached (.ask ready memory scAnswer)⟩
    | exit | cloneNo | clone => cases quiet
  have extend {before after : Cfg (TSO layout) (Res T)} {events : List Ev} {steps : Nat}
      (suffix : ProcessPrefix (TSO layout) actI before events steps after) :
      (∃ n, ProcessPrefix (TSO layout) actI initial [] n before) →
      PrivateBuffers footprint before.ms.1 → SCErreichbar layout (projected initial) (projected before) →
      events = [] → PrivateBuffers footprint after.ms.1 ∧
        SCErreichbar layout (projected initial) (projected after) := by
    induction suffix with
    | nil => intro _ owned reached _; exact ⟨owned, reached⟩
    | cons step _ ih =>
      intro previous owned reached silent
      obtain ⟨_, seen⟩ := previous
      obtain ⟨emptyStep, emptyTail⟩ := List.append_eq_nil_iff.mp silent
      have quietStep : ProcessStep (TSO layout) actI _ [] _ := emptyStep ▸ step
      obtain ⟨stillOwned, scPath⟩ := advance seen quietStep owned reached
      exact ih ⟨_, seen.trans (ProcessPrefix.ofStep quietStep)⟩ stillOwned scPath emptyTail
  exact extend path ⟨0, .nil _⟩ buffers .start rfl

end Gabbro.Stage0.Senke.BildMehr
