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
    (within : ∀ address, fussOp request address → footprint i address)
    (exclusive : schreibtOp request = true →
      ∀ address, fussOp request address → ∀ j, footprint j address → j = i) :
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
        exact ⟨within address touched, exclusive rfl address touched⟩
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
  have disjoint {state : TSt} (owned : PrivateBuffers footprint state) :
      ∀ i store, store ∈ state.buf i → ∀ j, j ≠ i →
        ∀ address, footprint j address → ¬ fenster store.1 address :=
    fun i store pending j different address present touched =>
      different ((owned i store pending address touched).2 j present)
  induction reached with
  | start => exact ⟨buffers, .start⟩
  | priv _ ready ih =>
    exact ⟨ih.1, .schritt ih.2 (.priv ready)⟩
  | ask _ ready memory answer within exclusive ih =>
    exact ⟨privateBuffers_answer ih.1 memory answer within exclusive,
      .schritt ih.2 (.ask ready memory
        (project_private_request memory answer footprint within exclusive (disjoint ih.1)))⟩
  | flush _ flush ih =>
    refine ⟨privateBuffers_flush ih.1 flush, ?_⟩
    rw [projectSCState_flush flush footprint
      (fun i store pending address touched => (ih.1 i store pending address touched).1) (disjoint ih.1)]
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

end Gabbro.Stage0.Senke.BildMehr
