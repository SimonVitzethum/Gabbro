module

public import Stage0.Senke.Bild.Mehr.ImageTransition
public import Stage0.Senke.Bild.Mehr.Ort.IRStartup
public import Stage0.Senke.Bild.ImageAddress
import Stage0.Senke.Images.DispatchSource
import Stage0.Senke.Bild.Ruf.GateTrace
import Stage0.Senke.Bild.RunnerFile
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

/-- Install the entered body into its actual process slot. The relation
    keeps the other body positions and every unstarted root intact. -/
theorem ImageRuntimeMatches.register_body [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before after : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {i : Nat} {entry : MLage (declOf output.compiled.unit).mitRuhe}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (empty : body[i]? = some none) (entryOK : entry.Ok)
    (exactProgram : entry.B.P = E.P.mitRuhe ∧ entry.B.O = O.mitRuhe ∧
      entry.B.passes = output.image.passes ∧ entry.B.L = output.image.Y.withIdle)
    (thread : entry.thr = i) (alive : state.lebt i = true) (waiting : state.wartet i = [])
    (sourceHead : state.m.faeden i = entry.M.faeden i)
    (threads : after.ths = before.ths.set i (some (.next entry.start)))
    (otherViews : ∀ j, j ≠ i → after.ms.1.view j = before.ms.1.view j)
    (buffers : PrivateBuffers footprint after.ms.1) (reads writes : W → Prop)
    (inside : ∀ byte, writes byte → reads byte)
    (accessible : ∀ byte, reads byte → ∀ j, footprint j byte → j = i)
    (owned : ∀ byte, writes byte → footprint i byte)
    (atFrame : GleichAuf reads (projectSCState footprint after.ms).1 entry.mb)
    (unchanged : ∀ byte, ¬ writes byte →
      GleichAt (projectSCState footprint after.ms).1 (projectSCState footprint before.ms).1 byte) :
    ImageRuntimeMatchesAt footprint output E O history after state := by
  obtain ⟨_, length, active, roots⟩ := partition
  let program : PCfg := ⟨(projectSCState footprint before.ms).1, body⟩
  have registered : ∃ snapshots positions committed,
      MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle program state
        snapshots positions committed ∧
      ∀ j s, snapshots j = some s → (positions j).thr = j ∧ SoloFootprint footprint j s := by
    rcases active with ⟨inactive, world⟩ | active
    · refine ⟨fun _ => none, fun _ => entry, program.m, MTRel.no_registered_threads _ inactive world, ?_⟩
      intro _ _ impossible
      cases impossible
    · exact active
  obtain ⟨snapshots, positions, committed, related, indices⟩ := registered
  let added : Solo := ⟨.next entry.start, entry.mb, reads, writes⟩
  let updated := body.set i (some (.next entry.start))
  have distinct (j : Nat) (s : Solo) (found : snapshots j = some s) : j ≠ i := by
    intro same
    subst j
    have occupied := related.zustand i s found
    change body[i]? = some (some s.r) at occupied
    rw [empty] at occupied
    cases occupied
  have fresh (j : Nat) (s : Solo) (found : snapshots j = some s) : (positions j).thr ≠ entry.thr := by
    rw [(indices j s found).1, thread]
    exact distinct j s found
  have entered := related.enter_pending_root empty entryOK exactProgram (thread.symm ▸ alive)
    (thread.symm ▸ waiting) (thread.symm ▸ sourceHead) fresh reads writes
      inside atFrame unchanged
      (fun j s found byte written read => distinct j s found (((indices j s found).2.read byte read i (owned byte written)).symm))
      (fun j s found byte written read => distinct j s found (accessible byte read j ((indices j s found).2.write byte written)))
  refine ⟨updated, buffers, ?_, .inr ⟨setzeS snapshots i added, _, committed, entered, ?_⟩, ?_⟩
  · simp only [updated, threads, List.length_set, length]
  · intro j s found
    rcases setzeS_fall found with ⟨rfl, rfl⟩ | ⟨different, known⟩
    · exact ⟨by simpa only [ite_true] using thread, ⟨accessible, owned⟩⟩
    · simpa only [ite_eq_right different] using indices j s known
  · intro j
    by_cases same : j = i
    · subst j
      have bodyIndex := (List.getElem?_eq_some_iff.mp empty).1
      have runnerIndex : i < before.ths.length := length ▸ bodyIndex
      left
      rw [threads]
      exact (List.getElem?_set_self bodyIndex).trans (List.getElem?_set_self runnerIndex).symm
    · have oldBody : updated[j]? = body[j]? := List.getElem?_set_ne (Ne.symm same)
      have oldThread : after.ths[j]? = before.ths[j]? := by
        rw [threads]
        exact List.getElem?_set_ne (Ne.symm same)
      rcases roots j with equal | ⟨control, absent, running, phase⟩
      · exact Or.inl (oldBody.trans (equal.trans oldThread.symm))
      · exact Or.inr ⟨control, oldBody.trans absent, oldThread.trans running,
          by rw [otherViews j same]; exact phase⟩

/-- Agreement in one issuer's view lifts to the projected memory when
    committed memory and every other view are unchanged. -/
private theorem imageProjection_agree [Kern] {before after : imageTSO.St}
    {footprint : Nat → W → Prop} {issuer : Nat} {region : W → Prop}
    (committed : after.1.m = before.1.m)
    (otherViews : ∀ thread, thread ≠ issuer → after.1.view thread = before.1.view thread)
    (issuerView : GleichAuf region (after.1.view issuer) (before.1.view issuer)) :
    GleichAuf region (projectSCState footprint after).1 (projectSCState footprint before).1 := by
  intro address outside
  change GleichAt (viewAt after.1 footprint address) (viewAt before.1 footprint address) address
  by_cases assigned : ∃ thread, footprint thread address
  · simp only [viewAt, dif_pos assigned]
    by_cases same : Classical.choose assigned = issuer
    · rw [same]
      exact issuerView address outside
    · rw [otherViews _ same]
      exact .refl _ _
  · rw [show viewAt after.1 footprint address = after.1.m from dif_neg assigned,
      show viewAt before.1 footprint address = before.1.m from dif_neg assigned, committed]
    exact .refl _ _

/-- Register the entered body with its writable stack and the shared
    bytes below every stack reservation, including the emitted code. -/
theorem ImageRuntimeMatches.register_private_body [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before after : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {i : Nat} {entry : MLage (declOf output.compiled.unit).mitRuhe}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (placed : ∀ thread byte, footprint thread byte → imageStackFootprint output thread byte ∨
      output.image.Y.lo ≤ byte.toNat ∧ byte.toNat < output.image.Y.hi)
    (ownsStack : ∀ byte, imageStackFootprint output i byte → footprint i byte)
    (empty : body[i]? = some none) (entryOK : entry.Ok)
    (exactProgram : entry.B.P = E.P.mitRuhe ∧ entry.B.O = O.mitRuhe ∧
      entry.B.passes = output.image.passes ∧ entry.B.L = output.image.Y.withIdle)
    (thread : entry.thr = i) (alive : state.lebt i = true) (waiting : state.wartet i = [])
    (sourceHead : state.m.faeden i = entry.M.faeden i)
    (threads : after.ths = before.ths.set i (some (.next entry.start)))
    (entryMemory : entry.mb = after.ms.1.view i)
    (shared : after.ms.1.m = before.ms.1.m)
    (otherViews : ∀ j, j ≠ i → after.ms.1.view j = before.ms.1.view j)
    (issuerView : GleichAuf (fun byte => ¬ imageStackFootprint output i byte)
      (after.ms.1.view i) (before.ms.1.view i))
    (buffers : PrivateBuffers footprint after.ms.1) :
    ImageRuntimeMatchesAt footprint output E O history after state := by
  let reads : W → Prop := fun byte => imageStackFootprint output i byte ∨ byte.toNat < output.image.fp0
  have accessible (byte : W) (among : reads byte) (j : Nat) (other : footprint j byte) : j = i := by
    rcases among with own | shared
    · exact imageStackFootprint_owner placed own other
    · rcases placed j byte other with theirs | ⟨world, _⟩
      · exact ((Nat.not_le_of_lt shared) ((Nat.le_add_right _ _).trans theirs.2.1)).elim
      · exact ((Nat.not_le_of_lt shared)
          ((Nat.le_add_right _ _).trans (output.stackReservation_bounds.1.trans world))).elim
  have atReads : GleichAuf reads
      (projectSCState footprint after.ms).1 entry.mb := by
    rw [entryMemory]
    intro address inside
    exact mergedView_accessible_at after.ms.1 footprint i address
      (fun j store pending byte touches => (buffers j store pending byte touches).1) (accessible address inside)
  exact ImageRuntimeMatches.register_body partition empty entryOK exactProgram thread alive waiting
    sourceHead threads otherViews buffers reads (imageStackFootprint output i) (fun _ proof => .inl proof)
    accessible ownsStack atReads (imageProjection_agree shared otherViews issuerView)

theorem ImageRootPhase.advance_source [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {memory : Mem} {history extension : List Ev} {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {thread : Nat} {control : Res T}
    (phase : ImageRootPhase output E history memory thread control before)
    (pastLoader : thread ≠ 0 ∨ control ≠ Runner.Beweis.t4)
    (sameHead : after.m.faeden thread = before.m.faeden thread) :
    ImageRootPhase output E (history ++ extension) memory thread control after := by
  obtain ⟨entry, loader, _⟩ | ⟨root, declared, head, code, frame, fits, args, pointer, site, phase⟩ := phase
  · exact (pastLoader.elim (· entry) (· loader)).elim
  refine .inr ⟨root, declared, ?_, code, frame, fits, args, pointer, site, ?_⟩
  · let ready (frame : RufFadenG (declOf output.compiled.unit).mitRuhe) : Prop :=
      frame = (imageSourceStart E).m.faeden thread ∨
        frame.stapel = [] ∧ frame.kopf.rest.2.2.2.2.anRueck = true
    change ready (after.m.faeden thread)
    exact Eq.mp (congrArg ready sameHead.symm) head
  rcases phase with advanced | pending | ⟨id, extra, event, pending⟩
  · exact .inl advanced
  · exact .inr (.inl pending)
  · exact .inr (.inr ⟨id, extra, List.mem_append_left _ event, pending⟩)

/-- Both clone outcomes continue with the same result-store tree. The
    existing root frame and its source head are kept. -/
theorem ImageRootPhase.resume_clone [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {memory : Mem} {history : List Ev} {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {parent child : T} {id extra : W}
    (root : ImageRootPhase output E history memory 0
      (.ask (.sys cloneReq) fun answer => opt answer fun pair =>
        if pair.1 = 0 then .next child else ret1 parent pair.1) before)
    (site : ImageRootInstruction output 0 parent) (machine : after.m = before.m) :
    ImageRootPhase output E (history ++ [(0, cloneReq, some (id, extra))]) memory 0 (ret1 parent id) after := by
  obtain ⟨_, loader, _⟩ | ⟨start, selected, head, code, frame, fits, args, _⟩ := root
  · cases loader
  exact .inr ⟨start, selected, by simpa only [machine] using head, code, frame, fits, args,
    parent, site, .inr (.inr ⟨id, extra, List.mem_append_right _ List.mem_cons_self, fun _ _ => RunP.refl _ _⟩)⟩

/-- The real successful worker launch preserves the runtime partition.
    The parent stays in its startup stub until it has stored the host
    reply, and the new child's exact prepared frame enters the next slot. -/
private theorem image_worker_activation [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev} {before after : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {id extra : W} {parent child : T}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (slots : ImageSlotsMatch output E O history before state)
    (trace : ImageForeignTrace output history state) (entrySlot : body[0]? = some none)
    (waiting : before.ths[0]? = some (some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)))
    (site : ImageRootInstruction output 0 parent)
    (parentReady : state.wartet 0 = []) (declared : before.ths.length < E.starts.length)
    (prepared : ImageRootPhase output E history (before.ms.1.view before.ths.length)
      before.ths.length (.next child) state)
    (observed : ProcessStep imageTSO actI before [(0, cloneReq, some (id, extra))] after)
    (positive : 0 < id.toInt) :
    let events : List Ev := [(0, cloneReq, some (id, extra))]
    ∃ next, ImageReach output E O state next ∧ ImageSlotsMatch output E O (history ++ events) after next ∧
      ImageForeignTrace output (history ++ events) next ∧
      ImageObservation output E O state next after (0, cloneReq, some (id, extra)) ∧
      ImageRuntimePartition footprint output E O (history ++ events) after next (body ++ [none]) := by
  intro events
  obtain ⟨buffers, length, admitted, roots⟩ := partition
  obtain ⟨next, _, _, reached, slots, machine, exactAfter, attach⟩ :=
    slots.observed_clone waiting parentReady declared observed positive
  have parentInside : 0 < before.ths.length := (List.getElem?_eq_some_iff.mp waiting).1
  have spawned : before.ths.length ≠ 0 := Nat.ne_of_gt parentInside
  let threads := before.ths.set 0 (some (ret1 parent id))
  have size : threads.length = before.ths.length := List.length_set
  have root : ImageRootPhase output E history (before.ms.1.view 0) 0
      (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1) state := by
    rcases roots 0 with same | ⟨control, _, ready, phase⟩
    · rw [waiting, entrySlot] at same
      cases same
    · rw [waiting] at ready
      cases ready
      exact phase
  have afterRoot : ImageRootPhase output E (history ++ events) (before.ms.1.view 0) 0 (ret1 parent id) next :=
    root.resume_clone site machine
  have internal : imageCanBeInternal (0, cloneReq, some (id, extra)) = true := by
    simp only [imageCanBeInternal, true_or, decide_true]
  have sameHistory : imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents state.m.lauf := by
    rw [machine]
  have foreign : ImageForeignTrace output (history ++ events) next := by
    apply trace.appendInternal
    · intro event inside
      exact (List.mem_singleton.mp inside).symm ▸ internal
    · exact sameHistory
  refine ⟨next, reached, slots, foreign, .inr ⟨internal, sameHistory⟩, ?_⟩
  rw [exactAfter]
  refine ⟨buffers, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, List.length_set, length]
  · rcases admitted with ⟨empty, world⟩ | ⟨snapshots, positions, committed, related, indices⟩
    · refine .inl ⟨?_, by simpa only [machine] using world⟩
      intro i control found
      by_cases inside : i < body.length
      · rw [List.getElem?_append_left inside] at found
        exact empty i control found
      · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at found
        cases offset : i - body.length <;> rw [offset] at found <;> cases found
    · exact .inr ⟨snapshots, positions, committed, attach related, indices⟩
  · intro i
    rcases Nat.lt_trichotomy i before.ths.length with beforeSpawn | isChild | absent
    · have inBody : i < body.length := length.symm ▸ beforeSpawn
      have inThreads : i < threads.length := size.symm ▸ beforeSpawn
      rw [List.getElem?_append_left inBody]
      change _ ∨ ∃ r, _ ∧ (threads ++ [some (.next child)])[i]? = some (some r) ∧ _
      rw [List.getElem?_append_left inThreads]
      by_cases first : i = 0
      · subst i
        exact .inr ⟨ret1 parent id, entrySlot, List.getElem?_set_self parentInside, afterRoot⟩
      · have unchanged : threads[i]? = before.ths[i]? := List.getElem?_set_ne (Ne.symm first)
        rcases roots i with same | ⟨control, pending, live, phase⟩
        · exact .inl (same.trans unchanged.symm)
        · exact .inr ⟨control, pending, unchanged.trans live,
            phase.advance_source (.inl first) (congrArg (fun m => m.faeden i) machine)⟩
    · subst i
      have newBody : (body ++ [none])[before.ths.length]? = some none := by
        rw [List.getElem?_append_right length.le, length, Nat.sub_self]
        rfl
      have newSlot : (threads ++ [some (.next child)])[before.ths.length]? = some (some (.next child)) := by
        rw [List.getElem?_append_right size.le, size, Nat.sub_self]
        rfl
      exact .inr ⟨.next child, newBody, newSlot,
        prepared.advance_source (.inl spawned) (congrArg (fun m => m.faeden before.ths.length) machine)⟩
    · left
      have beyondBody : (body ++ [none]).length ≤ i := by
        simpa only [List.length_append, List.length_singleton, length, Nat.succ_eq_add_one] using
          Nat.succ_le_of_lt absent
      have beyondThreads : (threads ++ [some (Res.next child)]).length ≤ i := by
        simpa only [List.length_append, List.length_singleton, size, Nat.succ_eq_add_one] using
          Nat.succ_le_of_lt absent
      rw [List.getElem?_eq_none_iff.mpr beyondBody, List.getElem?_eq_none_iff.mpr beyondThreads]

/-- A drained compare-and-swap changes committed memory exactly as the
    atomic memory operation of Lean IR, with no buffered effect. -/
private theorem tso_cas_committed {layout : Runner.Beweis.Lay} {before after : (TSO layout).St}
    {i : Nat} {address expected replacement : W} {answer : Ans}
    (step : (TSO layout).ans before i (.cas address expected replacement) answer after) :
    IR.memAns before.1.m (.cas address expected replacement) = some (answer, after.1.m) := by
  obtain ⟨drained, observed⟩ := tso_cas_updates_view step
  have stillDrained : after.1.buf i = [] := by
    rcases step.2 with ⟨_, _, same⟩ | ⟨_, _, _, _, updated⟩
    · rw [same]
      exact drained
    · rw [updated]
      exact drained
  simpa only [TSt.view, drained, stillDrained, List.foldl_nil] using observed

private theorem future_stack_step [Kern] {src : String} {reserve future : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {before after : Cfg imageTSO (Res T)} {events : List Ev}
    (idle : ImageIdleBuffers before)
    (privateWrites : ∀ owner store, store ∈ before.ms.1.buf owner → ∀ byte,
      fenster store.1 byte → imageStackFootprint output future byte → owner = future)
    (directEffects : ∀ {thread request resume reply memory},
      before.ths[thread]? = some (some (.ask request resume)) →
      imageTSO.ans before.ms thread request reply memory →
      match request with
      | .sys _ => GleichAuf (imageStackFootprint output future) before.ms.1.m memory.1.m
      | .cas address .. => ∀ byte, imageStackFootprint output future byte → ¬ fenster address byte
      | _ => True)
    (step : ProcessStep imageTSO actI before events after) (outside : after.ths.length ≤ future) :
    GleichAuf (imageStackFootprint output future) before.ms.1.m after.ms.1.m := by
  have cloneKeeps {state : imageTSO.St} {thread : Nat} {reply : Ans}
      (answered : imageTSO.ans before.ms thread (.sys cloneReq) reply state) : state = before.ms := by
    have host := answered.2
    change (if cloneReq = cloneReq then _ else _) at host
    rw [ite_eq_left rfl] at host
    exact host.1
  cases step with
  | tau flushed =>
    obtain ⟨owner, address, value, _, queued, updated⟩ := flushed
    have pending : (address, value) ∈ before.ms.1.buf owner := by
      rw [queued]
      exact List.mem_cons_self
    have other : owner ≠ future := by
      intro equal
      subst owner
      rw [idle _ outside] at pending
      cases pending
    intro byte belongs
    have untouched : ¬ fenster address byte := fun hit =>
      other (privateWrites owner _ pending byte hit belongs)
    rw [updated]
    exact ((write_nurIn _ address value.toNat).gleichAt untouched).symm
  | priv | exit => exact fun byte _ => GleichAt.refl _ byte
  | @ask _ control _ operation _ _ _ running offered _ answered _ =>
    cases control with
    | next | fault | unk => cases offered
    | ask request resume =>
      cases offered
      cases operation with
      | sys => exact directEffects running answered
      | cas address _ _ =>
        intro byte reserved
        exact ((memAns_nurIn (tso_cas_committed answered.1)).gleichAt
          (directEffects running answered byte reserved)).symm
      | rd | fp =>
        rw [answered.1.1]
        exact fun byte _ => GleichAt.refl _ byte
      | wr =>
        rcases answered.1 with ⟨_, _, same⟩ | ⟨_, _, enqueued⟩
        · rw [same]
          exact fun byte _ => GleichAt.refl _ byte
        · rw [enqueued]
          exact fun byte _ => GleichAt.refl _ byte
  | cloneNo _ _ answered _ _ | clone _ _ answered _ _ _ =>
    rw [cloneKeeps answered]
    exact fun byte _ => GleichAt.refl _ byte

/-- A successful clone in a prefix of the actual loaded IR activates
    the declared worker occurring at this site. The unallocated stack's
    representation comes from the original serialized arguments. -/
theorem LoadedIRImage.activate_worker [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {initial : imageTSO.St} (loaded : LoadedIRImage output initial)
    (unit : ImageModelUnit output E) {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {count index : Nat} {before after : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {id extra : W}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {start : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some start)
    (order : before.ths.length = index + 1)
    (path : ProcessPrefix imageTSO actI (output.irEntry initial) history count before)
    (reached : ImageReach output E O (imageSourceStart E) state)
    (buffers : ∀ {first : Cfg imageTSO (Res T)} {earlier : List Ev} {steps : Nat},
      ProcessPrefix imageTSO actI (output.irEntry initial) earlier steps first →
      ∀ owner store, store ∈ first.ms.1.buf owner → ∀ byte,
        fenster store.1 byte → imageStackFootprint output (index + 1) byte → owner = index + 1)
    (effects : ∀ {first : Cfg imageTSO (Res T)} {earlier : List Ev} {steps : Nat},
      ProcessPrefix imageTSO actI (output.irEntry initial) earlier steps first →
      first.ths.length ≤ index + 1 →
      ∀ {thread request resume reply memory}, first.ths[thread]? = some (some (.ask request resume)) →
      imageTSO.ans first.ms thread request reply memory →
      match request with
      | .sys _ => GleichAuf (imageStackFootprint output (index + 1)) first.ms.1.m memory.1.m
      | .cas address .. => ∀ byte, imageStackFootprint output (index + 1) byte → ¬ fenster address byte
      | _ => True)
    (code : BytesAt before.ms.1.m codeBase (output.image.code.flatMap encII))
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (slots : ImageSlotsMatch output E O history before state)
    (trace : ImageForeignTrace output history state) (entrySlot : body[0]? = some none)
    (parentReady : state.wartet 0 = [])
    (observed : ProcessStep imageTSO actI before [(0, cloneReq, some (id, extra))] after)
    (positive : 0 < id.toInt) :
    let parent : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * index + 2)), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    (∃ seen resume, before.ths[0]? = some (some (.ask (.sys seen) resume)) ∧
      output.SpawnPrefix index (.ask (.sys seen) resume) (before.ms.1.view 0)) →
    let events : List Ev := [(0, cloneReq, some (id, extra))]
    ∃ next, ImageReach output E O state next ∧ ImageSlotsMatch output E O (history ++ events) after next ∧
      ImageForeignTrace output (history ++ events) next ∧
      ImageObservation output E O state next after (0, cloneReq, some (id, extra)) ∧
      ImageRuntimePartition footprint output E O (history ++ events) after next (body ++ [none]) := by
  intro parent child startup events
  have within := (List.getElem?_eq_some_iff.mp declared).1
  obtain ⟨seen, resume, running, _, _, spawnTable, spawnCode, spawnFrame, solo, _⟩ := startup
  obtain ⟨_, _, _, _, confined⟩ := output.workerReference spawnTable spawnCode spawnFrame within
  have control := (confined solo).resolve_left fun memoryOnly => (Bool.false_ne_true memoryOnly.1)
  have parentEq : (⟨BitVec.ofNat 64 (codeBase + 16 * (10 * index)) + BitVec.ofNat 64 (16 * 2),
      BitVec.ofNat 64 output.image.fp0⟩ : T) = parent := by
    dsimp only [parent]
    rw [← BitVec.ofNat_add, Nat.mul_add, Nat.add_assoc]
  rw [parentEq] at control
  rw [control] at running
  have inside : before.ths.length < E.starts.length := by
    rw [order, unit.starts, List.length_cons]
    exact Nat.succ_lt_succ within
  have parentSite : ImageRootInstruction output 0 parent := by
    refine ⟨by simp only [parent, Nat.mul_zero, Nat.add_zero], 10 * index + 2, ?_, ?_, rfl⟩
    all_goals simp only [ite_true, startLen, Nat.zero_add]; omega
  have empty : ImageIdleBuffers (output.irEntry initial) := fun i _ => loaded.emptyBuffers i
  have childPhase := loaded.future_root_phase unit path order.le
    (fun prior step bound =>
      have length := processPrefix_threadSlots (ProcessPrefix.ofStep step)
      have unused := (Nat.le_add_right _ _).trans (length ▸ bound)
      future_stack_step (empty.follow prior) (buffers prior) (effects prior unused) step bound)
    declared code slots reached
  exact image_worker_activation partition slots trace entrySlot running parentSite parentReady inside
    (by simpa only [order] using childPhase) observed positive

end Gabbro.Stage0
