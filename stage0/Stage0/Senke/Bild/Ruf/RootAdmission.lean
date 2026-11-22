module

public import Stage0.Senke.Bild.Mehr.ImageTransition

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
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem} {i : Nat} {entry : MLage (declOf output.compiled.unit).mitRuhe}
    (length : body.length = before.ths.length)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint before.ms).1, body⟩ state snapshots positions committed)
    (indices : ∀ j s, snapshots j = some s → (positions j).thr = j ∧ footprint j = s.F)
    (roots : ∀ j, body[j]? = before.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ before.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (before.ms.1.view j) j r state)
    (empty : body[i]? = some none) (entryOK : entry.Ok)
    (exactProgram : entry.B.P = E.P.mitRuhe ∧ entry.B.O = O.mitRuhe ∧
      entry.B.passes = output.image.passes ∧ entry.B.L = output.image.Y.withIdle)
    (thread : entry.thr = i) (alive : state.lebt i = true) (waiting : state.wartet i = [])
    (sourceHead : state.m.faeden i = entry.M.faeden i)
    (threads : after.ths = before.ths.set i (some (.next entry.start)))
    (otherViews : ∀ j, j ≠ i → after.ms.1.view j = before.ms.1.view j)
    (buffers : PrivateBuffers footprint after.ms.1) (writes : W → Prop)
    (inside : ∀ byte, writes byte → footprint i byte)
    (atFrame : GleichAuf (footprint i) (projectSCState footprint after.ms).1 entry.mb)
    (unchanged : ∀ byte, ¬ writes byte →
      GleichAt (projectSCState footprint after.ms).1 (projectSCState footprint before.ms).1 byte)
    (entryPrivate : ∀ j s, snapshots j = some s → ∀ byte, writes byte → ¬ s.F byte)
    (existingPrivate : ∀ j s, snapshots j = some s → ∀ byte, s.Wr byte → ¬ footprint i byte) :
    ImageRuntimeMatches output E O history after state := by
  let added : Solo := ⟨.next entry.start, entry.mb, footprint i, writes⟩
  let registered := body.set i (some (.next entry.start))
  have fresh (j : Nat) (s : Solo) (found : snapshots j = some s) : (positions j).thr ≠ entry.thr := by
    rw [(indices j s found).1, thread]
    intro same
    subst j
    have occupied := related.zustand i s found
    change body[i]? = some (some s.r) at occupied
    rw [empty] at occupied
    cases occupied
  have entered := related.enter_pending_root empty entryOK exactProgram (thread.symm ▸ alive)
    (thread.symm ▸ waiting) (thread.symm ▸ sourceHead) fresh (footprint i) writes
      inside atFrame unchanged entryPrivate existingPrivate
  refine ⟨footprint, registered, buffers, ?_, .inr ⟨setzeS snapshots i added, _, committed, entered, ?_⟩, ?_⟩
  · simp only [registered, threads, List.length_set, length]
  · intro j s found
    rcases setzeS_fall found with ⟨rfl, rfl⟩ | ⟨different, known⟩
    · exact ⟨by simpa only [ite_true] using thread, rfl⟩
    · simpa only [ite_eq_right different] using indices j s known
  · intro j
    by_cases same : j = i
    · subst j
      have bodyIndex := (List.getElem?_eq_some_iff.mp empty).1
      have runnerIndex : i < before.ths.length := length ▸ bodyIndex
      left
      rw [threads]
      exact (List.getElem?_set_self bodyIndex).trans (List.getElem?_set_self runnerIndex).symm
    · have oldBody : registered[j]? = body[j]? := List.getElem?_set_ne (Ne.symm same)
      have oldThread : after.ths[j]? = before.ths[j]? := by
        rw [threads]
        exact List.getElem?_set_ne (Ne.symm same)
      rcases roots j with equal | ⟨control, absent, running, phase⟩
      · exact Or.inl (oldBody.trans (equal.trans oldThread.symm))
      · exact Or.inr ⟨control, oldBody.trans absent, oldThread.trans running,
          by rw [otherViews j same]; exact phase⟩

/-- When only the issuer's TSO view changes, the projected image memory
    is unchanged at every address outside that issuer's footprint. -/
theorem imageProjection_agree_other [Kern] {before after : imageTSO.St}
    {footprint : Nat → W → Prop} {issuer : Nat}
    (committed : after.1.m = before.1.m)
    (otherViews : ∀ thread, thread ≠ issuer → after.1.view thread = before.1.view thread) :
    ∀ address, ¬ footprint issuer address →
      GleichAt (projectSCState footprint after).1 (projectSCState footprint before).1 address := by
  intro address outside
  change GleichAt (viewAt after.1 footprint address) (viewAt before.1 footprint address) address
  by_cases assigned : ∃ thread, footprint thread address
  · have selected := Classical.choose_spec assigned
    have different : Classical.choose assigned ≠ issuer := fun same => outside (same ▸ selected)
    rw [show viewAt after.1 footprint address = after.1.view (Classical.choose assigned) from dif_pos assigned,
      show viewAt before.1 footprint address = before.1.view (Classical.choose assigned) from dif_pos assigned,
      otherViews _ different]
    exact .refl _ _
  · rw [show viewAt after.1 footprint address = after.1.m from dif_neg assigned,
      show viewAt before.1 footprint address = before.1.m from dif_neg assigned, committed]
    exact .refl _ _

/-- Register an entered root using its actual issuing view and the fixed
    stack reservations. Disjointness and projected memory stability
    follow from the emitted layout and the real prefix's view equalities. -/
theorem ImageRuntimeMatches.register_private_body [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before after : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {body : List (Option (Res T))}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem} {i : Nat} {entry : MLage (declOf output.compiled.unit).mitRuhe}
    (length : body.length = before.ths.length)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState (imageStackFootprint output) before.ms).1, body⟩ state snapshots positions committed)
    (indices : ∀ j s, snapshots j = some s → (positions j).thr = j ∧ imageStackFootprint output j = s.F)
    (roots : ∀ j, body[j]? = before.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ before.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (before.ms.1.view j) j r state)
    (empty : body[i]? = some none) (entryOK : entry.Ok)
    (exactProgram : entry.B.P = E.P.mitRuhe ∧ entry.B.O = O.mitRuhe ∧
      entry.B.passes = output.image.passes ∧ entry.B.L = output.image.Y.withIdle)
    (thread : entry.thr = i) (alive : state.lebt i = true) (waiting : state.wartet i = [])
    (sourceHead : state.m.faeden i = entry.M.faeden i)
    (threads : after.ths = before.ths.set i (some (.next entry.start)))
    (entryMemory : entry.mb = after.ms.1.view i)
    (shared : after.ms.1.m = before.ms.1.m)
    (otherViews : ∀ j, j ≠ i → after.ms.1.view j = before.ms.1.view j)
    (buffers : PrivateBuffers (imageStackFootprint output) after.ms.1) :
    ImageRuntimeMatches output E O history after state := by
  have different (j : Nat) (s : Solo) (found : snapshots j = some s) : j ≠ i := by
    intro same
    subst j
    have located := related.zustand i s found
    change body[i]? = some (some s.r) at located
    rw [empty] at located
    cases located
  have atStack : GleichAuf (imageStackFootprint output i)
      (projectSCState (imageStackFootprint output) after.ms).1 entry.mb := by
    rw [entryMemory]
    apply tso_views_merge
    intro j store pending k distinct address inside touches
    exact distinct (imageStackFootprint_disjoint inside (buffers j store pending address touches).1)
  have outside := imageProjection_agree_other shared otherViews
  refine ImageRuntimeMatches.register_body length related indices roots empty entryOK exactProgram thread alive waiting
    sourceHead threads otherViews buffers (imageStackFootprint output i) (fun _ proof => proof) atStack outside ?_ ?_
  · intro j s found address write owns
    rw [← (indices j s found).2] at owns
    exact different j s found (imageStackFootprint_disjoint owns write)
  · intro j s found address write current
    have owner := related.mem.wrF j s found address write
    rw [← (indices j s found).2] at owner
    exact different j s found (imageStackFootprint_disjoint owner current)

end Gabbro.Stage0
