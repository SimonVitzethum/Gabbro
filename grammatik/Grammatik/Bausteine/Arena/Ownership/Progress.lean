import Grammatik.Bausteine.Arena.Ownership.Framing

namespace Gabbro.Grammatik.ArenaOwnership

/-- Historical grants are never manufactured. A final cell whose grant
predates the transition already had that exact incarnation and grant at
entry. This composes through arbitrary calls, loops, loans and reuse. -/
def State.progress (before after : State) : Prop :=
  before.next ≤ after.next ∧
    ∀ slot cell, after.cells slot = some cell → cell.grant < before.next →
      ∃ old, before.cells slot = some old ∧ cell.allocation = old.allocation ∧ cell.grant = old.grant

theorem State.progress_refl (s : State) : s.progress s :=
  ⟨Nat.le_refl _, fun _ cell hc _ => ⟨cell, hc, rfl, rfl⟩⟩

theorem State.progress_trans {a b c : State} (hab : a.progress b) (hbc : b.progress c) : a.progress c := by
  refine ⟨Nat.le_trans hab.1 hbc.1, ?_⟩
  intro slot cell hc hlt
  obtain ⟨middle, hm, ha, hg⟩ := hbc.2 slot cell hc (Nat.lt_of_lt_of_le hlt hab.1)
  obtain ⟨old, ho, hma, hmg⟩ := hab.2 slot middle hm (hg ▸ hlt)
  exact ⟨old, ho, ha.trans hma, hg.trans hmg⟩

/-- Once no frame has a grant, every later progressing state still denies
it. The statement covers arbitrary mixed executions, not just one reuse. -/
theorem State.progress_no_revival {s s' : State} (hp : s.progress s') {h : Handle}
    (hclock : h.grant < s.next) (hdead : ∀ frame, ¬ s.access frame h) :
    ∀ frame, ¬ s'.access frame h := by
  intro frame ha
  unfold State.access at ha
  cases hc : s'.cells h.slot with
  | none => simp only [hc] at ha
  | some cell =>
    rw [hc] at ha
    obtain ⟨hm, _⟩ := ha
    obtain ⟨old, ho, hall, hgrant⟩ := hp.2 h.slot cell hc (hm.2 ▸ hclock)
    apply hdead old.holder
    simp only [State.access, ho]
    exact ⟨⟨hall.symm.trans hm.1, hgrant.symm.trans hm.2⟩, trivial⟩

theorem State.allocate_progress {s s' : State} {frame : Frame} {i : Int} {h : Handle}
    (ha : s.allocate frame i = some (s', h)) : s.progress s' := by
  unfold State.allocate at ha
  split at ha
  · cases ha
  · cases ha
    refine ⟨Nat.le_succ _, ?_⟩
    intro slot cell hc hlt
    by_cases he : slot = i
    · subst slot
      simp only [State.put_at, Option.some.injEq] at hc
      subst cell
      exact False.elim (Nat.lt_irrefl _ hlt)
    · exact ⟨cell, by simpa [State.put, he] using hc, rfl, rfl⟩

theorem State.release_progress {s s' : State} {frame : Frame} {h : Handle}
    (ha : s.release frame h = some s') : s.progress s' := by
  unfold State.release at ha
  split at ha
  · cases ha
    refine ⟨Nat.le_refl _, ?_⟩
    intro slot cell hc _
    by_cases he : slot = h.slot
    · subst slot; simp only [put, ↓reduceIte, reduceCtorEq] at hc
    · exact ⟨cell, by simpa [State.put, he] using hc, rfl, rfl⟩
  · cases ha

theorem State.move_progress {s s' : State} {frame other : Frame} {h k : Handle}
    (ha : s.move frame other h = some (s', k)) : s.progress s' := by
  unfold State.move at ha
  split at ha
  · cases ha
    refine ⟨Nat.le_succ _, ?_⟩
    intro slot cell hc hlt
    by_cases he : slot = h.slot
    · subst slot
      simp only [State.put_at, Option.some.injEq] at hc
      subst cell
      exact False.elim (Nat.lt_irrefl _ hlt)
    · exact ⟨cell, by simpa [State.put, he] using hc, rfl, rfl⟩
  · cases ha

theorem State.lend_progress {s s' : State} {frame other : Frame} {h : Handle}
    (ha : s.lend frame other h = some s') : s.progress s' := by
  unfold State.lend at ha
  split at ha
  · cases ha
  · rename_i old hold
    split at ha
    · cases ha
      refine ⟨Nat.le_refl _, ?_⟩
      intro slot cell hc _
      by_cases he : slot = h.slot
      · subst slot
        simp only [State.put_at, Option.some.injEq] at hc
        subst cell
        exact ⟨old, hold, rfl, rfl⟩
      · exact ⟨cell, by simpa [State.put, he] using hc, rfl, rfl⟩
    · cases ha

theorem State.endLoan_progress {s s' : State} {frame : Frame} {h : Handle}
    (ha : s.endLoan frame h = some s') : s.progress s' := by
  unfold State.endLoan at ha
  split at ha
  · cases ha
  · rename_i old hold
    split at ha
    · cases ha
    · split at ha
      · cases ha
        refine ⟨Nat.le_refl _, ?_⟩
        intro slot cell hc _
        by_cases he : slot = h.slot
        · subst slot
          simp only [State.put_at, Option.some.injEq] at hc
          subst cell
          exact ⟨old, hold, rfl, rfl⟩
        · exact ⟨cell, by simpa [State.put, he] using hc, rfl, rfl⟩
      · cases ha

theorem State.reset_progress (s : State) : s.progress s.reset :=
  ⟨Nat.le_refl _, fun _ _ hc _ => by cases hc⟩

/-- Completed activation effects forbid both damaging another activation's
rights and leaking a newly allocated object into an untracked activation. -/
def State.local (before after : State) (frame : Frame) : Prop :=
  before.framed after frame ∧ after.framed before frame

theorem State.local_refl (s : State) (frame : Frame) : s.local s frame :=
  ⟨s.framed_refl frame, s.framed_refl frame⟩

theorem State.local_trans {a b c : State} {frame : Frame}
    (hab : a.local b frame) (hbc : b.local c frame) : a.local c frame :=
  ⟨State.framed_trans hab.1 hbc.1, State.framed_trans hbc.2 hab.2⟩

theorem State.allocate_local {s s' : State} {frame : Frame} {i : Int} {h : Handle}
    (ha : s.allocate frame i = some (s', h)) : s.local s' frame := by
  refine ⟨State.allocate_framed ha, ?_⟩
  unfold State.allocate at ha
  split at ha
  · cases ha
  · cases ha
    intro j cell hc hf
    by_cases he : j = i
    · subst j
      simp only [State.put_at, Option.some.injEq] at hc
      subst cell
      exact False.elim (hf rfl)
    · simpa [State.put, he] using hc

theorem State.release_local {s s' : State} {frame : Frame} {h : Handle}
    (ha : s.release frame h = some s') : s.local s' frame := by
  refine ⟨State.release_framed ha, ?_⟩
  intro j cell hc _
  have hn : j ≠ h.slot := by
    intro he
    rw [he, (State.release_consumed ha).1] at hc
    cases hc
  rw [← State.release_other ha j hn]
  exact hc

theorem State.reset_local {s : State} {frame : Frame} (hs : s.canReset frame) : s.local s.reset frame := by
  constructor
  · intro _ _ hc hf
    exact False.elim (hf (hs _ _ hc).1)
  · intro _ _ hc _
    cases hc

def State.closed (s : State) (frame : Frame) : Prop :=
  ∀ slot cell, s.cells slot = some cell → cell.owner ≠ frame

def State.single (s : State) (frame : Frame) (h : Handle) : Prop :=
  ∀ slot cell, s.cells slot = some cell → cell.owner = frame → slot = h.slot ∧ cell.loans = []

#print axioms State.progress_no_revival
#print axioms State.progress_trans
#print axioms State.allocate_progress
#print axioms State.release_progress
#print axioms State.move_progress
#print axioms State.lend_progress
#print axioms State.endLoan_progress

end Gabbro.Grammatik.ArenaOwnership
