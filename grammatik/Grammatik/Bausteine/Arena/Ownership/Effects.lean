import Grammatik.Bausteine.Arena.Ownership.Calls

namespace Gabbro.Grammatik.ArenaOwnership

/-- A call effect is independent of the number of internal transfers.
Only the selected allocation may change; every unrelated grant is framed. -/
def State.sameOutside (before after : State) (slot : Int) : Prop :=
  ∀ j, j ≠ slot → after.cells j = before.cells j

def State.consumed (before after : State) (h : Handle) : Prop :=
  after.cells h.slot = none ∧ before.sameOutside after h.slot ∧ before.next ≤ after.next

def State.returned (before after : State) (frame : Frame) (h k : Handle) : Prop :=
  after.owns frame k ∧ k.slot = h.slot ∧ k.allocation = h.allocation ∧
    before.sameOutside after h.slot ∧ before.next ≤ after.next

theorem State.sameOutside_refl (s : State) (i : Int) : s.sameOutside s i := fun _ _ => rfl

theorem State.sameOutside_trans {a b c : State} {i : Int}
    (hab : a.sameOutside b i) (hbc : b.sameOutside c i) : a.sameOutside c i :=
  fun j hj => (hbc j hj).trans (hab j hj)

theorem State.release_consumed {s s' : State} {f : Frame} {h : Handle}
    (he : s.release f h = some s') : s.consumed s' h := by
  unfold State.release at he
  split at he
  · cases he
    exact ⟨State.put_at _ _ _, fun j hj => State.put_other _ _ _ _ hj, Nat.le_refl _⟩
  · cases he

theorem State.consumed_no_access {s s' : State} {h : Handle}
    (hc : s.consumed s' h) (f : Frame) : ¬ s'.access f h := by
  simp [State.access, hc.1]

theorem State.returned_refl {s : State} {f : Frame} {h : Handle}
    (ho : s.owns f h) : s.returned s f h h :=
  ⟨ho, rfl, rfl, State.sameOutside_refl _ _, Nat.le_refl _⟩

end Gabbro.Grammatik.ArenaOwnership
