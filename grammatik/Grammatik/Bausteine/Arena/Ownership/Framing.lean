import Grammatik.Bausteine.Arena.Ownership.Effects

namespace Gabbro.Grammatik.ArenaOwnership

/-- A completed activation preserves every grant initially owned by a
different activation, including its suspended loans. Payload framing is
handled by G's existing carrier/field theorems. -/
def State.framed (before after : State) (frame : Frame) : Prop :=
  ∀ i cell, before.cells i = some cell → cell.owner ≠ frame → after.cells i = some cell

theorem State.framed_refl (s : State) (frame : Frame) : s.framed s frame :=
  fun _ _ hc _ => hc

theorem State.framed_trans {a b c : State} {frame : Frame}
    (hab : a.framed b frame) (hbc : b.framed c frame) : a.framed c frame :=
  fun i cell hc hf => hbc i cell (hab i cell hc hf) hf

theorem State.owned_cell {s : State} {frame : Frame} {h : Handle} {cell : Cell}
    (ho : s.owns frame h) (hc : s.cells h.slot = some cell) :
    cell.matches h ∧ cell.owner = frame ∧ cell.loans = [] := by
  simpa only [State.owns, hc] using ho

theorem State.allocate_framed {s s' : State} {frame : Frame} {i : Int} {h : Handle}
    (ha : s.allocate frame i = some (s', h)) : s.framed s' frame := by
  intro j cell hc _
  have hn : j ≠ i := by
    intro he
    rw [he, State.allocate_empty ha] at hc
    cases hc
  rw [State.allocate_other ha j hn]
  exact hc

theorem State.release_framed {s s' : State} {frame : Frame} {h : Handle}
    (ha : s.release frame h = some s') : s.framed s' frame := by
  intro j cell hc hf
  have ho := State.release_requires_owner ha
  have hn : j ≠ h.slot := by
    intro he
    subst j
    exact hf (State.owned_cell ho hc).2.1
  rw [State.release_other ha j hn]
  exact hc

theorem State.move_framed {s s' : State} {frame other : Frame} {h k : Handle}
    (ha : s.move frame other h = some (s', k)) : s.framed s' frame := by
  have ho : s.owns frame h := by
    unfold State.move at ha
    split at ha
    · exact (by assumption : s.owns frame h ∧ frame.thread = other.thread).1
    · cases ha
  intro j cell hc hf
  have hn : j ≠ h.slot := by
    intro he
    subst j
    exact hf (State.owned_cell ho hc).2.1
  rw [State.move_other ha j hn]
  exact hc

#print axioms State.allocate_framed
#print axioms State.release_framed
#print axioms State.move_framed

end Gabbro.Grammatik.ArenaOwnership
