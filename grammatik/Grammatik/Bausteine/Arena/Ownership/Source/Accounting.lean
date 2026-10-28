import Grammatik.Bausteine.Arena.Ownership.Source.Allocation
import Grammatik.Bausteine.Arena.Ownership.Framing

namespace Gabbro.Grammatik.ArenaOwnership.Source

/-- Every object owned by the active frame has an outstanding source right.
Suspended loans belong in caller frames, never in the running frame's owned
scope. Dropping a local does not silently discard an outstanding right. -/
def Complete (c : Context) (g : Ghost) (s : State) (frame : Frame) : Prop :=
  ∀ slot cell, s.cells slot = some cell → cell.owner = frame →
    cell.loans = [] ∧ ∃ i h, c.rights i = some .owned ∧ g i = some h ∧ h.slot = slot ∧ cell.matches h

theorem Complete.handle {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hc : Complete c g s frame) {h : Handle} (ho : s.owns frame h) :
    ∃ i, c.rights i = some .owned ∧ g i = some h := by
  obtain ⟨cell, hcell⟩ := State.own_cell ho
  have hh := State.owned_cell ho hcell
  obtain ⟨_, i, k, hi, hg, hk, hm⟩ := hc h.slot cell hcell hh.2.1
  have hkown : s.owns frame k := by
    simp only [State.owns, hk, hcell]
    exact ⟨hm, hh.2⟩
  have hid := State.own_handles_equal hkown ho hk
  subst k
  exact ⟨i, hi, hg⟩

theorem Complete.bind {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hc : Complete c g s frame) (ref : Option Nat) : Complete (c.bind ref) g s frame := hc

theorem Complete.drop {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hc : Complete c g s frame) : Complete c.drop g s frame := hc

/-- Release removes its source right and its cell together. Every other
owned cell remains accounted for, including cells without a local alias. -/
theorem Complete.release {c : Context} {g : Ghost} {s s' : State} {frame : Frame} {h : Handle} {i : Nat}
    (hc : Complete c g s frame) (hg : g i = some h) (hs : s.release frame h = some s') :
    Complete (c.kill i) g s' frame := by
  intro slot cell hcell howner
  have hdead := (State.release_consumed hs).1
  have hne : slot ≠ h.slot := by
    intro he
    rw [he, hdead] at hcell
    cases hcell
  have hold : s.cells slot = some cell := by rw [← State.release_other hs slot hne]; exact hcell
  obtain ⟨hl, j, k, hj, hgk, hk, hm⟩ := hc slot cell hold howner
  have hjne : j ≠ i := by
    intro he
    subst j
    rw [hg] at hgk
    cases hgk
    exact hne hk.symm
  exact ⟨hl, j, k, by simpa [Context.kill, hjne] using hj, hgk, hk, hm⟩

/-- One rule accounts for a newly bound owning grant, whether it was
allocated locally or returned by a callee. -/
theorem Complete.bindOwning {c : Context} {g : Ghost} {s : State} {frame : Frame} {fresh : Handle}
    (hb : c.bounded) (ho : s.owns frame fresh)
    (rest : ∀ slot cell, s.cells slot = some cell → cell.owner = frame → slot ≠ fresh.slot →
      cell.loans = [] ∧ ∃ i h, c.rights i = some .owned ∧ g i = some h ∧ h.slot = slot ∧ cell.matches h) :
    Complete c.bindFresh (g.set c.next fresh) s frame := by
  intro slot cell hc hf
  by_cases hs : slot = fresh.slot
  · subst slot
    have hh := State.owned_cell ho hc
    exact ⟨hh.2.2, c.next, fresh, by simp only [Context.bindFresh, ↓reduceIte], Ghost.set_at _ _ _, rfl, hh.1⟩
  · obtain ⟨hl, i, h, hi, hg, hslot, hm⟩ := rest slot cell hc hf hs
    have hlt : i < c.next := by
      by_cases hlt : i < c.next
      · exact hlt
      · have hn := hb.1 i (Nat.le_of_not_gt hlt)
        rw [hn] at hi
        cases hi
    exact ⟨hl, i, h, by simpa [Context.bindFresh, Nat.ne_of_lt hlt] using hi,
      by simpa [Ghost.set, Nat.ne_of_lt hlt] using hg, hslot, hm⟩

theorem Complete.allocate {c : Context} {g : Ghost} {s s' : State} {frame : Frame} {slot : Int} {fresh : Handle}
    (hb : c.bounded) (hc : Complete c g s frame) (hv : s.valid)
    (hs : s.allocate frame slot = some (s', fresh)) (hslot : fresh.slot = slot) :
    Complete c.bindFresh (g.set c.next fresh) s' frame := by
  apply Complete.bindOwning hb (State.allocate_valid hv frame slot hs).2
  intro j cell hj hf hne
  have hn : j ≠ slot := hslot ▸ hne
  exact hc j cell (by rw [← State.allocate_other hs j hn]; exact hj) hf

theorem Complete.returned {c : Context} {g : Ghost} {s s' : State} {frame : Frame} {i : Nat} {h fresh : Handle}
    (hb : c.bounded) (hc : Complete c g s frame) (hg : g i = some h)
    (hs : s.returned s' frame h fresh) :
    Complete (c.kill i).bindFresh (g.set c.next fresh) s' frame := by
  apply Complete.bindOwning (Context.kill_bounded hb i) hs.1
  intro j cell hj hf hne
  have hn : j ≠ h.slot := hs.2.1 ▸ hne
  have hold : s.cells j = some cell := by rw [← hs.2.2.2.1 j hn]; exact hj
  obtain ⟨hl, k, old, hk, hgold, hslot, hm⟩ := hc j cell hold hf
  have hki : k ≠ i := by
    intro he
    subst k
    rw [hg] at hgold
    cases hgold
    exact hn hslot.symm
  exact ⟨hl, k, old, by simpa [Context.kill, hki] using hk, hgold, hslot, hm⟩

/-- Finite source return admission. An absent return origin requires every
owning right to have been consumed; an owning return may retain that origin
alone. The finite bound is maintained by the source judgment. -/
def finish (c : Context) (returned : Option Nat) : Bool :=
  (List.range c.next).all (fun i => c.rights i != some .owned || decide (returned = some i))

theorem finish_sound {c : Context} {returned : Option Nat} (hb : c.bounded)
    (hf : finish c returned = true) : ∀ i, c.rights i = some .owned → returned = some i := by
  intro i hi
  have hlt : i < c.next := by
    by_cases hlt : i < c.next
    · exact hlt
    · rw [hb.1 i (Nat.le_of_not_gt hlt)] at hi
      cases hi
  have hc := List.all_eq_true.mp hf i (List.mem_range.mpr hlt)
  simpa [hi] using hc

/-- A void/reason return with no outstanding owning right cannot leak an
owned allocation. The condition is a check on the finite source context. -/
theorem Complete.no_owned {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hc : Complete c g s frame) (hn : ∀ i, c.rights i ≠ some .owned) :
    ∀ slot cell, s.cells slot = some cell → cell.owner ≠ frame := by
  intro slot cell hcell howner
  obtain ⟨_, i, _, hi, _⟩ := hc slot cell hcell howner
  exact hn i hi

/-- At an owning return, all remaining ownership belongs to the returned
origin. Every frame-owned cell is therefore precisely the returned cell. -/
theorem Complete.only_returned {c : Context} {g : Ghost} {s : State} {frame : Frame} {i : Nat} {h : Handle}
    (hc : Complete c g s frame) (hg : g i = some h)
    (hn : ∀ j, c.rights j = some .owned → j = i) :
    ∀ slot cell, s.cells slot = some cell → cell.owner = frame → slot = h.slot ∧ cell.loans = [] := by
  intro slot cell hcell howner
  obtain ⟨hl, j, k, hj, hgk, hk, _⟩ := hc slot cell hcell howner
  have he := hn j hj
  subst j
  rw [hg] at hgk
  cases hgk
  exact ⟨hk.symm, hl⟩

/-- The active frame cannot disguise its own allocation as a borrow: it
would need an owning source right too, violating source separation. -/
theorem Complete.borrow_not_owned {c : Context} {g : Ghost} {s : State} {frame : Frame} {i : Nat} {h : Handle}
    (hc : Complete c g s frame) (hr : Rights c g s frame) (hi : c.rights i = some .borrowed)
    (hg : g i = some h) : ¬ s.owns frame h := by
  intro ho
  obtain ⟨j, hj, hgj⟩ := hc.handle ho
  have hne : i ≠ j := by intro he; subst j; rw [hi] at hj; cases hj
  exact hr.2 i j .borrowed .owned hi hj hne (Or.inr rfl) h h hg hgj rfl

theorem finish_void {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hb : c.bounded) (hc : Complete c g s frame) (hf : finish c none = true) :
    ∀ slot cell, s.cells slot = some cell → cell.owner ≠ frame := by
  apply hc.no_owned
  intro i hi
  have hn := finish_sound hb hf i hi
  cases hn

theorem finish_owned {c : Context} {g : Ghost} {s : State} {frame : Frame} {i : Nat} {h : Handle}
    (hb : c.bounded) (hc : Complete c g s frame) (hg : g i = some h)
    (hf : finish c (some i) = true) :
    ∀ slot cell, s.cells slot = some cell → cell.owner = frame → slot = h.slot ∧ cell.loans = [] :=
  hc.only_returned hg (fun j hj => (Option.some.inj (finish_sound hb hf j hj)).symm)

#print axioms Complete.release
#print axioms Complete.no_owned
#print axioms Complete.only_returned
#print axioms Complete.borrow_not_owned
#print axioms Complete.allocate
#print axioms Complete.returned
#print axioms finish_void
#print axioms finish_owned

end Gabbro.Grammatik.ArenaOwnership.Source
