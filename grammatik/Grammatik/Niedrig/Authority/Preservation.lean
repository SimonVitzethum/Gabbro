module

public import Grammatik.Niedrig.Authority.View

public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration} {P I : Type} {a : Authority D} {c c' : Context D P I}

/-- Issuing a view preserves every authority invariant and the unique accessor. -/
theorem ram_view_preserves (hc : c.Valid a) (r : ViewResult a c) : r.next.Valid a := by
  have hg := OwnerState.borrow_grant (D := D) hc.2.1 r.borrowed
  refine ⟨hc.1, hg.1, hg.2.1, ?_, ?_⟩
  · intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact ⟨r.admission.span, r.admission.epoch.2,
        r.admission.memoryClass, r.admission.bounds.1, r.admission.bounds.2,
        r.admission.owner, r.admission.epoch.1,
        r.admission.permissions.1, r.admission.permissions.2.1,
        r.admission.permissions.2.2.1, r.admission.permissions.2.2.2,
        r.admission.alignment.1, r.admission.alignment.2.1, r.admission.alignment.2.2,
        r.admission.mapping, r.admission.initialization⟩
    · exact hc.2.2.2.1 v hv
  · intro v hv w hw hne
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      rcases List.mem_cons.mp hw with he | hw
      · exact False.elim (hne he.symm)
      · exact (r.admission.compatible w hw).1
    · rcases List.mem_cons.mp hw with he | hw
      · subst w
        exact (r.admission.compatible v hv).2
      · exact hc.2.2.2.2 v hv w hw hne

/-- Returning removes exactly one live view and restores the ledger accessor. -/
theorem returnView_preserves (hc : c.Valid a) (h : returnView a c = .ok c') : c'.Valid a := by
  unfold returnView at h
  cases hv : c.views with
  | nil => simp only [hv] at h; cases h
  | cons v rest =>
      simp only [hv] at h
      split at h
      · cases hr : OwnerState.returnBorrow a.names c.owners c.frame v.lender a.token with
        | none => simp only [hr] at h; cases h
        | some owners =>
            simp only [hr] at h
            cases h
            have hg := OwnerState.returnBorrow_grant (D := D) hc.2.1 hr
            refine ⟨hc.1, hg.1, hg.2.1, ?_, ?_⟩
            · intro w hw
              exact hc.2.2.2.1 w (by rw [hv]; exact List.mem_cons_of_mem _ hw)
            · intro w hw z hz hne
              exact hc.2.2.2.2 w (by rw [hv]; exact List.mem_cons_of_mem _ hw)
                z (by rw [hv]; exact List.mem_cons_of_mem _ hz) hne
      · cases h

/-- The receipt has the exact inverse promised by the existing escrow model. -/
theorem ram_view_return (hc : c.Valid a) (r : ViewResult a c) :
    returnView a r.next = .ok c := by
  have hr := OwnerState.borrow_return (D := D) hc.2.1 r.borrowed
  simp only [returnView, ViewResult.next, r.admission.lender, hr, ↓reduceIte]

theorem ram_view_suspends (hc : c.Valid a) (r : ViewResult a c) :
    ¬ r.next.owners.access a.names c.frame a.token ∧
    ¬ r.next.owners.owns a.names r.next.frame a.token := by
  have h := OwnerState.borrow_grant (D := D) hc.2.1 r.borrowed
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem live_views_overlap_readonly (hc : c.Valid a) {v w : View D}
    (hv : v ∈ c.views) (hw : w ∈ c.views) (hne : v ≠ w) (overlap : v.Overlaps w) :
    v.rights.write = false ∧ w.rights.write = false :=
  hc.2.2.2.2 v hv w hw hne overlap

theorem ram_view_inside_span (r : ViewResult a c) {byte : Adresse}
    (h : r.view.Contains byte) :
    byte.1 = r.view.span.space.backing ∧ r.view.span.range.drin byte.2 := by
  obtain ⟨spanLow, spanHigh⟩ := r.admission.bounds
  obtain ⟨identity, viewLow, viewHigh⟩ := h
  refine ⟨identity, ?_, ?_⟩
  · change r.view.span.base ≤ byte.2
    omega
  · change byte.2 < r.view.span.base + r.view.span.length
    omega

/-- The complete borrowed interval fits in the address width, including its
    half-open endpoint. Successful bounds checks cannot hide integer wrap. -/
theorem ram_view_nonwrapping (hc : c.Valid a) (r : ViewResult a c) :
    r.view.base + r.view.length ≤ 2 ^ r.view.span.space.width := by
  have span := (hc.1.2.2.1 r.view.span r.admission.span).1
  have extent := span.2.1
  have bounds := r.admission.bounds.2
  omega

/-- Empty regions provide no access, including at their base. -/
theorem empty_view_no_byte (v : View D) (hn : v.length = 0) (byte : Adresse) :
    ¬ v.Contains byte := by
  intro h
  obtain ⟨_, low, high⟩ := h
  omega

/-- A borrower cannot consume, advance, or hand off the context while a view
    is outstanding, even through an inner call. -/
theorem view_blocks_consumption (hc : c.Valid a) (r : ViewResult a c)
    (into : ArenaOwnership.Frame) :
    OwnerState.retire a.names r.next.owners r.next.frame a.token = none ∧
    OwnerState.advance a.names r.next.owners r.next.frame a.token = none ∧
    OwnerState.transfer a.names r.next.owners r.next.frame into a.token = none :=
  OwnerState.borrower_restrictions (D := D) (N := a.names) (s := r.next.owners)
    (f := r.next.frame) (t := a.token) (ram_view_suspends hc r).2 into

end Gabbro.Grammatik.LowLevel
