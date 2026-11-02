module

public import Grammatik.Kern.Syntax.Marken.Owner.State

@[expose] public section

namespace Gabbro.Grammatik.OwnerState

variable {D : Deklaration}

private theorem allocated_key {s s' : ArenaOwnership.State} {f : ArenaOwnership.Frame}
    {key : Int} {h : ArenaOwnership.Handle}
    (ha : s.allocate f key = some (s', h)) : h.slot = key := by
  unfold ArenaOwnership.State.allocate at ha
  split at ha
  · cases ha
  · cases ha
    rfl

theorem empty_valid (N : OwnerNamespace D) : (empty : OwnerState D).Valid N := by
  refine ⟨ArenaOwnership.State.empty_valid, ?_⟩
  intro m c hc
  cases hc

/-- Minting establishes a valid grant for the declared identity and stage,
    with disjoint minted/initial provenance. The software-call premise still
    belongs to the canonical C08/G transition, not to this ledger lemma. -/
theorem mint_grant {N : OwnerNamespace D} {d : OwnerMintDecl D}
    {s s' : OwnerState D} {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (hv : s.ledger.valid) (h : recordMint N d s f = some (s', t)) :
    s'.ledger.valid ∧ s'.owns N f t ∧ s'.spent d.mark = true ∧ s'.initial d.mark = false := by
  unfold recordMint at h
  split at h
  · rename_i guard
    cases ha : s.ledger.allocate f (N.key d.mark) with
    | none => simp only [ha] at h; cases h
    | some result =>
      rcases result with ⟨ledger, handle⟩
      simp only [ha] at h
      cases h
      have hg := ArenaOwnership.State.allocate_valid hv f (N.key d.mark) ha
      refine ⟨hg.1, ?_, ?_, guard.1⟩
      · exact ⟨allocated_key ha, by simp only [↓reduceIte], hg.2⟩
      · simp only [↓reduceIte]
  · cases h

/-- Mint preserves the complete nominal-origin/stage invariant. -/
theorem mint_valid {N : OwnerNamespace D} {d : OwnerMintDecl D}
    {s s' : OwnerState D} {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (hv : s.Valid N) (h : recordMint N d s f = some (s', t)) : s'.Valid N := by
  unfold recordMint at h
  split at h
  · rename_i guard
    cases ha : s.ledger.allocate f (N.key d.mark) with
    | none => simp only [ha] at h; cases h
    | some result =>
      rcases result with ⟨ledger, handle⟩
      simp only [ha] at h
      cases h
      refine ⟨(ArenaOwnership.State.allocate_valid hv.1 f (N.key d.mark) ha).1, ?_⟩
      intro m c hc
      by_cases hm : m = d.mark
      · subst m
        exact ⟨by simpa only [↓reduceIte] using d.bounded,
          Or.inr ⟨guard.1, by simp only [↓reduceIte]⟩⟩
      · have hk : N.key m ≠ N.key d.mark := fun he => hm (N.injective _ _ he)
        have ho : s.ledger.cells (N.key m) = some c := by
          rw [← ArenaOwnership.State.allocate_other ha (N.key m) hk]
          exact hc
        simpa only [hm, ↓reduceIte] using hv.2 m c ho
  · cases h

/-- Replacing locations by a valid ledger with no new live identities preserves
    the nominal invariant. Transfers, loans and retirement use this interface. -/
theorem withLedger_valid {N : OwnerNamespace D} {s : OwnerState D}
    {ledger : ArenaOwnership.State} (hv : s.Valid N) (hl : ledger.valid)
    (hdom : ∀ m c, ledger.cells (N.key m) = some c →
      ∃ old, s.ledger.cells (N.key m) = some old) : (s.withLedger ledger).Valid N := by
  refine ⟨hl, ?_⟩
  intro m c hc
  obtain ⟨old, ho⟩ := hdom m c hc
  exact hv.2 m old ho

/-- A move hands over a fresh grant for the same owner and invalidates every
    saved use of the old grant, including uses by suspended callers. -/
theorem transfer_grant {N : OwnerNamespace D} {s s' : OwnerState D}
    {sourceFrame into : ArenaOwnership.Frame} {t t' : OwnerToken D}
    (hv : s.ledger.valid) (h : transfer N s sourceFrame into t = some (s', t')) :
    s'.ledger.valid ∧ s'.owns N into t' ∧ t'.mark = t.mark ∧ t'.stage = t.stage ∧
      (∀ frame, ¬ s'.access N frame t) ∧ s'.spent = s.spent := by
  unfold transfer at h
  split at h
  · rename_i guard
    cases hm : s.ledger.move sourceFrame into t.handle with
    | none => simp only [hm] at h; cases h
    | some result =>
      rcases result with ⟨ledger, handle⟩
      simp only [hm] at h
      cases h
      have hg := ArenaOwnership.State.move_valid hv sourceFrame into t.handle hm
      refine ⟨hg.1, ⟨hg.2.2.2.1.trans guard.1.1, guard.1.2.1, hg.2.1⟩,
        rfl, rfl, ?_, rfl⟩
      intro frame ha
      exact hg.2.2.1 frame ha.2.2
  · cases h

/-- Borrowing admits one accessor and disables both lender access and callee
    consumption. The existing escrow stack, including nesting, is reused. -/
theorem borrow_grant {N : OwnerNamespace D} {s s' : OwnerState D}
    {sourceFrame into : ArenaOwnership.Frame} {t : OwnerToken D}
    (hv : s.ledger.valid) (h : borrow N s sourceFrame into t = some s') :
    s'.ledger.valid ∧ s'.access N into t ∧ ¬ s'.access N sourceFrame t ∧
      ¬ s'.owns N into t ∧ s'.spent = s.spent ∧ s'.stage = s.stage := by
  unfold borrow at h
  split at h
  · rename_i guard
    cases hl : s.ledger.lend sourceFrame into t.handle with
    | none => simp only [hl, Option.map_none] at h; cases h
    | some ledger =>
      simp only [hl, Option.map_some] at h
      cases h
      have hg := ArenaOwnership.State.lend_valid hv sourceFrame into t.handle hl
      exact ⟨hg.1, ⟨guard.1.1, guard.1.2.1, hg.2.1⟩,
        fun ha => hg.2.2.2 ha.2.2, fun ho => hg.2.2.1 ho.2.2, rfl, rfl⟩
  · cases h

/-- Returning a borrow restores precisely the saved identity and stage. -/
theorem returnBorrow_grant {N : OwnerNamespace D} {s s' : OwnerState D}
    {callee lender : ArenaOwnership.Frame} {saved : OwnerToken D}
    (hv : s.ledger.valid) (h : returnBorrow N s callee lender saved = some s') :
    s'.ledger.valid ∧ s'.access N lender saved ∧ s'.spent = s.spent ∧ s'.stage = s.stage := by
  unfold returnBorrow at h
  split at h
  · rename_i guard
    cases hl : s.ledger.endLoan callee saved.handle with
    | none => simp only [hl] at h; cases h
    | some ledger =>
      simp only [hl] at h
      split at h
      · rename_i returned
        cases h
        exact ⟨ArenaOwnership.State.endLoan_valid hv callee saved.handle hl,
          ⟨guard.1.1, guard.1.2.1, returned⟩, rfl, rfl⟩
      · cases h
  · cases h

/-- A checked borrow has an exact inverse at its matching return. Applying this
    theorem from the innermost borrow outward restores nested exclusive loans. -/
theorem borrow_return {N : OwnerNamespace D} {s loaned : OwnerState D}
    {sourceFrame into : ArenaOwnership.Frame} {t : OwnerToken D}
    (hv : s.ledger.valid) (h : borrow N s sourceFrame into t = some loaned) :
    returnBorrow N loaned into sourceFrame t = some s := by
  unfold borrow at h
  split at h
  · rename_i guard
    obtain ⟨ledger, hl, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have ha : (s.withLedger ledger).access N into t :=
      ⟨guard.1.1, guard.1.2.1,
        (ArenaOwnership.State.lend_valid hv sourceFrame into t.handle hl).2.1⟩
    have hend := ArenaOwnership.State.lend_endLoan sourceFrame into t.handle hl
    unfold returnBorrow
    rw [if_pos ⟨ha, Ne.symm guard.2⟩]
    change (match ledger.endLoan into t.handle with
      | none => none
      | some returned => if returned.access sourceFrame t.handle then
          some ((s.withLedger ledger).withLedger returned) else none) = some s
    rw [hend, if_pos guard.1.2.2]
    cases s
    rfl
  · cases h

/-- Advancing updates the source stage but preserves the nominal identity and
    mint history. Every old-stage alias becomes unusable, in every frame. -/
theorem advance_grant {N : OwnerNamespace D} {s s' : OwnerState D}
    {f : ArenaOwnership.Frame} {t t' : OwnerToken D}
    (h : advance N s f t = some (s', t')) :
    s'.owns N f t' ∧ t'.mark = t.mark ∧ t'.stage = t.stage + 1 ∧
      s'.spent = s.spent ∧ (∀ frame, ¬ s'.access N frame t) := by
  unfold advance at h
  split at h
  · rename_i guard
    cases h
    refine ⟨⟨guard.1.1, by simp only [↓reduceIte], guard.1.2.2⟩,
      rfl, rfl, rfl, ?_⟩
    intro frame ha
    have he : t.stage + 1 = t.stage := by
      simpa only [↓reduceIte] using ha.2.1
    omega
  · cases h

theorem advance_valid {N : OwnerNamespace D} {s s' : OwnerState D}
    {f : ArenaOwnership.Frame} {t t' : OwnerToken D}
    (hv : s.Valid N) (h : advance N s f t = some (s', t')) : s'.Valid N := by
  unfold advance at h
  split at h
  · rename_i guard
    cases h
    refine ⟨hv.1, ?_⟩
    intro m c hc
    have old := hv.2 m c hc
    by_cases hm : m = t.mark
    · subst m
      exact ⟨by simpa only [↓reduceIte] using guard.2, old.2⟩
    · simpa only [hm, ↓reduceIte] using old
  · cases h

/-- The retired handle has no remaining accessor; mint authority stays spent. -/
theorem retire_grant {N : OwnerNamespace D} {s s' : OwnerState D}
    {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (hv : s.ledger.valid) (h : retire N s f t = some s') :
    s'.ledger.valid ∧ (∀ frame, ¬ s'.access N frame t) ∧ s'.spent = s.spent := by
  unfold retire at h
  split at h
  · cases hr : s.ledger.release f t.handle with
    | none => simp only [hr, Option.map_none] at h; cases h
    | some ledger =>
      simp only [hr, Option.map_some] at h
      cases h
      have hg := ArenaOwnership.State.release_valid hv f t.handle hr
      exact ⟨hg.1, fun frame ha => hg.2 frame ha.2.2, rfl⟩
  · cases h

/-- A loan cannot be consumed or advanced at the borrower, nor transferred as
    an owning result. Every such path needs the stronger unloaned `owns`. -/
theorem borrower_restrictions {N : OwnerNamespace D} {s : OwnerState D}
    {f : ArenaOwnership.Frame} {t : OwnerToken D} (h : ¬ s.owns N f t)
    (into : ArenaOwnership.Frame) :
    retire N s f t = none ∧ advance N s f t = none ∧ transfer N s f into t = none := by
  simp only [retire, advance, transfer, h, false_and, ↓reduceIte, and_self]

/-- Terminal consume never replenishes one-shot authority. -/
theorem retire_cannot_remint {N : OwnerNamespace D} {d : OwnerMintDecl D}
    {s s' : OwnerState D} {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (hv : s.ledger.valid) (hspent : s.spent d.mark = true)
    (hr : retire N s f t = some s') (root : ArenaOwnership.Frame) :
    recordMint N d s' root = none := by
  have he := (retire_grant hv hr).2.2
  apply mint_spent_refused N d s' root
  rw [he]
  exact hspent

end Gabbro.Grammatik.OwnerState
