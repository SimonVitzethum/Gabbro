module

public import Grammatik.Kern.Syntax.Marken.Owner.Flow
public import Grammatik.Bausteine.Arena.Ownership.State

@[expose] public section

namespace Gabbro.Grammatik

/-- An injective nominal namespace in the existing identity/grant ledger.
    These integers are ghost keys, never addresses or runtime epochs in `Ty`.
    Arena handles and owner marks use the same location/loan mechanism. -/
structure OwnerNamespace (D : Deklaration) where
  key : D.Marke → Int
  injective : ∀ a b, key a = key b → a = b

/-- Resolved provenance for a distinguished successful software-mint return.
    This declaration is not a hardware assumption or an executable foreign
    call: C08 must prove and retain the actual binding invocation and effects. -/
structure OwnerMintDecl (D : Deklaration) where
  mark : D.Marke
  minter : D.Ax
  root : D.Fn
  site : Nat
  stage : Nat
  owner : ∃ t, mark ∈ D.eigner t
  bounded : stage < D.stufen mark

/-- A dynamic grant for a nominal owner. It is ghost metadata, not a `Ty`
    constructor. Copying its representation cannot duplicate ledger access. -/
structure OwnerToken (D : Deklaration) where
  mark : D.Marke
  stage : Nat
  handle : ArenaOwnership.Handle

/-- Metadata over the existing grant/escrow ledger. Spent authority and the
    initial-origin classification survive every transfer, loan and retirement.
    The canonical G/GX transition integration remains required for admission. -/
structure OwnerState (D : Deklaration) where
  ledger : ArenaOwnership.State
  initial : D.Marke → Bool
  spent : D.Marke → Bool
  stage : D.Marke → Nat

namespace OwnerState

variable {D : Deklaration}

/-- No initial or minted owners. Initial owners need a separately checked
    initial ledger; ordinary signatures cannot establish them. -/
def empty : OwnerState D :=
  ⟨ArenaOwnership.State.empty, fun _ => false, fun _ => false, fun _ => 0⟩

def access (N : OwnerNamespace D) (s : OwnerState D)
    (f : ArenaOwnership.Frame) (t : OwnerToken D) : Prop :=
  t.handle.slot = N.key t.mark ∧ s.stage t.mark = t.stage ∧ s.ledger.access f t.handle

def owns (N : OwnerNamespace D) (s : OwnerState D)
    (f : ArenaOwnership.Frame) (t : OwnerToken D) : Prop :=
  t.handle.slot = N.key t.mark ∧ s.stage t.mark = t.stage ∧ s.ledger.owns f t.handle

instance (N : OwnerNamespace D) (s : OwnerState D)
    (f : ArenaOwnership.Frame) (t : OwnerToken D) : Decidable (s.access N f t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (N : OwnerNamespace D) (s : OwnerState D)
    (f : ArenaOwnership.Frame) (t : OwnerToken D) : Decidable (s.owns N f t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Each live nominal owner has bounded stage and a disjoint origin. The
    ledger already checks fresh grants and exclusive, acyclic loan stacks. -/
def Valid (N : OwnerNamespace D) (s : OwnerState D) : Prop :=
  s.ledger.valid ∧ ∀ m c, s.ledger.cells (N.key m) = some c →
    s.stage m < D.stufen m ∧
      ((s.initial m = true ∧ s.spent m = false) ∨
       (s.initial m = false ∧ s.spent m = true))

/-- Replace location/escrow data without changing nominal origin or stages.
    This central update has no operation that replenishes mint authority. -/
def withLedger (s : OwnerState D) (ledger : ArenaOwnership.State) : OwnerState D :=
  { s with ledger := ledger }

/-- Bookkeeping AFTER the authorized foreign binding returned successfully.
    This function neither invokes nor erases the binding. The canonical rule
    must also match the declaration's actual minter, root and source site. -/
def recordMint (N : OwnerNamespace D) (d : OwnerMintDecl D)
    (s : OwnerState D) (f : ArenaOwnership.Frame) : Option (OwnerState D × OwnerToken D) :=
  if s.initial d.mark = false ∧ s.spent d.mark = false ∧ f.activation = 0 then
    match s.ledger.allocate f (N.key d.mark) with
    | none => none
    | some (ledger, h) => some
        ({ s with ledger := ledger,
            spent := fun m => if m = d.mark then true else s.spent m,
            stage := fun m => if m = d.mark then d.stage else s.stage m },
         ⟨d.mark, d.stage, h⟩)
  else none

/-- Move between distinct activation identities of the same thread, using the existing
    fresh-grant operation. The call-log edge supplies the dynamic authorization;
    this ledger primitive does not infer one from stack depth. -/
def transfer (N : OwnerNamespace D) (s : OwnerState D)
    (sourceFrame into : ArenaOwnership.Frame) (t : OwnerToken D) :
    Option (OwnerState D × OwnerToken D) :=
  if s.owns N sourceFrame t ∧
      sourceFrame ≠ into then
    match s.ledger.move sourceFrame into t.handle with
    | none => none
    | some (ledger, h) => some (s.withLedger ledger, { t with handle := h })
  else none

/-- Exclusive call-scoped borrow, including a nested borrow from the
    current accessor. The call-log edge supplies the scope; the old holder
    loses access while the loan is active. -/
def borrow (N : OwnerNamespace D) (s : OwnerState D)
    (sourceFrame into : ArenaOwnership.Frame) (t : OwnerToken D) : Option (OwnerState D) :=
  if s.access N sourceFrame t ∧ sourceFrame ≠ into then
    (s.ledger.lend sourceFrame into t.handle).map s.withLedger
  else none

/-- Pop the innermost escrow and restore the saved nominal owner and stage.
    The proposed lender must actually be the accessor after this exact pop. -/
def returnBorrow (N : OwnerNamespace D) (s : OwnerState D)
    (callee lender : ArenaOwnership.Frame) (saved : OwnerToken D) : Option (OwnerState D) :=
  if s.access N callee saved ∧ callee ≠ lender then
    match s.ledger.endLoan callee saved.handle with
    | none => none
    | some ledger =>
        if ledger.access lender saved.handle then some (s.withLedger ledger) else none
  else none

/-- Stage advance is available only to an owner, never to a borrower or its
    suspended lender. A changing-stage handoff therefore requires a move. -/
def advance (N : OwnerNamespace D) (s : OwnerState D)
    (f : ArenaOwnership.Frame) (t : OwnerToken D) : Option (OwnerState D × OwnerToken D) :=
  if s.owns N f t ∧ t.stage + 1 < D.stufen t.mark then
    some ({ s with stage := fun m => if m = t.mark then t.stage + 1 else s.stage m },
      { t with stage := t.stage + 1 })
  else none

/-- Terminal consumption retires the grant but preserves spent authority.
    A borrowed owner cannot be consumed, even through an inner call. -/
def retire (N : OwnerNamespace D) (s : OwnerState D)
    (f : ArenaOwnership.Frame) (t : OwnerToken D) : Option (OwnerState D) :=
  if s.owns N f t then (s.ledger.release f t.handle).map s.withLedger else none

/-- Single-accessor property, including all suspended lenders. -/
theorem access_unique {N : OwnerNamespace D} {s : OwnerState D}
    {f g : ArenaOwnership.Frame} {t : OwnerToken D}
    (hf : s.access N f t) (hg : s.access N g t) : f = g :=
  ArenaOwnership.State.access_unique hf.2.2 hg.2.2

/-- Uniqueness is nominal, even for independently supplied handle records.
    A copied or forged handle cannot provide a second accessor at any stage. -/
theorem access_owner_unique {N : OwnerNamespace D} {s : OwnerState D}
    {f g : ArenaOwnership.Frame} {t u : OwnerToken D}
    (ht : s.access N f t) (hu : s.access N g u) (hm : t.mark = u.mark) :
    f = g ∧ t.stage = u.stage := by
  have hs : t.handle.slot = u.handle.slot :=
    ht.1.trans ((congrArg N.key hm).trans hu.1.symm)
  have hf := ht.2.2
  have hg := hu.2.2
  unfold ArenaOwnership.State.access at hf hg
  rw [hs] at hf
  refine ⟨?_, ht.2.1.symm.trans ((congrArg s.stage hm).trans hu.2.1)⟩
  cases hc : s.ledger.cells u.handle.slot with
  | none => simp only [hc] at hg
  | some c =>
      rw [hc] at hf hg
      exact hf.2.symm.trans hg.2

/-- Namespace injectivity prevents one grant from denoting two nominal owners. -/
theorem nominal_unique {N : OwnerNamespace D} {s : OwnerState D}
    {f g : ArenaOwnership.Frame} {t u : OwnerToken D}
    (ht : s.access N f t) (hu : s.access N g u) (h : t.handle.slot = u.handle.slot) :
    t.mark = u.mark :=
  N.injective t.mark u.mark (ht.1.symm.trans (h.trans hu.1))

theorem withLedger_spent (s : OwnerState D) (ledger : ArenaOwnership.State) :
    (s.withLedger ledger).spent = s.spent := rfl

/-- Permanent spent authority prevents minting, even after the cell is freed. -/
theorem mint_spent_refused (N : OwnerNamespace D) (d : OwnerMintDecl D)
    (s : OwnerState D) (f : ArenaOwnership.Frame) (h : s.spent d.mark = true) :
    recordMint N d s f = none := by
  simp [recordMint, h]

/-- An initial owner cannot also have a mint origin. -/
theorem mint_initial_refused (N : OwnerNamespace D) (d : OwnerMintDecl D)
    (s : OwnerState D) (f : ArenaOwnership.Frame) (h : s.initial d.mark = true) :
    recordMint N d s f = none := by
  simp [recordMint, h]

/-- A successful mint permanently spends exactly this authority. -/
theorem mint_spends {N : OwnerNamespace D} {d : OwnerMintDecl D}
    {s s' : OwnerState D} {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (h : recordMint N d s f = some (s', t)) : s'.spent d.mark = true := by
  unfold recordMint at h
  split at h
  · split at h
    · cases h
    · cases h
      simp only [↓reduceIte]
  · cases h

/-- Every previously spent authority stays spent after minting another owner. -/
theorem mint_spent_monotone {N : OwnerNamespace D} {d : OwnerMintDecl D}
    {s s' : OwnerState D} {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (h : recordMint N d s f = some (s', t)) (m : D.Marke) (hm : s.spent m = true) :
    s'.spent m = true := by
  unfold recordMint at h
  split at h
  · split at h
    · cases h
    · cases h
      by_cases he : m = d.mark <;> simp [he, hm]
  · cases h

end OwnerState

end Gabbro.Grammatik
