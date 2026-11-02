/-
  File:      Grammatik/Bausteine/Arena/ArenaPageReturn.lean
  Subject:   C18, Kern side: the page-return binding for static arrays.

  A `reset A at i count n` zeroes the selected range by stores. Returning
  the range's BACKING PAGES to the provider is a second step through an
  explicit user-supplied service, never an OS assumption (no
  madvise/mmap/unconditional demand-zero; no promised success from an
  ignored error result):

  * `BackingState` -- where one static range's backing stands: `resident`
    (the ordinary state), `pendingReturn` (the exclusive pending return
    authority, consumed once), `released` (pages returned, with the
    zero-on-next-read contract), `recommitted` (pages taken back, resident
    again). The permanent LOGICAL static extent is never the physical
    backing: reservation survives every transfer, and `speicherAdressen`
    keeps the reserved logical extent beside the physical grant
    correspondence.
  * `BackingStep` -- the only moves: request, release, recommit,
    occupy. A release consumes the pending authority exactly once; a
    resident range is never released silently, and a released range is
    never released twice.
  * `PageReturnContract` -- the binding data: the user service function
    that implements the return (an ordinary software service under the
    still-open C08 interface; its generic correspondence to actual backing
    storage and its resource-changing rules are the open bridge), and the
    provider granule in elements. Only fully covered granule-aligned pages
    return (`fullyCoveredPagesB`); selected boundary fragments are zeroed
    by stores and neighbours are preserved (`resetRange_reads_zero`,
    `resetRange_outside_same` in `ArenaStaticReset.lean`).
  * `ZeroObservation` -- the observation contract a released page keeps:
    every admitted read of the range observes the typed zero until the
    next admitted write to that element, including after recommit.
    `resetFinW_zero_observation` shows the store expansion meets it.

  A page release additionally requires the C08/C12 grant ledger duties,
  still open: no live owned allocation, borrowed view, outstanding RCU
  ticket, in-flight service or escaping alias that requires resident old
  contents anywhere in that entire page. Aliases are tracked through
  parameters, results, fields, suspended frames, indirect calls and
  starts; persistent logical aliases survive only with this same
  zero-on-next-read contract and synchronization. Never invalidate an
  outside live cell to obtain page alignment.
-/
module

public import Grammatik.Bausteine.Arena.ArenaStaticReset

@[expose] public section

namespace Gabbro.Grammatik

/-- Where one static range's physical backing stands. The logical static
    extent is permanent; this state is only about the backing. -/
inductive BackingState where
  | resident
  | pendingReturn
  | released
  | recommitted
  deriving DecidableEq, Repr

/-- The only backing moves: request the return, release it (consuming the
    pending authority), take the pages back, occupy them again. -/
inductive BackingStep : BackingState → BackingState → Prop where
  | request : BackingStep .resident .pendingReturn
  | release : BackingStep .pendingReturn .released
  | recommit : BackingStep .released .recommitted
  | occupy : BackingStep .recommitted .resident

/-- A release comes only from the pending authority. -/
theorem release_consumes_pending {a : BackingState}
    (h : BackingStep a .released) : a = .pendingReturn := by
  cases h; rfl

/-- A resident range is never released silently. -/
theorem no_silent_release : ¬ BackingStep .resident .released := by
  intro h; cases h

/-- A released range is never released twice: the pending authority is
    consumed once by the release. -/
theorem no_double_release : ¬ BackingStep .released .released := by
  intro h; cases h

/-- A pending return is never requested twice without an outcome. -/
theorem no_double_request :
    ¬ BackingStep .pendingReturn .pendingReturn := by
  intro h; cases h

/-- The binding data of a page return: the user service that implements
    the return and the provider granule in elements. The service is an
    ordinary software function of the program; an infallible source
    statement needs user proof of its completion and availability, and a
    fallible spelling would need its own approved source rule. -/
structure PageReturnContract (D : Deklaration) (g : D.Glob) where
  service : D.Fn
  granule : Nat
  granulePos : 0 < granule

/-- The released pages are exactly the fully covered granule-aligned
    pages `[a, b)` inside the reset range `[i, i + k)`. -/
def FullyCoveredPages (granule i k a b : Nat) : Prop :=
  i ≤ a ∧ b ≤ i + k ∧ a % granule = 0 ∧ b % granule = 0 ∧ a < b

/-- The same coverage, decided. -/
def fullyCoveredPagesB (granule i k a b : Nat) : Bool :=
  decide (i ≤ a) && decide (b ≤ i + k) && decide (a % granule = 0) &&
    decide (b % granule = 0) && decide (a < b)

theorem fullyCoveredPagesB_iff {granule i k a b : Nat} :
    fullyCoveredPagesB granule i k a b = true ↔
      FullyCoveredPages granule i k a b := by
  simp only [fullyCoveredPagesB, FullyCoveredPages, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- The observation contract of a released page: every admitted read of
    the range observes the typed zero until the next admitted write to
    that element, including after recommit. -/
def ZeroObservation {α : Type} {n : Nat} (read : Fin n → α) (zero : α)
    (i k : Nat) : Prop :=
  ∀ j : Fin n, i ≤ j.val → j.val < i + k → read j = zero

/-- The store expansion meets the observation contract. -/
theorem resetFinW_zero_observation {α : Type} {n : Nat} (a : Fin n → α)
    (i k : Nat) (zero : α) :
    ZeroObservation (resetFinW a i k zero) zero i k :=
  fun j h1 h2 => resetFinW_get_in a i k zero j h1 h2

theorem release_chain_zeuge : BackingStep .resident .pendingReturn ∧
    BackingStep .pendingReturn .released := ⟨.request, .release⟩

theorem fullyCoveredPages_zeuge : fullyCoveredPagesB 4 0 8 0 8 = true := rfl

theorem fullyCoveredPages_unaligned_zeuge :
    fullyCoveredPagesB 4 0 8 2 8 = false := rfl

theorem fullyCoveredPages_outside_zeuge :
    fullyCoveredPagesB 4 0 8 0 12 = false := rfl

#print axioms release_consumes_pending
#print axioms no_silent_release
#print axioms no_double_release
#print axioms no_double_request
#print axioms fullyCoveredPagesB_iff
#print axioms resetFinW_zero_observation

end Gabbro.Grammatik
