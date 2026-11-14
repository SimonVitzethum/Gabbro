module

public import Grammatik.Niedrig.Authority.Layout
public import Grammatik.Niedrig.Authority.Protocol
public import Grammatik.Kern.Syntax.Satz.T1Frame

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-!
Option R: this is a proof-relevant replay beside the existing G world, not a
new execution semantics for source programs. World has no owner field. In
particular, the identity fold ownerLedgerOf cannot describe a loan. The
ledger/world correspondence below records the actual OwnerState operations
in ViewResult/returnView and the existing G stores in one history.

Borrow, return and refusal are ghost operations with zero G steps. Relating
them to a source call requires the separate BorrowScopePremises boundary;
this replay alone does not establish source admission or a RufSchrittG.
-/

/-- Newest first, like World.spur. Protocol events are ghost evidence and are
    never inserted into the machine's ordinary access/lock trace. -/
inductive AuthorityEvent (D : Deklaration) where
  | borrowed (view : View D)
  | returned (view : View D)
  | refused (reason : ViewFailure)
  | wrote (view : View D)

/-- Every currently live view has an actual producer in the replay. Returned
    views may remain in history; membership alone does not make them live. -/
def TraceCoversViews {D : Deklaration} {P I : Type}
    (trace : List (AuthorityEvent D)) (c : Context D P I) : Prop :=
  ∀ view ∈ c.views, AuthorityEvent.borrowed view ∈ trace

/-- Replay from an explicit initial world and context. Each ghost move uses
    the canonical checked producer or return, which contains borrow/returnBorrow
    evidence. Each memory move is exactly an existing schreibSlot, including
    its access event and the original lock/effect premises.

    This does not assert that an arbitrary G run carries such a replay. -/
inductive LedgerMatchesWorld {D : Deklaration} {P I : Type}
    (a : Authority D) (origin : Context D P I) (initialWorld : World D) :
    List (AuthorityEvent D) → Context D P I → World D → Prop where
  | start : LedgerMatchesWorld a origin initialWorld [] origin initialWorld
  | borrow {trace : List (AuthorityEvent D)} {c : Context D P I} {world : World D}
      (previous : LedgerMatchesWorld a origin initialWorld trace c world)
      {space : Space D} (start : Address space) (length : Nat)
      (rights : DataRights) (borrower : ArenaOwnership.Frame) (r : ViewResult a c)
      (produced : ram_view a c start length rights borrower = .ok r) :
      LedgerMatchesWorld a origin initialWorld (.borrowed r.view :: trace) r.next world
  | restore {trace : List (AuthorityEvent D)} {c c' : Context D P I} {world : World D}
      (previous : LedgerMatchesWorld a origin initialWorld trace c world)
      (view : View D) (rest : List (View D)) (head : c.views = view :: rest)
      (returned : returnView a c = .ok c') :
      LedgerMatchesWorld a origin initialWorld (.returned view :: trace) c' world
  | refuse {trace : List (AuthorityEvent D)} {c : Context D P I} {world : World D}
      (previous : LedgerMatchesWorld a origin initialWorld trace c world)
      {space : Space D} (start : Address space) (length : Nat)
      (rights : DataRights) (borrower : ArenaOwnership.Frame) (reason : ViewFailure)
      (refused : ram_view a c start length rights borrower = .error reason) :
      LedgerMatchesWorld a origin initialWorld (.refused reason :: trace) c world
  | refuseReturn {trace : List (AuthorityEvent D)} {c : Context D P I} {world : World D}
      (previous : LedgerMatchesWorld a origin initialWorld trace c world)
      (reason : ViewFailure) (refused : returnView a c = .error reason) :
      LedgerMatchesWorld a origin initialWorld (.refused reason :: trace) c world
  | store {trace : List (AuthorityEvent D)} {c : Context D P I} {before after : World D}
      (previous : LedgerMatchesWorld a origin initialWorld trace c before)
      (layout : AdressLayout D) (correct : LayoutOk layout) (realizes : a.Realizes layout)
      (write : ViewWrite a c layout before after) (resources : List (Res D))
      (allowed : darf D write.view.span.table resources) (held : HeldIn resources before.haelt) :
      LedgerMatchesWorld a origin initialWorld (.wrote write.view :: trace) c
        (before.schreibSlot write.view.span.table resources write.index write.field write.value)

/-- An inhabited replay, a valid final context and coverage of all its live
    views. Initial grants are explicit premises; initial views cannot be
    fabricated. The history is existential because it is ghost evidence. -/
structure SimRel {D : Deklaration} {P I : Type}
    (a : Authority D) (c : Context D P I) (world : World D) : Prop where
  valid : c.Valid a
  replay : ∃ (origin : Context D P I) (initialWorld : World D)
      (trace : List (AuthorityEvent D)),
    origin.Valid a ∧ origin.views = [] ∧
    LedgerMatchesWorld a origin initialWorld trace c world ∧ TraceCoversViews trace c

variable {D : Deklaration} {P I : Type} {a : Authority D}
  {c c' : Context D P I} {world : World D}

/-- Extract the exact ghost pop, including the view stack and the unchanged
    architectural metadata. No memory is present in returnView to roll back. -/
theorem returnView_ledger (returned : returnView a c = .ok c') :
    ∃ (view : View D) (rest : List (View D)),
      c.views = view :: rest ∧ c.frame = view.borrower ∧
      OwnerState.returnBorrow a.names c.owners c.frame view.lender a.token = some c'.owners ∧
      c'.frame = view.lender ∧ c'.views = rest ∧
      c'.privilege = c.privilege ∧ c'.interrupt = c.interrupt := by
  unfold returnView at returned
  cases hv : c.views with
  | nil => simp only [hv] at returned; cases returned
  | cons view rest =>
    simp only [hv] at returned
    split at returned
    · rename_i frame
      cases hr : OwnerState.returnBorrow a.names c.owners c.frame view.lender a.token with
      | none => simp only [hr] at returned; cases returned
      | some owners =>
        simp only [hr] at returned
        cases returned
        exact ⟨view, rest, rfl, frame, hr, rfl, rfl, rfl, rfl⟩
    · cases returned

theorem returnView_views_subset (returned : returnView a c = .ok c') :
    ∀ view ∈ c'.views, view ∈ c.views := by
  obtain ⟨head, rest, stack, _, _, _, tail, _, _⟩ := returnView_ledger returned
  intro view member
  rw [tail] at member
  rw [stack]
  exact List.mem_cons_of_mem _ member

theorem simRel_initial (valid : c.Valid a) (empty : c.views = []) (world : World D) :
    SimRel a c world := by
  refine ⟨valid, ⟨c, world, [], valid, empty, .start, ?_⟩⟩
  intro view member
  rw [empty] at member
  cases member

/-- The producer receipt is also the complete ledger-level simulation: the
    old accessor is suspended, the borrower cannot consume, and mint/stage
    metadata are unchanged. A machine call is deliberately not concluded. -/
theorem borrow_sim (simulation : SimRel a c world) {space : Space D}
    (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame) (r : ViewResult a c)
    (produced : ram_view a c start length rights borrower = .ok r) :
    SimRel a r.next world ∧
    OwnerState.borrow a.names c.owners c.frame r.view.borrower a.token = some r.next.owners ∧
    r.next.owners.access a.names r.next.frame a.token ∧
    ¬ r.next.owners.access a.names c.frame a.token ∧
    ¬ r.next.owners.owns a.names r.next.frame a.token ∧
    r.next.owners.spent = c.owners.spent ∧ r.next.owners.stage = c.owners.stage := by
  have grant := OwnerState.borrow_grant simulation.valid.2.1 r.borrowed
  refine ⟨?_, r.borrowed, grant.2.1, grant.2.2.1, grant.2.2.2.1,
    grant.2.2.2.2.1, grant.2.2.2.2.2⟩
  obtain ⟨origin, initialWorld, trace, initialValid, empty, replay, covered⟩ := simulation.replay
  refine ⟨ram_view_preserves simulation.valid r,
    ⟨origin, initialWorld, .borrowed r.view :: trace, initialValid, empty,
      .borrow replay start length rights borrower r produced, ?_⟩⟩
  intro view member
  rcases List.mem_cons.mp member with same | old
  · subst view
    exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (covered view old)

theorem returnView_sim (simulation : SimRel a c world)
    (returned : returnView a c = .ok c') : SimRel a c' world := by
  obtain ⟨view, rest, stack, _, _, _, _, _, _⟩ := returnView_ledger returned
  obtain ⟨origin, initialWorld, trace, initialValid, empty, replay, covered⟩ := simulation.replay
  refine ⟨returnView_preserves simulation.valid returned,
    ⟨origin, initialWorld, .returned view :: trace, initialValid, empty,
      .restore replay view rest stack returned, ?_⟩⟩
  intro v member
  exact List.mem_cons_of_mem _ (covered v (returnView_views_subset returned v member))

end Gabbro.Grammatik.LowLevel
