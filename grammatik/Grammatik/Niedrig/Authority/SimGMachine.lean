module

public import Grammatik.Niedrig.Authority.SimGSaetze
public import Grammatik.Kern.Syntax.Marken.Owner.InvocationFlow
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil3a

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration} {P I : Type} {a : Authority D}
  {c : Context D P I}

/-- Once a machine transition has exactly the receipt's traced world, its
    carrier is both accessed and written in the EXISTING machine-G predicates.
    These predicates alone do not assert a RufSchrittG: source lowering must
    still supply the actual transition and these two world equalities. -/
theorem viewwrite_accessG {layout : AdressLayout D} {before after : World D}
    (write : ViewWrite a c layout before after) (resources : List (Res D))
    {first last : RufMaschineG D} {thread : Faden}
    (beforeWorld : first.weltVon thread = before)
    (afterWorld : last.weltVon thread =
      before.schreibSlot write.view.span.table resources write.index write.field write.value) :
    ZugriffG first last thread (.inl write.view.span.table) ∧
    SchreibG first last thread (.inl write.view.span.table) := by
  have oldTrace : (first.faeden thread).spur = before.spur :=
    congrArg World.spur beforeWorld
  have newTrace : (last.faeden thread).spur =
      .zugriff write.view.span.table true resources before.haelt :: before.spur := by
    change (last.weltVon thread).spur = _
    rw [afterWorld]
    rfl
  have delta : (last.faeden thread).spur =
      [Ereignis.zugriff write.view.span.table true resources before.haelt] ++
        (first.faeden thread).spur := by
    rw [newTrace, oldTrace]
    rfl
  have access : (Sum.inl write.view.span.table, true) ∈ zugriffe first last thread := by
    rw [zugriffe_ereignisse, ereignisse_eq delta]
    exact List.mem_cons_self ..
  exact ⟨Or.inl ⟨true, access⟩, Or.inl access⟩

/-!
The unresolved source-scope boundary is explicit below. Neither SimRel nor
borrow_sim obtains these obligations from two distinct frame numbers.

The caller must construct the actual canonical invocation push, identify the
receipt's lender/borrower with its activation serials, and connect the linear
source move to the actual resource inventories on both sides. The world
equality restricts this boundary to pushes with no ordinary memory/trace
effects. A general push that evaluates reading arguments or enters locks
needs an additional replay of those effects; no such replay is inferred here.

The existing ownerLedgerOf identity fold is deliberately not identified with
the changed loan ledger. Establishing this boundary at every admitted view
scope (and the matching return on both channels) remains checker/G integration.
-/

/-- Obligations for turning the ledger-level borrow into an actual source G
    push. This structure names the remaining premises; no existence theorem
    for arbitrary source scopes is claimed. -/
structure BorrowScopePremises {D : Deklaration} {P I : Type}
    (a : Authority D) (c : Context D P I) (receipt : ViewResult a c)
    (program : Programm D) (oracle : Orakel D) (passes : Nat)
    (first last : RufMaschineG D) where
  invocation : OwnerInvocation D
  push : invocation.Push program oracle passes first last
  caller : invocation.caller = c.frame
  borrower : invocation.frame = receipt.view.borrower
  linear : LinearContextStep a c (some receipt.view) receipt.next
  beforeBindings : ∀ resource ∈ OwnerBindings.resources (D := D) linear.before,
    resource ∈ (first.faeden invocation.thread).kopf.rest.2.2.1
  afterBindings : ∀ resource ∈ OwnerBindings.resources (D := D) linear.after,
    resource ∈ (last.faeden invocation.thread).kopf.rest.2.2.1
  world : last.weltVon invocation.thread = first.weltVon invocation.thread
  heldBefore : HeldIn (first.faeden invocation.thread).kopf.rest.2.2.1
    (first.weltVon invocation.thread).haelt
  heldAfter : HeldIn (last.faeden invocation.thread).kopf.rest.2.2.1
    (last.weltVon invocation.thread).haelt

/-- Under the explicit scope boundary the two borrow operations coincide.
    SpurInv survives because the acting trace is unchanged and the G step
    leaves every other thread alone. HeldIn and the source binding
    correspondence remain explicit obligations of that boundary. -/
theorem borrow_scope_sim {space : Space D} (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) (receipt : ViewResult a c)
    (produced : ram_view a c start length rights borrower = .ok receipt)
    {program : Programm D} {oracle : Orakel D} {passes : Nat}
    {first last : RufMaschineG D}
    (scope : BorrowScopePremises a c receipt program oracle passes first last)
    (simulation : SimRel a c (first.weltVon scope.invocation.thread))
    (invariant : SpurInv first) :
    RufSchrittG program oracle passes first scope.invocation.thread last ∧
    scope.push.borrow a.names c.owners a.token = some receipt.next.owners ∧
    SimRel a receipt.next (last.weltVon scope.invocation.thread) ∧ SpurInv last ∧
    HeldIn (last.faeden scope.invocation.thread).kopf.rest.2.2.1
      (last.weltVon scope.invocation.thread).haelt := by
  have preserved : SpurInv last := by
    intro thread
    by_cases same : thread = scope.invocation.thread
    · subst thread
      have trace : (last.faeden scope.invocation.thread).spur =
          (first.faeden scope.invocation.thread).spur := congrArg World.spur scope.world
      rw [trace]
      exact invariant _
    · rw [rufSchrittG_fremd scope.push.step thread same]
      exact invariant thread
  refine ⟨scope.push.step, ?_, ?_, preserved, scope.heldAfter⟩
  · change OwnerState.borrow a.names c.owners scope.invocation.caller
      scope.invocation.frame a.token = some receipt.next.owners
    rw [scope.caller, scope.borrower]
    exact receipt.borrowed
  · rw [scope.world]
    exact (borrow_sim simulation start length rights borrower receipt produced).1

end Gabbro.Grammatik.LowLevel
