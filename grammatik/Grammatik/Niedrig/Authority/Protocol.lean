module

public import Grammatik.Niedrig.Authority.Preservation

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-- The authority protocol beside G: pure address evaluation, checked view
    production, and return. This relation executes no source program. Only the
    ram_view producer has a view result; none produces a reference or code value. -/
inductive AuthorityStep {D : Deklaration} {P I : Type} (a : Authority D) :
    Context D P I → Option (View D) → Context D P I → Prop where
  | address {c : Context D P I} {space : Space D} (e : AddressExpr space) :
      AuthorityStep a c none c
  | ram {c : Context D P I} {space : Space D} (start : Address space)
      (length : Nat) (rights : DataRights) (borrower : ArenaOwnership.Frame)
      (r : ViewResult a c) (produced : ram_view a c start length rights borrower = .ok r) :
      AuthorityStep a c (some r.view) r.next
  | restore {c c' : Context D P I} (returned : returnView a c = .ok c') :
      AuthorityStep a c none c'
  | refuse {c : Context D P I} {space : Space D} (start : Address space)
      (length : Nat) (rights : DataRights) (borrower : ArenaOwnership.Frame)
      (reason : ViewFailure) (refused : ram_view a c start length rights borrower = .error reason) :
      AuthorityStep a c none c
  | refuseReturn {c : Context D P I} (reason : ViewFailure)
      (refused : returnView a c = .error reason) : AuthorityStep a c none c

/-- The source resource interpretation of one returning protocol operation.
    The existing move consumes the old binder and preserves the exact mark
    multiset. Admission must supply this evidence at the actual G call/scope. -/
structure LinearContextStep {D : Deklaration} {P I : Type} (a : Authority D)
    (c : Context D P I) (result : Option (View D)) (c' : Context D P I) where
  protocol : AuthorityStep a c result c'
  before : OwnerBindings D.Marke
  after : OwnerBindings D.Marke
  source : Nat
  into : Nat
  bound : ({ binder := source
             mark := a.token.mark
             stage := a.token.stage } : OwnerBinding D.Marke) ∈ before
  moved : OwnerBindings.move before source into = some after

variable {D : Deklaration} {P I : Type} {a : Authority D}
  {c c' : Context D P I} {result : Option (View D)}

theorem authority_step_preserves (hc : c.Valid a) (step : AuthorityStep a c result c') :
    c'.Valid a := by
  cases step with
  | address => exact hc
  | ram start length rights borrower r produced => exact ram_view_preserves hc r
  | restore returned => exact returnView_preserves hc returned
  | refuse => exact hc
  | refuseReturn => exact hc

/-- Each checked request has an explicit success or refusal step. Refusal
    returns exactly the input context; it neither drops it nor gets stuck. -/
theorem ram_view_progress {space : Space D} (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) :
    match ram_view a c start length rights borrower with
    | .error reason => AuthorityStep a c none c
    | .ok r => AuthorityStep a c (some r.view) r.next := by
  cases h : ram_view a c start length rights borrower with
  | error reason => exact .refuse start length rights borrower reason h
  | ok r => exact .ram start length rights borrower r h

/-- Address arithmetic cannot introduce region authority. Every view result
    must come from a successful ram_view with its actual checked loan receipt. -/
theorem view_only_from_ram {view : View D} (step : AuthorityStep a c (some view) c') :
    ∃ (space : Space D) (start : Address space) (length : _) (rights : _) (borrower : _) (r : ViewResult a c),
      ram_view a c start length rights borrower = .ok r ∧ view = r.view ∧ c' = r.next := by
  cases step with
  | ram start length rights borrower r produced =>
      exact ⟨_, start, length, rights, borrower, r, produced, rfl, rfl⟩

/-- A retained view cannot acquire a stale epoch through a protocol operation.
    L6 must add revocation with a strict epoch change and quiescence. -/
theorem authority_step_live_epoch (hc : c.Valid a) (step : AuthorityStep a c result c')
    {view : View D} (live : view ∈ c'.views) : view.epoch = a.epoch :=
  ((authority_step_preserves hc step).2.2.2.1 view live).2.1

/-- Context authority is present after a returning operation and occurs in a
    source inventory with no duplicate nominal identities. No liveness claim
    about eventual return from an infinite computation is made. -/
theorem context_no_drop_or_duplication (step : LinearContextStep a c result c') :
    Res.marke a.token.mark a.token.stage ∈ OwnerBindings.resources (D := D) step.after ∧
    (step.after.map OwnerBinding.mark).Nodup :=
  ⟨(OwnerBindings.move_resource_perm (D := D) step.moved).mem_iff.mp
      (List.mem_map.mpr
        ⟨({ binder := step.source
            mark := a.token.mark
            stage := a.token.stage } : OwnerBinding D.Marke), step.bound, rfl⟩),
    (OwnerBindings.move_valid (Marke := D.Marke) step.moved).2⟩

end Gabbro.Grammatik.LowLevel
