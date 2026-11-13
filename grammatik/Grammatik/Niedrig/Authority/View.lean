module

public import Grammatik.Niedrig.Authority.Model

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

inductive ViewFailure where
  | authority
  | bounds
  | memoryClass
  | permissions
  | alignment
  | mapping
  | initialization
  | conflictingLoan
  | escrow
  | noView
  deriving DecidableEq, Repr

/-- Executable local checks, separated from the boot/provider proof establishing
    that the ledger describes real memory. L1 refuses uninitialized views even
    for writes; L3 must add initialization tracking before relaxing this. -/
structure ViewAdmission {D : Deklaration} {P I : Type}
    (a : Authority D) (c : Context D P I) (v : View D) : Prop where
  span : v.span ∈ a.spans
  owner : v.span.owner = a.token.mark
  epoch : v.span.epoch = a.epoch ∧ v.epoch = a.epoch
  lender : v.lender = c.frame
  bounds : v.span.base ≤ v.base ∧ v.base + v.length ≤ v.span.base + v.span.length
  memoryClass : v.span.memoryClass = .ordinaryRam
  permissions : (v.rights.read = true ∨ v.rights.write = true) ∧
    (v.rights.read = true → v.span.rights.read = true) ∧
    (v.rights.write = true → v.span.rights.write = true) ∧
    v.rights.owner = v.span.rights.owner
  alignment : 0 < v.span.alignment ∧ v.base % v.span.alignment = 0 ∧
    v.length % v.span.alignment = 0
  mapping : v.span.mapped = true
  initialization : v.span.initialized = true
  compatible : ∀ w ∈ c.views, v.Compatible w ∧ w.Compatible v

/-- A checked receipt contains the actual existing owner-ledger transition.
    It creates no owner grant and retains the context's identity and stage. -/
structure ViewResult {D : Deklaration} {P I : Type}
    (a : Authority D) (c : Context D P I) where
  view : View D
  admission : ViewAdmission a c view
  owners : OwnerState D
  borrowed : OwnerState.borrow a.names c.owners c.frame view.borrower a.token = some owners

def ViewResult.next {D : Deklaration} {P I : Type} {a : Authority D}
    {c : Context D P I} (r : ViewResult a c) : Context D P I :=
  { owners := r.owners
    frame := r.view.borrower
    views := r.view :: c.views
    privilege := c.privilege
    interrupt := c.interrupt }

/-- Lift the admission proof into a data payload without changing its proposition.
    This helper is public because the exposed producer unfolds it. -/
def checkView {D : Deklaration} {P I : Type}
    (a : Authority D) (c : Context D P I) (v : View D) :
    Except ViewFailure (PLift (ViewAdmission a c v)) :=
  if ha : v.span ∈ a.spans ∧ v.span.owner = a.token.mark ∧
      (v.span.epoch = a.epoch ∧ v.epoch = a.epoch) ∧ v.lender = c.frame then
    if hb : v.span.base ≤ v.base ∧ v.base + v.length ≤ v.span.base + v.span.length then
      if hm : v.span.memoryClass = .ordinaryRam then
        if hp : (v.rights.read = true ∨ v.rights.write = true) ∧
            (v.rights.read = true → v.span.rights.read = true) ∧
            (v.rights.write = true → v.span.rights.write = true) ∧
            v.rights.owner = v.span.rights.owner then
          if hl : 0 < v.span.alignment ∧ v.base % v.span.alignment = 0 ∧
              v.length % v.span.alignment = 0 then
            if hmap : v.span.mapped = true then
              if hi : v.span.initialized = true then
                if hc : ∀ w ∈ c.views, v.Compatible w ∧ w.Compatible v then
                  Except.ok (PLift.up
                    { span := ha.1
                      owner := ha.2.1
                      epoch := ha.2.2.1
                      lender := ha.2.2.2
                      bounds := hb
                      memoryClass := hm
                      permissions := hp
                      alignment := hl
                      mapping := hmap
                      initialization := hi
                      compatible := hc })
                else Except.error ViewFailure.conflictingLoan
              else Except.error ViewFailure.initialization
            else Except.error ViewFailure.mapping
          else Except.error ViewFailure.alignment
        else Except.error ViewFailure.permissions
      else Except.error ViewFailure.memoryClass
    else Except.error ViewFailure.bounds
  else Except.error ViewFailure.authority

/-- The sole address-to-view producer. Selection is deterministic. An interior
    zero-length view is allowed but contains no byte; one-past selection fails.
    The borrow uses the existing exclusive, nested frame escrow: older views
    remain live but their lender frames are suspended until the inner return. -/
def ram_view {D : Deklaration} {P I : Type} {space : Space D}
    (a : Authority D) (c : Context D P I) (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) :
    Except ViewFailure (ViewResult a c) :=
  match a.spans.find? (fun s => decide (s.space = space ∧
      s.base ≤ start.byte ∧ start.byte < s.base + s.length)) with
  | none => Except.error ViewFailure.bounds
  | some span =>
    let view : View D :=
      { span := span
        base := start.byte
        length := length
        rights := rights
        lender := c.frame
        borrower := borrower
        epoch := a.epoch }
    match checkView a c view with
    | .error failure => Except.error failure
    | .ok admission =>
      match hb : OwnerState.borrow a.names c.owners c.frame borrower a.token with
      | none => Except.error ViewFailure.escrow
      | some owners => Except.ok
          { view := view
            admission := admission.down
            owners := owners
            borrowed := hb }

/-- Success corresponds to exactly the requested space, address, length,
    rights and borrower; the producer cannot silently substitute another span. -/
theorem ram_view_request {D : Deklaration} {P I : Type} {space : Space D}
    {a : Authority D} {c : Context D P I} {start : Address space} {length : Nat}
    {rights : DataRights} {borrower : ArenaOwnership.Frame} {r : ViewResult a c}
    (h : ram_view a c start length rights borrower = .ok r) :
    r.view.span.space = space ∧ r.view.base = start.byte ∧ r.view.length = length ∧
    r.view.rights = rights ∧ r.view.borrower = borrower := by
  unfold ram_view at h
  split at h
  · cases h
  · rename_i span selected
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        have chosen := List.find?_some selected
        have selectedSpan : span.space = space ∧ span.base ≤ start.byte ∧
            start.byte < span.base + span.length := by
          simpa only [decide_eq_true_eq] using chosen
        exact ⟨selectedSpan.1, rfl, rfl, rfl, rfl⟩

/-- Return the innermost view on every returning channel. Checking the actual
    current ledger rejects a stale receipt, another frame, or a second return.
    Memory written through ordinary carrier operations is never rolled back. -/
def returnView {D : Deklaration} {P I : Type} (a : Authority D)
    (c : Context D P I) : Except ViewFailure (Context D P I) :=
  match c.views with
  | [] => Except.error ViewFailure.noView
  | v :: rest =>
    if c.frame = v.borrower then
      match OwnerState.returnBorrow a.names c.owners c.frame v.lender a.token with
      | none => Except.error ViewFailure.escrow
      | some owners => Except.ok
          { c with
            owners := owners
            frame := v.lender
            views := rest }
    else Except.error ViewFailure.escrow

end Gabbro.Grammatik.LowLevel
