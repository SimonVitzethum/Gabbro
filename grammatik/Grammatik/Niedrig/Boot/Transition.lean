module

public import Grammatik.Niedrig.Authority.Protocol

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-- A neutral declaration of the chosen firmware boundary. The first target
    binding supplies the 64-bit firmware-entry instance. Entry is the named
    environment contract; transition and root establishment are user logic.
    Stack/mapping/image reservations belong in these predicates, not defaults. -/
structure BootContract (D : Deklaration) (P I : Type) where
  «entry» : Authority D → Context D P I → Prop
  transition : Authority D → Context D P I → Authority D → Context D P I → Prop
  root : Authority D → Context D P I → Prop

/-- A software proof obligation, never a hardware assumption. This does not
    claim to prove boot code before the declared entry boundary. -/
def BootObligation {D : Deklaration} {P I : Type} (b : BootContract D P I) : Prop :=
  ∀ a c a' c', b.«entry» a c → b.transition a c a' c' → b.root a' c'

/-- Actual linear handoff through the existing fresh-grant operation. No view
    may escape it; callers hand ordinary views to roots under separate contracts.
    Retaining a privileged context is expressed by choosing the receiving frame. -/
structure HandoffResult {D : Deklaration} {P I : Type}
    (a : Authority D) (c : Context D P I) where
  into : ArenaOwnership.Frame
  privilege : P
  interrupt : I
  owners : OwnerState D
  token : OwnerToken D
  quiescent : c.views = []
  moved : OwnerState.transfer a.names c.owners c.frame into a.token = some (owners, token)

def HandoffResult.authority {D : Deklaration} {P I : Type} {a : Authority D}
    {c : Context D P I} (r : HandoffResult a c) : Authority D := { a with token := r.token }

def HandoffResult.next {D : Deklaration} {P I : Type} {a : Authority D}
    {c : Context D P I} (r : HandoffResult a c) : Context D P I :=
  { owners := r.owners
    frame := r.into
    views := []
    privilege := r.privilege
    interrupt := r.interrupt }

/-- The protocol permits a privilege handoff only under its declared software
    contract. Actual binding operations and their intermediate steps are L4/L5. -/
inductive BootStep {D : Deklaration} {P I : Type} (b : BootContract D P I) :
    Authority D → Context D P I → Authority D → Context D P I → Prop where
  | software {a : Authority D} {c c' : Context D P I} {result : Option (View D)}
      (step : AuthorityStep a c result c') : BootStep b a c a c'
  | handoff {a : Authority D} {c : Context D P I} (r : HandoffResult a c)
      (contract : b.transition a c r.authority r.next) :
      BootStep b a c r.authority r.next

/-- Firmware supplies a declared initial context, including checked authority
    and a live unloaned initial grant. No address literal is an origin rule. -/
structure FirmwareEntry {D : Deklaration} {P I : Type} (b : BootContract D P I)
    (a : Authority D) (c : Context D P I) : Prop where
  contract : b.«entry» a c
  valid : c.Valid a
  initial : c.owners.initial a.token.mark = true
  unspent : c.owners.spent a.token.mark = false
  owned : c.owners.owns a.names c.frame a.token
  noViews : c.views = []

end Gabbro.Grammatik.LowLevel
