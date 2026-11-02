module

public import Grammatik.Kern.Syntax.Marken.Owner.Activation

@[expose] public section

namespace Gabbro.Grammatik.OwnerInvocation

variable {D : Deklaration}

/-- A loan is authorized by an actual canonical push, rather than by a pair
    of distinct ledger frame numbers alone. No source admission is implied. -/
def Push.borrow {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (_ : c.Push P O passes M M')
    (N : OwnerNamespace D) (s : OwnerState D) (t : OwnerToken D) : Option (OwnerState D) :=
  s.borrow N c.caller c.frame t

/-- A move uses the exact caller and callee identities of the canonical push. -/
def Push.transfer {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (_ : c.Push P O passes M M')
    (N : OwnerNamespace D) (s : OwnerState D) (t : OwnerToken D) :
    Option (OwnerState D × OwnerToken D) :=
  s.transfer N c.caller c.frame t

/-- Both canonical return channels discharge the same saved escrow. -/
def Return.restore {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (_ : c.Return P O passes M M')
    (N : OwnerNamespace D) (s : OwnerState D) (t : OwnerToken D) : Option (OwnerState D) :=
  s.returnBorrow N c.frame c.caller t

/-- Canonical entry and exit evidence compose with exact ledger restoration;
    nested execution may occur between the two machine edges. -/
theorem borrow_restore {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M0 M1 M2 M3 : RufMaschineG D}
    (push : c.Push P O passes M0 M1) (pop : c.Return P O passes M2 M3)
    {N : OwnerNamespace D} {s loaned : OwnerState D} {t : OwnerToken D}
    (valid : s.ledger.valid) (borrowed : push.borrow N s t = some loaned) :
    pop.restore N loaned t = some s :=
  OwnerState.borrow_return valid borrowed

end Gabbro.Grammatik.OwnerInvocation
