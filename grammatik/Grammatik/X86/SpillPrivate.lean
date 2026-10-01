/-
  File:      Grammatik/X86/SpillPrivate.lean
  Subject:   TSO-side private-spill producer half (lane 343, plan B3).

  TSO-side freshness implies per-byte disjointness, which implies
  commutation of a private spill fill/reload with a concurrent disjoint
  access, over the canonical `Speicher`/`TSO`/`Stapel` vocabulary only.
  No second IR, no second evaluator, no SCFG consumer is invented here:
  the SCFG-side application waits for the accepted 287 interface.
  Spills are ordinary permission-checked accesses, never invisible.
  The refusal `Bool` is validator admission, not a hardware fault.
-/
import Grammatik.X86.Stapel
import Grammatik.X86.TSO
import Grammatik.X86.SpeicherKommutation

namespace Gabbro.Grammatik.X86

/-- Spill slot address: the canonical frame slot, no new address model. -/
def spillSlot (r : Rahmen) (idx : Nat) : Adresse := r.schlitzAddr idx

/-- TSO-side freshness: no buffered byte of any core touches the
    eight spill footprint bytes. -/
def SpillFrisch (s : TSOZustand) (r : Rahmen) (idx : Nat) : Prop :=
  ∀ (c : Nat) (e : TSOEintrag), e ∈ s.puffer c →
    ∀ k : Nat, k < 8 → e.addr ≠ addrOff (spillSlot r idx) k

/-- Concurrent separation: the spill slot footprint shares no byte
    with the foreign access footprint. -/
def GetrenntK (r : Rahmen) (idx : Nat) (fremd : Adresse) : Prop :=
  Disjunkt (spillSlot r idx) fremd

/-- Validator admission for a spill slot: refused when the address was
    taken, when the slot is named by an extent, or when it lies outside
    the frame. Plain `Bool`; `false` refuses, it faults no hardware. -/
def spillPrivatOk (adressGenommen perExtentBenannt imRahmen : Bool) : Bool :=
  (!adressGenommen) && (!perExtentBenannt) && imRahmen

/- CUTS:
    - Skeleton only: freshness/disjointness/commutation lemmas follow.
    - No SCFG consumer: the SCFG-side application waits for the accepted
      287 interface and is not invented here.
    - No hardware claim beyond the canonical TSO/frame/memory facts reused.
-/

#print axioms spillSlot
#print axioms spillPrivatOk

end Gabbro.Grammatik.X86
