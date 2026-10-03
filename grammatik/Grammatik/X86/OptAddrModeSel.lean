/-
  File:      Grammatik/X86/OptAddrModeSel.lean
  Subject:   Address-mode selection rule lemma (lane 893).

  DESIGN section 7 row: smallest-first addressing (disp0/disp8/disp32,
  SIB, RIP-relative for image constants) with revalidation after
  patching. Certificate: local rewrite record plus recomputed analysis
  citations. Failure case: any unrevalidated patch, any large
  displacement narrowed, any RIP-relative form outside image constants.

  Proved over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.AddressEncoding`
  with `adrEff`/`dispWortArt`/`passtIn8`/`kompaktArt`/`fussZugelassen`).
  No `ensures` is derived, no refusal becomes a warning, no faulting
  form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.AddressEncoding

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one address-mode selection
    site (DESIGN section 7 row): the displacement recomputedly fits one
    signed byte, the selected address recomputedly admits its eight-byte
    footprint without wrap, a RIP-relative choice cites an image-constant
    mapping, and the patched bytes were revalidated after patching. -/
structure AddrSelCert where
  kleinOk : Bool
  keinUmbruch : Bool
  ripBildOk : Bool
  nachgeprueft : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def addrSelZulassen (c : AddrSelCert) : Bool :=
  c.kleinOk && c.keinUmbruch && c.ripBildOk && c.nachgeprueft

/- CUTS:
    - Skeleton only: refusal pins, value/fault/observation lemmas, the
      `OptAddrModeSel_verbindung` rule lemma and its joint `_zeuge`
      companion are still to come (see the lane task).
-/

#print axioms addrSelZulassen

end Gabbro.Grammatik.X86
