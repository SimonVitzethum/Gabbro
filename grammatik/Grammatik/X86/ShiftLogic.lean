/-
  File:      Grammatik/X86/ShiftLogic.lean
  Subject:   Shift/logic extension helpers over the canonical words (lane 337).

  Extension helpers for the SAME x86-64 target (WORK-ALLOCATION A3): NEG plus
  per-operation flag evidence for SHL/SHR/SAR/AND/OR/NOT/NEG with the
  architectural count mask (`schiebeZaehler` from `Ganzzahl.lean`), width-
  correct flag snapshots, the signed-division-vs-shift refusal and the float
  `x - x -> 0` refusal. Value operations (`shlB`/`shrB`/`sarB`/`andB`/`orB`/
  `notB`, `and64`/`or64`) and the validity relations (`SchiebeGueltig`,
  `LogikGueltig`) are REUSED from `Ganzzahl.lean`, carry/overflow
  characterisation from `FlagBeweis.lean`; nothing is redefined here. This
  file does NOT extend `Befehl` and does NOT change `schritt` (the 14 pilot
  forms are untouched); it exposes exactly how a future shift/logic
  instruction form must present its evidence (one `SchiebeNachweis` per
  shift, one width-correct flag snapshot per logic op).
-/
import Grammatik.X86.Ganzzahl
import Grammatik.X86.FlagBeweis
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Width-truncated NEG (two's complement): `0 - x` at width `b`. -/
def negW (b : Breite) (x : Wort) : Wort := subB b 0 x

/- CUTS:
   Shift/logic extension skeleton only: NEG value helper present, flag
   evidence, count-period pins, signed-division-vs-shift refusal, float
   refusal, memory witness and per-op flag facts are open. No `Befehl`
   extension, no `schritt` change, no encoding/decoding, no TSO bridge,
   no source correspondence, no cost transfer is claimed here. Count-mask
   widths (6 bits at 64, 5 bits narrow), NEG AF and shift CF/OF corners
   are stated executable semantics, not verified against silicon.
-/

#print axioms negW

end Gabbro.Grammatik.X86
