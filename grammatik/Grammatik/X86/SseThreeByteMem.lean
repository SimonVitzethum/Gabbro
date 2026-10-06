/-
  File:      Grammatik/X86/SseThreeByteMem.lean
  Subject:   Memory operands, MMX and REX.W forms of the SSSE3 three-byte
    maps over the 0F 38 / 0F 3A escapes.

  Lane 1377: Lane 1369 admitted register-direct XMM rows only
  (`SseThreeByte.lean`: PSHUFB `66 0F 38 00 /r`, PABSB/W/D
  `66 0F 38 1C/1D/1E /r`, PALIGNR `66 0F 3A 0F /r ib`). This file adds
  the three refused classes: memory-ModRM sources (ModRM with SIB,
  RIP-relative, disp8/disp32 through the accepted `AddressEncoding`
  vocabulary), MMX no-prefix forms (`NP 0F 38 ...`, `NP 0F 3A 0F`),
  and REX.W forms (silicon ignores REX.W on these rows). Semantics
  reuse the accepted lane vocabulary (`vecPabs`/`vecPshufb`/
  `vecPalignr`, never redefined); memory moves through the accepted
  `concLoad` TSO events. Silicon provenance: Intel SDM 325462-093US
  (Sep 2026), clone-local `.tmp/HARDWARE-REFERENCES/`
  `intel-instruction-reference.txt` (PABS 4-176, PALIGNR 4-216,
  PSHUFB 4-422).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Speicher.AddressEncoding
import Grammatik.X86.Befehle.Sse.SseThreeByte
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution
import Grammatik.X86.Flags.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- MMX registers mm0-mm7. Architecturally these alias the x87 stack;
    the coherent machine carries no MMX file, so MMX steps stay
    value-level in this file (see CUTS). -/
inductive MmxReg where
  | mm0 | mm1 | mm2 | mm3 | mm4 | mm5 | mm6 | mm7
  deriving DecidableEq, Repr

/-- Architectural MMX code: mm0=0 through mm7=7. -/
def mmCode : MmxReg → Nat
  | .mm0 => 0 | .mm1 => 1 | .mm2 => 2 | .mm3 => 3
  | .mm4 => 4 | .mm5 => 5 | .mm6 => 6 | .mm7 => 7

/-- Three-bit code back to an MMX register; extension bits are refused
    (under-admission: silicon has no mm8-mm15). -/
def codeMmx : Nat → Option MmxReg
  | 0 => some .mm0 | 1 => some .mm1 | 2 => some .mm2 | 3 => some .mm3
  | 4 => some .mm4 | 5 => some .mm5 | 6 => some .mm6 | 7 => some .mm7
  | _ => none

end Gabbro.Grammatik.X86
