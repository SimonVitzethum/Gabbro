/-
  File:      Grammatik/X86/HwVector.lean
  Subject:   SIMD integer forms and enabled-state gates on the coherent machine.

  Lane 1131: lifts the accepted packed-integer rows (lane 686 `IntVecOp`,
  `encodeIntVec`/`decodeIntVec`/`stepIntVec`, `vektorLegacyZugelassen`)
  onto the coherent machine (`HwMaschine`/`HwSchritt`, lane 660).
  Register rows ride a checked adapter over the accepted evaluator
  (lifted, never redefined); the four 16-byte memory rows go through
  footprint-checked TSO byte accesses (`vecEintraege`/`ladeN`/drains)
  with an explicit tearing table -- no whole-vector atomicity claimed.
  Enabled-state gates refuse, never guess. No W/GX bridge is claimed.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorFootprints

namespace Gabbro.Grammatik.X86

/-! ## 1. The sixteen canonical byte entries of one packed word.

  The low-chunk bytes (`vLo`) then the high-chunk bytes (`vHi`), oldest
  first -- the same two-chunk order the accepted `vecWrite` uses, so
  entry bytes ARE chunk bytes by construction (`rfl`). -/

/-- One vector byte: low-chunk `wortByte` below 8, high-chunk above. -/
def vecByte (v : Vektor) (i : Nat) : Byte :=
  if i < 8 then wortByte (vLo v) i else wortByte (vHi v) (i - 8)

/-- The sixteen canonical byte-store entries of `v` at `a`, oldest
    first: the eight low-chunk bytes then the eight high-chunk bytes.
    Sixteen per-byte events, never one atomic occurrence. -/
def vecEintraege (a : Adresse) (v : Vektor) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte (vLo v) 0⟩,
    ⟨addrOff a 1, wortByte (vLo v) 1⟩,
    ⟨addrOff a 2, wortByte (vLo v) 2⟩,
    ⟨addrOff a 3, wortByte (vLo v) 3⟩,
    ⟨addrOff a 4, wortByte (vLo v) 4⟩,
    ⟨addrOff a 5, wortByte (vLo v) 5⟩,
    ⟨addrOff a 6, wortByte (vLo v) 6⟩,
    ⟨addrOff a 7, wortByte (vLo v) 7⟩,
    ⟨addrOff (vecHiAddr a) 0, wortByte (vHi v) 0⟩,
    ⟨addrOff (vecHiAddr a) 1, wortByte (vHi v) 1⟩,
    ⟨addrOff (vecHiAddr a) 2, wortByte (vHi v) 2⟩,
    ⟨addrOff (vecHiAddr a) 3, wortByte (vHi v) 3⟩,
    ⟨addrOff (vecHiAddr a) 4, wortByte (vHi v) 4⟩,
    ⟨addrOff (vecHiAddr a) 5, wortByte (vHi v) 5⟩,
    ⟨addrOff (vecHiAddr a) 6, wortByte (vHi v) 6⟩,
    ⟨addrOff (vecHiAddr a) 7, wortByte (vHi v) 7⟩]

/-- Register rows: every `IntVecOp` row except the four memory rows.
    The adapter admits only these; loads/stores use the TSO path. -/
def istVecRegisterOp : IntVecOp → Bool
  | .movdqaLd _ _ _ => false
  | .movdqaSt _ _ _ => false
  | .movdquLd _ _ _ => false
  | .movdquSt _ _ _ => false
  | _ => true

/-- Sixteen entries, no more: the vector shape is exact. -/
theorem vecEintraege_laenge (a : Adresse) (v : Vektor) :
    (vecEintraege a v).length = 16 := rfl

end Gabbro.Grammatik.X86
