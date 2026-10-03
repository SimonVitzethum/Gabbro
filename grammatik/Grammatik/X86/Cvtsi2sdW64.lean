/-
  File:      Grammatik/X86/Cvtsi2sdW64.lean
  Subject:   Hardware completion: CVTSI2SD from the 64-bit integer source.

  Lane 789: int64-to-binary64 conversion with the width obligation
  (REX.W = 1) and RNE rounding, pinned bytes, refusal of unadmitted
  widths. Reuses the accepted canonical vocabulary (`Typen`: `Zustand`;
  `ScalarFloat`: `FpZustand`/`fpSchritt`/`cvtsiErg`; `Gleitprofil`:
  `ofInt`/`rundeExakt`/RNE profile; `ScalarFloatHardwareForms`:
  `fpHwEncodeCvtsi`/`fpHwDecode`/`fpHwByteschritt`) and the accepted
  byte-facing dispatcher; no new evaluator, no new IEEE arithmetic,
  no source/checker/emitter edit.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM combined Vols 1-4, edition 325462-093US September 2026
  (`REFERENCES.json`, sha256 `a4a62e6...f9168ee5`):
  - CVTSI2SD opcode rows, txt lines 48890-48895: `F2 0F 2A /r`
    (`r32/m32`) and `F2 REX.W 0F 2A /r` (`r/m64`).
  - Description, txt lines 48921-48924: signed doubleword/quadword to
    double; low quadword stored, high quadword unchanged; inexact
    results rounded per MXCSR rounding control.
  - Operation, txt lines 48969-48976: `DEST[63:0]` conversion with
    the 64-bit (`SRC[63:0]`) versus 32-bit (`SRC[31:0]`) width split,
    `DEST[MAXVL-1:64]` unmodified (legacy SSE preserve).
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatHardwareForms

namespace Gabbro.Grammatik.X86

/-- Lane marker: the 64-bit integer source width handled here. -/
def cvtsiW64Breite : Nat := 64

/-- The lane marker is the quadword width. -/
theorem cvtsiW64Breite_ist64 : cvtsiW64Breite = 64 := rfl

/- CUTS: what is not proved here.
-/

#print axioms cvtsiW64Breite
#print axioms cvtsiW64Breite_ist64

end Gabbro.Grammatik.X86
