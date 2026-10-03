/-
  File:      Grammatik/X86/CompactImm8Sub.lean
  Subject:   Connection for the REX.W 83/5 imm8 row (SUB r/m64, imm8).

  Lane 749: exactly one row -- REX.W + 83 /5 ib, SUB r/m64, imm8,
  register-direct (mod=3) -- with borrow/flag identity, pinned bytes
  and refusal outside the signed byte. Reuses the accepted producers
  (`IntegerHardwareForms`: encode/decode/step/fetch; `Wort.sub64`;
  canonical `Zustand`/`Speicher`; pilot `schritt` for the witness
  store). No new syntax, decoder, evaluator or state type.

  Manual: Intel SDM 325462-093US (Sep 2026), Vol. 2B 4-685/4-686,
  heading SUB-Subtract: row "REX.W + 83 /5 ib  SUB r/m64, imm8  MI
  Valid N.E. Subtract sign-extended imm8 from r/m64"; Operation
  DEST := (DEST - SRC); immediates sign-extended to the destination
  width; flags OF SF ZF AF PF CF set according to the result.
  Bundle: .tmp/HARDWARE-REFERENCES (REFERENCES.json + intel txt).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.IntegerHardwareForms

namespace Gabbro.Grammatik.X86

/-- Pinned compact bytes: `sub rax, 1` is REX.W, 83, E8, 01. -/
theorem pin_sub_kompakt :
    encodeIntHwImm (.subI .rax 1) =
      [natByte 72, natByte 131, natByte 232, natByte 1] := by
  decide

/- CUTS (skeleton; extended below):
   No hardware correspondence beyond the stated row; no source, TSO,
   cost or whole-image claim.
-/

#print axioms pin_sub_kompakt

end Gabbro.Grammatik.X86
