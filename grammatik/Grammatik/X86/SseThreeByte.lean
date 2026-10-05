/-
  File:      Grammatik/X86/SseThreeByte.lean
  Subject:   SSSE3 three-byte forms over the 0F 38 / 0F 3A escapes,
    connected to the coherent machine and the capstone chain.

  Lane 1369: admitted register-direct XMM rows only -- PSHUFB
  (`66 0F 38 00 /r`), PABSB/W/D (`66 0F 38 1C/1D/1E /r`) and PALIGNR
  (`66 0F 3A 0F /r ib`). Canonical REX (`64 + 4*R + B`, W=0/X=0) is
  required, exactly like the accepted `VectorCodec` rows. Semantics
  reuse the accepted lane vocabulary (`laneNat`/`vecMk`, `sVal` for
  the PABS sign); no evaluator is redefined. Memory ModRM forms,
  MMX (NP) forms, REX.W forms and every other third byte stay
  refused (see CUTS). Silicon provenance: Intel SDM 325462-093US
  (Sep 2026), clone-local `.tmp/HARDWARE-REFERENCES/`
  `intel-instruction-reference.txt`.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Kern.Ganzzahl
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Admitted SSSE3 register forms: shuffle, packed absolute value at
    8/16/32 bits, and align-right with an immediate byte count. -/
inductive SseThreeOp where
  | pshufbRR (dst src : XmmReg)
  | pabsBRR (dst src : XmmReg)
  | pabsWRR (dst src : XmmReg)
  | pabsDRR (dst src : XmmReg)
  | palignrRR (dst src : XmmReg) (imm : Byte)
  deriving DecidableEq, Repr

/-- Escape byte after `0F`: `0F 38` for shuffle/abs, `0F 3A`
    for align-right (PALIGNR lives in the `0F 3A` map, SDM Vol. 2B
    4-216: `66 0F 3A 0F /r ib`). -/
def sseThreeEscape : SseThreeOp → Nat
  | .pshufbRR _ _ => 56
  | .pabsBRR _ _ => 56
  | .pabsWRR _ _ => 56
  | .pabsDRR _ _ => 56
  | .palignrRR _ _ _ => 58

/-- Third opcode byte: `00` PSHUFB (SDM 4-422), `1C/1D/1E`
    PABSB/W/D (SDM 4-176), `0F` PALIGNR. -/
def sseThreeThird : SseThreeOp → Nat
  | .pshufbRR _ _ => 0
  | .pabsBRR _ _ => 28
  | .pabsWRR _ _ => 29
  | .pabsDRR _ _ => 30
  | .palignrRR _ _ _ => 15

/-- Canonical REX byte for one form (W=0, X=0, always emitted, exactly
    like the accepted `vectorRex`). -/
def sseThreeRex : SseThreeOp → Byte
  | .pshufbRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pabsBRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pabsWRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pabsDRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .palignrRR dst src _ => natByte (64 + 4 * xmmHigh dst + xmmHigh src)

/-- Canonical byte encoding: REX, `66`, `0F`, escape, third byte,
    register-direct ModRM (mod=3, reg=dst, r/m=src), plus the imm8 of
    PALIGNR. 6 bytes, 7 for PALIGNR. -/
def encodeSseThree : SseThreeOp → List Byte
  | op@(.pshufbRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsBRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsWRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsDRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.palignrRR dst src imm) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src), imm]

/-- Every canonical encoding without an immediate is 6 bytes. -/
theorem encodeSseThree_len6 (dst src : XmmReg) :
    (encodeSseThree (.pshufbRR dst src)).length = 6 := rfl

/-- Every canonical PALIGNR encoding is 7 bytes. -/
theorem encodeSseThree_len7 (dst src : XmmReg) (imm : Byte) :
    (encodeSseThree (.palignrRR dst src imm)).length = 7 := rfl

/-- The old capstone chain refuses the canonical PSHUFB bytes. -/
theorem kap_weist_pshufb_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PABSB bytes. -/
theorem kap_weist_pabsb_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 28, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PABSW bytes. -/
theorem kap_weist_pabsw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 29, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PABSD bytes. -/
theorem kap_weist_pabsd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 30, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PALIGNR bytes. -/
theorem kap_weist_palignr_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200, natByte 4] = none := by
  decide

/-! ## 2. Canonical decoder.

  The decoder parses bytes, never encode-equality. Only the canonical
  REX prefix (`64 + 4*R + B`: W=0, X=0), then `66`, `0F`, the escape
  (`38`/`3A`), the third byte, and a register-direct ModRM (mod=3,
  reg=dst, r/m=src) are admitted; PALIGNR takes one trailing imm8.
  Anything else refuses with `none`. -/

/-- A decoded three-byte form: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure SseThreeDec where
  op : SseThreeOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Decode one register-direct ModRM byte after the admitted prefix,
    escape and third byte. PALIGNR reads its imm8 behind the ModRM. -/
def decodeSseThreeModrm (esc opByte rBit bBit : Nat) :
    List Byte → Option (SseThreeOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src =>
        match esc, opByte with
        | 56, 0 => some ((.pshufbRR dst src), rest)
        | 56, 28 => some ((.pabsBRR dst src), rest)
        | 56, 29 => some ((.pabsWRR dst src), rest)
        | 56, 30 => some ((.pabsDRR dst src), rest)
        | 58, 15 =>
          match rest with
          | [] => none
          | imm :: rest2 => some ((.palignrRR dst src imm), rest2)
        | _, _ => none
      | _, _ => none
    else none

/-- Decode after the canonical REX prefix: `66`, then `0F`, then the
    escape byte (`38`/`3A`), the third byte, then ModRM. -/
def decodeSseThreeNach (rBit bBit : Nat) :
    List Byte → Option (SseThreeOp × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 102 then
      match rest with
      | [] => none
      | p2 :: rest2 =>
        if byteNat p2 == 15 then
          match rest2 with
          | [] => none
          | esc :: rest3 =>
            if byteNat esc == 56 || byteNat esc == 58 then
              match rest3 with
              | [] => none
              | op :: rest4 =>
                decodeSseThreeModrm (byteNat esc) (byteNat op)
                  rBit bBit rest4
            else none
        else none
    else none

/-- Top-level three-byte decode: the REX prefix selects the extension
    bits; anything without a canonical REX refuses. The decoded length
    is the canonical encoding length of the decoded form. -/
def decodeSseThree : List Byte → Option (SseThreeDec × List Byte)
  | [] => none
  | r :: tail =>
    let nach (rBit bBit : Nat) :=
      match decodeSseThreeNach rBit bBit tail with
      | some (op, rest) =>
        some ((⟨op, (encodeSseThree op).length⟩ : SseThreeDec), rest)
      | none => none
    match byteNat r with
    | 64 => nach 0 0
    | 65 => nach 0 1
    | 68 => nach 1 0
    | 69 => nach 1 1
    | _ => none

/-- Round trip for PSHUFB, over any suffix. -/
theorem roundtrip_pshufb (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pshufbRR dst src) ++ suffix) =
      some ((⟨.pshufbRR dst src,
        (encodeSseThree (.pshufbRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PABSB, over any suffix. -/
theorem roundtrip_pabsb (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pabsBRR dst src) ++ suffix) =
      some ((⟨.pabsBRR dst src,
        (encodeSseThree (.pabsBRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PABSW, over any suffix. -/
theorem roundtrip_pabsw (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pabsWRR dst src) ++ suffix) =
      some ((⟨.pabsWRR dst src,
        (encodeSseThree (.pabsWRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PABSD, over any suffix. -/
theorem roundtrip_pabsd (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pabsDRR dst src) ++ suffix) =
      some ((⟨.pabsDRR dst src,
        (encodeSseThree (.pabsDRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PALIGNR, over any suffix. -/
theorem roundtrip_palignr (dst src : XmmReg) (imm : Byte)
    (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.palignrRR dst src imm) ++ suffix) =
      some ((⟨.palignrRR dst src imm,
        (encodeSseThree (.palignrRR dst src imm)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every covered row, over any suffix.
    The decoded length is the canonical encoding length. -/
theorem roundtripSseThree (op : SseThreeOp) (suffix : List Byte) :
    decodeSseThree (encodeSseThree op ++ suffix) =
      some ((⟨op, (encodeSseThree op).length⟩ : SseThreeDec), suffix) := by
  cases op with
  | pshufbRR dst src => exact roundtrip_pshufb dst src suffix
  | pabsBRR dst src => exact roundtrip_pabsb dst src suffix
  | pabsWRR dst src => exact roundtrip_pabsw dst src suffix
  | pabsDRR dst src => exact roundtrip_pabsd dst src suffix
  | palignrRR dst src imm => exact roundtrip_palignr dst src imm suffix

/-- A memory ModRM (mod≠3) is refused: only register forms are covered. -/
theorem sseThree_nichts_speicher :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 8] = none := rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem sseThree_nichts_kurz :
    decodeSseThree [natByte 64, natByte 102] = none := rfl

/-- A wrong escape (`0F 39`) is refused. -/
theorem sseThree_nichts_escape :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 57,
      natByte 0, natByte 200] = none := rfl

/-- MOVBE (`0F 38 F0`) is refused: a different family owns it. -/
theorem sseThree_nichts_movbe :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 200] = none := rfl

/-- An MMX (NP, no `66`) form is refused: only the `66` XMM rows are covered. -/
theorem sseThree_nichts_mmx :
    decodeSseThree [natByte 15, natByte 56, natByte 28,
      natByte 200] = none := rfl

/-- A REX.W form is refused: only the canonical W=0 REX is admitted
    (silicon ignores REX.W here; the canonical subset does not cover it). -/
theorem sseThree_nichts_rexw :
    decodeSseThree [natByte 72, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := rfl

/-- PALIGNR without its imm8 is refused. -/
theorem sseThree_nichts_ohne_imm :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200] = none := rfl

/-- Another `0F 3A` third byte (BLENDVPS `0F 3A 14`) is refused. -/
theorem sseThree_nichts_blendv :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 20, natByte 200, natByte 0] = none := rfl

end Gabbro.Grammatik.X86
