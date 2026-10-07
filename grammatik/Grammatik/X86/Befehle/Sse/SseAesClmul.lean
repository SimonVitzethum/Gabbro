/-
  File:      Grammatik/X86/SseAesClmul.lean
  Subject:   AES-NI, PCLMULQDQ, MOVBE and the SSSE3 remainder over the
             coherent machine and the capstone chain.

  Lane 1373: admitted canonical rows only -- AESENC/AESENCLAST/AESDEC/
  AESDECLAST/AESIMC (`66 0F 38 DC/DD/DE/DF/DB /r`), AESKEYGENASSIST
  (`66 0F 3A DF /r ib`), PCLMULQDQ (`66 0F 3A 44 /r ib`), MOVBE
  (`0F 38 F0/F1`, 16/32/64-bit, base+disp memory only, no SIB), and
  PHADDW/PHADDD/PHSUBW/PHSUBD/PSIGNB/W/D/PMULHRSW (`66 0F 38
  01/02/05/06/08/09/0A/0B /r`). Register XMM rows reuse the accepted
  lane vocabulary (`laneNat`/`vecMk`); MOVBE reuses the accepted
  `bswap32`/`bswap64`, `concIssue`/`concLoad`, `mergeRegNarrow` and
  `adrEff`. Silicon provenance: Intel SDM 325462-093US (Sep 2026),
  clone-local `.tmp/HARDWARE-REFERENCES/`
  `intel-instruction-reference.txt`. No silicon correspondence is
  claimed beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Sse.SseThreeByte
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Befehle.Arithmetik.ByteSwap
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Speicher.AddressEncoding
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- MOVBE operand width: 16 (`66`), 32 (default), 64 (`REX.W`). -/
inductive MovbeWeite where
  | w16 | w32 | w64
  deriving DecidableEq, Repr

/-- MOVBE direction: `F0` loads (`r <- m`), `F1` stores (`m <- r`). -/
inductive MovbeRichtung where
  | lad | spei
  deriving DecidableEq, Repr

/-- MOVBE displacement: `kurz` is mod=01 with a sign-extended disp8,
    `lang` is mod=10 with a disp32. -/
inductive MovbeDisp where
  | kurz (d8 : Byte)
  | lang (d32 : BitVec 32)
  deriving DecidableEq, Repr

/-- Admitted family operations: five AES rounds, the key assist, the
    carry-less multiply, two MOVBE directions at three widths, and the
    eight SSSE3 remainder rows. All XMM rows are register-direct. -/
inductive AesClmulOp where
  | aesencRR (dst src : XmmReg)
  | aesenclastRR (dst src : XmmReg)
  | aesdecRR (dst src : XmmReg)
  | aesdeclastRR (dst src : XmmReg)
  | aesimcRR (dst src : XmmReg)
  | aeskeygenRR (dst src : XmmReg) (imm : Byte)
  | pclmulRR (dst src : XmmReg) (imm : Byte)
  | movbe (r : MovbeRichtung) (w : MovbeWeite) (reg base : Register)
    (d : MovbeDisp)
  | phaddwRR (dst src : XmmReg)
  | phadddRR (dst src : XmmReg)
  | phsubwRR (dst src : XmmReg)
  | phsubdRR (dst src : XmmReg)
  | psignbRR (dst src : XmmReg)
  | psignwRR (dst src : XmmReg)
  | psigndRR (dst src : XmmReg)
  | pmulhrswRR (dst src : XmmReg)
  deriving DecidableEq, Repr

/-- A decoded family form: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure AesClmulDec where
  op : AesClmulOp
  laenge : Nat
  deriving DecidableEq, Repr

/-! ## 1. Canonical encoder.

  XMM rows take the canonical REX (`64 + 4*R + B`: W=0, X=0, exactly
  like the accepted `vectorRex`), then `66`, `0F`, the escape
  (`38`/`3A`), the third byte, register-direct ModRM, and the imm8
  where the form has one. MOVBE rows take the canonical REX first
  (W selects 32/64-bit, X=0), then the optional `66` (16-bit only),
  `0F 38 F0/F1`, a base+disp ModRM (mod=01 with disp8, mod=10 with
  disp32, never SIB), and the displacement bytes. -/

/-- Escape byte after `0F`: `0F 38` for rounds/MOVBE/SSSE3 remainder,
    `0F 3A` for the key assist and the carry-less multiply. -/
def aesClmulEscape : AesClmulOp → Nat
  | .aeskeygenRR _ _ _ => 58
  | .pclmulRR _ _ _ => 58
  | _ => 56

/-- Third opcode byte (SDM Vol. 2A 3-33/3-45/3-51/3-57, Vol. 2B
    4-45/4-242/4-294/4-302/4-375/4-437). -/
def aesClmulThird : AesClmulOp → Nat
  | .aesencRR _ _ => 220
  | .aesenclastRR _ _ => 221
  | .aesdecRR _ _ => 222
  | .aesdeclastRR _ _ => 223
  | .aesimcRR _ _ => 219
  | .aeskeygenRR _ _ _ => 223
  | .pclmulRR _ _ _ => 68
  | .movbe .lad _ _ _ _ => 240
  | .movbe .spei _ _ _ _ => 241
  | .phaddwRR _ _ => 1
  | .phadddRR _ _ => 2
  | .phsubwRR _ _ => 5
  | .phsubdRR _ _ => 6
  | .psignbRR _ _ => 8
  | .psignwRR _ _ => 9
  | .psigndRR _ _ => 10
  | .pmulhrswRR _ _ => 11

/-- Canonical REX for an XMM row (W=0, X=0). -/
def aesClmulRex (dst src : XmmReg) : Byte :=
  natByte (64 + 4 * xmmHigh dst + xmmHigh src)

/-- Canonical REX for a MOVBE row (W selects 64-bit, X=0). -/
def movbeRex (w : MovbeWeite) (reg base : Register) : Byte :=
  match w with
  | .w64 => natByte (72 + 4 * regHigh reg + regHigh base)
  | _ => natByte (64 + 4 * regHigh reg + regHigh base)

/-- ModRM for a base+disp8 byte (mod=01, never SIB). -/
def modrmDisp8 (rl rm : Nat) : Byte := natByte (64 + 8 * (rl % 8) + rm % 8)

/-- Canonical byte encoding of an XMM row (6 bytes, 7 with imm8). -/
def encodeXmmRow (esc third : Nat) (dst src : XmmReg) : List Byte :=
  [aesClmulRex dst src, natByte 102, natByte 15, natByte esc,
    natByte third, modrmReg (xmmLow dst) (xmmLow src)]

/-- Canonical byte encoding of a MOVBE row. The list is flat (at
    most one trailing append for disp32): nested appends block
    definitional unfolding in decode round trips. Dispatch uses
    nested single matches only. -/
def encodeMovbeRow (r : MovbeRichtung) (w : MovbeWeite)
    (reg base : Register) (d : MovbeDisp) : List Byte :=
  let dirByte := match r with | .lad => 240 | .spei => 241
  match d with
  | .kurz d8 =>
    let modrm := modrmDisp8 (regLow reg) (regLow base)
    match w with
    | .w16 =>
      [movbeRex w reg base, natByte 102, natByte 15, natByte 56,
        natByte dirByte, modrm, d8]
    | _ =>
      [movbeRex w reg base, natByte 15, natByte 56,
        natByte dirByte, modrm, d8]
  | .lang d32 =>
    let modrm := modrmMem (regLow reg) (regLow base)
    match w with
    | .w16 =>
      [movbeRex w reg base, natByte 102, natByte 15, natByte 56,
        natByte dirByte, modrm] ++ leBytes32 d32
    | _ =>
      [movbeRex w reg base, natByte 15, natByte 56,
        natByte dirByte, modrm] ++ leBytes32 d32

/-- Canonical byte encoding of every admitted form. -/
def encodeAesClmul : AesClmulOp → List Byte
  | op@(.aesencRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.aesenclastRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.aesdecRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.aesdeclastRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.aesimcRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.aeskeygenRR dst src imm) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src ++ [imm]
  | op@(.pclmulRR dst src imm) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src ++ [imm]
  | .movbe r w reg base d => encodeMovbeRow r w reg base d
  | op@(.phaddwRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.phadddRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.phsubwRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.phsubdRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.psignbRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.psignwRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.psigndRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src
  | op@(.pmulhrswRR dst src) =>
    encodeXmmRow (aesClmulEscape op) (aesClmulThird op) dst src

/-! ## 2. The old chain refuses the new bytes.

  One closed pin per admitted shape: where the old chain already
  accepted a byte string, the new arm would shadow it. A failing pin
  is a finding (the row stays with the old chain), never a repair of
  the old chain. -/

theorem kap_weist_aesenc_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 220, natByte 192] = none := by
  decide

theorem kap_weist_aesenclast_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 221, natByte 192] = none := by
  decide

theorem kap_weist_aesdec_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 222, natByte 192] = none := by
  decide

theorem kap_weist_aesdeclast_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 223, natByte 192] = none := by
  decide

theorem kap_weist_aesimc_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 219, natByte 192] = none := by
  decide

theorem kap_weist_aeskeygen_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 223, natByte 192, natByte 0] = none := by
  decide

theorem kap_weist_pclmul_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 68, natByte 192, natByte 0] = none := by
  decide

theorem kap_weist_phaddw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 1, natByte 192] = none := by
  decide

theorem kap_weist_phaddd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 2, natByte 192] = none := by
  decide

theorem kap_weist_phsubw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 5, natByte 192] = none := by
  decide

theorem kap_weist_phsubd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 6, natByte 192] = none := by
  decide

theorem kap_weist_psignb_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 8, natByte 192] = none := by
  decide

theorem kap_weist_psignw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 9, natByte 192] = none := by
  decide

theorem kap_weist_psignd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 10, natByte 192] = none := by
  decide

theorem kap_weist_pmulhrsw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 11, natByte 192] = none := by
  decide

theorem kap_weist_movbe32_lad_kurz_zurueck :
    kapDecode [natByte 64, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] = none := by
  decide

theorem kap_weist_movbe32_lad_lang_zurueck :
    kapDecode [natByte 64, natByte 15, natByte 56,
      natByte 240, natByte 129, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

theorem kap_weist_movbe32_spei_kurz_zurueck :
    kapDecode [natByte 64, natByte 15, natByte 56,
      natByte 241, natByte 65, natByte 0] = none := by
  decide

theorem kap_weist_movbe16_lad_kurz_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] = none := by
  decide

theorem kap_weist_movbe64_lad_kurz_zurueck :
    kapDecode [natByte 72, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] = none := by
  decide

/-! ## 3. Canonical decoder.

  The decoder parses bytes, never encode-equality. Tree convention
  first: the canonical REX leads (`64/65/68/69` for W=0, `72/73/76/77`
  for W=1, X=0 always), then the optional `66`, then `0F`, the escape
  (`38`/`3A`), the third byte, and a ModRM. Register-direct ModRM
  (mod=3) serves the XMM rows; base+disp ModRM (mod=01 with disp8,
  mod=10 with disp32, never the SIB rm=4) serves MOVBE. Anything else
  refuses with `none`. -/

/-- Decode one register-direct ModRM byte for the XMM rows. Third
    bytes outside the admitted map refuse. -/
def decodeAesClmulModrmXmm (esc opByte rBit bBit : Nat) :
    List Byte → Option (AesClmulOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src =>
        match esc, opByte with
        | 56, 220 => some ((.aesencRR dst src), rest)
        | 56, 221 => some ((.aesenclastRR dst src), rest)
        | 56, 222 => some ((.aesdecRR dst src), rest)
        | 56, 223 => some ((.aesdeclastRR dst src), rest)
        | 56, 219 => some ((.aesimcRR dst src), rest)
        | 56, 1 => some ((.phaddwRR dst src), rest)
        | 56, 2 => some ((.phadddRR dst src), rest)
        | 56, 5 => some ((.phsubwRR dst src), rest)
        | 56, 6 => some ((.phsubdRR dst src), rest)
        | 56, 8 => some ((.psignbRR dst src), rest)
        | 56, 9 => some ((.psignwRR dst src), rest)
        | 56, 10 => some ((.psigndRR dst src), rest)
        | 56, 11 => some ((.pmulhrswRR dst src), rest)
        | 58, 223 =>
          match rest with
          | [] => none
          | imm :: rest2 => some ((.aeskeygenRR dst src imm), rest2)
        | 58, 68 =>
          match rest with
          | [] => none
          | imm :: rest2 => some ((.pclmulRR dst src imm), rest2)
        | _, _ => none
      | _, _ => none
    else none

/-- Decode one base+disp ModRM tail for a MOVBE row. Only mod=01
    (disp8) and mod=10 (disp32) arrive here; the SIB rm=4 refuses
    outright (the accepted `decodeMemC` shape, minus its SIB arm). -/
def decodeMovbeTail (dir : MovbeRichtung) (w : MovbeWeite)
    (rBit bBit reg rm : Nat) (kurz : Bool) :
    List Byte → Option (AesClmulOp × List Byte)
  | [] => none
  | b :: rest =>
    if rm == 4 then none
    else
      match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
      | some rr, some bb =>
        if kurz then
          some ((.movbe dir w rr bb (.kurz b)), rest)
        else
          match parseLe32 (b :: rest) with
          | some (d32, rest2) =>
            some ((.movbe dir w rr bb (.lang d32)), rest2)
          | none => none
      | _, _ => none

/-- Decode one base+disp ModRM byte for a MOVBE row: mod selects the
    displacement shape (the accepted `decodeCRex` shape: mod=01 with
    disp8, mod=10 with disp32; mod=00 and mod=11 refuse). -/
def decodeMovbeModrm (dir : MovbeRichtung) (w : MovbeWeite)
    (rBit bBit : Nat) : List Byte → Option (AesClmulOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 1 => decodeMovbeTail dir w rBit bBit reg rm true rest
    | 2 => decodeMovbeTail dir w rBit bBit reg rm false rest
    | _ => none

/-- Decode after REX and the optional `66`: `0F`, escape, third byte,
    then the operand. Without `66` only MOVBE 32/64-bit rows decode;
    with `66` the XMM rows (W must be 0) and MOVBE 16-bit decode.
    Dispatch uses `if` chains on direct byte projections only (never
    a pair-match on computed values). -/
def decodeAesClmulNach66 (has66 : Bool) (wBit rBit bBit : Nat) :
    List Byte → Option (AesClmulOp × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 15 then
      match rest with
      | [] => none
      | esc :: rest2 =>
        if byteNat esc == 56 then
          match rest2 with
          | [] => none
          | third :: rest3 =>
            if !has66 then
              if byteNat third == 240 then
                decodeMovbeModrm .lad
                  (if wBit == 1 then .w64 else .w32) rBit bBit rest3
              else if byteNat third == 241 then
                decodeMovbeModrm .spei
                  (if wBit == 1 then .w64 else .w32) rBit bBit rest3
              else none
            else if wBit == 1 then none
            else if byteNat third == 240 then
              decodeMovbeModrm .lad .w16 rBit bBit rest3
            else if byteNat third == 241 then
              decodeMovbeModrm .spei .w16 rBit bBit rest3
            else
              decodeAesClmulModrmXmm 56 (byteNat third)
                rBit bBit rest3
        else if byteNat esc == 58 then
          match rest2 with
          | [] => none
          | third :: rest3 =>
            decodeAesClmulModrmXmm 58 (byteNat third) rBit bBit rest3
        else none
    else none

/-- Decode after the canonical REX: the optional `66`, then the tail. -/
def decodeAesClmulNachRex (wBit rBit bBit : Nat) :
    List Byte → Option (AesClmulOp × List Byte)
  | [] => none
  | p :: rest =>
    if byteNat p == 102 then decodeAesClmulNach66 true wBit rBit bBit rest
    else decodeAesClmulNach66 false wBit rBit bBit (p :: rest)

/-- Top-level family decode: the canonical REX selects extension and
    width bits; anything without a canonical REX refuses. The decoded
    length is the canonical encoding length of the decoded form. -/
def decodeAesClmul : List Byte → Option (AesClmulDec × List Byte)
  | [] => none
  | r :: tail =>
    let nach (wBit rBit bBit : Nat) :=
      match decodeAesClmulNachRex wBit rBit bBit tail with
      | some (op, rest) =>
        some ((⟨op, (encodeAesClmul op).length⟩ : AesClmulDec), rest)
      | none => none
    match byteNat r with
    | 64 => nach 0 0 0
    | 65 => nach 0 0 1
    | 68 => nach 0 1 0
    | 69 => nach 0 1 1
    | 72 => nach 1 0 0
    | 73 => nach 1 0 1
    | 76 => nach 1 1 0
    | 77 => nach 1 1 1
    | _ => none

/-! ## 4. Round trips.

  Decoding inverts encoding on every covered row, over any suffix.
  The decoded length is the canonical encoding length. -/

theorem roundtrip_aesenc (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.aesencRR dst src) ++ suffix) =
      some ((⟨.aesencRR dst src,
        (encodeAesClmul (.aesencRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_aesenclast (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.aesenclastRR dst src) ++ suffix) =
      some ((⟨.aesenclastRR dst src,
        (encodeAesClmul (.aesenclastRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_aesdec (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.aesdecRR dst src) ++ suffix) =
      some ((⟨.aesdecRR dst src,
        (encodeAesClmul (.aesdecRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_aesdeclast (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.aesdeclastRR dst src) ++ suffix) =
      some ((⟨.aesdeclastRR dst src,
        (encodeAesClmul (.aesdeclastRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_aesimc (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.aesimcRR dst src) ++ suffix) =
      some ((⟨.aesimcRR dst src,
        (encodeAesClmul (.aesimcRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_phaddw (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.phaddwRR dst src) ++ suffix) =
      some ((⟨.phaddwRR dst src,
        (encodeAesClmul (.phaddwRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_phaddd (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.phadddRR dst src) ++ suffix) =
      some ((⟨.phadddRR dst src,
        (encodeAesClmul (.phadddRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_phsubw (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.phsubwRR dst src) ++ suffix) =
      some ((⟨.phsubwRR dst src,
        (encodeAesClmul (.phsubwRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_phsubd (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.phsubdRR dst src) ++ suffix) =
      some ((⟨.phsubdRR dst src,
        (encodeAesClmul (.phsubdRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_psignb (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.psignbRR dst src) ++ suffix) =
      some ((⟨.psignbRR dst src,
        (encodeAesClmul (.psignbRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_psignw (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.psignwRR dst src) ++ suffix) =
      some ((⟨.psignwRR dst src,
        (encodeAesClmul (.psignwRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_psignd (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.psigndRR dst src) ++ suffix) =
      some ((⟨.psigndRR dst src,
        (encodeAesClmul (.psigndRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_pmulhrsw (dst src : XmmReg) (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.pmulhrswRR dst src) ++ suffix) =
      some ((⟨.pmulhrswRR dst src,
        (encodeAesClmul (.pmulhrswRR dst src)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for AESKEYGENASSIST, over any suffix (imm8 opaque). -/
theorem roundtrip_aeskeygen (dst src : XmmReg) (imm : Byte)
    (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.aeskeygenRR dst src imm) ++ suffix) =
      some ((⟨.aeskeygenRR dst src imm,
        (encodeAesClmul (.aeskeygenRR dst src imm)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PCLMULQDQ, over any suffix (imm8 opaque). -/
theorem roundtrip_pclmul (dst src : XmmReg) (imm : Byte)
    (suffix : List Byte) :
    decodeAesClmul (encodeAesClmul (.pclmulRR dst src imm) ++ suffix) =
      some ((⟨.pclmulRR dst src imm,
        (encodeAesClmul (.pclmulRR dst src imm)).length⟩ : AesClmulDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for MOVBE with disp8, over any suffix (disp8 opaque),
    away from SIB bases (the decoder refuses rm=4, like the accepted
    compact `Disp0` rows refuse their special cases). -/
theorem roundtrip_movbe_kurz (r : MovbeRichtung) (w : MovbeWeite)
    (reg base : Register) (d8 : Byte) (suffix : List Byte)
    (hb1 : base ≠ .rsp) (hb2 : base ≠ .r12) :
    decodeAesClmul
      (encodeAesClmul (.movbe r w reg base (.kurz d8)) ++ suffix) =
      some ((⟨.movbe r w reg base (.kurz d8),
        (encodeAesClmul (.movbe r w reg base (.kurz d8))).length⟩ :
        AesClmulDec), suffix) := by
  cases r <;> cases w <;> cases reg <;> cases base <;>
    first | rfl | (exfalso; first | exact hb1 rfl | exact hb2 rfl)

/-- Intermediate unfolding of MOVBE-disp32 decode down to its
    `parseLe32` call (the CompactForms pattern: case-split registers,
    then the reused `parseLe32_leBytes32`). -/
theorem decodeAesClmul_movbe_lang_entfaltet (r : MovbeRichtung)
    (w : MovbeWeite) (reg base : Register) (d32 : BitVec 32)
    (suffix : List Byte)
    (hb1 : base ≠ .rsp) (hb2 : base ≠ .r12) :
    decodeAesClmul
      (encodeAesClmul (.movbe r w reg base (.lang d32)) ++ suffix) =
      (match parseLe32 (leBytes32 d32 ++ suffix) with
        | some (v, rest) =>
          some ((⟨.movbe r w reg base (.lang v),
            (encodeAesClmul (.movbe r w reg base (.lang v))).length⟩ :
            AesClmulDec), rest)
        | none => none) := by
  cases r <;> cases w <;> cases reg <;> cases base <;>
    first | rfl | (exfalso; first | exact hb1 rfl | exact hb2 rfl)

/-- Round trip for MOVBE with disp32, over any suffix. -/
theorem roundtrip_movbe_lang (r : MovbeRichtung) (w : MovbeWeite)
    (reg base : Register) (d32 : BitVec 32) (suffix : List Byte)
    (hb1 : base ≠ .rsp) (hb2 : base ≠ .r12) :
    decodeAesClmul
      (encodeAesClmul (.movbe r w reg base (.lang d32)) ++ suffix) =
      some ((⟨.movbe r w reg base (.lang d32),
        (encodeAesClmul (.movbe r w reg base (.lang d32))).length⟩ :
        AesClmulDec), suffix) := by
  rw [decodeAesClmul_movbe_lang_entfaltet _ _ _ _ _ _ hb1 hb2,
    parseLe32_leBytes32]

/-- Decoding inverts encoding on every covered row, over any suffix.
    The decoded length is the canonical encoding length. MOVBE rows
    are covered away from SIB bases. -/
theorem roundtripAesClmul (op : AesClmulOp) (suffix : List Byte)
    (hsib : ∀ (r : MovbeRichtung) (w : MovbeWeite) (reg base : Register)
      (d : MovbeDisp),
      op = .movbe r w reg base d → base ≠ .rsp ∧ base ≠ .r12) :
    decodeAesClmul (encodeAesClmul op ++ suffix) =
      some ((⟨op, (encodeAesClmul op).length⟩ : AesClmulDec), suffix) := by
  cases op with
  | aesencRR dst src => exact roundtrip_aesenc dst src suffix
  | aesenclastRR dst src => exact roundtrip_aesenclast dst src suffix
  | aesdecRR dst src => exact roundtrip_aesdec dst src suffix
  | aesdeclastRR dst src => exact roundtrip_aesdeclast dst src suffix
  | aesimcRR dst src => exact roundtrip_aesimc dst src suffix
  | aeskeygenRR dst src imm => exact roundtrip_aeskeygen dst src imm suffix
  | pclmulRR dst src imm => exact roundtrip_pclmul dst src imm suffix
  | movbe r w reg base d =>
    obtain ⟨hb1, hb2⟩ := hsib r w reg base d rfl
    cases d with
    | kurz d8 => exact roundtrip_movbe_kurz r w reg base d8 suffix hb1 hb2
    | lang d32 => exact roundtrip_movbe_lang r w reg base d32 suffix hb1 hb2
  | phaddwRR dst src => exact roundtrip_phaddw dst src suffix
  | phadddRR dst src => exact roundtrip_phaddd dst src suffix
  | phsubwRR dst src => exact roundtrip_phsubw dst src suffix
  | phsubdRR dst src => exact roundtrip_phsubd dst src suffix
  | psignbRR dst src => exact roundtrip_psignb dst src suffix
  | psignwRR dst src => exact roundtrip_psignw dst src suffix
  | psigndRR dst src => exact roundtrip_psignd dst src suffix
  | pmulhrswRR dst src => exact roundtrip_pmulhrsw dst src suffix

/-! ## 5. Planted decoder refusals.

  Every unsupported shape refuses explicitly: memory ModRM on an
  XMM-only row, truncated prefixes, wrong escapes, MMX (NP) forms,
  REX.W on XMM rows, `66`+REX.W, mod=00/11 and SIB on MOVBE, missing
  immediates, the CRC32 (`F2`) neighbour, and the sibling SSSE3 rows
  (disjointness with the accepted `SseThreeByte` arm). -/

/-- A memory ModRM (mod≠3) is refused on an XMM-only row. -/
theorem aesClmul_nichts_speicher :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 220, natByte 8] = none := rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem aesClmul_nichts_kurz :
    decodeAesClmul [natByte 64, natByte 102] = none := rfl

/-- A wrong escape (`0F 39`) is refused. -/
theorem aesClmul_nichts_escape :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 57,
      natByte 220, natByte 192] = none := rfl

/-- An MMX (NP, no `66`) AES row is refused. -/
theorem aesClmul_nichts_mmx :
    decodeAesClmul [natByte 15, natByte 56, natByte 220,
      natByte 192] = none := rfl

/-- A REX.W form is refused on XMM rows. -/
theorem aesClmul_nichts_rexw :
    decodeAesClmul [natByte 72, natByte 102, natByte 15, natByte 56,
      natByte 220, natByte 192] = none := rfl

/-- `66`+REX.W is refused (no canonical width owns it). -/
theorem aesClmul_nichts_66w :
    decodeAesClmul [natByte 72, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] = none := rfl

/-- MOVBE mod=00 (no displacement) is refused. -/
theorem aesClmul_nichts_mod00 :
    decodeAesClmul [natByte 64, natByte 15, natByte 56,
      natByte 240, natByte 1, natByte 0] = none := rfl

/-- MOVBE mod=11 is refused: MOVBE has no register-register form. -/
theorem aesClmul_nichts_mod11 :
    decodeAesClmul [natByte 64, natByte 15, natByte 56,
      natByte 240, natByte 193, natByte 0] = none := rfl

/-- MOVBE with a SIB byte (rm=4) is refused. -/
theorem aesClmul_nichts_sib :
    decodeAesClmul [natByte 64, natByte 15, natByte 56,
      natByte 240, natByte 68, natByte 0] = none := rfl

/-- PCLMULQDQ without its imm8 is refused. -/
theorem aesClmul_nichts_ohne_imm :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 68, natByte 192] = none := rfl

/-- The CRC32 (`F2`) neighbour is refused. -/
theorem aesClmul_nichts_crc32 :
    decodeAesClmul [natByte 242, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] = none := rfl

/-- An AES row without `66` is refused (only MOVBE owns it). -/
theorem aesClmul_nichts_aes_ohne_66 :
    decodeAesClmul [natByte 64, natByte 15, natByte 56,
      natByte 220, natByte 192] = none := rfl

/-- Another `0F 3A` third byte is refused on the imm path. -/
theorem aesClmul_nichts_3a_fremd :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 221, natByte 192, natByte 0] = none := rfl

/-- A BLENDVPS `0F 3A` row is refused. -/
theorem aesClmul_nichts_blendv :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 20, natByte 200, natByte 0] = none := rfl

/-- The sibling PSHUFB row is refused (disjoint arms). -/
theorem aesClmul_nichts_pshufb :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := rfl

/-- The sibling PALIGNR row is refused (disjoint arms). -/
theorem aesClmul_nichts_palignr :
    decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200, natByte 4] = none := rfl

/-! ## 6. MOVBE value semantics.

  The swap reuses the accepted `bswap32`/`bswap64` (`ByteSwap.lean`,
  themselves linked to the accepted `bswap32n`/`bswap64n` of
  `Grammatik.Bits`); only the 16-bit swap is new, with the same
  shape. Loads merge through the accepted `mergeRegNarrow` at the
  step (8/16-bit writes merge into the low bits, 32-bit writes
  zero-extend, 64-bit writes whole), and stores issue the low swapped
  bytes through the accepted `entriesOf`. -/

/-- MOVBE width as an architectural width. -/
def movbeBreite : MovbeWeite → Breite
  | .w16 => .b16
  | .w32 => .b32
  | .w64 => .b64

/-- 16-bit byte reversal with zero extension (the `bswap16n` shape:
    the low two bytes reverse, the upper six clear). -/
def bswap16 (v : Wort) : Wort :=
  BitVec.ofNat 64 ((wortByte v 1).toNat + (wortByte v 0).toNat * 256)

/-- The MOVBE byte swap at the row width (an involution on the low
    bytes; the operation pseudocode of SDM Vol. 2B 4-45). -/
def movbeTausch : MovbeWeite → Wort → Wort
  | .w16, v => bswap16 v
  | .w32, v => bswap32 v
  | .w64, v => bswap64 v

/-- Silicon spot-check: 16-bit swap. -/
theorem movbeTausch_silicon16 :
    movbeTausch .w16 (BitVec.ofNat 64 0x1234) =
      BitVec.ofNat 64 0x3412 := by
  decide

/-- Silicon spot-check: 32-bit swap. -/
theorem movbeTausch_silicon32 :
    movbeTausch .w32 (BitVec.ofNat 64 0x01020304) =
      BitVec.ofNat 64 0x04030201 := by
  decide

/-- Silicon spot-check: 64-bit swap. -/
theorem movbeTausch_silicon64 :
    movbeTausch .w64 (BitVec.ofNat 64 0x0102030405060708) =
      BitVec.ofNat 64 0x0807060504030201 := by
  decide

/-- Silicon spot-check: the swap is an involution on a byte pattern. -/
theorem movbeTausch_invol32 :
    movbeTausch .w32 (movbeTausch .w32
      (BitVec.ofNat 64 0xA5A5A5A5)) =
      BitVec.ofNat 64 0xA5A5A5A5 := by
  decide

/-! ## 7. AES value semantics.

  The published FIPS-197 algorithms over the accepted lane
  vocabulary: the S-box (and its inverse) as closed tables, `xtime`
  and carry-less GF doubling, ShiftRows/InvShiftRows as lane
  permutations, MixColumns/InvMixColumns over GF(2^8), and the five
  round transforms exactly in the SDM pseudocode order (Vol. 2A
  3-33/3-39/3-45/3-51/3-57): SubBytes/ShiftRows/MixColumns then XOR
  with the round key -- the initial whitening is a separate PXOR, as
  on silicon. State byte `i` is lane `i` (column-major, matching the
  FIPS test-vector layout). -/

/-- AES S-box entries 0..31 (FIPS-197 §5.1.1, rows 0-1). -/
def aesSBox00 : List Nat :=
  [0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
   0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
   0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0,
   0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0]

/-- AES S-box entries 32..63 (FIPS-197 §5.1.1, rows 2-3). -/
def aesSBox32 : List Nat :=
  [0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc,
   0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
   0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a,
   0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75]

/-- AES S-box entries 64..95 (FIPS-197 §5.1.1, rows 4-5). -/
def aesSBox64 : List Nat :=
  [0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0,
   0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
   0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b,
   0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf]

/-- AES S-box entries 96..127 (FIPS-197 §5.1.1, rows 6-7). -/
def aesSBox96 : List Nat :=
  [0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85,
   0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
   0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
   0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2]

/-- AES S-box entries 128..159 (FIPS-197 §5.1.1, rows 8-9). -/
def aesSBox128 : List Nat :=
  [0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17,
   0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
   0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88,
   0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb]

/-- AES S-box entries 160..191 (FIPS-197 §5.1.1, rows A-B). -/
def aesSBox160 : List Nat :=
  [0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c,
   0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
   0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9,
   0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08]

/-- AES S-box entries 192..223 (FIPS-197 §5.1.1, rows C-D). -/
def aesSBox192 : List Nat :=
  [0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6,
   0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
   0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e,
   0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e]

/-- AES S-box entries 224..255 (FIPS-197 §5.1.1, rows E-F). -/
def aesSBox224 : List Nat :=
  [0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94,
   0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
   0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68,
   0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

/-- The full AES S-box: 256 entries. -/
def aesSBox : List Nat :=
  aesSBox00 ++ aesSBox32 ++ aesSBox64 ++ aesSBox96 ++
  aesSBox128 ++ aesSBox160 ++ aesSBox192 ++ aesSBox224

/-- Index into a natural table (0 past the end; structural, no
    list API beyond constructors). -/
def listZeige : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listZeige xs n

/-- S-box lookup on a byte value (0 outside the table). -/
def aesSBoxNat (b : Nat) : Nat := listZeige aesSBox b

/-- AES inverse S-box entries 0..31. -/
def aesInvSBox00 : List Nat :=
  [0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38,
   0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
   0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87,
   0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb]

/-- AES inverse S-box entries 32..63. -/
def aesInvSBox32 : List Nat :=
  [0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d,
   0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
   0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2,
   0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25]

/-- AES inverse S-box entries 64..95. -/
def aesInvSBox64 : List Nat :=
  [0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16,
   0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
   0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda,
   0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84]

/-- AES inverse S-box entries 96..127. -/
def aesInvSBox96 : List Nat :=
  [0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a,
   0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
  0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02,
  0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b]

/-- AES inverse S-box entries 128..159. -/
def aesInvSBox128 : List Nat :=
  [0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea,
   0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
   0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85,
   0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e]

/-- AES inverse S-box entries 160..191. -/
def aesInvSBox160 : List Nat :=
  [0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89,
   0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
   0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20,
   0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4]

/-- AES inverse S-box entries 192..223. -/
def aesInvSBox192 : List Nat :=
  [0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31,
   0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
   0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d,
   0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef]

/-- AES inverse S-box entries 224..255. -/
def aesInvSBox224 : List Nat :=
  [0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0,
   0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
   0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26,
   0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d]

/-- The full AES inverse S-box: 256 entries. -/
def aesInvSBox : List Nat :=
  aesInvSBox00 ++ aesInvSBox32 ++ aesInvSBox64 ++ aesInvSBox96 ++
  aesInvSBox128 ++ aesInvSBox160 ++ aesInvSBox192 ++ aesInvSBox224

/-- Inverse S-box lookup on a byte value (0 outside the table). -/
def aesInvSBoxNat (b : Nat) : Nat := listZeige aesInvSBox b

set_option maxRecDepth 10000 in
/-- Both tables hold 256 entries. -/
theorem aesSBox_laenge : aesSBox.length = 256 := rfl

set_option maxRecDepth 10000 in
/-- Both tables hold 256 entries. -/
theorem aesInvSBox_laenge : aesInvSBox.length = 256 := rfl

/-- GF(2^8) doubling (`xtime`): shift left, reduce by `0x11b` past
    eight bits. -/
def aesXtime (a : Nat) : Nat :=
  if a < 128 then (2 * a) % 256 else ((2 * a) % 256) ^^^ 0x1b

/-- GF(2^8) multiply by Russian peasant over eight bits. -/
def aesMulAux (a b acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 =>
    aesMulAux (aesXtime a) (b / 2)
      (if b % 2 == 1 then acc ^^^ a else acc) n

/-- GF(2^8) product of two bytes. -/
def aesMul (a b : Nat) : Nat := aesMulAux a b 0 8

/-- ShiftRows lane index: new lane `i` (row `i % 4`, column `i / 4`)
    takes the old lane shifted by its row. -/
def aesSrIdx (i : Nat) : Nat := 4 * ((i / 4 + i % 4) % 4) + i % 4

/-- InvShiftRows lane index. -/
def aesInvSrIdx (i : Nat) : Nat :=
  4 * ((i / 4 + 4 - i % 4) % 4) + i % 4

/-- MixColumns of one column (top to bottom). -/
def aesMixCol (c0 c1 c2 c3 : Nat) : Nat × Nat × Nat × Nat :=
  ((aesMul 2 c0 ^^^ aesMul 3 c1 ^^^ c2 ^^^ c3),
   (c0 ^^^ aesMul 2 c1 ^^^ aesMul 3 c2 ^^^ c3),
   (c0 ^^^ c1 ^^^ aesMul 2 c2 ^^^ aesMul 3 c3),
   (aesMul 3 c0 ^^^ c1 ^^^ c2 ^^^ aesMul 2 c3))

/-- InvMixColumns of one column (top to bottom). -/
def aesInvMixCol (c0 c1 c2 c3 : Nat) : Nat × Nat × Nat × Nat :=
  ((aesMul 0x0e c0 ^^^ aesMul 0x0b c1 ^^^ aesMul 0x0d c2 ^^^ aesMul 0x09 c3),
   (aesMul 0x09 c0 ^^^ aesMul 0x0e c1 ^^^ aesMul 0x0b c2 ^^^ aesMul 0x0d c3),
   (aesMul 0x0d c0 ^^^ aesMul 0x09 c1 ^^^ aesMul 0x0e c2 ^^^ aesMul 0x0b c3),
   (aesMul 0x0b c0 ^^^ aesMul 0x0d c1 ^^^ aesMul 0x09 c2 ^^^ aesMul 0x0e c3))

/-- One AESENC round (SDM Vol. 2A 3-45): ShiftRows, SubBytes,
    MixColumns, then XOR with the round key. -/
def aesEncRound (st key : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    let c0 := aesSBoxNat (laneNat .b8 st (aesSrIdx (4 * (i / 4))))
    let c1 := aesSBoxNat (laneNat .b8 st (aesSrIdx (4 * (i / 4) + 1)))
    let c2 := aesSBoxNat (laneNat .b8 st (aesSrIdx (4 * (i / 4) + 2)))
    let c3 := aesSBoxNat (laneNat .b8 st (aesSrIdx (4 * (i / 4) + 3)))
    let col := aesMixCol c0 c1 c2 c3
    let m := match i % 4 with
      | 0 => col.1 | 1 => col.2.1 | 2 => col.2.2.1 | _ => col.2.2.2
    m ^^^ laneNat .b8 key i)

/-- One AESENCLAST round (no MixColumns). -/
def aesEnclastRound (st key : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    aesSBoxNat (laneNat .b8 st (aesSrIdx i)) ^^^ laneNat .b8 key i)

/-- One AESDEC round (Equivalent Inverse Cipher order). -/
def aesDecRound (st key : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    let c0 := aesInvSBoxNat (laneNat .b8 st (aesInvSrIdx (4 * (i / 4))))
    let c1 := aesInvSBoxNat (laneNat .b8 st (aesInvSrIdx (4 * (i / 4) + 1)))
    let c2 := aesInvSBoxNat (laneNat .b8 st (aesInvSrIdx (4 * (i / 4) + 2)))
    let c3 := aesInvSBoxNat (laneNat .b8 st (aesInvSrIdx (4 * (i / 4) + 3)))
    let col := aesInvMixCol c0 c1 c2 c3
    let m := match i % 4 with
      | 0 => col.1 | 1 => col.2.1 | 2 => col.2.2.1 | _ => col.2.2.2
    m ^^^ laneNat .b8 key i)

/-- One AESDECLAST round (no InvMixColumns). -/
def aesDeclastRound (st key : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    aesInvSBoxNat (laneNat .b8 st (aesInvSrIdx i)) ^^^ laneNat .b8 key i)

/-- AESIMC: InvMixColumns of the source word. -/
def aesImc (src : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    let c0 := laneNat .b8 src (4 * (i / 4))
    let c1 := laneNat .b8 src (4 * (i / 4) + 1)
    let c2 := laneNat .b8 src (4 * (i / 4) + 2)
    let c3 := laneNat .b8 src (4 * (i / 4) + 3)
    let col := aesInvMixCol c0 c1 c2 c3
    match i % 4 with
      | 0 => col.1 | 1 => col.2.1 | 2 => col.2.2.1 | _ => col.2.2.2)

/-- RotWord after SubWord of the word at `base` (key assist). -/
def aesRotSub (s : Vektor) (base : Nat) : Nat × Nat × Nat × Nat :=
  let s0 := aesSBoxNat (laneNat .b8 s base)
  let s1 := aesSBoxNat (laneNat .b8 s (base + 1))
  let s2 := aesSBoxNat (laneNat .b8 s (base + 2))
  let s3 := aesSBoxNat (laneNat .b8 s (base + 3))
  (s1, s2, s3, s0)

/-- AESKEYGENASSIST (SDM Vol. 2A 3-58): `SubWord(X1)` and
    `RotWord(SubWord(X1)) XOR RCON` into lanes 0-7, the same of `X3`
    into lanes 8-15. -/
def aesKeygen (src : Vektor) (imm : Byte) : Vektor :=
  vecMk .b8 (fun i =>
    let rcon := byteNat imm
    if i < 4 then aesSBoxNat (laneNat .b8 src (4 + i))
    else if i < 8 then
      let q := aesRotSub src 4
      let v := match i with
        | 4 => q.1 | 5 => q.2.1 | 6 => q.2.2.1 | _ => q.2.2.2
      if i == 4 then v ^^^ rcon else v
    else if i < 12 then aesSBoxNat (laneNat .b8 src (12 + (i - 8)))
    else
      let q := aesRotSub src 12
      let v := match i with
        | 12 => q.1 | 13 => q.2.1 | 14 => q.2.2.1 | _ => q.2.2.2
      if i == 12 then v ^^^ rcon else v)

/-- S-box spot-checks (FIPS-197 known answers). -/
theorem aesSBox_silicon :
    aesSBoxNat 0 = 0x63 ∧ aesSBoxNat 0x01 = 0x7c ∧
      aesSBoxNat 0x09 = 0x01 ∧ aesSBoxNat 0x10 = 0xca ∧
      aesSBoxNat 0x53 = 0xed ∧ aesSBoxNat 0x63 = 0xfb ∧
      aesSBoxNat 0x7c = 0x10 ∧ aesSBoxNat 0xff = 0x16 := by
  decide

/-- Inverse S-box spot-checks (FIPS-197 known answers). -/
theorem aesInvSBox_silicon :
    aesInvSBoxNat 0 = 0x52 ∧ aesInvSBoxNat 0x63 = 0 ∧
      aesInvSBoxNat 0xed = 0x53 ∧ aesInvSBoxNat 0x16 = 0xff := by
  decide

set_option maxRecDepth 10000 in
/-- The tables are mutual inverses on every byte (transcription
    cross-check over all 256 inputs). -/
theorem aesSBox_inv (b : Nat) (h : b < 256) :
    aesInvSBoxNat (aesSBoxNat b) = b := by
  have h256 : ∀ k, k < 256 → aesInvSBoxNat (aesSBoxNat k) = k := by
    decide
  exact h256 b h

set_option maxRecDepth 10000 in
/-- The tables are mutual inverses, the other direction. -/
theorem aesInvSBox_inv (b : Nat) (h : b < 256) :
    aesSBoxNat (aesInvSBoxNat b) = b := by
  have h256 : ∀ k, k < 256 → aesSBoxNat (aesInvSBoxNat k) = k := by
    decide
  exact h256 b h

/-- `xtime` spot-checks (FIPS-197 §4.2 known answers). -/
theorem aesXtime_silicon : aesXtime 0x57 = 0xae ∧ aesXtime 0x80 = 0x1b := by
  decide

/-- ShiftRows and InvShiftRows invert each other on every lane. -/
theorem aesSr_inv (i : Nat) (h : i < 16) :
    aesInvSrIdx (aesSrIdx i) = i := by
  have h16 : ∀ k, k < 16 → aesInvSrIdx (aesSrIdx k) = k := by
    decide
  exact h16 i h

/-- AESENC of the zero state with the zero key is all `0x63`
    (SubBytes(0), ShiftRows-invariant, MixColumns fixes the constant
    column, XOR 0). -/
theorem aesEncRound_silicon :
    laneNat .b8 (aesEncRound 0 0) 3 = 0x63 ∧
      laneNat .b8 (aesEncRound 0 0) 11 = 0x63 := by
  decide

/-- AESENCLAST of zero with zero is all `0x63`. -/
theorem aesEnclastRound_silicon :
    laneNat .b8 (aesEnclastRound 0 0) 5 = 0x63 := by
  decide

/-- AESDEC of the zero state with the zero key is all `0x52`
    (InvSubBytes(0), InvMixColumns fixes the constant column). -/
theorem aesDecRound_silicon :
    laneNat .b8 (aesDecRound 0 0) 7 = 0x52 := by
  decide

/-- AESDECLAST of zero with zero is all `0x52`. -/
theorem aesDeclastRound_silicon :
    laneNat .b8 (aesDeclastRound 0 0) 9 = 0x52 := by
  decide

/-- AESIMC of zero is zero. -/
theorem aesImc_silicon : aesImc 0 = 0 := by
  decide

/-- InvMixColumns inverts MixColumns on a non-constant column. -/
theorem aesMixCol_inv_silicon :
    (fun q : Nat × Nat × Nat × Nat =>
      aesInvMixCol q.1 q.2.1 q.2.2.1 q.2.2.2)
      (aesMixCol 0x00 0x11 0x22 0x33) = (0x00, 0x11, 0x22, 0x33) := by
  decide

/-- AESDECLAST inverts AESENCLAST under the zero key on a concrete
    state (whitening/ShiftRows/SubBytes cancel lane by lane). -/
theorem aesLastRound_inv_silicon :
    aesDeclastRound
      (aesEnclastRound (vecMk .b8 (fun i => i + 1)) 0) 0 =
      vecMk .b8 (fun i => i + 1) := by
  decide

/-- AESKEYGENASSIST spot-check: `X1 = [1,2,3,4]`, RCON `0x01`
    (`SubWord` into lanes 0-3, rotated+XOR into lanes 4-7). -/
theorem aesKeygen_silicon :
    laneNat .b8 (aesKeygen
      (vecMk .b8 (fun i => if i < 4 then 0
        else if i = 4 then 1 else if i = 5 then 2
        else if i = 6 then 3 else if i = 7 then 4 else 0))
      (natByte 1)) 0 = 0x7c ∧
    laneNat .b8 (aesKeygen
      (vecMk .b8 (fun i => if i < 4 then 0
        else if i = 4 then 1 else if i = 5 then 2
        else if i = 6 then 3 else if i = 7 then 4 else 0))
      (natByte 1)) 4 = 0x76 := by
  decide

/-! ## 8. PCLMULQDQ and SSSE3 remainder value semantics.

  The carry-less multiply is the published PCLMUL128 helper (SDM
  Vol. 2B 4-242: bit `i` is the XOR over `j` of `X[j] AND Y[i-j]`);
  imm8[0] selects the first-source half, imm8[4] the second-source
  half, all other imm bits ignored. PHADD/PHSUB wrap (SDM: "it does
  not set bits in the EFLAGS register ... software must control the
  ranges"; only PHADDSW saturates, which stays refused). PSIGN
  negates/zeroes/keeps by the control sign; PMULHRSW takes
  `((a*b) >> 14) + 1`, bits `[16:1]` (arithmetic shifts). -/

/-- Carry-less product of two 64-bit values. -/
def pclmulNat (x y : Nat) : Nat :=
  ((List.range 64).filter (fun j => x.testBit j)).foldl
    (fun acc j => acc ^^^ (y * 2 ^ j)) 0

/-- Low 64 bits of a 128-bit word as a natural. -/
def xmmLo64 (v : Vektor) : Nat := v.toNat % 2 ^ 64

/-- High 64 bits of a 128-bit word as a natural. -/
def xmmHi64 (v : Vektor) : Nat := v.toNat / 2 ^ 64

/-- PCLMULQDQ with the imm8 half selection. -/
def vecPclmul (dst src : Vektor) (imm : Byte) : Vektor :=
  let x := if byteNat imm % 2 == 1 then xmmHi64 dst else xmmLo64 dst
  let y := if byteNat imm / 16 % 2 == 1 then xmmHi64 src else xmmLo64 src
  BitVec.ofNat 128 (pclmulNat x y)

/-- Carry-less spot-checks (hand-verified bit XORs). -/
theorem pclmulNat_silicon : pclmulNat 3 3 = 5 ∧ pclmulNat 0x11 0x11 = 0x101 := by
  decide

/-- PCLMULQDQ low/low selection (imm8 `0x00`). -/
theorem vecPclmul_silicon_lo :
    xmmLo64 (vecPclmul
      (vecMk .b64 (fun i => if i = 0 then 3 else 7))
      (vecMk .b64 (fun i => if i = 0 then 5 else 11))
      (natByte 0)) = 15 := by
  decide

/-- PCLMULQDQ high/high selection (imm8 `0x11`). -/
theorem vecPclmul_silicon_hi :
    xmmLo64 (vecPclmul
      (vecMk .b64 (fun i => if i = 0 then 3 else 7))
      (vecMk .b64 (fun i => if i = 0 then 5 else 11))
      (natByte 0x11)) = 0x31 := by
  decide

/-- Horizontal add of adjacent pairs (PHADDW/PHADDD): the low half
    sums destination pairs, the high half source pairs; wrapping. -/
def vecPhadd (b : Breite) (dst src : Vektor) : Vektor :=
  vecMk b (fun i =>
    if i < laneCount b / 2 then
      laneNat b dst (2 * i) + laneNat b dst (2 * i + 1)
    else
      laneNat b src (2 * i - laneCount b) +
        laneNat b src (2 * i - laneCount b + 1))

/-- Horizontal subtract of adjacent pairs (PHSUBW/PHSUBD): least
    minus most, wrapping. -/
def vecPhsub (b : Breite) (dst src : Vektor) : Vektor :=
  vecMk b (fun i =>
    if i < laneCount b / 2 then
      laneNat b dst (2 * i) + 2 ^ b.bits - laneNat b dst (2 * i + 1)
    else
      laneNat b src (2 * i - laneCount b) + 2 ^ b.bits -
        laneNat b src (2 * i - laneCount b + 1))

/-- Signed value of a lane (two's complement). -/
def laneSigned (b : Breite) (u : Nat) : Int :=
  if u < 2 ^ (b.bits - 1) then (u : Int) else (u : Int) - 2 ^ b.bits

/-- One PSIGN lane: negate/zero/keep by the control sign (`negate`
    wraps, so INT_MIN stays). -/
def psignLane (b : Breite) (ctl val : Nat) : Nat :=
  if laneSigned b ctl < 0 then (2 ^ b.bits - val) % 2 ^ b.bits
  else if laneSigned b ctl == 0 then 0
  else val

/-- Packed sign (PSIGNB/W/D). -/
def vecPsign (b : Breite) (dst src : Vektor) : Vektor :=
  vecMk b (fun i => psignLane b (laneNat b src i) (laneNat b dst i))

/-- One PMULHRSW lane: `((a * b) >> 14) + 1`, bits `[16:1]`
    (arithmetic shifts; the bit selection wraps). -/
def pmulhrswLane (a b : Nat) : Nat :=
  let temp : Int := laneSigned .b16 a * laneSigned .b16 b / 16384 + 1
  (temp / 2).emod 65536 |>.toNat

/-- Packed multiply-high with round and scale (PMULHRSW). -/
def vecPmulhrsw (dst src : Vektor) : Vektor :=
  vecMk .b16 (fun i =>
    pmulhrswLane (laneNat .b16 dst i) (laneNat .b16 src i))

/-- Per-lane horizontal add. -/
theorem laneNat_phadd (b : Breite) (dst src : Vektor) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (vecPhadd b dst src) i =
      ((if i < laneCount b / 2 then
        laneNat b dst (2 * i) + laneNat b dst (2 * i + 1)
      else
        laneNat b src (2 * i - laneCount b) +
          laneNat b src (2 * i - laneCount b + 1)) %
        2 ^ b.bits) := by
  unfold vecPhadd
  exact laneGet_mk b _ i hi

/-- Per-lane horizontal subtract. -/
theorem laneNat_phsub (b : Breite) (dst src : Vektor) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (vecPhsub b dst src) i =
      ((if i < laneCount b / 2 then
        laneNat b dst (2 * i) + 2 ^ b.bits - laneNat b dst (2 * i + 1)
      else
        laneNat b src (2 * i - laneCount b) + 2 ^ b.bits -
          laneNat b src (2 * i - laneCount b + 1)) %
        2 ^ b.bits) := by
  unfold vecPhsub
  exact laneGet_mk b _ i hi

/-- Per-lane sign. -/
theorem laneNat_psign (b : Breite) (dst src : Vektor) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (vecPsign b dst src) i =
      (psignLane b (laneNat b src i) (laneNat b dst i) %
        2 ^ b.bits) := by
  unfold vecPsign
  exact laneGet_mk b _ i hi

/-- Per-lane multiply-high. -/
theorem laneNat_pmulhrsw (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b16) :
    laneNat .b16 (vecPmulhrsw dst src) i =
      (pmulhrswLane (laneNat .b16 dst i) (laneNat .b16 src i) %
        2 ^ Breite.b16.bits) := by
  unfold vecPmulhrsw
  exact laneGet_mk .b16 _ i hi

/-- PHADDW spot-check: pairs sum, low half from DEST. -/
theorem vecPhadd_silicon :
    laneNat .b16 (vecPhadd .b16
      (vecMk .b16 (fun i => i + 1)) (vecMk .b16 (fun _ => 10))) 0 = 3 ∧
    laneNat .b16 (vecPhadd .b16
      (vecMk .b16 (fun i => i + 1)) (vecMk .b16 (fun _ => 10))) 4 = 20 := by
  decide

/-- PHSUBW spot-checks: least minus most, wrapping past zero. -/
theorem vecPhsub_silicon :
    laneNat .b16 (vecPhsub .b16
      (vecMk .b16 (fun i => if i = 0 then 5 else 3))
      (vecMk .b16 (fun _ => 0))) 0 = 2 ∧
    laneNat .b16 (vecPhsub .b16
      (vecMk .b16 (fun i => if i = 0 then 3 else 5))
      (vecMk .b16 (fun _ => 0))) 0 = 65534 := by
  decide

/-- PSIGN spot-checks: negate on negative, zero on zero, keep. -/
theorem psignLane_silicon :
    psignLane .b8 0xff 5 = 251 ∧ psignLane .b8 0 5 = 0 ∧
      psignLane .b8 3 5 = 5 ∧ psignLane .b16 0x8000 1 = 0xffff := by
  decide

/-- PMULHRSW spot-check: rounding of a half product. -/
theorem pmulhrswLane_silicon_rund :
    pmulhrswLane 16384 16384 = 8192 := by
  decide

/-- PMULHRSW spot-check: `0x7FFF * 0x7FFF` rounds to `0x7FFE`
    (`0x3FFF0001 >> 14 = 0xFFFC`, `+1`, bits `[16:1]`). -/
theorem pmulhrswLane_silicon_max :
    pmulhrswLane 32767 32767 = 32766 := by
  decide

/-- PMULHRSW spot-check: bit selection, not saturation --
    `0x8000 * 0x8000` gives `0x8000` (saturation would give `0x7FFF`). -/
theorem pmulhrswLane_silicon_nosat :
    pmulhrswLane 32768 32768 = 32768 := by
  decide

/-- PMULHRSW spot-check: a negative product. -/
theorem pmulhrswLane_silicon_neg :
      pmulhrswLane 32768 1 = 65535 := by
  decide

/-! ## 9. Step semantics on the shared XMM state.

  `stepAesClmulReg` steps the fifteen XMM rows on the SAME
  `FpZustand` the scalar FP and vector steps use (`xmmSet` writes the
  whole 128-bit register, `ripNach` advances RIP, `vecEintritt` gates
  on OS vector state). Legacy forms read DEST as the state and SRC as
  the round key and write DEST; AESIMC transforms SRC into DST. Flags,
  memory, GPRs and every other XMM register are untouched -- these
  forms have no flag, fault or memory effect (SDM: "Flags Affected:
  None", "SIMD Floating-Point Exceptions: None"). -/

/-- Single family register step; `none` is an explicit refusal (bad
    length, refused OS vector state, or a memory row). -/
def stepAesClmulReg (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) : Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match vecEintritt b with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.op with
      | .aesencRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (aesEncRound (t.xmm dst) (t.xmm src)) }
      | .aesenclastRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (aesEnclastRound (t.xmm dst) (t.xmm src)) }
      | .aesdecRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (aesDecRound (t.xmm dst) (t.xmm src)) }
      | .aesdeclastRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (aesDeclastRound (t.xmm dst) (t.xmm src)) }
      | .aesimcRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (aesImc (t.xmm src)) }
      | .aeskeygenRR dst src imm =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (aesKeygen (t.xmm src) imm) }
      | .pclmulRR dst src imm =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPclmul (t.xmm dst) (t.xmm src) imm) }
      | .movbe _ _ _ _ _ => none
      | .phaddwRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPhadd .b16 (t.xmm dst) (t.xmm src)) }
      | .phadddRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPhadd .b32 (t.xmm dst) (t.xmm src)) }
      | .phsubwRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPhsub .b16 (t.xmm dst) (t.xmm src)) }
      | .phsubdRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPhsub .b32 (t.xmm dst) (t.xmm src)) }
      | .psignbRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPsign .b8 (t.xmm dst) (t.xmm src)) }
      | .psignwRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPsign .b16 (t.xmm dst) (t.xmm src)) }
      | .psigndRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPsign .b32 (t.xmm dst) (t.xmm src)) }
      | .pmulhrswRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPmulhrsw (t.xmm dst) (t.xmm src)) }

/-- A bad decode length refuses every register form. -/
theorem stepAesClmulReg_laenge_verweigert (d : AesClmulDec)
    (t : FpZustand) (b : BereitProfil)
    (h : laengeOk d.laenge = false) :
    stepAesClmulReg d t b = none := by
  unfold stepAesClmulReg
  simp [h]

/-- Refused OS vector state refuses every register form. -/
theorem stepAesClmulReg_profil_verweigert (d : AesClmulDec)
    (t : FpZustand) (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (h : vecEintritt b = false) :
    stepAesClmulReg d t b = none := by
  unfold stepAesClmulReg
  simp [hok, h]

/-- A MOVBE row is refused on the register path (memory path only). -/
theorem stepAesClmulReg_movbe_verweigert (d : AesClmulDec)
    (t : FpZustand) (b : BereitProfil) (r : MovbeRichtung)
    (w : MovbeWeite) (reg base : Register) (dp : MovbeDisp)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .movbe r w reg base dp) :
    stepAesClmulReg d t b = none := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `aesenc`: the destination holds the round output. -/
theorem stepAesClmulReg_aesenc (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .aesencRR dst src) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (aesEncRound (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `aesenclast`: the destination holds the last-round output. -/
theorem stepAesClmulReg_aesenclast (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .aesenclastRR dst src) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (aesEnclastRound (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `aesdec`: the destination holds the decrypt-round output. -/
theorem stepAesClmulReg_aesdec (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .aesdecRR dst src) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (aesDecRound (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `aesdeclast`: the destination holds the last decrypt round. -/
theorem stepAesClmulReg_aesdeclast (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .aesdeclastRR dst src) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (aesDeclastRound (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `aesimc`: the destination holds the transformed source key. -/
theorem stepAesClmulReg_aesimc (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .aesimcRR dst src) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (aesImc (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `aeskeygenassist`: the destination holds the assist output. -/
theorem stepAesClmulReg_aeskeygen (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (imm : Byte)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .aeskeygenRR dst src imm) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (aesKeygen (t.xmm src) imm) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `pclmulqdq`: the destination holds the carry-less product. -/
theorem stepAesClmulReg_pclmul (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (imm : Byte)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pclmulRR dst src imm) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPclmul (t.xmm dst) (t.xmm src) imm) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-- `phaddw/phaddd`: the destination holds the horizontal sums. -/
theorem stepAesClmulReg_phadd (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (bw : Breite)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : (d.op = .phaddwRR dst src ∧ bw = .b16) ∨
      (d.op = .phadddRR dst src ∧ bw = .b32)) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPhadd bw (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp]
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp [h]

/-- `phsubw/phsubd`: the destination holds the horizontal differences. -/
theorem stepAesClmulReg_phsub (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (bw : Breite)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : (d.op = .phsubwRR dst src ∧ bw = .b16) ∨
      (d.op = .phsubdRR dst src ∧ bw = .b32)) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPhsub bw (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp]
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp [h]

/-- `psignb/w/d`: the destination holds the signed values. -/
theorem stepAesClmulReg_psign (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (bw : Breite)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : (d.op = .psignbRR dst src ∧ bw = .b8) ∨
      (d.op = .psignwRR dst src ∧ bw = .b16) ∨
      (d.op = .psigndRR dst src ∧ bw = .b32)) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPsign bw (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp]
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp [h]

/-- `pmulhrsw`: the destination holds the rounded high words. -/
theorem stepAesClmulReg_pmulhrsw (d : AesClmulDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pmulhrswRR dst src) :
    stepAesClmulReg d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPmulhrsw (t.xmm dst) (t.xmm src)) } := by
  unfold stepAesClmulReg
  simp [hok, hfp, h]

/-! ## 10. Register-step frames: flags, memory, GPRs, other registers, RIP.

  Every XMM row preserves rFLAGS, changes no memory byte, keeps every
  GPR, keeps every other XMM register whole, and advances RIP past
  the decoded length. -/

/-- The destination register an XMM row writes (MOVBE has none). -/
def aesClmulDstXmm : AesClmulOp → Option XmmReg
  | .aesencRR dst _ => some dst
  | .aesenclastRR dst _ => some dst
  | .aesdecRR dst _ => some dst
  | .aesdeclastRR dst _ => some dst
  | .aesimcRR dst _ => some dst
  | .aeskeygenRR dst _ _ => some dst
  | .pclmulRR dst _ _ => some dst
  | .movbe _ _ _ _ _ => none
  | .phaddwRR dst _ => some dst
  | .phadddRR dst _ => some dst
  | .phsubwRR dst _ => some dst
  | .phsubdRR dst _ => some dst
  | .psignbRR dst _ => some dst
  | .psignwRR dst _ => some dst
  | .psigndRR dst _ => some dst
  | .pmulhrswRR dst _ => some dst

/-- Every register step advances RIP past the decoded length. -/
theorem stepAesClmulReg_rip (d : AesClmulDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepAesClmulReg d t b = some t') :
    t'.kern.rip = ripNach t.kern.rip d.laenge := by
  revert hstep
  unfold stepAesClmulReg
  rw [hok, hfp]
  cases hop : d.op with
  | aesencRR dst src => intro hstep; cases hstep; rfl
  | aesenclastRR dst src => intro hstep; cases hstep; rfl
  | aesdecRR dst src => intro hstep; cases hstep; rfl
  | aesdeclastRR dst src => intro hstep; cases hstep; rfl
  | aesimcRR dst src => intro hstep; cases hstep; rfl
  | aeskeygenRR dst src imm => intro hstep; cases hstep; rfl
  | pclmulRR dst src imm => intro hstep; cases hstep; rfl
  | movbe r w reg base dp => intro hstep; cases hstep
  | phaddwRR dst src => intro hstep; cases hstep; rfl
  | phadddRR dst src => intro hstep; cases hstep; rfl
  | phsubwRR dst src => intro hstep; cases hstep; rfl
  | phsubdRR dst src => intro hstep; cases hstep; rfl
  | psignbRR dst src => intro hstep; cases hstep; rfl
  | psignwRR dst src => intro hstep; cases hstep; rfl
  | psigndRR dst src => intro hstep; cases hstep; rfl
  | pmulhrswRR dst src => intro hstep; cases hstep; rfl

/-- Every register step preserves the flags. -/
theorem stepAesClmulReg_flags (d : AesClmulDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepAesClmulReg d t b = some t') :
    t'.kern.flags = t.kern.flags := by
  revert hstep
  unfold stepAesClmulReg
  rw [hok, hfp]
  cases hop : d.op with
  | aesencRR dst src => intro hstep; cases hstep; rfl
  | aesenclastRR dst src => intro hstep; cases hstep; rfl
  | aesdecRR dst src => intro hstep; cases hstep; rfl
  | aesdeclastRR dst src => intro hstep; cases hstep; rfl
  | aesimcRR dst src => intro hstep; cases hstep; rfl
  | aeskeygenRR dst src imm => intro hstep; cases hstep; rfl
  | pclmulRR dst src imm => intro hstep; cases hstep; rfl
  | movbe r w reg base dp => intro hstep; cases hstep
  | phaddwRR dst src => intro hstep; cases hstep; rfl
  | phadddRR dst src => intro hstep; cases hstep; rfl
  | phsubwRR dst src => intro hstep; cases hstep; rfl
  | phsubdRR dst src => intro hstep; cases hstep; rfl
  | psignbRR dst src => intro hstep; cases hstep; rfl
  | psignwRR dst src => intro hstep; cases hstep; rfl
  | psigndRR dst src => intro hstep; cases hstep; rfl
  | pmulhrswRR dst src => intro hstep; cases hstep; rfl

/-- Every register step changes no memory byte. -/
theorem stepAesClmulReg_speicher (d : AesClmulDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepAesClmulReg d t b = some t') :
    t'.kern.speicher = t.kern.speicher := by
  revert hstep
  unfold stepAesClmulReg
  rw [hok, hfp]
  cases hop : d.op with
  | aesencRR dst src => intro hstep; cases hstep; rfl
  | aesenclastRR dst src => intro hstep; cases hstep; rfl
  | aesdecRR dst src => intro hstep; cases hstep; rfl
  | aesdeclastRR dst src => intro hstep; cases hstep; rfl
  | aesimcRR dst src => intro hstep; cases hstep; rfl
  | aeskeygenRR dst src imm => intro hstep; cases hstep; rfl
  | pclmulRR dst src imm => intro hstep; cases hstep; rfl
  | movbe r w reg base dp => intro hstep; cases hstep
  | phaddwRR dst src => intro hstep; cases hstep; rfl
  | phadddRR dst src => intro hstep; cases hstep; rfl
  | phsubwRR dst src => intro hstep; cases hstep; rfl
  | phsubdRR dst src => intro hstep; cases hstep; rfl
  | psignbRR dst src => intro hstep; cases hstep; rfl
  | psignwRR dst src => intro hstep; cases hstep; rfl
  | psigndRR dst src => intro hstep; cases hstep; rfl
  | pmulhrswRR dst src => intro hstep; cases hstep; rfl

/-- Every register step keeps every GPR. -/
theorem stepAesClmulReg_gpr (d : AesClmulDec) (t t' : FpZustand)
    (b : BereitProfil) (q : Register)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepAesClmulReg d t b = some t') :
    t'.kern.register q = t.kern.register q := by
  revert hstep
  unfold stepAesClmulReg
  rw [hok, hfp]
  cases hop : d.op with
  | aesencRR dst src => intro hstep; cases hstep; rfl
  | aesenclastRR dst src => intro hstep; cases hstep; rfl
  | aesdecRR dst src => intro hstep; cases hstep; rfl
  | aesdeclastRR dst src => intro hstep; cases hstep; rfl
  | aesimcRR dst src => intro hstep; cases hstep; rfl
  | aeskeygenRR dst src imm => intro hstep; cases hstep; rfl
  | pclmulRR dst src imm => intro hstep; cases hstep; rfl
  | movbe r w reg base dp => intro hstep; cases hstep
  | phaddwRR dst src => intro hstep; cases hstep; rfl
  | phadddRR dst src => intro hstep; cases hstep; rfl
  | phsubwRR dst src => intro hstep; cases hstep; rfl
  | phsubdRR dst src => intro hstep; cases hstep; rfl
  | psignbRR dst src => intro hstep; cases hstep; rfl
  | psignwRR dst src => intro hstep; cases hstep; rfl
  | psigndRR dst src => intro hstep; cases hstep; rfl
  | pmulhrswRR dst src => intro hstep; cases hstep; rfl

/-- Every register step keeps every other XMM register whole. -/
theorem stepAesClmulReg_fremd (d : AesClmulDec) (t t' : FpZustand)
    (b : BereitProfil) (q dst : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepAesClmulReg d t b = some t')
    (hdst : aesClmulDstXmm d.op = some dst) (hq : q ≠ dst) :
    t'.xmm q = t.xmm q := by
  revert hstep hdst hq
  unfold stepAesClmulReg
  rw [hok, hfp]
  cases hop : d.op with
  | aesencRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (aesEncRound (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | aesenclastRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (aesEnclastRound (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | aesdecRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (aesDecRound (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | aesdeclastRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (aesDeclastRound (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | aesimcRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (aesImc (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | aeskeygenRR dst' src imm =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (aesKeygen (t.xmm src) imm)) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | pclmulRR dst' src imm =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPclmul (t.xmm dst') (t.xmm src) imm)) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | movbe r w reg base dp => intro hstep hdst hq; cases hstep
  | phaddwRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPhadd .b16 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | phadddRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPhadd .b32 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | phsubwRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPhsub .b16 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | phsubdRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPhsub .b32 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | psignbRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPsign .b8 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | psignwRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPsign .b16 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | psigndRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPsign .b32 (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)
  | pmulhrswRR dst' src =>
    intro hstep hdst hq; cases hstep
    have heq : dst' = dst := by simpa [aesClmulDstXmm, hop] using hdst
    show (xmmSet t.xmm dst' (vecPmulhrsw (t.xmm dst') (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by rw [heq]; exact hq)

/-! ## 11. MOVBE memory steps on the coherent machine.

  Addresses come from the accepted `adrEff` (`AddressEncoding`,
  never a second model); bytes move through the accepted
  width-selected `concIssue`/`concLoad` on the shared TSO view. The
  store issues the swapped low bytes; the load swaps the forwarded
  bytes into the destination through the accepted `mergeRegNarrow`
  (8/16-bit writes merge, 32-bit writes zero-extend). -/

/-- Displacement of a MOVBE row as a 32-bit word (disp8
    sign-extended, exactly as the architecture fetches mod=01). -/
def movbeDisp32 : MovbeDisp → BitVec 32
  | .kurz d8 =>
    if byteNat d8 < 128 then BitVec.ofNat 32 (byteNat d8)
    else BitVec.ofNat 32 (byteNat d8 + 2 ^ 32 - 256)
  | .lang d32 => d32

/-- Address of a MOVBE row from the acting core's registers. -/
def movbeAddrOf (m : HwMaschine) (c : Nat) (ripNext : Adresse)
    (base : Register) (d : MovbeDisp) : Adresse :=
  adrEff (projZustand m c) ripNext (basisForm base (movbeDisp32 d))

/-- The MOVBE address reads the acting core's base register. -/
theorem movbeAddrOf_basisForm (m : HwMaschine) (c : Nat)
    (ripNext : Adresse) (base : Register) (d : MovbeDisp) :
    movbeAddrOf m c ripNext base d =
      effAddr (projZustand m c) base (movbeDisp32 d) := by
  unfold movbeAddrOf
  rw [adrEff_basisForm]

/-- MOVBE store on the coherent machine: the swapped low bytes issue
    into the acting core's buffer (never the SC word effect); RIP
    advances past `len`. -/
def movbeStore (m : HwMaschine) (c : Nat) (w : MovbeWeite)
    (base src : Register) (d : MovbeDisp) (ripNext : Adresse)
    (len : Nat) : Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    let a := movbeAddrOf m c ripNext base d
    match concIssue (tsoAnsicht m) c (movbeBreite w) a
      (movbeTausch w ((m.kerne c).register src)) with
    | none => none
    | some s' => some ({ setTso m s' with kerne := fun e => if e = c then { m.kerne c with rip := ripNach (m.kerne c).rip len } else m.kerne e })

/-- MOVBE load on the coherent machine: the forwarded bytes swap into
    the destination with the narrow-merge discipline; RIP advances
    past `len`. -/
def movbeLoad (m : HwMaschine) (c : Nat) (w : MovbeWeite)
    (dst base : Register) (d : MovbeDisp) (ripNext : Adresse)
    (len : Nat) : Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    match concLoad (tsoAnsicht m) c (movbeBreite w)
      (movbeAddrOf m c ripNext base d) with
    | none => none
    | some v => some ({ m with kerne := fun e => if e = c then { m.kerne c with register := regSet (m.kerne c).register dst (mergeRegNarrow (movbeBreite w) ((m.kerne c).register dst) (movbeTausch w v)), rip := ripNach (m.kerne c).rip len } else m.kerne e })

/-- A bad length refuses every MOVBE store. -/
theorem movbeStore_laenge_verweigert (m : HwMaschine) (c : Nat)
    (w : MovbeWeite) (base src : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : laengeOk len = false) :
    movbeStore m c w base src d ripNext len = none := by
  unfold movbeStore
  simp [h]

/-- A bad length refuses every MOVBE load. -/
theorem movbeLoad_laenge_verweigert (m : HwMaschine) (c : Nat)
    (w : MovbeWeite) (dst base : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : laengeOk len = false) :
    movbeLoad m c w dst base d ripNext len = none := by
  unfold movbeLoad
  simp [h]

/-- A store keeps the flags. -/
theorem movbeStore_flags (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (base src : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : movbeStore m c w base src d ripNext len = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold movbeStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d)
        (movbeTausch w ((m.kerne c).register src)) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store advances RIP past its length. -/
theorem movbeStore_rip (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (base src : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : movbeStore m c w base src d ripNext len = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip len := by
  unfold movbeStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d)
        (movbeTausch w ((m.kerne c).register src)) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store changes no canonical byte (buffer only). -/
theorem movbeStore_kein_speicher (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (base src : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat) (x : Adresse)
    (h : movbeStore m c w base src d ripNext len = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold movbeStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d)
        (movbeTausch w ((m.kerne c).register src)) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      have he := concIssue_kein_speicher (tsoAnsicht m) s' c
        (movbeBreite w) (movbeAddrOf m c ripNext base d)
        (movbeTausch w ((m.kerne c).register src)) hi x
      simpa [tsoAnsicht, setTso] using he

/-- A store preserves well-formedness (profiles untouched). -/
theorem movbeStore_wf (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (base src : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : movbeStore m c w base src d ripNext len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold movbeStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d)
        (movbeTausch w ((m.kerne c).register src)) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      exact hwf

/-- A load writes the swapped value through the accepted merge. -/
theorem movbeLoad_dst (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (dst base : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat) (v : Wort)
    (hload : concLoad (tsoAnsicht m) c (movbeBreite w)
      (movbeAddrOf m c ripNext base d) = some v)
    (hlen : laengeOk len = true)
    (h : movbeLoad m c w dst base d ripNext len = some m') :
    (m'.kerne c).register dst =
      mergeRegNarrow (movbeBreite w) ((m.kerne c).register dst)
        (movbeTausch w v) := by
  unfold movbeLoad at h
  simp only [hlen] at h
  rw [hload] at h
  simp only at h
  cases h
  simp [regSet_gleich]

/-- A load keeps the flags. -/
theorem movbeLoad_flags (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (dst base : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : movbeLoad m c w dst base d ripNext len = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold movbeLoad at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concLoad (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d) with
    | none => simp [hi] at h
    | some v =>
      simp [hi] at h
      cases h
      simp

/-- A load advances RIP past its length. -/
theorem movbeLoad_rip (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (dst base : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : movbeLoad m c w dst base d ripNext len = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip len := by
  unfold movbeLoad at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concLoad (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d) with
    | none => simp [hi] at h
    | some v =>
      simp [hi] at h
      cases h
      simp

/-- A load preserves well-formedness (profiles untouched). -/
theorem movbeLoad_wf (m m' : HwMaschine) (c : Nat)
    (w : MovbeWeite) (dst base : Register) (d : MovbeDisp)
    (ripNext : Adresse) (len : Nat)
    (h : movbeLoad m c w dst base d ripNext len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold movbeLoad at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concLoad (tsoAnsicht m) c (movbeBreite w)
        (movbeAddrOf m c ripNext base d) with
    | none => simp [hi] at h
    | some v =>
      simp [hi] at h
      cases h
      exact hwf

/-! ## 12. Extended capstone chain.

  `kapDecodeAes` runs the accepted `kapDecode` first and consults the
  family decoder only where the old chain refuses, so dispatch is
  disjoint by construction. A maintainer wires the family in by
  adding the `decodeAesClmul` arm behind every earlier arm of
  `HwKapsteinDecoder.kapDecode` (same position as the `avx2` arm:
  last, tried only where all earlier arms refuse). -/

/-- One row of the extended chain: the old chain first, the new
    family only where it refuses. -/
inductive KapAes where
  | alt : KapDekodiert → KapAes
  | neu : AesClmulDec → KapAes
  deriving DecidableEq, Repr

/-- Extended chain: `kapDecode` first, the family decoder only where
    the old chain refuses. No old row is shadowed. -/
def kapDecodeAes : List Byte → Option (KapAes × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.alt k, rest)
    | none =>
      match decodeAesClmul bs with
      | some (d, rest) => some (.neu d, rest)
      | none => none

/-- The extended chain agrees with the old chain on every byte string
    the old chain accepts: no existing form is shadowed. -/
theorem kapDecodeAes_alt (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeAes bs = some (.alt k, rest) := by
  unfold kapDecodeAes
  rw [h]

/-- Where the old chain refuses, a covered family row is taken. -/
theorem kapDecodeAes_neu (bs : List Byte) (d : AesClmulDec)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeAesClmul bs = some (d, rest)) :
    kapDecodeAes bs = some (.neu d, rest) := by
  unfold kapDecodeAes
  rw [h1, h2]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeAes_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeAesClmul bs = none) :
    kapDecodeAes bs = none := by
  unfold kapDecodeAes
  rw [h1, h2]

/-- Extended-chain pin: AESENC xmm0, xmm0 decodes through the new arm. -/
theorem kapAes_pin_aesenc :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 220, natByte 192] =
      some (KapAes.neu (⟨.aesencRR .xmm0 .xmm0, 6⟩ : AesClmulDec), []) := by
  decide

/-- Extended-chain pin: AESDECLAST xmm1, xmm2 decodes. -/
theorem kapAes_pin_aesdeclast :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 223, natByte 202] =
      some (KapAes.neu (⟨.aesdeclastRR .xmm1 .xmm2, 6⟩ : AesClmulDec),
        []) := by
  decide

/-- Extended-chain pin: AESIMC xmm3, xmm4 decodes. -/
theorem kapAes_pin_aesimc :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 219, natByte 220] =
      some (KapAes.neu (⟨.aesimcRR .xmm3 .xmm4, 6⟩ : AesClmulDec),
        []) := by
  decide

/-- Extended-chain pin: AESKEYGENASSIST xmm5, xmm6, 7 decodes. -/
theorem kapAes_pin_aeskeygen :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 223, natByte 238, natByte 7] =
      some (KapAes.neu
        (⟨.aeskeygenRR .xmm5 .xmm6 (natByte 7), 7⟩ : AesClmulDec),
        []) := by
  decide

/-- Extended-chain pin: PCLMULQDQ xmm1, xmm0, 0 decodes. -/
theorem kapAes_pin_pclmul :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 68, natByte 200, natByte 0] =
      some (KapAes.neu
        (⟨.pclmulRR .xmm1 .xmm0 (natByte 0), 7⟩ : AesClmulDec),
        []) := by
  decide

/-- Extended-chain pin: MOVBE r32 <- [rcx] decodes. -/
theorem kapAes_pin_movbe32 :
    kapDecodeAes [natByte 64, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] =
      some (KapAes.neu
        (⟨.movbe .lad .w32 .rax .rcx (.kurz (natByte 0)), 6⟩ :
          AesClmulDec), []) := by
  decide

/-- Extended-chain pin: MOVBE r64 <- [rcx+disp32] decodes. -/
theorem kapAes_pin_movbe64 :
    kapDecodeAes [natByte 72, natByte 15, natByte 56,
      natByte 240, natByte 129, natByte 5, natByte 0,
      natByte 0, natByte 0] =
      some (KapAes.neu
        (⟨.movbe .lad .w64 .rax .rcx
          (.lang (BitVec.ofNat 32 5)), 9⟩ : AesClmulDec), []) := by
  decide

/-- Extended-chain pin: PHADDW xmm2, xmm3 decodes. -/
theorem kapAes_pin_phaddw :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 1, natByte 211] =
      some (KapAes.neu (⟨.phaddwRR .xmm2 .xmm3, 6⟩ : AesClmulDec),
        []) := by
  decide

/-- Extended-chain pin: PMULHRSW xmm4, xmm5 decodes. -/
theorem kapAes_pin_pmulhrsw :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 11, natByte 229] =
      some (KapAes.neu (⟨.pmulhrswRR .xmm4 .xmm5, 6⟩ : AesClmulDec),
        []) := by
  decide

/-- The extended chain refuses the sibling PSHUFB row. -/
theorem kapAes_nichts_pshufb :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none :=
  kapDecodeAes_nichts _ kap_weist_pshufb_zurueck aesClmul_nichts_pshufb

/-- The extended chain refuses the CRC32 neighbour: the old chain
    never took `F2` (no accepted row starts there) and the family
    decoder requires a canonical REX first. -/
theorem kapAes_nichts_crc32 :
    kapDecodeAes [natByte 242, natByte 15, natByte 56,
      natByte 240, natByte 65, natByte 0] = none := by
  decide

/-- The extended chain refuses BLENDVPS: neither chain admits it. -/
theorem kapAes_nichts_blendv :
    kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 20, natByte 200, natByte 0] = none :=
  kapDecodeAes_nichts _ kap_weist_blendv_zurueck aesClmul_nichts_blendv

/-! ## 13. Machine adapter: the family on the coherent machine.

  The producer plug instantiates `HwAdapter AesClmulDec`: XMM rows
  ride the register step (re-embedded over shared memory); MOVBE rows
  ride the TSO memory steps with the decode length and the core RIP
  as the address base (unused for base+disp forms, which never read
  it). Refusals admit no successor state. -/

/-- An XMM (register-only) row: everything but MOVBE. -/
def istXmmZeile : AesClmulOp → Bool
  | .movbe _ _ _ _ _ => false
  | _ => true

/-- The family plug: one checked family event step on the coherent
    machine. `none` = refusal, never a silent successor. -/
def adapterAesClmul : HwAdapter AesClmulDec :=
  ⟨fun m c d =>
    match d.op with
    | .movbe .lad w reg base dp =>
      movbeLoad m c w reg base dp (m.kerne c).rip d.laenge
    | .movbe .spei w reg base dp =>
      movbeStore m c w base reg dp (m.kerne c).rip d.laenge
    | _ =>
      match stepAesClmulReg d (projFp m c) (m.bereit c) with
      | some t' => some (setKernVonFp m c t')
      | none => none⟩

/-- Every adapter step preserves well-formedness: only core data,
    memory or buffers move through checked steps; profiles are
    untouched. -/
theorem adapterAesClmul_wf (m : HwMaschine) (c : Nat)
    (d : AesClmulDec) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterAesClmul).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterAesClmul at h
  simp only at h
  cases hop : d.op with
  | movbe r w reg base dp =>
    cases r with
    | lad =>
      rw [hop] at h
      simp only at h
      exact movbeLoad_wf _ _ _ _ _ _ _ _ _ h hwf
    | spei =>
      rw [hop] at h
      simp only at h
      exact movbeStore_wf _ _ _ _ _ _ _ _ _ h hwf
  | aesencRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesenclastRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesdecRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesdeclastRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesimcRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aeskeygenRR dst src imm =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | pclmulRR dst src imm =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phaddwRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phadddRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phsubwRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phsubdRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | psignbRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | psignwRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | psigndRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | pmulhrswRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact hwf
    | none =>
      rw [hsch] at h
      simp only at h
      cases h

/-- Agreement: on an XMM row the adapter succeeds exactly where the
    register step succeeds, re-embedded over shared memory. -/
theorem adapterAesClmul_reg (m : HwMaschine) (c : Nat)
    (d : AesClmulDec) (t' : FpZustand)
    (hxmm : istXmmZeile d.op = true)
    (h : stepAesClmulReg d (projFp m c) (m.bereit c) = some t') :
    (adapterAesClmul).schritt m c d = some (setKernVonFp m c t') := by
  unfold adapterAesClmul
  simp only
  cases hop : d.op with
  | movbe r w reg base dp =>
    rw [hop] at hxmm
    simp only [istXmmZeile] at hxmm
    exact absurd hxmm (by decide)
  | aesencRR dst src => simp only [h]
  | aesenclastRR dst src => simp only [h]
  | aesdecRR dst src => simp only [h]
  | aesdeclastRR dst src => simp only [h]
  | aesimcRR dst src => simp only [h]
  | aeskeygenRR dst src imm => simp only [h]
  | pclmulRR dst src imm => simp only [h]
  | phaddwRR dst src => simp only [h]
  | phadddRR dst src => simp only [h]
  | phsubwRR dst src => simp only [h]
  | phsubdRR dst src => simp only [h]
  | psignbRR dst src => simp only [h]
  | psignwRR dst src => simp only [h]
  | psigndRR dst src => simp only [h]
  | pmulhrswRR dst src => simp only [h]

/-- Agreement: on a MOVBE load row the adapter is the memory load. -/
theorem adapterAesClmul_lad (m : HwMaschine) (c : Nat)
    (d : AesClmulDec) (w : MovbeWeite) (reg base : Register)
    (dp : MovbeDisp)
    (h : d.op = .movbe .lad w reg base dp) :
    (adapterAesClmul).schritt m c d =
      movbeLoad m c w reg base dp (m.kerne c).rip d.laenge := by
  unfold adapterAesClmul
  simp only [h]

/-- Agreement: on a MOVBE store row the adapter is the memory store. -/
theorem adapterAesClmul_spei (m : HwMaschine) (c : Nat)
    (d : AesClmulDec) (w : MovbeWeite) (reg base : Register)
    (dp : MovbeDisp)
    (h : d.op = .movbe .spei w reg base dp) :
    (adapterAesClmul).schritt m c d =
      movbeStore m c w base reg dp (m.kerne c).rip d.laenge := by
  unfold adapterAesClmul
  simp only [h]

/-- A bad decode length admits no AESENC adapter step. -/
theorem adapterAesClmul_aesenc_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (dst src : XmmReg) (len : Nat)
    (h : laengeOk len = false) :
    (adapterAesClmul).schritt m c
      (⟨.aesencRR dst src, len⟩ : AesClmulDec) = none := by
  have hstep := stepAesClmulReg_laenge_verweigert
    (⟨.aesencRR dst src, len⟩ : AesClmulDec) (projFp m c)
    (m.bereit c) h
  unfold adapterAesClmul
  simp only [hstep]

/-- Refused OS vector state admits no PCLMULQDQ adapter step. -/
theorem adapterAesClmul_pclmul_verweigert_bei_profil (m : HwMaschine)
    (c : Nat) (dst src : XmmReg) (imm : Byte)
    (hok : laengeOk 7 = true)
    (h : vecEintritt (m.bereit c) = false) :
    (adapterAesClmul).schritt m c
      (⟨.pclmulRR dst src imm, 7⟩ : AesClmulDec) = none := by
  have hstep := stepAesClmulReg_profil_verweigert
    (⟨.pclmulRR dst src imm, 7⟩ : AesClmulDec) (projFp m c)
    (m.bereit c) hok h
  unfold adapterAesClmul
  simp only [hstep]

/-- A bad decode length admits no MOVBE adapter step. -/
theorem adapterAesClmul_movbe_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (r : MovbeRichtung) (w : MovbeWeite) (reg base : Register)
    (dp : MovbeDisp) (len : Nat)
    (h : laengeOk len = false) :
    (adapterAesClmul).schritt m c
      (⟨.movbe r w reg base dp, len⟩ : AesClmulDec) = none := by
  cases r with
  | lad =>
    have hstep := movbeLoad_laenge_verweigert m c w reg base dp
      (m.kerne c).rip len h
    unfold adapterAesClmul
    show movbeLoad m c w reg base dp (m.kerne c).rip len = none
    exact hstep
  | spei =>
    have hstep := movbeStore_laenge_verweigert m c w base reg dp
      (m.kerne c).rip len h
    unfold adapterAesClmul
    show movbeStore m c w base reg dp (m.kerne c).rip len = none
    exact hstep

/-- An XMM adapter step keeps the shared memory and every buffer. -/
theorem adapterAesClmul_reg_mem (m : HwMaschine) (c : Nat)
    (d : AesClmulDec) (m' : HwMaschine)
    (hxmm : istXmmZeile d.op = true)
    (h : (adapterAesClmul).schritt m c d = some m') :
    m'.mem = m.mem ∧ ∀ e : Nat, m'.puffer e = m.puffer e := by
  unfold adapterAesClmul at h
  simp only at h
  cases hop : d.op with
  | movbe r w reg base dp =>
    rw [hop] at hxmm
    simp only [istXmmZeile] at hxmm
    exact absurd hxmm (by decide)
  | aesencRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesenclastRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesdecRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesdeclastRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aesimcRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | aeskeygenRR dst src imm =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | pclmulRR dst src imm =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phaddwRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phadddRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phsubwRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | phsubdRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | psignbRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | psignwRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | psigndRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h
  | pmulhrswRR dst src =>
    rw [hop] at h
    simp only at h
    cases hsch : stepAesClmulReg d (projFp m c) (m.bereit c) with
    | some t' =>
      rw [hsch] at h
      simp only at h
      cases h
      exact ⟨setKernVonFp_speicher _ _ _,
        fun e => setKernVonFp_puffer _ _ _ e⟩
    | none =>
      rw [hsch] at h
      simp only at h
      cases h

/-! ## 14. Joint witness: two cores, family steps, buffered store.

  Core 0 takes an AESENC round over zero state and zero key (every
  lane becomes `0x63`); core 1 stores `0x1234` with MOVBE16 to
  `[rcx]` (bytes `12 34` issue into core 1's buffer, observed by
  forwarding on core 1 only, then drained into shared memory). The
  memory half reuses the accepted TSO equations; the issue itself
  goes through the family adapter. Non-degenerate: XMM bytes change
  and shared memory changes, on two cores. -/

/-- Witness XMM files: core 0 holds zero state and zero key. -/
def aesWitXmm0 : XmmDatei := fun _ => BitVec.ofNat 128 0

/-- Witness core-1 registers: source `0x1234` in rax, base `12288`
    in rcx. -/
def aesWitReg1 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 0x1234
  else if q = Register.rcx then BitVec.ofNat 64 12288
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 encrypts, core 1 stores. -/
def aesWitKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, aesWitXmm0, kontextReset⟩
  | 1 => ⟨aesWitReg1, zeugeFlags,
      BitVec.ofNat 64 4096, fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two family cores, empty
    buffers, full silicon. -/
def aesWitStart : HwMaschine :=
  ⟨zeugeSpeicher, aesWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem aesWitStart_wf : HwWf aesWitStart := by
  intro c f _
  cases f <;> rfl

/-- Core 0 AESENC step through the adapter. -/
def aesWitOut0 : Option HwMaschine :=
  (adapterAesClmul).schritt aesWitStart 0
    (⟨.aesencRR .xmm0 .xmm1, 6⟩ : AesClmulDec)

/-- Core 1 MOVBE16 store step through the adapter. -/
def aesWitOut1 : Option HwMaschine :=
  (adapterAesClmul).schritt aesWitStart 1
    (⟨.movbe .spei .w16 .rax .rcx (.kurz (natByte 0)), 7⟩ :
      AesClmulDec)

/-- Read one byte lane out of an adapter outcome. -/
def aesWitLane (o : Option HwMaschine) (c : Nat) (r : XmmReg)
    (i : Nat) : Option Nat :=
  match o with
  | some m => some (laneNat .b8 ((m.kerne c).xmm r) i)
  | none => none

/-- Read one core register out of an adapter outcome. -/
def aesWitReg (o : Option HwMaschine) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | some m => some ((m.kerne c).register q)
  | none => none

/-- Read one RIP out of an adapter outcome. -/
def aesWitRip (o : Option HwMaschine) (c : Nat) : Option Wort :=
  match o with
  | some m => some ((m.kerne c).rip)
  | none => none

/-- Core 0 AESENC: lane 0 becomes `0x63`. -/
theorem aesWit_enc_lane0 :
    aesWitLane aesWitOut0 0 XmmReg.xmm0 0 = some 99 := by
  decide

/-- The round destination started zeroed: the step changes XMM. -/
theorem aesWit_enc_vorher :
    laneNat .b8 (aesWitXmm0 XmmReg.xmm0) 0 = 0 := by
  decide

/-- Witness data address. -/
def aesWitAdr : Adresse := BitVec.ofNat 64 12288

/-- Core 1 MOVBE16 store: the swapped bytes issue into its buffer. -/
theorem aesWit_store_puffer :
    aesWitOut1.map (fun m => m.puffer 1) =
      some [⟨aesWitAdr, natByte 0x12⟩,
        ⟨addrOff aesWitAdr 1, natByte 0x34⟩] := by
  decide

/-- Core 1 MOVBE16 store advances RIP past 7 bytes. -/
theorem aesWit_store_rip :
    aesWitRip aesWitOut1 1 = some (BitVec.ofNat 64 4103) := by
  decide

/-- The machine after the core-1 store, if reached. -/
def aesWitM1 : Option HwMaschine := aesWitOut1

/-- Core 1 observes its first swapped byte (forwarding). -/
def aesWitEigen : Option (Option Byte) :=
  match aesWitM1 with
  | some m => some (loadByte (tsoAnsicht m) 1 aesWitAdr)
  | none => none

/-- Core 0 observes the old byte (no foreign forwarding). -/
def aesWitFremd : Option (Option Byte) :=
  match aesWitM1 with
  | some m => some (loadByte (tsoAnsicht m) 0 aesWitAdr)
  | none => none

/-- First drain of core 1's buffer. -/
def aesWitTso1 : Option TSOZustand :=
  match aesWitM1 with
  | some m => flushKern (tsoAnsicht m) 1
  | none => none

/-- Second drain of core 1's buffer. -/
def aesWitTso2 : Option TSOZustand :=
  match aesWitTso1 with
  | some s => flushKern s 1
  | none => none

/-- The shared bytes after both drains. -/
def aesWitNachFlush : Option (Option Byte × Option Byte) :=
  match aesWitTso2 with
  | some s => some (some (s.mem.bytes aesWitAdr),
      some (s.mem.bytes (addrOff aesWitAdr 1)))
  | none => none

/-- The data cell starts zeroed. -/
theorem aesWit_anfang_null :
    zeugeSpeicher.bytes aesWitAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 1 reads its own unflushed swapped byte. -/
theorem aesWit_weiterleitung :
    aesWitEigen = some (some (natByte 0x12)) := by
  decide

/-- No foreign forwarding: core 0 still reads zero. -/
theorem aesWit_fremd_alt :
    aesWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drains change shared memory: the cells read `12 34`. -/
theorem aesWit_spuelung_aendert_speicher :
    aesWitNachFlush =
      some (some (natByte 0x12), some (natByte 0x34)) := by
  decide

/-- A bad decode length refuses the adapter step beside the run. -/
theorem aesWit_schlechte_laenge_verweigert :
    (adapterAesClmul).schritt aesWitStart 0
      (⟨.aesencRR .xmm0 .xmm1, 0⟩ : AesClmulDec) = none :=
  adapterAesClmul_aesenc_verweigert_bei_laenge _ _ _ _ _ (by decide)

/-- The joint witness: a reached two-core family run (AESENC on core
    0, MOVBE16 store on core 1) with owner-only forwarding and a
    drain that changes actual shared memory from 0 to `12 34` --
    with the well-formedness, refusal and decode refusals beside it.
    Non-degenerate: XMM bytes change and shared memory changes. -/
theorem aesClmulWit_zeuge :
    aesWitLane aesWitOut0 0 XmmReg.xmm0 0 = some 99 ∧
      laneNat .b8 (aesWitXmm0 XmmReg.xmm0) 0 = 0 ∧
      aesWitOut1.map (fun m => m.puffer 1) =
        some [⟨aesWitAdr, natByte 0x12⟩,
          ⟨addrOff aesWitAdr 1, natByte 0x34⟩] ∧
      aesWitRip aesWitOut1 1 = some (BitVec.ofNat 64 4103) ∧
      aesWitEigen = some (some (natByte 0x12)) ∧
      aesWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      aesWitNachFlush =
        some (some (natByte 0x12), some (natByte 0x34)) ∧
      zeugeSpeicher.bytes aesWitAdr = BitVec.ofNat 8 0 ∧
      HwWf aesWitStart ∧
      (adapterAesClmul).schritt aesWitStart 0
        (⟨.aesencRR .xmm0 .xmm1, 0⟩ : AesClmulDec) = none ∧
      decodeAesClmul [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 0, natByte 200] = none ∧
      kapDecodeAes [natByte 64, natByte 102, natByte 15, natByte 58,
        natByte 20, natByte 200, natByte 0] = none := by
  refine ⟨aesWit_enc_lane0, aesWit_enc_vorher, aesWit_store_puffer,
    aesWit_store_rip, aesWit_weiterleitung, aesWit_fremd_alt,
    aesWit_spuelung_aendert_speicher, aesWit_anfang_null,
    aesWitStart_wf, aesWit_schlechte_laenge_verweigert,
    aesClmul_nichts_pshufb, kapAes_nichts_blendv⟩

/- CUTS:
   Proved here: seventeen admitted rows (AESENC/AESENCLAST/AESDEC/
   AESDECLAST/AESIMC `66 0F 38 DC/DD/DE/DF/DB`, AESKEYGENASSIST
   `66 0F 3A DF + imm8`, PCLMULQDQ `66 0F 3A 44 + imm8`, MOVBE
   `0F 38 F0/F1` at 16/32/64-bit over base+disp memory, PHADDW/
   PHADDD/PHSUBW/PHSUBD/PSIGNB/W/D/PMULHRSW `66 0F 38
   01/02/05/06/08/09/0A/0B`) with canonical encoding, a canonical
   decoder, per-row round trips, planted decoder refusals, twenty
   decide-pins that the old capstone chain refuses the new bytes,
   value semantics from the accepted lane vocabulary with per-lane
   equations and silicon spot-checks (S-box/InvS-box known answers
   plus mutual inversion over all 256 bytes, ShiftRows inversion,
   MixColumns inversion, round spot-checks, carry-less spot-checks
   with both imm8 half selections, byte-swap spot-checks), family
   register and MOVBE memory steps with frame theorems, the extended
   chain `kapDecodeAes` with exact agreement and extended-chain
   pins, the `HwAdapter AesClmulDec` plug with well-formedness
   preservation and planted refusals, and a reached two-core run
   (AESENC on core 0, MOVBE16 store on core 1) with owner-only
   forwarding and a memory-changing drain.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the canonical subset
     with self-consistency only, not x86 truth. Silicon assumptions
     named: the opcode rows (SDM Vol. 2A 3-33/3-39/3-45/3-51/3-57/
     3-58, Vol. 2B 4-45/4-242/4-294/4-302/4-375/4-437), the AES
     round order (ShiftRows/SubBytes/MixColumns, key XOR last),
     SubWord/RotWord/RCON of the key assist, the PCLMUL128 bit
     formula with imm8[0]/imm8[4] half selection, MOVBE byte
     reversal with F0=load/F1=store, PHADD/PHSUB wrapping (NOT
     saturating: only PHADDSW saturates), PSIGN negate/zero/keep,
     PMULHRSW `((a*b)>>14)+1` bits `[16:1]` with arithmetic shifts,
     legacy-SSE whole-register XMM writes, no flag/memory/GPR
     effect, disp8 sign extension. The S-box table transcription
     past the checked pins is a NAMED assumption. REX-first byte
     order follows the accepted tree convention (VectorCodec,
     SseThreeByte); silicon wants legacy prefixes before REX.
   - No MMX (NP) forms, no XMM memory ModRM forms, no SIB/index
     forms, no RIP-relative or disp-less MOVBE, no REX.W on XMM
     rows, no `66`+REX.W, no VEX/EVEX, no PHADDSW saturation, no
     other third byte in either escape (SSE4.1/SSE4.2/CRC32 stay
     refused).
   - No LOCK path, no fault delivery beyond explicit refusal
     (`#UD` on missing CPUID, `#GP` on unaligned XMM memory and
     LOCK+MOVBE are named, not modelled), no source/IR/ABI/loader/
     entry/budget link, no per-access target-to-W/GX simulation,
     no timing/power behaviour.
   - A maintainer wires the family in by adding the
     `decodeAesClmul` arm behind every earlier arm of
     `HwKapsteinDecoder.kapDecode`.
-/

#print axioms encodeAesClmul
#print axioms decodeAesClmul
#print axioms roundtripAesClmul
#print axioms movbeTausch
#print axioms aesSBoxNat
#print axioms aesEncRound
#print axioms aesKeygen
#print axioms vecPclmul
#print axioms vecPhadd
#print axioms vecPsign
#print axioms vecPmulhrsw
#print axioms stepAesClmulReg
#print axioms movbeStore
#print axioms movbeLoad
#print axioms kapDecodeAes
#print axioms adapterAesClmul
#print axioms adapterAesClmul_wf
#print axioms aesWitStart_wf
#print axioms aesClmulWit_zeuge

end Gabbro.Grammatik.X86
