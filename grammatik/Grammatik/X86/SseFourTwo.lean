/-
  File:      Grammatik/X86/SseFourTwo.lean
  Subject:   SSE4.2 register-direct rows (string compares, PCMPGTQ, CRC32),
    connected to the coherent machine and the capstone chain.

  Lane 1379: admitted register-direct forms only --
  PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM (`66 0F 3A 60-63 /r ib`),
  PCMPGTQ (`66 0F 38 37 /r`), CRC32 r32/r64 (`F2 0F 38 F0/F1 /r`).
  Semantics follow the Intel SDM (clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  Vol. 2B section 4.1 (imm8 matrix), PCMPESTRI/PCMPESTRM/PCMPISTRI
  pages (lengths, flags, ECX/XMM0 outputs), PCMPGTQ (signed qwords),
  CRC32 (polynomial 11EDC6F41H, DEST[63:32] := 0 always).
  Memory ModRM forms, VEX/EVEX and every other row stay refused.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Admitted SSE4.2 string-compare kinds (opcode selects
    explicit/implicit lengths and index/mask output). -/
inductive StrArt where
  | estri | estrm | istri | istrm
  deriving DecidableEq, Repr

/-- Decoded imm8 mode: data format, aggregation, polarity,
    output select (SDM Vol. 2B Table 4-8). -/
structure StrModus where
  format : Nat
  aggreg : Nat
  polar : Nat
  mssb : Bool
  deriving DecidableEq, Repr

/-- Decode the imm8 control byte into its four fields. -/
def modusVonImm (imm : Nat) : StrModus :=
  ⟨imm % 4, imm / 4 % 4, imm / 16 % 4, decide (imm / 64 % 2 = 1)⟩

/-- The mode fields invert the control byte below 128. -/
theorem modusVonImm_felder (imm : Nat) :
    (modusVonImm imm).format = imm % 4 ∧
      (modusVonImm imm).aggreg = imm / 4 % 4 ∧
      (modusVonImm imm).polar = imm / 16 % 4 := by
  unfold modusVonImm
  exact ⟨rfl, rfl, rfl⟩

/-- CRC32 source widths: byte, word, dword, qword
    (the F0 row takes byte, the F1 row takes word/dword/qword). -/
inductive CrcWeite where
  | b8 | b16 | b32 | b64
  deriving DecidableEq, Repr

/-- Admitted SSE4.2 register-direct forms: the four string compares
    (with their imm8), the signed-qword compare, and the five CRC32
    destination/source-width rows (r64 destination only with a
    byte or qword source, SDM Vol. 2A 3-205 table). -/
inductive Sse42Op where
  | strRR (art : StrArt) (dst src : XmmReg) (imm : Nat)
  | pcmpgtqRR (dst src : XmmReg)
  | crc32 (w64 : Bool) (sw : CrcWeite) (dst src : Register)
  deriving DecidableEq, Repr

/-- Third opcode byte: `60-63` for the string compares over the
    `0F 3A` escape, `37` for PCMPGTQ over `0F 38`,
    `F0/F1` for CRC32 over `0F 38` (SDM pages). -/
def sse42Third : Sse42Op → Nat
  | .strRR .estrm _ _ _ => 96
  | .strRR .estri _ _ _ => 97
  | .strRR .istrm _ _ _ => 98
  | .strRR .istri _ _ _ => 99
  | .pcmpgtqRR _ _ => 55
  | .crc32 _ .b8 _ _ => 240
  | .crc32 _ _ _ _ => 241

/-- Canonical REX byte (X=0, no SIB anywhere in this family):
    string/qword rows fix W=0; CRC32 carries W for an r64
    destination. `64 + 8*W + 4*R + B`. -/
def sse42Rex : Sse42Op → Byte
  | .strRR _ dst src _ => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pcmpgtqRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .crc32 w64 _ dst src =>
    natByte (64 + (if w64 then 8 else 0) + 4 * regHigh dst + regHigh src)

/-- Canonical byte encoding. String rows: REX, `66`, `0F`, `3A`,
    third byte, register-direct ModRM, imm8 (7 bytes). PCMPGTQ:
    REX, `66`, `0F`, `38`, `37`, ModRM (6 bytes). CRC32: `F2`,
    optional `66` for a word source, REX, `0F`, `38`, `F0/F1`,
    ModRM (6 or 7 bytes). -/
def encodeSse42 : Sse42Op → List Byte
  | op@(.strRR _ dst src imm) =>
    [sse42Rex op, natByte 102, natByte 15, natByte 58,
      natByte (sse42Third op), modrmReg (xmmLow dst) (xmmLow src),
      natByte (imm % 256)]
  | op@(.pcmpgtqRR dst src) =>
    [sse42Rex op, natByte 102, natByte 15, natByte 56,
      natByte (sse42Third op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.crc32 _ sw dst src) =>
    (natByte 242 ::
      (match sw with | .b16 => [natByte 102] | _ => []) ++
      [sse42Rex op, natByte 15, natByte 56,
        natByte (sse42Third op),
        modrmReg (regLow dst) (regLow src)])

/-- Every canonical string encoding is 7 bytes. -/
theorem encodeSse42_str_len (art : StrArt) (dst src : XmmReg)
    (imm : Nat) :
    (encodeSse42 (.strRR art dst src imm)).length = 7 := by
  cases art <;> cases dst <;> cases src <;> rfl

/-- Every canonical PCMPGTQ encoding is 6 bytes. -/
theorem encodeSse42_pcmpgtq_len (dst src : XmmReg) :
    (encodeSse42 (.pcmpgtqRR dst src)).length = 6 := by
  cases dst <;> cases src <;> rfl

/-- Canonical CRC32 length: 7 exactly for a word source
    (the `66` prefix), 6 otherwise. -/
theorem encodeSse42_crc_len (w64 : Bool) (sw : CrcWeite)
    (dst src : Register) :
    (encodeSse42 (.crc32 w64 sw dst src)).length =
      (match sw with | .b16 => 7 | _ => 6) := by
  cases sw <;> cases dst <;> cases src <;> rfl

/-! ## 3. No shadowing: the old chain refuses the new rows. -/

/-- The old capstone chain refuses the canonical PCMPESTRI bytes. -/
theorem kap_weist_estri_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 97, natByte 200, natByte 0] = none := by
  decide

/-- The old capstone chain refuses the canonical PCMPESTRM bytes. -/
theorem kap_weist_estrm_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 96, natByte 200, natByte 0] = none := by
  decide

/-- The old capstone chain refuses the canonical PCMPISTRI bytes. -/
theorem kap_weist_istri_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 99, natByte 200, natByte 0] = none := by
  decide

/-- The old capstone chain refuses the canonical PCMPISTRM bytes. -/
theorem kap_weist_istrm_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 98, natByte 200, natByte 0] = none := by
  decide

/-- The old capstone chain refuses the canonical PCMPGTQ bytes. -/
theorem kap_weist_pcmpgtq_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 55, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical CRC32 bytes. -/
theorem kap_weist_crc32_zurueck :
    kapDecode [natByte 242, natByte 64, natByte 15, natByte 56,
      natByte 241, natByte 192] = none := by
  decide

/-! ## 4. Canonical decoder.

  The decoder parses bytes, never encode-equality. String and
  qword rows take the canonical W=0 REX (`64 + 4*R + B`), then
  `66`, `0F`, the escape, the third byte, a register-direct
  ModRM (mod=3, reg=dst, r/m=src) and (strings) the imm8.
  CRC32 rows take `F2`, an optional `66` (word source only),
  a canonical X=0 REX (W selects an r64 destination), `0F`,
  `38`, `F0` (byte source) or `F1`, and a register-direct
  ModRM. Anything else refuses with `none`. -/

/-- A decoded SSE4.2 form: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure Sse42Dec where
  op : Sse42Op
  laenge : Nat
  deriving DecidableEq, Repr

/-- Decode one register-direct ModRM byte to a GPR pair. -/
def decodeModrmGPR (rBit bBit : Nat) :
    List Byte → Option ((Register × Register) × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (rBit * 8 + byteNat m / 8 % 8),
        codeReg (bBit * 8 + byteNat m % 8) with
      | some dst, some src => some ((dst, src), rest)
      | _, _ => none
    else none

/-- Decode one register-direct ModRM byte to an XMM pair. -/
def decodeModrmXMM (rBit bBit : Nat) :
    List Byte → Option ((XmmReg × XmmReg) × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + byteNat m / 8 % 8),
        codeXmm (bBit * 8 + byteNat m % 8) with
      | some dst, some src => some ((dst, src), rest)
      | _, _ => none
    else none

/-- String art of a third opcode byte over the `0F 3A` escape. -/
def strArtVonThird : Nat → Option StrArt
  | 96 => some .estrm
  | 97 => some .estri
  | 98 => some .istrm
  | 99 => some .istri
  | _ => none

/-- Decode after `66 0F 3A`: the third byte selects the art;
    then a register-direct ModRM and the imm8 tail. -/
def decodeSse42StrDritt (t rBit bBit : Nat) :
    List Byte → Option (Sse42Op × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + byteNat m / 8 % 8),
        codeXmm (bBit * 8 + byteNat m % 8) with
      | some dst, some src =>
        match strArtVonThird t with
        | some art =>
          match rest with
          | [] => none
          | imm :: rest2 =>
            some ((.strRR art dst src (byteNat imm)), rest2)
        | none => none
      | _, _ => none
    else none

/-- Decode after `66 0F`: the escape selects the string map
    (`3A`, third byte plus imm8 tail) or the qword row
    (`38` with third byte `37`). -/
def decodeSse42NachEscape (rBit bBit : Nat) :
    List Byte → Option (Sse42Op × List Byte)
  | [] => none
  | e :: rest =>
    if byteNat e == 58 then
      match rest with
      | [] => none
      | t :: rest2 =>
        decodeSse42StrDritt (byteNat t) rBit bBit rest2
    else if byteNat e == 56 then
      match rest with
      | [] => none
      | t :: rest2 =>
        if byteNat t == 55 then
          match decodeModrmXMM rBit bBit rest2 with
          | none => none
          | some ((dst, src), rest3) =>
            some ((.pcmpgtqRR dst src), rest3)
        else none
    else none

/-- Decode after a W=0 REX with extension bits: `66`, `0F`,
    then the escape. -/
def decodeSse42VecNach (rBit bBit : Nat) :
    List Byte → Option (Sse42Op × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 102 then
      match rest with
      | [] => none
      | p2 :: rest2 =>
        if byteNat p2 == 15 then
          decodeSse42NachEscape rBit bBit rest2
        else none
    else none

/-- CRC32 width of the `F0/F1` third byte with the `66` flag
    and the REX.W bit: `F1` without `66` is a dword source at
    W=0 and a qword source at W=1 (operand-size rule). -/
def crcWeiteVon (hat66 : Bool) (w dritt : Nat) : Option CrcWeite :=
  match hat66, w, dritt with
  | false, 0, 240 => some .b8
  | false, 1, 240 => some .b8
  | false, 0, 241 => some .b32
  | false, 1, 241 => some .b64
  | true, 0, 241 => some .b16
  | _, _, _ => none

/-- Decode after `F2`, the optional `66` and the REX byte:
    `0F`, `38`, third byte, register-direct ModRM. An r64
    destination (REX.W) is admitted only with a byte or qword
    source (SDM Vol. 2A 3-205 table has no r64 row for
    word/dword). -/
def decodeCrcNachRex (hat66 : Bool) (w rBit bBit : Nat) :
    List Byte → Option (Sse42Op × List Byte)
  | [] => none
  | q :: rest3 =>
    if byteNat q == 15 then
      match rest3 with
      | [] => none
      | e :: rest4 =>
        if byteNat e == 56 then
          match rest4 with
          | [] => none
          | t :: rest5 =>
            match crcWeiteVon hat66 w (byteNat t) with
            | none => none
            | some sw =>
              match decodeModrmGPR rBit bBit rest5 with
              | none => none
              | some ((dst, src), rest6) =>
                some ((.crc32 (w == 1) sw dst src), rest6)
        else none
    else none

/-- REX dispatch for CRC32: the eight canonical X=0 bytes,
    back to the W/R/B extension bits. -/
def decodeCrcRex (hat66 : Bool) :
    List Byte → Option (Sse42Op × List Byte)
  | [] => none
  | r :: rest2 =>
    match byteNat r with
    | 64 => decodeCrcNachRex hat66 0 0 0 rest2
    | 65 => decodeCrcNachRex hat66 0 0 1 rest2
    | 68 => decodeCrcNachRex hat66 0 1 0 rest2
    | 69 => decodeCrcNachRex hat66 0 1 1 rest2
    | 72 => decodeCrcNachRex hat66 1 0 0 rest2
    | 73 => decodeCrcNachRex hat66 1 0 1 rest2
    | 76 => decodeCrcNachRex hat66 1 1 0 rest2
    | 77 => decodeCrcNachRex hat66 1 1 1 rest2
    | _ => none

/-- Decode after `F2`: optional `66`, then the REX byte. -/
def decodeCrcNachF2 : List Byte → Option (Sse42Op × List Byte)
  | [] => none
  | p :: rest =>
    if byteNat p == 102 then decodeCrcRex true rest
    else decodeCrcRex false (p :: rest)

/-- Top-level SSE4.2 decode: the first byte selects the prefix
    family (`F2` for CRC32, canonical W=0 REX for the vector
    rows). The decoded length is the canonical encoding length
    of the decoded form. -/
def decodeSse42 : List Byte → Option (Sse42Dec × List Byte)
  | [] => none
  | r :: tail =>
    let nach (rBit bBit : Nat) :=
      match decodeSse42VecNach rBit bBit tail with
      | some (op, rest) =>
        some ((⟨op, (encodeSse42 op).length⟩ : Sse42Dec), rest)
      | none => none
    if byteNat r == 242 then
      match decodeCrcNachF2 tail with
      | some (op, rest) =>
        some ((⟨op, (encodeSse42 op).length⟩ : Sse42Dec), rest)
      | none => none
    else
      match byteNat r with
      | 64 => nach 0 0
      | 65 => nach 0 1
      | 68 => nach 1 0
      | 69 => nach 1 1
      | _ => none

/-! ## 5. Round trip and planted refusals. -/

/-- Probe pin: PCMPESTRI xmm1, xmm0, 0 decodes. -/
theorem sonden_estri :
    decodeSse42 [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 97, natByte 200, natByte 0] =
      some ((⟨.strRR .estri .xmm1 .xmm0 0, 7⟩ : Sse42Dec), []) := by
  decide

/-- Probe pin: PCMPGTQ xmm1, xmm0 decodes. -/
theorem sonden_pcmpgtq :
    decodeSse42 [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 55, natByte 200] =
      some ((⟨.pcmpgtqRR .xmm1 .xmm0, 6⟩ : Sse42Dec), []) := by
  decide

/-- Probe pin: CRC32 eax, eax decodes. -/
theorem sonden_crc :
    decodeSse42 [natByte 242, natByte 64, natByte 15, natByte 56,
      natByte 241, natByte 192] =
      some ((⟨.crc32 false .b32 .rax .rax, 6⟩ : Sse42Dec), []) := by
  decide

/-- Normal form: the decoded imm8 is the encoded byte value,
    stated exactly as the decoder computes it. -/
def sse42Norm : Sse42Op → Sse42Op
  | .strRR art dst src imm =>
    .strRR art dst src (byteNat (natByte (imm % 256)))
  | op => op

/-- The normal form is the byte value of the control byte. -/
theorem sse42Norm_imm_eq (art : StrArt) (dst src : XmmReg)
    (imm : Nat) :
    sse42Norm (.strRR art dst src imm) =
      .strRR art dst src (imm % 256) := by
  simp only [sse42Norm, byteNat_natByte_mod]

/-- Round trip for the string rows, over any suffix. -/
theorem roundtrip_str (art : StrArt) (dst src : XmmReg)
    (imm : Nat) (suffix : List Byte) :
    decodeSse42 (encodeSse42 (.strRR art dst src imm) ++ suffix) =
      some ((⟨sse42Norm (.strRR art dst src imm),
        (encodeSse42 (sse42Norm (.strRR art dst src imm))).length⟩ :
        Sse42Dec), suffix) := by
  cases art <;> cases dst <;> cases src <;> rfl

/-- Round trip for PCMPGTQ, over any suffix. -/
theorem roundtrip_pcmpgtq (dst src : XmmReg) (suffix : List Byte) :
    decodeSse42 (encodeSse42 (.pcmpgtqRR dst src) ++ suffix) =
      some ((⟨.pcmpgtqRR dst src,
        (encodeSse42 (.pcmpgtqRR dst src)).length⟩ : Sse42Dec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Admitted CRC32 width rows (SDM Vol. 2A 3-205 table):
    r32 destination with byte/word/dword source, r64
    destination with byte/qword source. -/
def crcZulaessig (w64 : Bool) (sw : CrcWeite) : Bool :=
  match w64, sw with
  | false, .b8 => true
  | false, .b16 => true
  | false, .b32 => true
  | true, .b8 => true
  | true, .b64 => true
  | _, _ => false

/-- Round trip for CRC32, over any suffix, on admitted rows. -/
theorem roundtrip_crc (w64 : Bool) (sw : CrcWeite)
    (dst src : Register) (suffix : List Byte)
    (h : crcZulaessig w64 sw = true) :
    decodeSse42 (encodeSse42 (.crc32 w64 sw dst src) ++ suffix) =
      some ((⟨.crc32 w64 sw dst src,
        (encodeSse42 (.crc32 w64 sw dst src)).length⟩ : Sse42Dec),
        suffix) := by
  cases w64 with
  | false =>
    cases sw with
    | b8 => cases dst <;> cases src <;> rfl
    | b16 => cases dst <;> cases src <;> rfl
    | b32 => cases dst <;> cases src <;> rfl
    | b64 => simp [crcZulaessig] at h
  | true =>
    cases sw with
    | b8 => cases dst <;> cases src <;> rfl
    | b16 => simp [crcZulaessig] at h
    | b32 => simp [crcZulaessig] at h
    | b64 => cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every covered row, over any
    suffix, up to imm8 normalisation and on admitted CRC rows. -/
theorem roundtripSse42 (op : Sse42Op) (suffix : List Byte)
    (h : match op with
      | .crc32 w64 sw _ _ => crcZulaessig w64 sw = true
      | _ => True) :
    decodeSse42 (encodeSse42 op ++ suffix) =
      some ((⟨sse42Norm op,
        (encodeSse42 (sse42Norm op)).length⟩ : Sse42Dec),
        suffix) := by
  cases op with
  | strRR art dst src imm => exact roundtrip_str art dst src imm suffix
  | pcmpgtqRR dst src => exact roundtrip_pcmpgtq dst src suffix
  | crc32 w64 sw dst src => exact roundtrip_crc w64 sw dst src suffix h

/-- A memory ModRM (mod≠3) is refused on the string rows. -/
theorem sse42_nichts_speicher :
    decodeSse42 [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 97, natByte 8, natByte 0] = none := rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem sse42_nichts_kurz :
    decodeSse42 [natByte 64, natByte 102] = none := rfl

/-- A REX.W form is refused on the string rows. -/
theorem sse42_nichts_rexw :
    decodeSse42 [natByte 72, natByte 102, natByte 15, natByte 58,
      natByte 97, natByte 200, natByte 0] = none := rfl

/-- An uncovered `0F 38` third byte (PMOVSXBW `20`) is refused
    here: the SSE4.1 family owns it. -/
theorem sse42_nichts_pmovsxbw :
    decodeSse42 [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 32, natByte 200] = none := rfl

/-- An uncovered `0F 3A` third byte is refused. -/
theorem sse42_nichts_dritt :
    decodeSse42 [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200, natByte 4] = none := rfl

/-- A missing `F2` prefix is refused on the CRC32 rows. -/
theorem sse42_nichts_ohne_f2 :
    decodeSse42 [natByte 64, natByte 15, natByte 56,
      natByte 241, natByte 192] = none := rfl

/-- An r64 destination with a word source is refused (the SDM
    table has no such row). -/
theorem sse42_nichts_crc64_wort :
    decodeSse42 [natByte 242, natByte 102, natByte 72, natByte 15,
      natByte 56, natByte 241, natByte 192] = none := rfl

/-- The r64/F1 byte string decodes as the qword-source row:
    REX.W over `F1` IS a 64-bit source (operand-size rule, exactly
    like silicon), so encoding aliases the refused dword row here. -/
theorem sse42_crc64_dwort_ist_qwort :
    decodeSse42 [natByte 242, natByte 72, natByte 15, natByte 56,
      natByte 241, natByte 192] =
      some ((⟨.crc32 true .b64 .rax .rax, 6⟩ : Sse42Dec), []) := by
  decide

/-! ## 6. Semantics from the SDM pages.

  Built from the accepted lane vocabulary only (`laneNat`/`vecMk`,
  `trunc`, `mergeRegNarrow`); no evaluator is redefined.
  - PCMPGTQ (Vol. 2B 4-264): signed qword greater-than, all-ones
    on true else zero, no flag effect.
  - CRC32 (Vol. 2A 3-205): polynomial 11EDC6F41H in reflected
    bit order (reflected form 0xEDB88320 = 3988292384), result
    in the low doubleword, DEST[63:32] := 0 always, no flag
    effect. With REX in the canonical bytes, source codes 4-7
    are SPL/BPL/SIL/DIL (low bytes, SDM note 1); the source is
    always the low byte/word/dword/qword of the GPR.
  - String compares (Vol. 2B 4.1/4-254ff): full imm8 matrix over
    explicit (|EAX|/|EDX| saturated) or implicit (null scan)
    lengths, Table 4-7 invalid override, Table 4-4 polarity,
    ECX index / XMM0 mask outputs, and the overloaded flags
    (CF = res2 != 0, ZF/SF = short-or-null per side,
    OF = res2[0], AF = PF = false). -/

/-- Signed value of a 64-bit lane: `u` below 2^63, else `u - 2^64`. -/
def sVal64 (u : Nat) : Int :=
  if u < 2 ^ 63 then (u : Int) else (u : Int) - 2 ^ 64

/-- Signed qword greater-than (PCMPGTQ): lane all-ones iff the
    old destination lane is strictly greater than the source
    lane, else zero. -/
def vecPcmpgtq (dst src : Vektor) : Vektor :=
  vecMk .b64 (fun i =>
    if sVal64 (laneNat .b64 src i) < sVal64 (laneNat .b64 dst i) then
      2 ^ 64 - 1
    else 0)

/-- Per-lane greater-than is the signed comparison function. -/
theorem laneNat_pcmpgtq (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b64) :
    laneNat .b64 (vecPcmpgtq dst src) i =
      ((if sVal64 (laneNat .b64 src i) < sVal64 (laneNat .b64 dst i) then
        2 ^ 64 - 1 else 0) % 2 ^ Breite.b64.bits) := by
  unfold vecPcmpgtq
  exact laneGet_mk .b64 _ i hi

/-- Silicon spot-check: greater picks the greater lane, equal
    gives zero, and the comparison is signed (max-positive beats
    min-negative, where unsigned order would say otherwise). -/
theorem vecPcmpgtq_silicon :
    laneNat .b64 (vecPcmpgtq (vecMk .b64 (fun _ => 8))
      (vecMk .b64 (fun _ => 7))) 0 = 18446744073709551615 ∧
    laneNat .b64 (vecPcmpgtq (vecMk .b64 (fun _ => 7))
      (vecMk .b64 (fun _ => 7))) 0 = 0 ∧
    laneNat .b64 (vecPcmpgtq
      (vecMk .b64 (fun _ => 9223372036854775807))
      (vecMk .b64 (fun _ => 9223372036854775808))) 0 =
      18446744073709551615 := by
  decide

/-- One reflected CRC step over a single data bit: shift right,
    xor the reflected polynomial 0xEDB88320 iff the outgoing
    bit disagrees with the data bit (SDM pseudocode, reflected
    half of the MOD2 division by 11EDC6F41H). -/
def crcBit (s d : Nat) : Nat :=
  let bit := (s + d) % 2
  let halb := s / 2
  if bit = 1 then Nat.xor halb 3988292384 else halb

/-- `n` reflected CRC steps consuming the low bits of `d`. -/
def crcBits (s d : Nat) : Nat → Nat
  | 0 => s
  | n + 1 => crcBits (crcBit s (d % 2)) (d / 2) n

/-- CRC over the `k` low bytes of `v` (little-endian order). -/
def crcBytes (s v : Nat) : Nat → Nat
  | 0 => s
  | k + 1 => crcBytes (crcBits s (v % 256) 8) (v / 256) k

/-- Source bytes of one CRC32 width. -/
def crcQuellBytes : CrcWeite → Nat
  | .b8 => 1 | .b16 => 2 | .b32 => 4 | .b64 => 8

/-- Full CRC32 value: the source bytes accumulated into the low
    doubleword of the destination (DEST[63:32] := 0, SDM). -/
def crcWert (dst src : Wort) (sw : CrcWeite) : Wort :=
  BitVec.ofNat 64 (crcBytes ((trunc .b32 dst).toNat) src.toNat
    (crcQuellBytes sw) % 2 ^ 32)

/-- Mechanism pins: a zero step fixes zero, a one bit xors the
    reflected polynomial, and empty input keeps the state. -/
theorem crcBit_pine :
    crcBit 0 0 = 0 ∧ crcBit 0 1 = 3988292384 ∧
    crcBytes 12345 678 0 = 12345 ∧
    crcQuellBytes .b8 = 1 ∧ crcQuellBytes .b16 = 2 ∧
    crcQuellBytes .b32 = 4 ∧ crcQuellBytes .b64 = 8 := by
  decide

/-! ## 7. String comparison matrix (SDM Vol. 2B 4.1).

  Element index `i` runs over the first operand (ModRM reg,
  EAX side), `j` over the second (ModRM r/m, EDX side); the
  intermediate result has one bit per second-operand element
  (Tables 4-2/4-3), polarity follows Table 4-4, validity
  override Table 4-7. -/

/-- Lane width of a data format (imm8 bit 0). -/
def strWeite (fmt : Nat) : Breite :=
  if fmt % 2 = 0 then .b8 else .b16

/-- Element count of a data format: 16 bytes or 8 words. -/
def strAnzahl (fmt : Nat) : Nat :=
  if fmt % 2 = 0 then 16 else 8

/-- Signedness of a data format (imm8 bit 1). -/
def strSigniert (fmt : Nat) : Bool :=
  decide (fmt / 2 % 2 = 1)

/-- Signed value at element width `w` (8 or 16). -/
def sValW (w x : Nat) : Int :=
  if x < 2 ^ (w - 1) then (x : Int) else (x : Int) - 2 ^ w

/-- Unsigned/signed less-or-equal at element width `w`. -/
def strKleinGleich (signiert : Bool) (w x y : Nat) : Bool :=
  if signiert then decide (sValW w x ≤ sValW w y)
  else decide (x ≤ y)

/-- Null-element scan: index of the first zero element, or the
    full count when no element is null (implicit lengths, the
    least-significant null itself counts invalid). -/
def strNullAux (elem : Nat → Nat) : Nat → Nat → Nat
  | start, 0 => start
  | start, fuel + 1 =>
    if elem start == 0 then start
    else strNullAux elem (start + 1) fuel

/-- Implicit length of one string fragment. -/
def strNullStelle (elem : Nat → Nat) (anzahl : Nat) : Nat :=
  strNullAux elem 0 anzahl

/-- Absolute saturated length (explicit lengths: |value| of the
    low doubleword, saturated to the element count). -/
def strAbsLaenge (v : Wort) (anzahl : Nat) : Nat :=
  let u := v.toNat % 2 ^ 32
  let a := if u < 2 ^ 31 then u else 2 ^ 32 - u
  if a < anzahl then a else anzahl

/-- Pairwise comparison with invalid override (Table 4-7):
    `agg` 0 equal-any, 1 ranges (pairs in the first operand:
    even bound below, odd bound above), 2 equal-each, 3 equal-
    ordered. `vai`/`vbj` are the validity bits. -/
def strBool (agg : Nat) (signiert : Bool) (w : Nat)
    (a b : Nat → Nat) (vai vbj : Bool) (j i : Nat) : Bool :=
  let eq : Bool := a i == b j
  let ge : Bool := strKleinGleich signiert w (a i) (b j)
  let le : Bool := strKleinGleich signiert w (b j) (a i)
  match agg with
  | 0 => vai && vbj && eq
  | 1 => vai && vbj && (if i % 2 = 0 then ge else le)
  | 2 => (!vai && !vbj) || (vai && vbj && eq)
  | _ => !vai || (vbj && eq)

/-- Disjunctive fold over `n` values from `start`. -/
def orFalte (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => false
  | start, n + 1 => f start || orFalte f (start + 1) n

/-- Conjunctive fold over `n` values from `start`. -/
def andFalte (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | start, n + 1 => f start && andFalte f (start + 1) n

/-- Intermediate bit `j` (Table 4-3): equal-any ors the column,
    ranges ors the even/odd pair conjunctions, equal-each takes
    the diagonal, equal-ordered ands the shifted diagonal. -/
def strRes1Bit (agg anzahl : Nat) (f : Nat → Nat → Bool)
    (j : Nat) : Bool :=
  match agg with
  | 0 => orFalte (f j) 0 anzahl
  | 1 => orFalte (fun k => f j (2 * k) && f j (2 * k + 1)) 0
      (anzahl / 2)
  | 2 => f j j
  | _ => andFalte (fun t => f (j + t) t) 0 (anzahl - j)

/-- Output bit `j` (Table 4-4): positive keeps, negative
    complements, masked keeps on invalid second-operand
    elements and complements the valid ones. -/
def strRes2Bit (pol : Nat) (res1 : Nat → Bool)
    (vbj : Bool) (j : Nat) : Bool :=
  match pol with
  | 0 => res1 j
  | 1 => !res1 j
  | 2 => res1 j
  | _ => if vbj then !res1 j else res1 j

/-- Bitmask of the first `n` output bits from `start`. -/
def strRes2 (f : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | start, n + 1 =>
    (if f start then 2 ^ start else 0) + strRes2 f (start + 1) n

/-- Least-significant set bit below `anzahl`, else `anzahl`. -/
def strErsterAux (res2 : Nat) : Nat → Nat → Nat
  | j, 0 => j
  | j, fuel + 1 =>
    if res2 / 2 ^ j % 2 = 1 then j
    else strErsterAux res2 (j + 1) fuel

/-- Least-significant set bit of the intermediate result. -/
def strErster (res2 anzahl : Nat) : Nat :=
  strErsterAux res2 0 anzahl

/-- Most-significant set bit below `anzahl`, else `anzahl`. -/
def strLetzterAux (res2 anzahl : Nat) : Nat → Nat
  | 0 => anzahl
  | j + 1 =>
    if res2 / 2 ^ j % 2 = 1 then j
    else strLetzterAux res2 anzahl j

/-- Most-significant set bit of the intermediate result. -/
def strLetzter (res2 anzahl : Nat) : Nat :=
  strLetzterAux res2 anzahl anzahl

/-- Overloaded arithmetic flags (CF = result nonzero, ZF/SF =
    short-or-null per side, OF = bit 0, AF = PF = reset). -/
def strFlags (zf sf : Bool) (res2 : Nat) : Flags :=
  { cf := res2 != 0, pf := false, af := some false, zf := zf,
    sf := sf, of := res2 % 2 = 1 }

/-- One full string evaluation: intermediate mask, ECX index,
    XMM0 mask word, and flags. Lengths come from EAX/EDX
    (explicit) or the null scan (implicit); null presence is
    length below the full count. -/
structure StrErg where
  res2 : Nat
  index : Nat
  maske : Vektor
  flags : Flags
  deriving DecidableEq, Repr

/-- Full string evaluation for one art and mode. -/
def strAuswertung (art : StrArt) (modus : StrModus)
    (dstV srcV : Vektor) (dstR srcR : Wort) : StrErg :=
  let w := strWeite modus.format
  let anzahl := strAnzahl modus.format
  let signiert := strSigniert modus.format
  let elemD : Nat → Nat := fun i => laneNat w dstV i
  let elemS : Nat → Nat := fun j => laneNat w srcV j
  let explizit : Bool :=
    match art with | .estri => true | .estrm => true | _ => false
  let la : Nat :=
    if explizit then strAbsLaenge dstR anzahl
    else strNullStelle elemD anzahl
  let lb : Nat :=
    if explizit then strAbsLaenge srcR anzahl
    else strNullStelle elemS anzahl
  let f : Nat → Nat → Bool := fun j i =>
    strBool modus.aggreg signiert w.bits elemD elemS
      (decide (i < la)) (decide (j < lb)) j i
  let res1 : Nat → Bool := fun j => strRes1Bit modus.aggreg anzahl f j
  let res2bit : Nat → Bool := fun j =>
    strRes2Bit modus.polar res1 (decide (j < lb)) j
  let res2 := strRes2 res2bit 0 anzahl
  let index :=
    if modus.mssb then strLetzter res2 anzahl
    else strErster res2 anzahl
  let maske :=
    if modus.mssb then
      vecMk w (fun j =>
        if res2 / 2 ^ j % 2 = 1 then 2 ^ w.bits - 1 else 0)
    else BitVec.ofNat 128 res2
  let zf := if explizit then decide (lb < anzahl) else decide (lb < anzahl)
  let sf := if explizit then decide (la < anzahl) else decide (la < anzahl)
  ⟨res2, index, maske, strFlags zf sf res2⟩

/-! ## 8. Step semantics on the shared XMM/GPR state.

  `stepSse42` steps ONLY the admitted forms on the SAME
  `FpZustand` the scalar FP and vector steps use (`xmmSet`
  writes the whole 128-bit register, `regSet`/`mergeRegNarrow`
  write GPRs with the architectural upper-bit discipline,
  `ripNach` advances RIP, `vecEintritt` gates on OS vector
  state). String forms read EAX/EDX lengths and write ECX
  (index) or XMM0 (mask) plus the overloaded flags; PCMPGTQ
  writes the destination XMM and keeps flags; CRC32 writes the
  destination GPR (zero-extended, DEST[63:32] := 0) and keeps
  flags. Memory and every untouched register are preserved --
  no admitted form has a memory or fault effect. -/

/-- Single SSE4.2 step; `none` is an explicit refusal (bad
    length, refused OS vector state, or refused width row). -/
def stepSse42 (d : Sse42Dec) (t : FpZustand) (b : BereitProfil) :
    Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match vecEintritt b with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.op with
      | .strRR art dst src imm =>
        let erg := strAuswertung art (modusVonImm (imm % 256))
          (t.xmm dst) (t.xmm src)
          (t.kern.register .rax) (t.kern.register .rdx)
        let rcxNeu := mergeRegNarrow .b32 (t.kern.register .rcx)
          (BitVec.ofNat 64 erg.index)
        match art with
        | .estri =>
          some ⟨⟨regSet t.kern.register .rcx rcxNeu, erg.flags,
            nach, t.kern.speicher⟩, t.xmm, t.fp⟩
        | .istri =>
          some ⟨⟨regSet t.kern.register .rcx rcxNeu, erg.flags,
            nach, t.kern.speicher⟩, t.xmm, t.fp⟩
        | .estrm =>
          some ⟨⟨t.kern.register, erg.flags, nach,
            t.kern.speicher⟩, xmmSet t.xmm .xmm0 erg.maske, t.fp⟩
        | .istrm =>
          some ⟨⟨t.kern.register, erg.flags, nach,
            t.kern.speicher⟩, xmmSet t.xmm .xmm0 erg.maske, t.fp⟩
      | .pcmpgtqRR dst src =>
        some ⟨⟨t.kern.register, t.kern.flags, nach,
          t.kern.speicher⟩,
          xmmSet t.xmm dst (vecPcmpgtq (t.xmm dst) (t.xmm src)),
          t.fp⟩
      | .crc32 w64 sw dst src =>
        match crcZulaessig w64 sw with
        | false => none
        | true =>
          let vd := mergeRegNarrow .b32 (t.kern.register dst)
            (crcWert (t.kern.register dst)
              (t.kern.register src) sw)
          some ⟨⟨regSet t.kern.register dst vd, t.kern.flags,
            nach, t.kern.speicher⟩, t.xmm, t.fp⟩

/-- A bad decode length refuses every SSE4.2 form. -/
theorem stepSse42_laenge_verweigert (d : Sse42Dec)
    (t : FpZustand) (b : BereitProfil)
    (h : laengeOk d.laenge = false) : stepSse42 d t b = none := by
  unfold stepSse42
  simp [h]

/-- Refused OS vector state refuses every SSE4.2 form. -/
theorem stepSse42_profil_verweigert (d : Sse42Dec)
    (t : FpZustand) (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (h : vecEintritt b = false) :
    stepSse42 d t b = none := by
  unfold stepSse42
  simp [hok, h]

/-- A refused CRC32 width row admits no step. -/
theorem stepSse42_crc_verweigert (w64 : Bool) (sw : CrcWeite)
    (dst src : Register) (l : Nat) (t : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (h : crcZulaessig w64 sw = false) :
    stepSse42 (⟨.crc32 w64 sw dst src, l⟩ : Sse42Dec) t b =
      none := by
  unfold stepSse42
  simp [hok, hfp, h]

/-- Every SSE4.2 step advances RIP past the decoded length. -/
theorem stepSse42_rip (d : Sse42Dec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSse42 d t b = some t') :
    t'.kern.rip = ripNach t.kern.rip d.laenge := by
  revert hstep
  unfold stepSse42
  rw [hok, hfp]
  cases hop : d.op with
  | strRR art dst src imm =>
    cases art with
    | estri => intro hstep; cases hstep; rfl
    | estrm => intro hstep; cases hstep; rfl
    | istri => intro hstep; cases hstep; rfl
    | istrm => intro hstep; cases hstep; rfl
  | pcmpgtqRR dst src => intro hstep; cases hstep; rfl
  | crc32 w64 sw dst src =>
    cases hw : crcZulaessig w64 sw with
    | true =>
      intro hstep; simp only [hw] at hstep; cases hstep; rfl
    | false =>
      intro hstep; simp only [hw] at hstep; cases hstep

/-- Every SSE4.2 step changes no memory byte. -/
theorem stepSse42_speicher (d : Sse42Dec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSse42 d t b = some t') :
    t'.kern.speicher = t.kern.speicher := by
  revert hstep
  unfold stepSse42
  rw [hok, hfp]
  cases hop : d.op with
  | strRR art dst src imm =>
    cases art with
    | estri => intro hstep; cases hstep; rfl
    | estrm => intro hstep; cases hstep; rfl
    | istri => intro hstep; cases hstep; rfl
    | istrm => intro hstep; cases hstep; rfl
  | pcmpgtqRR dst src => intro hstep; cases hstep; rfl
  | crc32 w64 sw dst src =>
    cases hw : crcZulaessig w64 sw with
    | true =>
      intro hstep; simp only [hw] at hstep; cases hstep; rfl
    | false =>
      intro hstep; simp only [hw] at hstep; cases hstep

/-- A string step installs the evaluated flags. -/
theorem stepSse42_flags_str (art : StrArt) (dst src : XmmReg)
    (imm l : Nat) (t t' : FpZustand) (b : BereitProfil)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (hstep : stepSse42 (⟨.strRR art dst src imm, l⟩ : Sse42Dec)
      t b = some t') :
    t'.kern.flags =
      (strAuswertung art (modusVonImm (imm % 256))
        (t.xmm dst) (t.xmm src)
        (t.kern.register .rax) (t.kern.register .rdx)).flags := by
  revert hstep
  unfold stepSse42
  simp only [hok, hfp]
  cases art <;> intro hstep <;> cases hstep <;> rfl

/-- A PCMPGTQ step preserves the flags. -/
theorem stepSse42_flags_pcmpgtq (dst src : XmmReg) (l : Nat)
    (t t' : FpZustand) (b : BereitProfil)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (hstep : stepSse42 (⟨.pcmpgtqRR dst src, l⟩ : Sse42Dec)
      t b = some t') :
    t'.kern.flags = t.kern.flags := by
  revert hstep
  unfold stepSse42
  simp only [hok, hfp]
  intro hstep; cases hstep; rfl

/-- A CRC32 step preserves the flags. -/
theorem stepSse42_flags_crc (w64 : Bool) (sw : CrcWeite)
    (dst src : Register) (l : Nat) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (hz : crcZulaessig w64 sw = true)
    (hstep : stepSse42 (⟨.crc32 w64 sw dst src, l⟩ : Sse42Dec)
      t b = some t') :
    t'.kern.flags = t.kern.flags := by
  revert hstep
  unfold stepSse42
  simp only [hok, hfp, hz]
  intro hstep; cases hstep; rfl

/-- A CRC32 destination holds the accumulated value,
    zero-extended (DEST[63:32] := 0). -/
theorem stepSse42_crc_wert (w64 : Bool) (sw : CrcWeite)
    (dst src : Register) (l : Nat) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (hz : crcZulaessig w64 sw = true)
    (hstep : stepSse42 (⟨.crc32 w64 sw dst src, l⟩ : Sse42Dec)
      t b = some t') :
    t'.kern.register dst =
      mergeRegNarrow .b32 (t.kern.register dst)
        (crcWert (t.kern.register dst)
          (t.kern.register src) sw) := by
  revert hstep
  unfold stepSse42
  simp only [hok, hfp, hz]
  intro hstep; cases hstep
  show regSet t.kern.register dst _ dst = _
  simp [regSet]

/-- A PCMPGTQ step keeps every other XMM register whole. -/
theorem stepSse42_pcmpgtq_fremd (dst src : XmmReg) (l : Nat)
    (t t' : FpZustand) (b : BereitProfil) (q : XmmReg)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (hstep : stepSse42 (⟨.pcmpgtqRR dst src, l⟩ : Sse42Dec)
      t b = some t') (hq : q ≠ dst) :
    t'.xmm q = t.xmm q := by
  revert hstep hq
  unfold stepSse42
  simp only [hok, hfp]
  intro hstep hq; cases hstep
  show (xmmSet t.xmm dst (vecPcmpgtq (t.xmm dst) (t.xmm src))) q = _
  exact xmmSet_fremd _ _ _ _ hq

/-- An index-returning string step keeps every XMM register. -/
theorem stepSse42_stri_xmm (art : StrArt) (dst src : XmmReg)
    (imm l : Nat) (t t' : FpZustand) (b : BereitProfil)
    (q : XmmReg)
    (hok : laengeOk l = true) (hfp : vecEintritt b = true)
    (hart : art = .estri ∨ art = .istri)
    (hstep : stepSse42 (⟨.strRR art dst src imm, l⟩ : Sse42Dec)
      t b = some t') :
    t'.xmm q = t.xmm q := by
  revert hstep
  unfold stepSse42
  simp only [hok, hfp]
  cases hart with
  | inl h =>
    rw [h]; intro hstep; cases hstep; rfl
  | inr h =>
    rw [h]; intro hstep; cases hstep; rfl

end Gabbro.Grammatik.X86
