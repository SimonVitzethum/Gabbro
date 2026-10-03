/-
  File:      Grammatik/X86/CompactImmMov32Zero.lean
  Subject:   Compact zero-extending MOV reg, imm32 (lane 746).

  Covers exactly one row: no-REX.W `B8+rd id` (MOV r32, imm32), whose
  32-bit result is zero-extended into the 64-bit destination. Reuses the
  canonical `Register`/`Zustand`/`Speicher` (`Typen`), `trunc` (`Wort`),
  the 32-bit clearing discipline (`NarrowOps.mergeRegNarrow_b32`), the
  register-file helpers (`Ausfuehrung`: `laengeOk`/`ripNach`/`regSet`),
  little-endian bytes (`Codec`), the fetch discipline (`Byteschritt`)
  and decoder-side suffix facts (`DecodingCoverage`). No new word,
  register, state or source type is created.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`,
  Intel SDM 325462-093US, September 2026):
  - MOV opcode table (Vol. 2B, section MOV-Move, txt lines 65710-65712):
    `B8+ rd id MOV r32, imm32` versus `REX.W + B8+ rd io MOV r64,
    imm64`. Without REX.W the B8+rd row carries imm32, never imm64.
  - Operand-size rule (Vol. 1, BASIC EXECUTION ENVIRONMENT, Table 3-2
    context, txt lines 4375-4382): 32-bit operands generate a 32-bit
    result, zero-extended to a 64-bit result in the destination
    general-purpose register.
  - MOV Description: in 64-bit mode the default operation size is 32
    bits; REX.R permits R8-R15; REX.W promotes operation to 64 bits.
  - Flags Affected: None (MOV entry).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.NarrowOps
import Grammatik.X86.DecodingCoverage

namespace Gabbro.Grammatik.X86

/-- The one covered row: compact move of a 32-bit immediate into the
    low half of a 64-bit register, zero-extending above bit 31. -/
inductive CompactImmMov32 where
  | mov32imm (dst : Register) (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- A decoded compact move with its consumed length (checked data). -/
structure CompactDec where
  op : CompactImmMov32
  laenge : Nat
  deriving DecidableEq, Repr

/-- The zero-extended value: exactly the low 32 bits as a word, reusing
    the canonical `trunc` (no second extension operator). -/
def compactWert (imm : BitVec 32) : Wort :=
  trunc .b32 (BitVec.ofNat 64 imm.toNat)

/-! ## 1. Canonical encoding.

    Opcode `B8+rd` with the 32-bit immediate in little-endian order
    (MOV opcode table: `B8+ rd id MOV r32, imm32`). Low registers need
    no prefix (5 bytes); extended registers take one REX byte `0x41`
    (W=0, R=0, X=0, B=1; MOV Description: REX.R reaches R8-R15 while
    REX.W stays clear, so operation stays 32-bit). A redundant `0x40`
    prefix is refused (non-canonical here); any REX with W/R/X bits is
    refused (W=1 is the pilot `movImm64` domain). -/

/-- Opcode byte `B8+rd` over the low three register bits. -/
def compactOpcode (dst : Register) : Byte := natByte (184 + regLow dst)

/-- Canonical byte encoding of the one covered row. -/
def encodeCompact : CompactImmMov32 → List Byte
  | .mov32imm dst imm =>
    if regHigh dst == 0 then compactOpcode dst :: leBytes32 imm
    else natByte 65 :: compactOpcode dst :: leBytes32 imm

/-- Consumed length: 5 without prefix, 6 with the REX.B byte. -/
def compactLen (dst : Register) : Nat :=
  if regHigh dst == 0 then 5 else 6

/-- The encoding is exactly the decoded length. -/
theorem encodeCompact_len (dst : Register) (imm : BitVec 32) :
    (encodeCompact (.mov32imm dst imm)).length = compactLen dst := by
  by_cases h : regHigh dst == 0
  · simp [encodeCompact, compactLen, h, leBytes32]
  · simp [encodeCompact, compactLen, h, leBytes32]

/-- Every covered encoding fits the 15-byte instruction cap. -/
theorem encodeCompact_cap (dst : Register) (imm : BitVec 32) :
    1 ≤ (encodeCompact (.mov32imm dst imm)).length ∧
      (encodeCompact (.mov32imm dst imm)).length ≤ 15 := by
  rw [encodeCompact_len]
  unfold compactLen
  split <;> decide

/-! ## 2. Width-exact zeroing (operand-size rule).

    Vol. 1 Table 3-2 context: a 32-bit operand generates a 32-bit
    result, zero-extended to a 64-bit result. Every lemma below reuses
    the accepted `narrowTruncMod` bridge; no new arithmetic is proved. -/

/-- The value is exactly the immediate as a natural number: no high
    bit is ever set by the extension. -/
theorem compactWert_nat (imm : BitVec 32) :
    (compactWert imm).toNat = imm.toNat := by
  have himm := imm.isLt
  have hbits : Breite.bits .b32 = 32 := rfl
  simp only [compactWert, narrowTruncMod, hbits, BitVec.toNat_ofNat]
  omega

/-- The zero-extended value fits 32 bits: the upper half is cleared. -/
theorem compactWert_fits (imm : BitVec 32) :
    (compactWert imm).toNat < 2 ^ 32 := by
  rw [compactWert_nat]
  exact imm.isLt

/-- Truncation is idempotent on compact values (already 32-bit). -/
theorem trunc_compactWert (imm : BitVec 32) :
    trunc .b32 (compactWert imm) = compactWert imm := by
  apply BitVec.eq_of_toNat_eq
  rw [narrowTruncMod, compactWert_nat]
  exact Nat.mod_eq_of_lt imm.isLt

/-- The compact value follows the accepted 32-bit clearing discipline:
    merging it over any old destination value is the value itself. -/
theorem compactWert_gleich_merge (oldVal : Wort) (imm : BitVec 32) :
    mergeRegNarrow .b32 oldVal (compactWert imm) = compactWert imm := by
  rw [mergeRegNarrow_b32]
  exact trunc_compactWert imm

/-- The compact value is the accepted zero extension at 32 bits. -/
theorem compactWert_gleich_extend (imm : BitVec 32) :
    extendNarrow .zero .b32 (compactWert imm) = compactWert imm := by
  rw [extendNarrow_zero]
  exact trunc_compactWert imm

/-! ## 3. Bounded independent decoder.

    Bare `B8+rd` names a low register (length 5); a `0x41` prefix adds
    8 to the register code (length 6). Every other first byte refuses:
    in particular REX.W prefixes (`0x48` and friends) stay the pilot
    `movImm64` domain and `0x40` (redundant REX) is non-canonical here. -/

/-- Decode after the optional REX.B byte: opcode plus imm32. -/
def decodeCompactTail : List Byte → Option (CompactDec × List Byte)
  | [] => none
  | op :: rest =>
    let n := byteNat op
    if 184 ≤ n ∧ n < 192 then
      match codeReg (n - 184), parseLe32 rest with
      | some dst, some (v, rest') => some (⟨.mov32imm dst v, 5⟩, rest')
      | _, _ => none
    else none

/-- Top-level decode: one canonical REX.B byte or the bare row. -/
def decodeCompact : List Byte → Option (CompactDec × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b == 65 then
      match decodeCompactTail rest with
      | some (dd, rest') =>
        match dd.op with
        | .mov32imm dstLow v =>
          match codeReg (regCode dstLow + 8) with
          | some dst => some (⟨.mov32imm dst v, 6⟩, rest')
          | none => none
      | none => none
    else decodeCompactTail (b :: rest)

/-- Round trip for low registers (bare 5-byte form). -/
theorem roundtrip_compact_low (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) (hlow : regHigh dst = 0) :
    decodeCompact (encodeCompact (.mov32imm dst imm) ++ suffix) =
      some (⟨.mov32imm dst imm, (encodeCompact (.mov32imm dst imm)).length⟩,
        suffix) := by
  cases dst <;>
    simp_all [encodeCompact, decodeCompact, decodeCompactTail,
      compactOpcode, regCode, regHigh, regLow, codeReg, leBytes32,
      parseLe32_cons]

/-- Round trip for extended registers (0x41-prefixed 6-byte form). -/
theorem roundtrip_compact_high (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) (hhigh : regHigh dst = 1) :
    decodeCompact (encodeCompact (.mov32imm dst imm) ++ suffix) =
      some (⟨.mov32imm dst imm, (encodeCompact (.mov32imm dst imm)).length⟩,
        suffix) := by
  cases dst <;>
    simp_all [encodeCompact, decodeCompact, decodeCompactTail,
      compactOpcode, regCode, regHigh, regLow, codeReg, leBytes32,
      parseLe32_cons]

/-- Decoding inverts encoding on the one covered row, over any suffix.
    The decoded length is the consumed prefix length. -/
theorem roundtripCompact (op : CompactImmMov32) (suffix : List Byte) :
    decodeCompact (encodeCompact op ++ suffix) =
      some (⟨op, (encodeCompact op).length⟩, suffix) := by
  cases op with
  | mov32imm dst imm =>
    by_cases h : regHigh dst = 0
    case pos => exact roundtrip_compact_low dst imm suffix h
    case neg =>
      have h1 : regHigh dst = 1 := by
        cases hd : regHigh dst with
        | zero => simp [hd] at h
        | succ n =>
          cases n with
          | zero => rfl
          | succ m =>
            have hlt := regHigh_lt dst
            omega
      exact roundtrip_compact_high dst imm suffix h1

/-- A successful round trip consumes exactly its prefix, within 1..15. -/
theorem roundtripCompact_len_ok (op : CompactImmMov32)
    (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decodeCompact (encodeCompact op ++ suffix) = some (⟨op, n⟩, rest) ∧
        n + rest.length = (encodeCompact op ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 := by
  cases op with
  | mov32imm dst imm =>
    refine ⟨(encodeCompact (.mov32imm dst imm)).length, suffix,
      roundtripCompact _ suffix, ?_, ?_, ?_⟩
    · rw [List.length_append]
    · exact (encodeCompact_cap dst imm).1
    · exact (encodeCompact_cap dst imm).2

/-! ## 4. Pilot disjointness and the combined dispatcher.

    The pilot `decode` refuses every compact encoding (bare `B8+rd`
    is no pilot row; `0x41` starts only push/pop there, never `B8`):
    canonical-first dispatch never collides. -/

/-- DISJOINTNESS: the pilot refuses every covered compact encoding. -/
theorem compact_pilot_verweigert (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decode (encodeCompact (.mov32imm dst imm) ++ suffix) = none := by
  cases dst <;> rfl

/-- Combined decode: the pilot first, the compact row only where the
    pilot refuses. No pilot form is shadowed. -/
def decodeComboCompact (bs : List Byte) :
    Option ((Decodiert ⊕ CompactDec) × List Byte) :=
  match decode bs with
  | some (d, rest) => some (.inl d, rest)
  | none =>
    match decodeCompact bs with
    | some (n, rest) => some (.inr n, rest)
    | none => none

/-- The combined decoder agrees with the pilot wherever it accepts. -/
theorem decodeComboCompact_kanonisch (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    decodeComboCompact bs = some (.inl d, rest) := by
  unfold decodeComboCompact
  rw [h]

/-- Where the pilot refuses, a covered compact row is taken. -/
theorem decodeComboCompact_erweitert (bs : List Byte) (d : CompactDec)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeCompact bs = some (d, rest)) :
    decodeComboCompact bs = some (.inr d, rest) := by
  unfold decodeComboCompact
  rw [h1, h2]

/-- Where both refuse, the combined decoder refuses. -/
theorem decodeComboCompact_nichts (bs : List Byte) (h1 : decode bs = none)
    (h2 : decodeCompact bs = none) :
    decodeComboCompact bs = none := by
  unfold decodeComboCompact
  rw [h1, h2]

/-! ## 5. Arbitrary-input coverage: every success consumes its length.

    Proved from the decoder side only (never from encoder round
    trips), reusing `DecodingCoverage.parseLe32_suffix`. Needs the
    import for that fact; the statement below reuses nothing else. -/

/-- Coverage shape: the one covered row at its exact length (5 bare,
    6 with the REX.B byte). -/
def compactDecktAb (d : CompactDec) : Prop :=
  ∃ dst imm, d.op = .mov32imm dst imm ∧ (d.laenge = 5 ∨ d.laenge = 6)

/-- Tail shape: the tail row always claims length 5. -/
def compactTailAb (d : CompactDec) : Prop :=
  ∃ dst imm, d.op = .mov32imm dst imm ∧ d.laenge = 5

/-- Tail coverage: opcode byte plus four immediate bytes. -/
theorem decodeCompactTail_abdeckung (bs : List Byte) (d : CompactDec)
    (rest : List Byte)
    (h : decodeCompactTail bs = some (d, rest)) :
    (∃ pre, bs = pre ++ rest ∧ pre.length = d.laenge) ∧
      laengeOk d.laenge = true ∧ compactTailAb d := by
  cases bs with
  | nil => simp [decodeCompactTail] at h
  | cons op t =>
    simp only [decodeCompactTail] at h
    split at h
    · cases hparse : parseLe32 t with
      | none =>
        cases hc : codeReg (byteNat op - 184) with
        | none => simp [hparse, hc] at h
        | some dst => simp [hparse, hc] at h
      | some pr =>
        obtain ⟨v, mid⟩ := pr
        simp only [hparse] at h
        cases hc : codeReg (byteNat op - 184) with
        | none => simp [hc] at h
        | some dst =>
          simp only [hc] at h
          obtain ⟨b0, b1, b2, b3, h4⟩ :=
            parseLe32_suffix t v mid hparse
          cases h
          refine ⟨⟨[op, b0, b1, b2, b3], by simp [h4], rfl⟩, rfl, ?_⟩
          exact ⟨_, _, rfl, rfl⟩
    · simp at h

/-- Tail shape implies the full shape (length 5 is a covered length). -/
theorem compactTail_zu_Ab (d : CompactDec) (h : compactTailAb d) :
    compactDecktAb d := by
  obtain ⟨dst, imm, hop, h5⟩ := h
  exact ⟨dst, imm, hop, Or.inl h5⟩

/-- Top-level coverage: the REX.B prefix plus the tail row. -/
theorem decodeCompact_abdeckung (bs : List Byte) (d : CompactDec)
    (rest : List Byte) (h : decodeCompact bs = some (d, rest)) :
    (∃ pre, bs = pre ++ rest ∧ pre.length = d.laenge) ∧
      laengeOk d.laenge = true ∧ compactDecktAb d := by
  cases bs with
  | nil => simp [decodeCompact] at h
  | cons b t =>
    simp only [decodeCompact] at h
    split at h
    · cases ht : decodeCompactTail t with
      | none => simp [ht] at h
      | some pr =>
        obtain ⟨dd, mid⟩ := pr
        simp only [ht] at h
        cases hop : dd.op with
        | mov32imm dstLow v =>
          simp only [hop] at h
          cases hc : codeReg (regCode dstLow + 8) with
          | none => simp [hc] at h
          | some dst =>
            simp only [hc] at h
            cases h
            have hsub := decodeCompactTail_abdeckung t dd rest ht
            obtain ⟨⟨pre, hbs, hlen⟩, _, _, _, _, h5⟩ := hsub
            refine ⟨⟨b :: pre, by simp [hbs], by simp [hlen, h5]⟩, rfl, ?_⟩
            exact ⟨_, _, rfl, Or.inr rfl⟩
    · have hsub := decodeCompactTail_abdeckung (b :: t) d rest h
      exact ⟨hsub.1, hsub.2.1, compactTail_zu_Ab d hsub.2.2⟩

/-- Every successful decode of an arbitrary input consumes exactly its
    stated length within 1..15. -/
theorem decodeCompact_consumes (bs : List Byte) (d : CompactDec)
    (rest : List Byte) (h : decodeCompact bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  obtain ⟨⟨pre, hbs, hlen⟩, hok, _⟩ := decodeCompact_abdeckung bs d rest h
  have hbl : bs.length = pre.length + rest.length := by
    rw [hbs, List.length_append]
  have hb : 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
    simp only [laengeOk, decide_eq_true_eq] at hok
    exact hok
  exact ⟨by omega, hb.1, hb.2⟩

/-! ## 6. Values needing imm64 are refused by this row.

    MOV opcode table: `B8+ rd id` carries imm32; only `REX.W + B8+
    rd io` carries imm64 (the pilot `movImm64` domain, whose round
    trip `roundtrip_movImm64` already proves that row exists). The
    gate below is exact in both directions. -/

/-- A word needs the 10-byte REX.W form iff it does not fit 32 bits. -/
def brauchtImm64 (v : Wort) : Bool := decide (2 ^ 32 ≤ v.toNat)

/-- The gate answers the size question exactly. -/
theorem brauchtImm64_genau (v : Wort) :
    brauchtImm64 v = true ↔ 2 ^ 32 ≤ v.toNat := by
  simp [brauchtImm64]

/-- REFUSAL: no compact immediate denotes a word needing imm64. -/
theorem keinKompaktFuerGross (v : Wort) (h : brauchtImm64 v = true)
    (imm : BitVec 32) : compactWert imm ≠ v := by
  have hfit := compactWert_fits imm
  have hle : 2 ^ 32 ≤ v.toNat := (brauchtImm64_genau v).mp h
  intro heq
  have hcon := congrArg BitVec.toNat heq
  omega

/-- POSITIVE: every sub-2^32 word has a compact immediate. -/
theorem kompaktFuerKlein (v : Wort) (h : v.toNat < 2 ^ 32) :
    ∃ imm : BitVec 32, compactWert imm = v := by
  refine ⟨BitVec.ofNat 32 v.toNat, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [compactWert_nat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/- CUTS:
    Skeleton only: encoder, decoder, execution and witnesses are open.
-/

#print axioms compactWert

end Gabbro.Grammatik.X86
