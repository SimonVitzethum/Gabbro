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
import Grammatik.X86.Byteschritt
import Grammatik.X86.NarrowCodec

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

/-! ## 7. Execution: the accepted 32-bit clearing step plus advance.

    MOV Flags Affected: None -- flags are preserved. No memory operand
    exists, so no permission is consulted and no TSO event is produced;
    `stepCompact_ohne_speicher` pins that memory-independence. The
    destination takes the zero-extended immediate through the same
    register-file helpers as every pilot step. -/

/-- Compact step: destination takes the zero-extended immediate, RIP
    advances past the decoded length. Bad lengths refuse. -/
def stepCompact (d : CompactDec) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.op with
    | .mov32imm dst imm => some ({ s with register := regSet s.register dst (compactWert imm), rip := nach })

/-- The canonical lengths pass the length guard. -/
theorem compactLen_ok (dst : Register) :
    laengeOk (compactLen dst) = true := by
  cases dst <;> rfl

/-- Step equation: the destination lands the zero-extended value. -/
theorem stepCompact_mov32imm (d : CompactDec) (s : Zustand)
    (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm) :
    stepCompact d s = some ({ s with register := regSet s.register dst (compactWert imm), rip := ripNach s.rip d.laenge }) := by
  unfold stepCompact
  rw [hok, h]

/-- A bad decode length refuses, unconditionally. -/
theorem stepCompact_laenge_verweigert (d : CompactDec) (s : Zustand)
    (h : laengeOk d.laenge = false) : stepCompact d s = none := by
  unfold stepCompact
  simp [h]

/-- The destination holds exactly the zero-extended immediate. -/
theorem stepCompact_wert (d : CompactDec) (s s' : Zustand) (dst : Register)
    (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm)
    (hstep : stepCompact d s = some s') :
    s'.register dst = compactWert imm := by
  rw [stepCompact_mov32imm d s dst imm hok h] at hstep
  cases hstep
  exact regSet_gleich _ _ _

/-- Every other register keeps its value. -/
theorem stepCompact_fremd (d : CompactDec) (s s' : Zustand) (dst q : Register)
    (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm)
    (hstep : stepCompact d s = some s') (hq : q ≠ dst) :
    s'.register q = s.register q := by
  rw [stepCompact_mov32imm d s dst imm hok h] at hstep
  cases hstep
  exact regSet_fremd _ _ _ _ hq

/-- Flags are preserved (MOV Flags Affected: None). -/
theorem stepCompact_flags (d : CompactDec) (s s' : Zustand) (dst : Register)
    (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm)
    (hstep : stepCompact d s = some s') :
    s'.flags = s.flags := by
  rw [stepCompact_mov32imm d s dst imm hok h] at hstep
  cases hstep
  rfl

/-- No memory byte changes (no memory operand exists). -/
theorem stepCompact_speicher (d : CompactDec) (s s' : Zustand) (dst : Register)
    (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm)
    (hstep : stepCompact d s = some s') :
    s'.speicher = s.speicher := by
  rw [stepCompact_mov32imm d s dst imm hok h] at hstep
  cases hstep
  rfl

/-- RIP advances past the decoded length. -/
theorem stepCompact_rip (d : CompactDec) (s s' : Zustand) (dst : Register)
    (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm)
    (hstep : stepCompact d s = some s') :
    s'.rip = ripNach s.rip d.laenge := by
  rw [stepCompact_mov32imm d s dst imm hok h] at hstep
  cases hstep
  rfl

/-- The step lands the accepted 32-bit merge: same discipline as every
    narrow 32-bit move, not a second semantics. -/
theorem stepCompact_gleich_merge (d : CompactDec) (s s' : Zustand) (dst : Register)
    (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32imm dst imm)
    (hstep : stepCompact d s = some s') :
    s'.register dst =
      mergeRegNarrow .b32 (s.register dst) (compactWert imm) := by
  have hw := stepCompact_wert d s s' dst imm hok h hstep
  rw [hw]
  exact (compactWert_gleich_merge (s.register dst) imm).symm

/-- DESTINATION-DEAD proof obligation: the successor destination is
    the zero-extended immediate whatever the old value was. A compiler
    may treat the destination as killed by this row. -/
theorem compact_dst_tot (s : Zustand) (dst : Register) (imm : BitVec 32)
    (alt : Wort) (s1' s2' : Zustand)
    (h1 : stepCompact ⟨.mov32imm dst imm, compactLen dst⟩
      { s with register := regSet s.register dst alt } = some s1')
    (h2 : stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ s = some s2') :
    s1'.register dst = s2'.register dst := by
  have hok := compactLen_ok dst
  have e1 := stepCompact_wert ⟨.mov32imm dst imm, compactLen dst⟩ _ s1' dst imm hok rfl h1
  have e2 := stepCompact_wert ⟨.mov32imm dst imm, compactLen dst⟩ _ s2' dst imm hok rfl h2
  rw [e1, e2]

/-- NO MEMORY ACCESS: the step never consults memory. Two states
    differing only in memory agree on destination, RIP and flags of
    their successors. No TSO event, no fault class and no permission
    gate arises from this row. -/
theorem stepCompact_ohne_speicher (s : Zustand) (m : Speicher)
    (dst : Register) (imm : BitVec 32) (s1' s2' : Zustand)
    (h1 : stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ { s with speicher := m } = some s1')
    (h2 : stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ s = some s2') :
    s1'.register dst = s2'.register dst ∧ s1'.rip = s2'.rip ∧
      s1'.flags = s2'.flags := by
  have hok := compactLen_ok dst
  have w1 := stepCompact_wert ⟨.mov32imm dst imm, compactLen dst⟩ _ s1' dst imm hok rfl h1
  have w2 := stepCompact_wert ⟨.mov32imm dst imm, compactLen dst⟩ _ s2' dst imm hok rfl h2
  have r1 := stepCompact_rip ⟨.mov32imm dst imm, compactLen dst⟩ _ s1' dst imm hok rfl h1
  have r2 := stepCompact_rip ⟨.mov32imm dst imm, compactLen dst⟩ _ s2' dst imm hok rfl h2
  have f1 := stepCompact_flags ⟨.mov32imm dst imm, compactLen dst⟩ _ s1' dst imm hok rfl h1
  have f2 := stepCompact_flags ⟨.mov32imm dst imm, compactLen dst⟩ _ s2' dst imm hok rfl h2
  exact ⟨by rw [w1, w2], by simp [r1, r2], by simp [f1, f2]⟩

/-! ## 8. Fetch and byte-step from actual executable memory.

    The `fetchDekodiert` discipline lifted to the compact row: the
    fetched window is the state's ACTUAL bytes at `rip`
    (`Byteschritt.geholt`), admission checks the consumed length
    against the window, the length guard and execute permission of the
    consumed prefix. No caller-supplied decoded value is trusted. -/

/-- Compact admission: length equation, length guard and execute
    permission of the consumed prefix. -/
def compactZugelassen (s : Zustand) (fenster : List Byte) (d : CompactDec)
    (rest : List Byte) : Bool :=
  decide (d.laenge + rest.length = fenster.length) &&
    laengeOk d.laenge &&
    ausfuehrbarN s.speicher s.rip d.laenge

/-- Admission carries the length equation. -/
theorem compactZugelassen_summe (s : Zustand) (fenster : List Byte)
    (d : CompactDec) (rest : List Byte)
    (h : compactZugelassen s fenster d rest = true) :
    d.laenge + rest.length = fenster.length := by
  unfold compactZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsum, _⟩, _⟩ := h
  exact of_decide_eq_true hsum

/-- Admission carries the length guard. -/
theorem compactZugelassen_laenge (s : Zustand) (fenster : List Byte)
    (d : CompactDec) (rest : List Byte)
    (h : compactZugelassen s fenster d rest = true) :
    laengeOk d.laenge = true := by
  unfold compactZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hlen⟩, _⟩ := h
  exact hlen

/-- Admission carries execute permission of the consumed prefix. -/
theorem compactZugelassen_ausfuehrbar (s : Zustand) (fenster : List Byte)
    (d : CompactDec) (rest : List Byte)
    (h : compactZugelassen s fenster d rest = true) :
    ausfuehrbarN s.speicher s.rip d.laenge = true := by
  unfold compactZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hexe⟩ := h
  exact hexe

/-- Fetch and decode over actual bytes, gated by admission. -/
def fetchCompact (s : Zustand) : Option (CompactDec × List Byte) :=
  match decodeCompact (geholt s) with
  | none => none
  | some p =>
    if compactZugelassen s (geholt s) p.1 p.2 then some p else none

/-- A successful fetch decodes to the admitted row with length
    equation, length guard and execute permission. -/
theorem fetchCompact_erfolg (s : Zustand) (d : CompactDec)
    (rest : List Byte)
    (h : fetchCompact s = some (d, rest)) :
    decodeCompact (geholt s) = some (d, rest) ∧
      d.laenge + rest.length = (geholt s).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN s.speicher s.rip d.laenge = true := by
  have e : fetchCompact s =
      match decodeCompact (geholt s) with
      | none => (none : Option (CompactDec × List Byte))
      | some p =>
        if compactZugelassen s (geholt s) p.1 p.2
        then some p else (none : Option (CompactDec × List Byte)) := rfl
  rw [e] at h
  cases hdec : decodeCompact (geholt s) with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : compactZugelassen s (geholt s) p.1 p.2 = true
    case pos =>
      simp [hz] at h
      rw [h] at hz
      exact ⟨by rw [h],
        compactZugelassen_summe s (geholt s) _ _ hz,
        compactZugelassen_laenge s (geholt s) _ _ hz,
        compactZugelassen_ausfuehrbar s (geholt s) _ _ hz⟩
    case neg =>
      simp [hz] at h

/-- Byte-step outcome: success carries the successor, refusal is
    explicit. No halt constructor: `verweigert` is no transition,
    never a fault claim. -/
inductive CompactAusgang where
  | weiter : Zustand → CompactAusgang
  | verweigert : CompactAusgang

/-- One byte step from actual memory: fetch, decode, then the compact
    step. Takes ONLY the state, so a forged `CompactDec` cannot inject
    an instruction. -/
def compactByteschritt (s : Zustand) : CompactAusgang :=
  match fetchCompact s with
  | none => .verweigert
  | some (d, _) =>
    match stepCompact d s with
    | none => .verweigert
    | some s' => .weiter s'

/-- Selection: a fetched row with a successful step continues. -/
theorem compactByteschritt_weiter (s s' : Zustand) (d : CompactDec)
    (rest : List Byte)
    (hf : fetchCompact s = some (d, rest))
    (hs : stepCompact d s = some s') :
    compactByteschritt s = .weiter s' := by
  have e : compactByteschritt s =
      match fetchCompact s with
      | none => CompactAusgang.verweigert
      | some (dd, _) =>
        match stepCompact dd s with
        | none => CompactAusgang.verweigert
        | some t => CompactAusgang.weiter t := rfl
  rw [e, hf]
  simp [hs]

/-- Selection: a fetched row with a failed step refuses. -/
theorem compactByteschritt_schritt_verweigert (s : Zustand)
    (d : CompactDec) (rest : List Byte)
    (hf : fetchCompact s = some (d, rest))
    (hs : stepCompact d s = none) :
    compactByteschritt s = .verweigert := by
  have e : compactByteschritt s =
      match fetchCompact s with
      | none => CompactAusgang.verweigert
      | some (dd, _) =>
        match stepCompact dd s with
        | none => CompactAusgang.verweigert
        | some t => CompactAusgang.weiter t := rfl
  rw [e, hf]
  simp [hs]

/-- Selection: fetch refusal is byte-step refusal (never a fault). -/
theorem compactByteschritt_hol_verweigert (s : Zustand)
    (hf : fetchCompact s = none) :
    compactByteschritt s = .verweigert := by
  have e : compactByteschritt s =
      match fetchCompact s with
      | none => CompactAusgang.verweigert
      | some (dd, _) =>
        match stepCompact dd s with
        | none => CompactAusgang.verweigert
        | some t => CompactAusgang.weiter t := rfl
  rw [e, hf]

/-! ## 9. The connection and its joint witness.

    `CompactImmMov32Zero_verbindung` ties bytes to execution: decode
    of the canonical encoding, the zero-extended destination, flag
    and memory preservation, and the width-exact bound. -/

/-- END-TO-END CONNECTION: canonical bytes decode, the destination
    takes the zero-extended immediate, flags and memory are preserved,
    and the value fits 32 bits. -/
theorem CompactImmMov32Zero_verbindung (dst : Register) (imm : BitVec 32)
    (s : Zustand) (hok : laengeOk (compactLen dst) = true) :
    decodeCompact (encodeCompact (.mov32imm dst imm)) =
      some (⟨.mov32imm dst imm, compactLen dst⟩, []) ∧
    (stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ s).map
      (fun t => t.register dst) = some (compactWert imm) ∧
    (stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ s).map
      (fun t => t.flags) = some s.flags ∧
    (stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ s).map
      (fun t => t.speicher) = some s.speicher ∧
    (compactWert imm).toNat < 2 ^ 32 := by
  have hlen := encodeCompact_len dst imm
  have hdec : decodeCompact (encodeCompact (.mov32imm dst imm)) =
      some (⟨.mov32imm dst imm, compactLen dst⟩, []) := by
    have hr := roundtripCompact (.mov32imm dst imm) []
    simp only [List.append_nil] at hr
    rw [hlen] at hr
    exact hr
  have hstep : stepCompact ⟨.mov32imm dst imm, compactLen dst⟩ s = some ({ s with register := regSet s.register dst (compactWert imm), rip := ripNach s.rip (compactLen dst) }) :=
    stepCompact_mov32imm _ s dst imm hok rfl
  exact ⟨hdec, by simp [hstep, regSet_gleich], by simp [hstep], by simp [hstep], compactWert_fits imm⟩

/-- Hostile witness registers: every register holds all-ones, so the
    zeroing above bit 31 is observable, not vacuous. -/
def kompaktWitReg : Register → Wort :=
  fun _ => BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF

/-- Witness start state: hostile registers, code at 4096. -/
def kompaktWitState : Zustand :=
  { register := kompaktWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- JOINT WITNESS: the connection instantiated at `rax := 0x80000001`
    over hostile all-ones registers (upper half observably cleared),
    together with the reached memory-changing run from actual
    `Ausfuehrung` vocabulary (cell 8192 goes 0 to 42). Non-degenerate:
    a register-changing reached step plus a store-changing reached
    run, jointly instantiated. -/
theorem CompactImmMov32Zero_verbindung_zeuge :
    (stepCompact ⟨.mov32imm .rax (BitVec.ofNat 32 0x80000001), 5⟩
      kompaktWitState).map (fun t => t.register .rax) =
      some (BitVec.ofNat 64 0x80000001) ∧
    (stepCompact ⟨.mov32imm .rax (BitVec.ofNat 32 0x80000001), 5⟩
      kompaktWitState).map (fun t => t.flags) =
      some kompaktWitState.flags ∧
    decodeCompact (encodeCompact
        (.mov32imm .rax (BitVec.ofNat 32 0x80000001))) =
      some (⟨.mov32imm .rax (BitVec.ofNat 32 0x80000001),
        compactLen .rax⟩, []) ∧
    (compactWert (BitVec.ofNat 32 0x80000001)).toNat < 2 ^ 32 ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := by
  have hverb := CompactImmMov32Zero_verbindung .rax
    (BitVec.ofNat 32 0x80000001) kompaktWitState (compactLen_ok .rax)
  obtain ⟨hd, _, _, _, hfit⟩ := hverb
  obtain ⟨_, hmem, hnull⟩ := zeuge_speicher_aendert_sich
  exact ⟨by decide, by decide, hd, hfit, hmem, hnull⟩

/-! ## 10. Pinned bytes and explicit refusals. -/

/-- Pinned bytes: `mov eax, 1` is B8 01 00 00 00. -/
theorem pin_mov32imm_eax_eins :
    encodeCompact (.mov32imm .rax (BitVec.ofNat 32 1)) =
      [natByte 184, natByte 1, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: the same five bytes name rax at length 5. -/
theorem pin_mov32imm_eax_eins_dekode :
    decodeCompact
      [natByte 184, natByte 1, natByte 0, natByte 0, natByte 0] =
      some ((⟨.mov32imm .rax (BitVec.ofNat 32 1), 5⟩ : CompactDec),
        []) := by
  decide

/-- Pinned bytes: `mov r15d, 0xFFFFFFFF` takes the REX.B byte. -/
theorem pin_mov32imm_r15 :
    encodeCompact (.mov32imm .r15 (BitVec.ofNat 32 0xFFFFFFFF)) =
      [natByte 65, natByte 191, natByte 255, natByte 255, natByte 255,
        natByte 255] := by
  decide

/-- Pinned decode: the REX.B form names r15 at length 6. -/
theorem pin_mov32imm_r15_dekode :
    decodeCompact [natByte 65, natByte 191, natByte 255, natByte 255,
      natByte 255, natByte 255] =
      some ((⟨.mov32imm .r15 (BitVec.ofNat 32 0xFFFFFFFF), 6⟩ : CompactDec),
        []) := by
  decide

/-- The empty input decodes to nothing. -/
theorem kompakt_nichts_leer : decodeCompact [] = none := rfl

/-- A bare opcode without its immediate is truncated. -/
theorem kompakt_nichts_abgeschnitten :
    decodeCompact [natByte 184] = none := rfl

/-- A REX.W prefix stays the pilot's domain (10-byte `movImm64`):
    refused by this row. -/
theorem kompakt_nichts_rex_w :
    decodeCompact [natByte 72, natByte 184, natByte 1, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0] =
      none := rfl

/-- A redundant REX byte (W=R=X=B=0) is non-canonical here. -/
theorem kompakt_nichts_rex_leer :
    decodeCompact [natByte 64, natByte 184, natByte 1, natByte 0,
      natByte 0, natByte 0] = none := rfl

/-- A REX.X prefix is not canonical. -/
theorem kompakt_nichts_rex_x :
    decodeCompact [natByte 66, natByte 184, natByte 1, natByte 0,
      natByte 0, natByte 0] = none := rfl

/-- An unknown opcode is refused. -/
theorem kompakt_nichts_unbekannt :
    decodeCompact [natByte 255] = none := rfl

/-- NARROW DISJOINTNESS: the accepted narrow decoder refuses every
    covered compact encoding (bare B8 is no REX prefix; the 0x41
    prefix never continues into a narrow opcode). -/
theorem kompakt_narrow_verweigert (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decodeNarrow (encodeCompact (.mov32imm dst imm) ++ suffix) = none := by
  cases dst <;> rfl

/-- JOINT REFUSAL PIN: the word `2 ^ 32` needs imm64, so no compact
    immediate denotes it. -/
theorem kompakt_gross_verweigert_pin (imm : BitVec 32) :
    compactWert imm ≠ BitVec.ofNat 64 (2 ^ 32) := by
  have hfit := compactWert_fits imm
  have hval : (BitVec.ofNat 64 (2 ^ 32)).toNat = 2 ^ 32 := by
    rw [BitVec.toNat_ofNat]
  intro heq
  have hcon := congrArg BitVec.toNat heq
  omega

/- CUTS:
    Proved here, over the REUSED canonical vocabulary (`Typen`,
    `Wort.trunc`/`narrowTruncMod`, `Speicher`, `Ausfuehrung.laengeOk`/
    `ripNach`/`effAddr`-free `regSet`, `Codec.codeReg`/`regCode`/
    `regHigh`/`regLow`/`parseLe32`/`leBytes32`, `Byteschritt.geholt`/
    `ausfuehrbarN`, `DecodingCoverage.parseLe32_suffix`,
    `NarrowOps.mergeRegNarrow`/`extendNarrow` and the UNCHANGED pilot
    `Codec.decode`/`decodeNarrow`):
    - the one covered row (`CompactImmMov32`/`CompactDec`) with its
      canonical encoder (`encodeCompact`: bare B8+rd, 5 bytes; 0x41
      REX.B prefix for r8-r15, 6 bytes), exact decoded lengths
      (`encodeCompact_len`, the 1..15 cap), generic round trips
      (`roundtripCompact`, `roundtripCompact_len_ok`) and pinned bytes
      for `mov eax, 1` and `mov r15d, 0xFFFFFFFF`;
    - decoder-side arbitrary-input coverage
      (`decodeCompact_abdeckung` with the tail shape
      `compactTailAb`, plus `decodeCompact_consumes`);
    - width-exact zeroing through the canonical `trunc`
      (`compactWert_nat`/`compactWert_fits`, the merge-discipline
      bridge `compactWert_gleich_merge`, the extension bridge
      `compactWert_gleich_extend`);
    - the exact imm64 gate in both directions
      (`keinKompaktFuerGross` refusal, `kompaktFuerKlein` positive,
      plus the joint pin `kompakt_gross_verweigert_pin`);
    - execution through the common `Zustand` (`stepCompact` with per-
      form step equation, value/frame/RIP facts, the merge-discipline
      bridge `stepCompact_gleich_merge`, the DESTINATION-DEAD
      obligation `compact_dst_tot`, the no-memory-access fact
      `stepCompact_ohne_speicher`, length refusal);
    - fetch and byte-step from actual executable memory
      (`compactZugelassen` carriers, `fetchCompact_erfolg`,
      `compactByteschritt` with the three selection facts) following
      the `fetchDekodiert` discipline;
    - pilot-first combined dispatch (`decodeComboCompact` and its
      three dispatch facts) with pilot disjointness
      (`compact_pilot_verweigert`) and narrow disjointness
      (`kompakt_narrow_verweigert`);
    - explicit refusals (empty, truncated, REX.W in the pilot domain,
      redundant REX, REX.X, unknown opcode);
    - the end-to-end `CompactImmMov32Zero_verbindung` with its joint
      companion `CompactImmMov32Zero_verbindung_zeuge` (hostile
      all-ones registers with `rax := 0x80000001`, plus the reached
      memory-changing `lauf` run taking cell 8192 from 0 to 42).
    NOT proved here, and not claimed:
    - No hardware correspondence: the encoding is the stated canonical
      row (MOV opcode table `B8+ rd id`, operand-size rule, default
      32-bit operation size, Flags Affected None) with
      self-consistency only, not silicon verification. Encoder
      round-trip consistency is not hardware fidelity.
    - No other MOV rows: 16-bit (`66 B8`), r/m32 immediates (`C7 /0`),
      segment-register moves, `moffs` forms and the REX.W 10-byte form
      (pilot `movImm64`, reused by reference) stay open; each new row
      needs its own encoding, coverage and execution proof.
    - No fetch rewiring: the shared `Byteschritt.byteschritt` and
      `ExtendedExecution.extByteschritt` still dispatch without this
      row; routing them through `decodeComboCompact` waits on the
      dispatcher owners and is the next integration.
    - No #UD membership: refused neighbours are proved refusal only;
      which refused bytes are truly illegal encodings stays OPEN
      (same honesty as `HardwareFaults.fehlbyte_kein_stiller_ud`).
    - No TSO/concurrency bridge: the no-memory-access fact is
      sequential over one `Speicher`; per-access target-to-W/GX
      simulation stays with the TSO bridge lanes.
    - No source correspondence, no ABI/image/entry/relocation/cost
      claim: `verweigert`/`none` is the absence of a transition, never
      a halt claim; no new hardware or software assumption beyond the
      named manual entries.
-/

#print axioms encodeCompact_len
#print axioms roundtripCompact
#print axioms decodeCompact_abdeckung
#print axioms decodeCompact_consumes
#print axioms compactWert_fits
#print axioms keinKompaktFuerGross
#print axioms kompaktFuerKlein
#print axioms stepCompact_mov32imm
#print axioms compact_dst_tot
#print axioms stepCompact_ohne_speicher
#print axioms fetchCompact_erfolg
#print axioms compactByteschritt_weiter
#print axioms CompactImmMov32Zero_verbindung
#print axioms CompactImmMov32Zero_verbindung_zeuge
#print axioms pin_mov32imm_eax_eins_dekode
#print axioms pin_mov32imm_r15_dekode
#print axioms kompakt_narrow_verweigert
#print axioms kompakt_gross_verweigert_pin

end Gabbro.Grammatik.X86
