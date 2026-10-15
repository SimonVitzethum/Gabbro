/-
  File:      Grammatik/X86/MulDivCodec.lean
  Subject:   Canonical byte codec for a MUL/IMUL/DIV/IDIV subset, connected
             to the accepted MulDiv execution (lane 336, reviewed lane 374).

  Lane 563 (connection wave): the producer interface for the unified
  extended path (lane 575). Canonical REX.W register-direct encodings
  (Group 3 `F7 /4 /6 /7`, two-operand `0F AF /r`), actual byte decoding
  with derived lengths, round trips, and generic execute correspondence
  against the REUSED `mulDivSchritt` (implicit RDX:RAX inputs, divide
  refusal/trap distinction, value/flag semantics). No duplicated
  evaluator, no source or hardware claim.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.MulDiv

namespace Gabbro.Grammatik.X86

/-- Canonical byte encoding of one MulDiv operation: Group 3 `F7 /4`
    (MUL), `/6` (DIV), `/7` (IDIV) over REX.W plus the ModRM opcode
    extension, and two-operand `0F AF /r` (IMUL). Register-direct only
    (mod=3); REX.R extends the IMUL destination, REX.B the Group-3 and
    IMUL source. Reuses `rexByte`/`modrmReg` from the pilot codec. -/
def mulDivEncode : MulDivBefehl → List Byte
  | .mulRax src => [rexByte 0 (regHigh src), natByte 247, modrmReg 4 (regLow src)]
  | .divRax src => [rexByte 0 (regHigh src), natByte 247, modrmReg 6 (regLow src)]
  | .idivRax src => [rexByte 0 (regHigh src), natByte 247, modrmReg 7 (regLow src)]
  | .imul2 dst src =>
    [rexByte (regHigh dst) (regHigh src), natByte 15, natByte 175,
      modrmReg (regLow dst) (regLow src)]

/-- Every canonical MulDiv encoding is 3 or 4 bytes long. -/
theorem mulDivEncode_len (b : MulDivBefehl) :
    (mulDivEncode b).length = 3 ∨ (mulDivEncode b).length = 4 := by
  cases b with
  | mulRax src => exact Or.inl rfl
  | divRax src => exact Or.inl rfl
  | idivRax src => exact Or.inl rfl
  | imul2 dst src => exact Or.inr rfl

/-- Every canonical MulDiv encoding fits the 1..15 length window. -/
theorem mulDivEncode_len_ok (b : MulDivBefehl) :
    1 ≤ (mulDivEncode b).length ∧ (mulDivEncode b).length ≤ 15 := by
  cases hlen : mulDivEncode_len b with
  | inl h3 => rw [h3]; decide
  | inr h4 => rw [h4]; decide

/-- Decode one Group-3 ModRM byte (mod=3, opcode extension in the reg
    field): `/4` is MUL, `/6` is DIV, `/7` is IDIV over RDX:RAX. Any
    other extension digit, any non-register mode, or an unencodable
    register code refuses with `none`. -/
def decodeF7Modrm (bBit : Nat) :
    List Byte → Option (MulDivDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match reg with
      | 4 =>
        match codeReg (bBit * 8 + rm) with
        | some src => some (⟨.mulRax src, 3⟩, rest)
        | none => none
      | 6 =>
        match codeReg (bBit * 8 + rm) with
        | some src => some (⟨.divRax src, 3⟩, rest)
        | none => none
      | 7 =>
        match codeReg (bBit * 8 + rm) with
        | some src => some (⟨.idivRax src, 3⟩, rest)
        | none => none
      | _ => none
    else none

/-- Decode one two-operand IMUL ModRM byte (mod=3): the reg field names
    the destination (REX.R extension), the r/m field the source
    (REX.B extension). -/
def decodeImulModrm (rBit bBit : Nat) :
    List Byte → Option (MulDivDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
      | some dst, some src => some (⟨.imul2 dst src, 4⟩, rest)
      | _, _ => none
    else none

/-- Decode after one canonical IMUL REX.W prefix and the `0F` escape:
    the second opcode byte must be `AF` (175). -/
def decodeImulRex (rBit bBit : Nat) :
    List Byte → Option (MulDivDecodiert × List Byte)
  | [] => none
  | op2 :: rest =>
    if byteNat op2 == 175 then decodeImulModrm rBit bBit rest
    else none

/-- Decode after a REX.W prefix with a clear R bit (72, 73): either
    the Group-3 opcode `F7` (247) or the IMUL `0F` escape (15). -/
def decodeNachRex (rBit bBit : Nat) :
    List Byte → Option (MulDivDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if byteNat op == 247 then decodeF7Modrm bBit rest
    else if byteNat op == 15 then decodeImulRex rBit bBit rest
    else none

/-- Decode after a REX.W+R prefix (76, 77): only the IMUL `0F` escape
    (15). A Group-3 opcode here carries a set R bit over the opcode
    extension and is not canonical for the one-operand forms. -/
def decodeNachRexR (rBit bBit : Nat) :
    List Byte → Option (MulDivDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if byteNat op == 15 then decodeImulRex rBit bBit rest
    else none

/-- Decode the first canonical MulDiv instruction, returning it with its
    consumed length and the remaining bytes. Only canonical REX.W
    register-direct encodings are accepted; anything else (missing REX,
    REX.X set, REX.R set on a Group-3 opcode, wrong opcode,
    non-register mode, wrong extension digit, truncated input) refuses
    with `none`. The decoder parses bytes and never compares against
    `mulDivEncode` output. -/
def decodeMulDiv : List Byte → Option (MulDivDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match byteNat b with
  | 72 => decodeNachRex 0 0 rest
  | 73 => decodeNachRex 0 1 rest
  | 76 => decodeNachRexR 1 0 rest
  | 77 => decodeNachRexR 1 1 rest
  | _ => none

/-- Round trip for `mulRax`: decoding the canonical bytes returns the
    operation with its consumed length. -/
theorem roundtrip_mulRax (src : Register) (suffix : List Byte) :
    decodeMulDiv (mulDivEncode (.mulRax src) ++ suffix) =
      some (⟨.mulRax src, (mulDivEncode (.mulRax src)).length⟩, suffix) := by
  cases src <;> rfl

/-- Round trip for `divRax`. -/
theorem roundtrip_divRax (src : Register) (suffix : List Byte) :
    decodeMulDiv (mulDivEncode (.divRax src) ++ suffix) =
      some (⟨.divRax src, (mulDivEncode (.divRax src)).length⟩, suffix) := by
  cases src <;> rfl

/-- Round trip for `idivRax`. -/
theorem roundtrip_idivRax (src : Register) (suffix : List Byte) :
    decodeMulDiv (mulDivEncode (.idivRax src) ++ suffix) =
      some (⟨.idivRax src, (mulDivEncode (.idivRax src)).length⟩, suffix) := by
  cases src <;> rfl

/-- Round trip for two-operand `imul2`. -/
theorem roundtrip_imul2 (dst src : Register) (suffix : List Byte) :
    decodeMulDiv (mulDivEncode (.imul2 dst src) ++ suffix) =
      some (⟨.imul2 dst src, (mulDivEncode (.imul2 dst src)).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every MulDiv operation, over any
    suffix. The decoded length is the consumed prefix length. -/
theorem roundtrip_muldiv (b : MulDivBefehl) (suffix : List Byte) :
    decodeMulDiv (mulDivEncode b ++ suffix) =
      some (⟨b, (mulDivEncode b).length⟩, suffix) := by
  cases b with
  | mulRax src => exact roundtrip_mulRax src suffix
  | divRax src => exact roundtrip_divRax src suffix
  | idivRax src => exact roundtrip_idivRax src suffix
  | imul2 dst src => exact roundtrip_imul2 dst src suffix

/-- A successful round trip consumes exactly its prefix, within 1..15. -/
theorem roundtrip_muldiv_len_ok (b : MulDivBefehl) (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decodeMulDiv (mulDivEncode b ++ suffix) = some (⟨b, n⟩, rest) ∧
        n + rest.length = (mulDivEncode b ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 := by
  refine ⟨(mulDivEncode b).length, suffix, roundtrip_muldiv b suffix, ?_,
    (mulDivEncode_len_ok b).1, (mulDivEncode_len_ok b).2⟩
  rw [List.length_append]

/-- ARBITRARY-INPUT LENGTH (Group 3): any successful decode reports
    length 3 and consumes exactly its one ModRM byte; the REX and opcode
    bytes are consumed by the calling layer. -/
theorem decodeF7Modrm_len (bBit : Nat) (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte)
    (h : decodeF7Modrm bBit bs = some (d, rest)) :
    d.laenge = 3 ∧ rest.length + 1 = bs.length := by
  cases bs with
  | nil => simp [decodeF7Modrm] at h
  | cons m t =>
    simp only [decodeF7Modrm] at h
    by_cases hmod : byteNat m / 64 == 3
    · rw [if_pos hmod] at h
      split at h
      · split at h
        · cases h; exact ⟨rfl, by simp⟩
        · simp at h
      · split at h
        · cases h; exact ⟨rfl, by simp⟩
        · simp at h
      · split at h
        · cases h; exact ⟨rfl, by simp⟩
        · simp at h
      · simp at h
    · rw [if_neg hmod] at h
      simp at h

/-- ARBITRARY-INPUT LENGTH (IMUL ModRM): any successful decode reports
    length 4 and consumes exactly its one ModRM byte. -/
theorem decodeImulModrm_len (rBit bBit : Nat) (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte)
    (h : decodeImulModrm rBit bBit bs = some (d, rest)) :
    d.laenge = 4 ∧ rest.length + 1 = bs.length := by
  cases bs with
  | nil => simp [decodeImulModrm] at h
  | cons m t =>
    simp only [decodeImulModrm] at h
    by_cases hmod : byteNat m / 64 == 3
    · rw [if_pos hmod] at h
      split at h
      · cases h; exact ⟨rfl, by simp⟩
      · simp at h
    · rw [if_neg hmod] at h
      simp at h

/-- ARBITRARY-INPUT LENGTH (IMUL escape): any successful decode reports
    length 4 and consumes exactly the `AF` byte plus its one ModRM
    byte. -/
theorem decodeImulRex_len (rBit bBit : Nat) (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte)
    (h : decodeImulRex rBit bBit bs = some (d, rest)) :
    d.laenge = 4 ∧ rest.length + 2 = bs.length := by
  cases bs with
  | nil => simp [decodeImulRex] at h
  | cons op2 t =>
    simp only [decodeImulRex] at h
    by_cases haf : byteNat op2 == 175
    · rw [if_pos haf] at h
      obtain ⟨hlen, hcon⟩ := decodeImulModrm_len rBit bBit t d rest h
      refine ⟨hlen, ?_⟩
      simp only [List.length_cons]
      omega
    · rw [if_neg haf] at h
      simp at h

/-- ARBITRARY-INPUT LENGTH (REX without R): any successful decode
    reports length 3 or 4 and consumes exactly its opcode plus inner
    bytes; the REX byte itself is consumed by the calling layer. -/
theorem decodeNachRex_len (rBit bBit : Nat) (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte)
    (h : decodeNachRex rBit bBit bs = some (d, rest)) :
    (d.laenge = 3 ∨ d.laenge = 4) ∧
      d.laenge + rest.length = bs.length + 1 := by
  cases bs with
  | nil => simp [decodeNachRex] at h
  | cons op t =>
    simp only [decodeNachRex] at h
    by_cases hf7 : byteNat op == 247
    · rw [if_pos hf7] at h
      obtain ⟨hlen, hcon⟩ := decodeF7Modrm_len bBit t d rest h
      refine ⟨Or.inl hlen, ?_⟩
      simp only [List.length_cons]
      omega
    · rw [if_neg hf7] at h
      by_cases h0f : byteNat op == 15
      · rw [if_pos h0f] at h
        obtain ⟨hlen, hcon⟩ := decodeImulRex_len rBit bBit t d rest h
        refine ⟨Or.inr hlen, ?_⟩
        simp only [List.length_cons]
        omega
      · rw [if_neg h0f] at h
        simp at h

/-- ARBITRARY-INPUT LENGTH (REX with R): any successful decode reports
    length 4 and consumes exactly its opcode plus inner bytes; the REX
    byte itself is consumed by the calling layer. -/
theorem decodeNachRexR_len (rBit bBit : Nat) (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte)
    (h : decodeNachRexR rBit bBit bs = some (d, rest)) :
    d.laenge = 4 ∧ d.laenge + rest.length = bs.length + 1 := by
  cases bs with
  | nil => simp [decodeNachRexR] at h
  | cons op t =>
    simp only [decodeNachRexR] at h
    by_cases h0f : byteNat op == 15
    · rw [if_pos h0f] at h
      obtain ⟨hlen, hcon⟩ := decodeImulRex_len rBit bBit t d rest h
      refine ⟨hlen, ?_⟩
      simp only [List.length_cons]
      omega
    · rw [if_neg h0f] at h
      simp at h

/-- ARBITRARY-INPUT LENGTH SOUNDNESS: any successful decode of an
    arbitrary input consumes exactly its stated length, within 1..15.
    The stated length is the consumed REX/opcode/ModRM prefix; the
    remainder is the untouched suffix. -/
theorem decodeMulDiv_len_ok (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (h : decodeMulDiv bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  cases bs with
  | nil => simp [decodeMulDiv] at h
  | cons b t =>
    simp only [decodeMulDiv] at h
    split at h
    · obtain ⟨h34, heq⟩ := decodeNachRex_len 0 0 t d rest h
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · cases h34 with
        | inl h3 => omega
        | inr h4 => omega
      · cases h34 with
        | inl h3 => omega
        | inr h4 => omega
    · obtain ⟨h34, heq⟩ := decodeNachRex_len 0 1 t d rest h
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · cases h34 with
        | inl h3 => omega
        | inr h4 => omega
      · cases h34 with
        | inl h3 => omega
        | inr h4 => omega
    · obtain ⟨hlen, heq⟩ := decodeNachRexR_len 1 0 t d rest h
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · omega
      · omega
    · obtain ⟨hlen, heq⟩ := decodeNachRexR_len 1 1 t d rest h
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · omega
      · omega
    · simp at h

/-- A decoded length is always a valid step length: bytes that decode
    never carry a bad length into the step. -/
theorem decodiert_laenge_ok (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (h : decodeMulDiv bs = some (d, rest)) :
    laengeOk d.laenge = true := by
  obtain ⟨_, hlo, hhi⟩ := decodeMulDiv_len_ok bs d rest h
  simp only [laengeOk, decide_eq_true_eq]
  omega

/-- DECODE-TO-EXECUTE (MUL): bytes decoding to `mulRax` step through
    the REUSED unsigned product with the REUSED unsigned flag snapshot;
    RAX holds the low word, RDX the high word. -/
theorem decode_exec_mul (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .mulRax src) :
    mulDivSchritt d s = .ok { s with register := regSet (regSet s.register Register.rax (mulLow .b64 (s.register Register.rax) (s.register src))) Register.rdx (mulHighU .b64 (s.register Register.rax) (s.register src)), rip := ripNach s.rip d.laenge, flags := mulFlagsU s.flags (s.register Register.rax) (s.register src) } := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_mul_erfolg d s src hok h

/-- DECODE-TO-EXECUTE (IMUL): bytes decoding to `imul2` step through
    the REUSED truncated product with the REUSED signed flag snapshot. -/
theorem decode_exec_imul (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (dst src : Register) (s : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .imul2 dst src) :
    mulDivSchritt d s = .ok { s with register := regSet s.register dst (mulLow .b64 (s.register dst) (s.register src)), rip := ripNach s.rip d.laenge, flags := mulFlagsS s.flags (s.register dst) (s.register src) } := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_imul_erfolg d s dst src hok h

/-- DECODE-TO-EXECUTE (DIV success): bytes decoding to `divRax` with a
    defined wide quotient step through the REUSED unsigned division;
    RAX holds the quotient, RDX the remainder, flags are preserved
    (every DIV flag is undefined). The implicit RDX:RAX dividend is read
    from the pre-state register file. -/
theorem decode_exec_div_ok (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand) (q r : Wort)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .divRax src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = some (q, r)) :
    mulDivSchritt d s = .ok { s with register := regSet (regSet s.register Register.rax q) Register.rdx r, rip := ripNach s.rip d.laenge } := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_div_erfolg d s src q r hok h hqr

/-- DECODE-TO-EXECUTE (DIV trap): bytes decoding to `divRax` with an
    undefined wide quotient (divisor zero or 65-bit quotient) trap to
    the hardware halt, never to a value. -/
theorem decode_exec_div_halt (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .divRax src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = none) :
    mulDivSchritt d s = .hardwareHalt := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_div_halt d s src hok h hqr

/-- DECODE-TO-EXECUTE (IDIV success): bytes decoding to `idivRax` with a
    defined signed quotient step through the REUSED truncation-toward-
    zero division (never SAR floor); quotient into RAX, remainder into
    RDX, flags preserved. -/
theorem decode_exec_idiv_ok (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand) (q r : Wort)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .idivRax src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src) = some (q, r)) :
    mulDivSchritt d s = .ok { s with register := regSet (regSet s.register Register.rax q) Register.rdx r, rip := ripNach s.rip d.laenge } := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_idiv_erfolg d s src q r hok h hqr

/-- DECODE-TO-EXECUTE (IDIV trap): bytes decoding to `idivRax` with a
    zero divisor or an out-of-range truncated quotient trap. -/
theorem decode_exec_idiv_halt (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .idivRax src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src) = none) :
    mulDivSchritt d s = .hardwareHalt := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_idiv_halt d s src hok h hqr

/-- GUARD-TRAP AGREEMENT (decoded DIV): a decoded DIV image refused by
    the decided admission guard traps in the step. Refusal and trap
    agree on actual decoded bytes. -/
theorem decode_div_verweigert_heisst_halt (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .divRax src)
    (hzu : zugelassen (.divRax src) s = false) :
    mulDivSchritt d s = .hardwareHalt := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact verweigert_heisst_halt d s src h hok hzu

/-- GUARD-TRAP AGREEMENT (decoded IDIV): a decoded IDIV image with an
    undefined signed quotient traps in the step. -/
theorem decode_idiv_verweigert_heisst_halt (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .idivRax src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src) = none) :
    mulDivSchritt d s = .hardwareHalt := by
  have hok := decodiert_laenge_ok bs d rest hdec
  exact md_idiv_halt d s src hok h hqr

/-! ## Same target state: what a decoded step leaves alone.

    Every decoded MulDiv step runs on the canonical `Zustand` with the
    shared `regSet`/`ripNach`/`laengeOk` shapes: MUL/IMUL touch only
    their destination registers, flags and RIP; DIV/IDIV touch only
    RAX/RDX and RIP. Memory permission maps are never rewritten by a
    decoded step. -/

/-- A decoded MUL step changes no memory byte. -/
theorem decode_mul_speicher (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s s' : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .mulRax src)
    (hstep : mulDivSchritt d s = .ok s') :
    s'.speicher = s.speicher := by
  have hok := decodiert_laenge_ok bs d rest hdec
  rw [md_mul_erfolg d s src hok h] at hstep
  cases hstep
  rfl

/-- A decoded DIV step preserves the flags. -/
theorem decode_div_flags (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s s' : Zustand) (q r : Wort)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .divRax src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = some (q, r))
    (hstep : mulDivSchritt d s = .ok s') :
    s'.flags = s.flags := by
  have hok := decodiert_laenge_ok bs d rest hdec
  rw [md_div_erfolg d s src q r hok h hqr] at hstep
  cases hstep
  rfl

/-! ## Pinned bytes: one canonical encoding per admitted form.

    Each pin fixes the exact REX/opcode/ModRM bytes: MUL and IDIV over
    a low register, DIV over an extended register (REX.B set), IMUL
    over two extended registers (REX.R and REX.B set). -/

/-- Pinned bytes: MUL over RCX (`REX.W, F7 /4, ModRM E1`). -/
theorem pin_mulRax_rcx :
    mulDivEncode (.mulRax .rcx) =
      [natByte 72, natByte 247, natByte 225] := by
  decide

/-- Pinned decode: MUL over RCX. -/
theorem pin_mulRax_rcx_dekode :
    decodeMulDiv [natByte 72, natByte 247, natByte 225] =
      some ((⟨.mulRax .rcx, 3⟩ : MulDivDecodiert), []) := by
  decide

/-- Pinned bytes: DIV over r8 (`REX.W+B, F7 /6, ModRM F0`). -/
theorem pin_divRax_r8 :
    mulDivEncode (.divRax .r8) =
      [natByte 73, natByte 247, natByte 240] := by
  decide

/-- Pinned decode: DIV over r8. -/
theorem pin_divRax_r8_dekode :
    decodeMulDiv [natByte 73, natByte 247, natByte 240] =
      some ((⟨.divRax .r8, 3⟩ : MulDivDecodiert), []) := by
  decide

/-- Pinned bytes: IDIV over RCX (`REX.W, F7 /7, ModRM F9`). -/
theorem pin_idivRax_rcx :
    mulDivEncode (.idivRax .rcx) =
      [natByte 72, natByte 247, natByte 249] := by
  decide

/-- Pinned decode: IDIV over RCX. -/
theorem pin_idivRax_rcx_dekode :
    decodeMulDiv [natByte 72, natByte 247, natByte 249] =
      some ((⟨.idivRax .rcx, 3⟩ : MulDivDecodiert), []) := by
  decide

/-- Pinned bytes: IMUL r9, r15 (`REX.W+R+B, 0F AF, ModRM CF`). -/
theorem pin_imul2_r9_r15 :
    mulDivEncode (.imul2 .r9 .r15) =
      [natByte 77, natByte 15, natByte 175, natByte 207] := by
  decide

/-- Pinned decode: IMUL r9, r15. -/
theorem pin_imul2_r9_r15_dekode :
    decodeMulDiv [natByte 77, natByte 15, natByte 175, natByte 207] =
      some ((⟨.imul2 .r9 .r15, 4⟩ : MulDivDecodiert), []) := by
  decide

/-- A decoded MUL step advances RIP past exactly the consumed bytes. -/
theorem decode_mul_rip (bs : List Byte) (d : MulDivDecodiert)
    (rest : List Byte) (src : Register) (s s' : Zustand)
    (hdec : decodeMulDiv bs = some (d, rest))
    (h : d.befehl = .mulRax src)
    (hstep : mulDivSchritt d s = .ok s') :
    s'.rip = ripNach s.rip d.laenge := by
  have hok := decodiert_laenge_ok bs d rest hdec
  rw [md_mul_erfolg d s src hok h] at hstep
  cases hstep
  rfl

/-! ## Refusals: truncated and non-canonical inputs.

    A lone REX, a missing ModRM, a missing REX, a set REX.X bit, a set
    REX.R bit over the Group-3 opcode extension, a wrong extension
    digit, a memory-mode ModRM and a wrong second opcode byte all
    refuse. Truncation refuses at every prefix length. -/

/-- The empty input decodes to nothing. -/
theorem md_decode_nichts_leer : decodeMulDiv [] = none := rfl

/-- A lone REX prefix is truncated. -/
theorem md_decode_nichts_rex_allein : decodeMulDiv [natByte 72] = none := by
  decide

/-- REX plus Group-3 opcode without ModRM is truncated. -/
theorem md_decode_nichts_modrm_fehlt :
    decodeMulDiv [natByte 72, natByte 247] = none := by
  decide

/-- REX plus the IMUL escape without its second opcode byte is
    truncated. -/
theorem md_decode_nichts_zweitop_fehlt :
    decodeMulDiv [natByte 72, natByte 15] = none := by
  decide

/-- REX plus both IMUL opcode bytes without ModRM is truncated. -/
theorem md_decode_nichts_imul_modrm_fehlt :
    decodeMulDiv [natByte 72, natByte 15, natByte 175] = none := by
  decide

/-- A Group-3 opcode without REX.W is not canonical. -/
theorem md_decode_nichts_ohne_rex :
    decodeMulDiv [natByte 247, natByte 225] = none := by
  decide

/-- A REX prefix with the X bit set is not canonical. -/
theorem md_decode_nichts_rex_x :
    decodeMulDiv [natByte 74, natByte 247, natByte 225] = none := by
  decide

/-- A Group-3 opcode with the REX.R bit set is not canonical for the
    one-operand forms (the R bit would extend the opcode digit). -/
theorem md_decode_nichts_rex_r_gruppe3 :
    decodeMulDiv [natByte 76, natByte 247, natByte 225] = none := by
  decide

/-- Extension digit `/5` is no MulDiv operation. -/
theorem md_decode_nichts_falsche_nummer :
    decodeMulDiv [natByte 72, natByte 247, natByte 233] = none := by
  decide

/-- A memory-mode ModRM is not canonical for these forms. -/
theorem md_decode_nichts_speicher_modus :
    decodeMulDiv [natByte 72, natByte 247, natByte 161] = none := by
  decide

/-- A wrong second opcode byte after the IMUL escape refuses. -/
theorem md_decode_nichts_zweitop_falsch :
    decodeMulDiv [natByte 72, natByte 15, natByte 174, natByte 193] =
      none := by
  decide

/-- An IMUL memory-mode ModRM refuses. -/
theorem md_decode_nichts_imul_speicher_modus :
    decodeMulDiv [natByte 72, natByte 15, natByte 175, natByte 129] =
      none := by
  decide

/-! ## Signed division probes: negative values and overflow.

    IDIV truncates toward zero (never SAR floor): `-7 / 2` is `-3`
    remainder `-1`, `7 / -1` is `-7` remainder `0`. `INT_MIN / -1`
    overflows the signed range and traps. Each probe runs the REUSED
    step on a concrete RDX:RAX state. -/

/-- Witness registers for `-7 / 2`: RAX holds `-7`, RDX its sign
    extension `-1`, RCX the divisor `2`. -/
def idivNegReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 (2 ^ 64 - 7)
  else if q = Register.rdx then BitVec.ofNat 64 (2 ^ 64 - 1)
  else if q = Register.rcx then 2
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the negative-dividend division `-7 / 2`. -/
def idivNegZustand : Zustand :=
  { register := idivNegReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for `7 / -1`: RAX holds `7`, RDX zero, RCX the
    negative divisor `-1`. -/
def idivNegTeilerReg : Register → Wort := fun q =>
  if q = Register.rax then 7
  else if q = Register.rdx then 0
  else if q = Register.rcx then BitVec.ofNat 64 (2 ^ 64 - 1)
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the negative-divisor division `7 / -1`. -/
def idivNegTeilerZustand : Zustand :=
  { register := idivNegTeilerReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for `INT_MIN / -1`: RDX:RAX holds the sign
    extended minimum, RCX the divisor `-1`. -/
def idivMinReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 (2 ^ 63)
  else if q = Register.rdx then BitVec.ofNat 64 (2 ^ 64 - 1)
  else if q = Register.rcx then BitVec.ofNat 64 (2 ^ 64 - 1)
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the overflowing division `INT_MIN / -1`. -/
def idivMinZustand : Zustand :=
  { register := idivMinReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Negative dividend truncates: `-7 / 2` lands RAX = `-3`, RDX =
    `-1`, flags kept (never SAR floor, which would give `-4`). -/
theorem probe_idiv_negativ :
    okWerte (mulDivSchritt ⟨.idivRax .rcx, 3⟩ idivNegZustand) =
      some (0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFF, false) := by
  decide

/-- Negative divisor truncates: `7 / -1` lands RAX = `-7`, RDX = `0`. -/
theorem probe_idiv_neg_teiler :
    okWerte (mulDivSchritt ⟨.idivRax .rcx, 3⟩ idivNegTeilerZustand) =
      some (0xFFFFFFFFFFFFFFF9, 0, false) := by
  decide

/-- Quotient overflow traps: `INT_MIN / -1` halts the step and is
    refused by the decided guard. -/
theorem probe_idiv_min_halt :
    istHalt (mulDivSchritt ⟨.idivRax .rcx, 3⟩ idivMinZustand) = true ∧
    zugelassen (.idivRax .rcx) idivMinZustand = false := by
  refine ⟨by decide, by decide⟩

/-- Zero divisor traps on IDIV too: the step halts and the decided
    guard refuses. -/
theorem probe_idiv_null_halt :
    istHalt (mulDivSchritt ⟨.idivRax .rcx, 3⟩ mdZustandNull) = true ∧
    zugelassen (.idivRax .rcx) mdZustandNull = false := by
  refine ⟨by decide, by decide⟩

/-! ## Joint witness: decoded bytes, execution, memory and refusals.

    The canonical MUL bytes decode, step to the product `42` through
    the REUSED execution, and the product goes through real
    permission-checked memory with an observable change — while the
    planted DIV-by-zero image traps with its guard refusal and
    truncated bytes refuse. Everything is instantiated jointly on
    nondegenerate states (a memory-changing store plus loud
    refusals). -/

/-- Witness memory: the decoded MUL product `42` at address zero. -/
def mulCodecSpeicher42 : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 42 }

/-- JOINT WITNESS over decoded bytes: MUL bytes decode and step to
    `42`, the product changes real memory observably, DIV-by-zero
    traps with its guard refusal, and truncated bytes refuse. -/
theorem muldiv_codec_zeuge :
    decodeMulDiv (mulDivEncode (.mulRax .rcx)) =
        some (⟨.mulRax .rcx, 3⟩, []) ∧
      okWerte (mulDivSchritt ⟨.mulRax .rcx, 3⟩ mdZustandMul) =
        some (42, 0, false) ∧
      (∃ m1 : Speicher,
        write64 zeugenSpeicher 0 42 = some m1 ∧
        read64 m1 0 = some 42 ∧
        zeugenSpeicher.bytes 0 ≠ m1.bytes 0) ∧
      istHalt (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = true ∧
      zugelassen (.divRax .rcx) mdZustandNull = false ∧
      decodeMulDiv [natByte 72, natByte 247] = none := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide⟩
  refine ⟨mulCodecSpeicher42, ?_, ?_, ?_⟩
  · have hwr : write64 zeugenSpeicher 0 42 = some mulCodecSpeicher42 := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr
  · have hwr : write64 zeugenSpeicher 0 42 = some mulCodecSpeicher42 := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd : lesbar8 zeugenSpeicher 0 = true := rfl
    exact read64_nach_write64 zeugenSpeicher _ 0 42 hwr hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0 42
      8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 42 0
    unfold writeBytes
    rw [hhit]
    decide

/- CUTS:
   Proved here: canonical REX.W register-direct byte encodings for the
   four MulDiv operations (`mulDivEncode` with 3/4-byte lengths in the
   1..15 window), an independent byte parser (`decodeMulDiv` through
   the REX/opcode/ModRM layers, never encode-equality), per-form and
   generic round trips, ARBITRARY-INPUT length soundness
   (`decodeMulDiv_len_ok`: every successful decode of any input
   consumes exactly its stated length within 1..15, via the per-layer
   consumption facts), decoded lengths always passing `laengeOk`,
   generic decode-to-execute correspondence against the REUSED
   `mulDivSchritt` for all four forms (success and trap, with the
   implicit RDX:RAX dividend, the divide refusal/trap distinction and
   the REUSED value/flag semantics), decoded DIV/IDIV guard-trap
   agreement, same-state frame facts (MUL changes no memory, DIV keeps
   flags, MUL RIP advances past the consumed bytes), eight pinned
   byte/decode pairs, twelve truncation/non-canonical refusals,
   negative-dividend/negative-divisor truncation probes, zero-divisor
   and INT_MIN overflow trap probes with guard refusals, and the joint
   decode/execute/memory/refusal witness `muldiv_codec_zeuge`.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings, the ModRM digit choice,
     the truncation direction and the quotient-overflow rule are STATED
     canonical semantics, not verified against silicon. The refusal of
     a set REX.R bit over a Group-3 opcode and of a set REX.X bit is a
     canonical-subset choice (one encoding per operation for the
     validator); architecturally the R bit over an opcode extension
     may be ignored by hardware, which this subset refuses instead.
   - No memory-form MUL/DIV/IDIV (`F7 /m` with mod ≠ 3) and no
     one-operand IMUL (`F6/F7`-style) or immediate IMUL forms: only the
     register-direct subset above decodes; everything else refuses.
   - No source correspondence: nothing here speaks about Gabbro source
     division, ranges, duties, lowering or bridges (lanes 277/287
     business); source division is never reinterpreted as floor.
   - No physical-fault or source-stop transfer: `hardwareHalt` NAMES
     the divide-error stop class the source `FortschrittG` already has;
     the guard/fault/channel/order correspondence stays OPEN, as does
     physical delivery (#DE vectoring, handler entry).
   - No fetch integration: this file decodes caller-supplied byte
     lists, never actual executable memory; permission-checked fetch
     and the byte step belong to the unified path (lane 575), which
     consumes `mulDivEncode`/`decodeMulDiv`/`roundtrip_muldiv`/
     `decodeMulDiv_len_ok`/`decodiert_laenge_ok` and the
     `decode_exec_*` selection as its producer interface.
   - No TSO/concurrency bridge: all facts are sequential over one
     `Zustand`; aligned multi-byte atomicity, tearing and the GX
     refinement stay with the TSO lane.
   - No cost transfer: MUL/IMUL/DIV/IDIV latency or throughput and
     budget simulation are not modelled.
   - No new hardware or software assumptions and no checker rule: no
     diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms mulDivEncode_len
#print axioms mulDivEncode_len_ok
#print axioms roundtrip_mulRax
#print axioms roundtrip_divRax
#print axioms roundtrip_idivRax
#print axioms roundtrip_imul2
#print axioms roundtrip_muldiv
#print axioms roundtrip_muldiv_len_ok
#print axioms decodeF7Modrm_len
#print axioms decodeImulModrm_len
#print axioms decodeImulRex_len
#print axioms decodeNachRex_len
#print axioms decodeNachRexR_len
#print axioms decodeMulDiv_len_ok
#print axioms decodiert_laenge_ok
#print axioms decode_exec_mul
#print axioms decode_exec_imul
#print axioms decode_exec_div_ok
#print axioms decode_exec_div_halt
#print axioms decode_exec_idiv_ok
#print axioms decode_exec_idiv_halt
#print axioms decode_div_verweigert_heisst_halt
#print axioms decode_idiv_verweigert_heisst_halt
#print axioms decode_mul_speicher
#print axioms decode_div_flags
#print axioms decode_mul_rip
#print axioms pin_mulRax_rcx
#print axioms pin_mulRax_rcx_dekode
#print axioms pin_divRax_r8
#print axioms pin_divRax_r8_dekode
#print axioms pin_idivRax_rcx
#print axioms pin_idivRax_rcx_dekode
#print axioms pin_imul2_r9_r15
#print axioms pin_imul2_r9_r15_dekode
#print axioms md_decode_nichts_leer
#print axioms md_decode_nichts_rex_allein
#print axioms md_decode_nichts_modrm_fehlt
#print axioms md_decode_nichts_zweitop_fehlt
#print axioms md_decode_nichts_imul_modrm_fehlt
#print axioms md_decode_nichts_ohne_rex
#print axioms md_decode_nichts_rex_x
#print axioms md_decode_nichts_rex_r_gruppe3
#print axioms md_decode_nichts_falsche_nummer
#print axioms md_decode_nichts_speicher_modus
#print axioms md_decode_nichts_zweitop_falsch
#print axioms md_decode_nichts_imul_speicher_modus
#print axioms probe_idiv_negativ
#print axioms probe_idiv_neg_teiler
#print axioms probe_idiv_min_halt
#print axioms probe_idiv_null_halt
#print axioms muldiv_codec_zeuge

end Gabbro.Grammatik.X86
