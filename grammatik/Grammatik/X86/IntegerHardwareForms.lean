/-
  File:      Grammatik/X86/IntegerHardwareForms.lean
  Subject:   Practical integer logical/test rows over shared width-parametric rules.

  Lane 666: missing practical scalar AND/OR/TEST/NOT/NEG rows reusing the
  canonical producers (Ganzzahl andB/orB/notB, ShiftLogic negW/logikFlags/
  NegGueltig, NarrowOps mergeRegNarrow). No new evaluator of pilot forms,
  no integer-to-pointer conversion. AF none is undefined, never false.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.ShiftLogic
import Grammatik.X86.NarrowOps
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86

/-- Practical integer logical rows: register AND/OR, non-writing TEST,
    flag-preserving NOT, flag-defining NEG. Width is explicit data. -/
inductive IntHwOp where
  | andRR (b : Breite) (dst src : Register)
  | orRR (b : Breite) (dst src : Register)
  | testRR (b : Breite) (lhs rhs : Register)
  | notR (b : Breite) (dst : Register)
  | negR (b : Breite) (dst : Register)
  deriving DecidableEq, Repr

/-- Shared value dispatch: every row routes to its canonical producer. -/
def intHwWert (op : IntHwOp) (x y : Wort) : Wort :=
  match op with
  | .andRR b _ _ => andB b x y
  | .orRR b _ _ => orB b x y
  | .testRR b _ _ => andB b x y
  | .notR b _ => notB b x
  | .negR b _ => negW b x

/-- Routing is definitional for each row. -/
theorem intHwWert_routen (b : Breite) (x y : Wort) (d s : Register) :
    intHwWert (.andRR b d s) x y = andB b x y ∧
    intHwWert (.orRR b d s) x y = orB b x y ∧
    intHwWert (.notR b d) x y = notB b x ∧
    intHwWert (.negR b d) x y = negW b x := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 1. Flags: defined versus undefined (AF abstraction).

    AND/OR/TEST reuse `logikFlags` (CF/OF cleared, AF none = undefined,
    width-correct sign via negB). NOT preserves flags exactly (no snapshot).
    NEG reuses `negWf` (fully defined, AF = nibble borrow). The AF-none
    observation abstraction: two snapshots valid for the same AND value
    agree on every DEFINED flag; AF itself is never read as false. -/

/-- Flag snapshot of a writing logic row (AND/OR) at its width. -/
def intHwFlagsLogik (b : Breite) (r : Wort) : Flags := logikFlags b r

/-- TEST flags equal the AND flags of the same value: TEST writes no
    register but observes the identical flag snapshot. -/
theorem test_flags_eq_and (b : Breite) (x y : Wort) :
    intHwFlagsLogik b (intHwWert (.testRR b .rax .rcx) x y) =
      (andW b x y).2 := by
  simp [intHwWert, intHwFlagsLogik, andW]

/-- AF of every logic snapshot is undefined (none), never false. -/
theorem inthw_logik_af_none (b : Breite) (r : Wort) :
    (intHwFlagsLogik b r).af = none := by
  simp [intHwFlagsLogik, logikFlags]

/-- At full width the admitted snapshot agrees with `and64`/`or64`. -/
theorem inthw_b64_agrees (x y : Wort) :
    intHwFlagsLogik .b64 (andB .b64 x y) = (and64 x y).2 ∧
    intHwFlagsLogik .b64 (orB .b64 x y) = (or64 x y).2 := by
  constructor
  · simp [intHwFlagsLogik, logikFlags, negB_b64, andB_b64, and64]
  · simp [intHwFlagsLogik, logikFlags, negB_b64, orB_b64, or64]

/-- NEG snapshot is the canonical defined one (AF defined, not none
    in general is false: it is `some` by construction). -/
theorem inthw_neg_defined (b : Breite) (x : Wort) :
    (negWf b x).2.af = some (afSub 0 (trunc b x)) := by
  simp [negWf]

/-! ## 2. Width discipline: 32-bit zero-upper, 8/16-bit partial merge.

    Register writes reuse `mergeRegNarrow`: 32-bit clears the upper half,
    8/16-bit keep the unaffected upper bits, 64-bit is the full word.
    Narrow value semantics (andB/orB/notB/negW) are proved at every width;
    the byte codec below admits b64/b32; b8/b16 codec rows stay OPEN. -/

/-- Destination value written by a writing row at its width. -/
def intHwDst (op : IntHwOp) (oldVal x y : Wort) : Wort :=
  match op with
  | .andRR b _ _ => mergeRegNarrow b oldVal (andB b x y)
  | .orRR b _ _ => mergeRegNarrow b oldVal (orB b x y)
  | .testRR _ _ _ => oldVal
  | .notR b _ => mergeRegNarrow b oldVal (notB b x)
  | .negR b _ => mergeRegNarrow b oldVal (negW b x)

/-- 32-bit writes clear the upper half (generic, by reuse). -/
theorem inthw_b32_clears (op : IntHwOp) (oldVal x y : Wort)
    (d s : Register) (h : op = .andRR .b32 d s ∨ op = .orRR .b32 d s) :
    (intHwDst op oldVal x y).toNat < 2 ^ 32 := by
  cases h with
  | inl h1 =>
    subst h1
    simp only [intHwDst]
    exact mergeRegNarrow_b32_fits oldVal _
  | inr h1 =>
    subst h1
    simp only [intHwDst]
    exact mergeRegNarrow_b32_fits oldVal _

/-- 64-bit writes are the full canonical value. -/
theorem inthw_b64_full (oldVal x y : Wort) (d s : Register) :
    intHwDst (.andRR .b64 d s) oldVal x y = andB .b64 x y ∧
    intHwDst (.orRR .b64 d s) oldVal x y = orB .b64 x y ∧
    intHwDst (.notR .b64 d) oldVal x y = notB .b64 x := by
  simp [intHwDst, mergeRegNarrow_b64, andB_b64, orB_b64, notB_b64]

/-- 8-bit AND/OR pins: partial-register merge keeps upper bits. -/
theorem inthw_b8_pins :
    mergeRegNarrow .b8 0xABCDEF1234567890 (andB .b8 0xF0 0x0F) =
      0xABCDEF1234567800 ∧
    intHwWert (.orRR .b8 .rax .rcx) 0x80 0x01 = 0x81 := by
  constructor
  · decide
  · decide

/-! ## 3. Canonical byte codec (b64/b32 register rows).

    AND is 0x21, OR is 0x09, TEST is 0x85 (all mod=3), NOT/NEG are group
    F7 /2 /3 (mod=3). b64 uses REX.W (72/73/76/77, X=0); b32 uses REX
    W=0 (64/65/68/69). b8/b16 have no codec row here (OPEN). Digits /2/3
    are disjoint from MulDiv's /4/6/7; opcodes differ from pilot/shift/
    narrow/control rows. Decoder parses bytes, never encode-equality. -/

/-- Decoded row with consumed length (always 3 here). -/
structure IntHwDec where
  op : IntHwOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- REX.W byte (X=0): R=rh, B=bh extension bits. -/
def intHwRexW (rh bh : Nat) : Byte := rexByte rh bh

/-- REX W=0 byte (X=0): R=rh, B=bh extension bits. -/
def intHwRex0 (rh bh : Nat) : Byte := natByte (64 + 4 * rh + bh)

/-- Opcode of a row family: AND 33, OR 9, TEST 133. -/
def intHwOpcode : IntHwOp → Nat
  | .andRR _ _ _ => 33
  | .orRR _ _ _ => 9
  | .testRR _ _ _ => 133
  | .notR _ _ => 247
  | .negR _ _ => 247

/-- Canonical encoding of one register row (b64/b32 only). -/
def encodeIntHw : IntHwOp → List Byte
  | .andRR .b64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 33,
     modrmReg (regLow src) (regLow dst)]
  | .andRR .b32 dst src =>
    [natByte (64 + 4 * regHigh src + regHigh dst), natByte 33,
     modrmReg (regLow src) (regLow dst)]
  | .orRR .b64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 9,
     modrmReg (regLow src) (regLow dst)]
  | .orRR .b32 dst src =>
    [natByte (64 + 4 * regHigh src + regHigh dst), natByte 9,
     modrmReg (regLow src) (regLow dst)]
  | .testRR .b64 lhs rhs =>
    [rexByte (regHigh rhs) (regHigh lhs), natByte 133,
     modrmReg (regLow rhs) (regLow lhs)]
  | .testRR .b32 lhs rhs =>
    [natByte (64 + 4 * regHigh rhs + regHigh lhs), natByte 133,
     modrmReg (regLow rhs) (regLow lhs)]
  | .notR .b64 dst =>
    [rexByte 0 (regHigh dst), natByte 247,
     modrmReg 2 (regLow dst)]
  | .notR .b32 dst =>
    [natByte (64 + regHigh dst), natByte 247,
     modrmReg 2 (regLow dst)]
  | .negR .b64 dst =>
    [rexByte 0 (regHigh dst), natByte 247,
     modrmReg 3 (regLow dst)]
  | .negR .b32 dst =>
    [natByte (64 + regHigh dst), natByte 247,
     modrmReg 3 (regLow dst)]
  | _ => []

/-- Every canonical register encoding is exactly 3 bytes (b64/b32). -/
theorem encodeIntHw_len_b64 (dst src : Register) :
    (encodeIntHw (.andRR .b64 dst src)).length = 3 ∧
    (encodeIntHw (.orRR .b64 dst src)).length = 3 ∧
    (encodeIntHw (.testRR .b64 dst src)).length = 3 ∧
    (encodeIntHw (.notR .b64 dst)).length = 3 ∧
    (encodeIntHw (.negR .b64 dst)).length = 3 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Narrow (b8/b16) rows have no codec row: the encoder is empty there. -/
theorem encodeIntHw_schmal_leer (dst src : Register) (b : Breite)
    (h : b = .b8 ∨ b = .b16) :
    encodeIntHw (.andRR b dst src) = [] ∧
    encodeIntHw (.orRR b dst src) = [] := by
  cases h with
  | inl h8 => subst h8; exact ⟨rfl, rfl⟩
  | inr h16 => subst h16; exact ⟨rfl, rfl⟩

/-- Decode one mod=3 ModRM byte for AND/OR/TEST at the named width. -/
def decodeIntHwModrm (b : Breite) (op : Nat) (rBit bBit : Nat) :
    List Byte → Option (IntHwDec × List Byte)
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
      | some rs, some rd =>
        match op with
        | 33 => some (⟨.andRR b rd rs, 3⟩, rest)
        | 9 => some (⟨.orRR b rd rs, 3⟩, rest)
        | 133 => some (⟨.testRR b rd rs, 3⟩, rest)
        | _ => none
      | _, _ => none
    else none
  | [] => none

/-- Decode one group-F7 ModRM byte: /2 is NOT, /3 is NEG (mod=3 only).
    Digits /4/6/7 belong to MulDiv and refuse here. -/
def decodeIntHwF7 (b : Breite) (bBit : Nat) :
    List Byte → Option (IntHwDec × List Byte)
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match reg with
      | 2 =>
        match codeReg (bBit * 8 + rm) with
        | some rd => some (⟨.notR b rd, 3⟩, rest)
        | none => none
      | 3 =>
        match codeReg (bBit * 8 + rm) with
        | some rd => some (⟨.negR b rd, 3⟩, rest)
        | none => none
      | _ => none
    else none
  | [] => none

/-- Decode after REX: opcode 33/9/133 via ModRM, 247 via group F7. -/
def decodeIntHwNach (b : Breite) (rBit bBit : Nat) :
    List Byte → Option (IntHwDec × List Byte)
  | op :: rest =>
    if byteNat op == 33 then decodeIntHwModrm b 33 rBit bBit rest
    else if byteNat op == 9 then decodeIntHwModrm b 9 rBit bBit rest
    else if byteNat op == 133 then decodeIntHwModrm b 133 rBit bBit rest
    else if byteNat op == 247 then decodeIntHwF7 b bBit rest
    else none
  | [] => none

/-- Top-level decode: REX.W rows are b64, REX W=0 rows are b32;
    anything else (no REX, REX.X, 66 prefix, high-byte regs) refuses. -/
def decodeIntHw : List Byte → Option (IntHwDec × List Byte)
  | r :: rest =>
    match byteNat r with
    | 72 => decodeIntHwNach .b64 0 0 rest
    | 73 => decodeIntHwNach .b64 0 1 rest
    | 76 => decodeIntHwNach .b64 1 0 rest
    | 77 => decodeIntHwNach .b64 1 1 rest
    | 64 => decodeIntHwNach .b32 0 0 rest
    | 65 => decodeIntHwNach .b32 0 1 rest
    | 68 => decodeIntHwNach .b32 1 0 rest
    | 69 => decodeIntHwNach .b32 1 1 rest
    | _ => none
  | [] => none

/-! ## 4. Round trips, disjointness, refusals.

    Per-form round trips by register case analysis; the pilot refuses
    every new row (opcodes 33/9/133/247 never decode as pilot); MulDiv
    digits /4/6/7 refuse in the F7 arm. -/

/-- Round trip for 64-bit AND. -/
theorem roundtrip_inthw_and64 (dst src : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.andRR .b64 dst src) ++ suffix) =
      some (⟨.andRR .b64 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 64-bit OR. -/
theorem roundtrip_inthw_or64 (dst src : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.orRR .b64 dst src) ++ suffix) =
      some (⟨.orRR .b64 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 64-bit TEST. -/
theorem roundtrip_inthw_test64 (lhs rhs : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.testRR .b64 lhs rhs) ++ suffix) =
      some (⟨.testRR .b64 lhs rhs, 3⟩, suffix) := by
  cases lhs <;> cases rhs <;> rfl

/-- Round trip for 64-bit NOT. -/
theorem roundtrip_inthw_not64 (dst : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.notR .b64 dst) ++ suffix) =
      some (⟨.notR .b64 dst, 3⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 64-bit NEG. -/
theorem roundtrip_inthw_neg64 (dst : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.negR .b64 dst) ++ suffix) =
      some (⟨.negR .b64 dst, 3⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 32-bit AND. -/
theorem roundtrip_inthw_and32 (dst src : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.andRR .b32 dst src) ++ suffix) =
      some (⟨.andRR .b32 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 32-bit OR. -/
theorem roundtrip_inthw_or32 (dst src : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.orRR .b32 dst src) ++ suffix) =
      some (⟨.orRR .b32 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 32-bit TEST. -/
theorem roundtrip_inthw_test32 (lhs rhs : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.testRR .b32 lhs rhs) ++ suffix) =
      some (⟨.testRR .b32 lhs rhs, 3⟩, suffix) := by
  cases lhs <;> cases rhs <;> rfl

/-- Round trip for 32-bit NOT/NEG. -/
theorem roundtrip_inthw_notneg32 (dst : Register) (suffix : List Byte) :
    decodeIntHw (encodeIntHw (.notR .b32 dst) ++ suffix) =
        some (⟨.notR .b32 dst, 3⟩, suffix) ∧
      decodeIntHw (encodeIntHw (.negR .b32 dst) ++ suffix) =
        some (⟨.negR .b32 dst, 3⟩, suffix) := by
  cases dst <;> exact ⟨rfl, rfl⟩

/-- The pilot refuses every new b64 register row (opcodes differ). -/
theorem inthw_pilot_verweigert64 (dst src : Register) (suffix : List Byte) :
    decode (encodeIntHw (.andRR .b64 dst src) ++ suffix) = none ∧
    decode (encodeIntHw (.orRR .b64 dst src) ++ suffix) = none ∧
    decode (encodeIntHw (.testRR .b64 dst src) ++ suffix) = none ∧
    decode (encodeIntHw (.notR .b64 dst) ++ suffix) = none ∧
    decode (encodeIntHw (.negR .b64 dst) ++ suffix) = none := by
  cases dst <;> cases src <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Pinned bytes: 64-bit AND of ecx into eax. -/
theorem pin_inthw_and_eax_ecx :
    encodeIntHw (.andRR .b64 .rax .rcx) =
      [natByte 72, natByte 33, natByte 200] := by
  decide

/-- Pinned decode: 64-bit AND of ecx into eax. -/
theorem pin_inthw_and_eax_ecx_dekode :
    decodeIntHw [natByte 72, natByte 33, natByte 200] =
      some ((⟨.andRR .b64 .rax .rcx, 3⟩ : IntHwDec), []) := by
  decide

/-- Pinned bytes: 64-bit TEST rax, rax. -/
theorem pin_inthw_test_rax :
    encodeIntHw (.testRR .b64 .rax .rax) =
      [natByte 72, natByte 133, natByte 192] := by
  decide

/-- Pinned bytes: 64-bit NEG r9 (REX.B set). -/
theorem pin_inthw_neg_r9 :
    encodeIntHw (.negR .b64 .r9) =
      [natByte 73, natByte 247, natByte 217] := by
  decide

/-- Pinned decode: 64-bit NEG r9. -/
theorem pin_inthw_neg_r9_dekode :
    decodeIntHw [natByte 73, natByte 247, natByte 217] =
      some ((⟨.negR .b64 .r9, 3⟩ : IntHwDec), []) := by
  decide

/-- Planted refusals: empty, lone REX, unknown opcode, mod≠3,
    MulDiv digit /4 in the F7 arm, REX.X set, no-REX row. -/
theorem sonde_inthw_verweigert :
    decodeIntHw [] = none ∧
    decodeIntHw [natByte 72] = none ∧
    decodeIntHw [natByte 72, natByte 1, natByte 200] = none ∧
    decodeIntHw [natByte 72, natByte 33, natByte 8] = none ∧
    decodeIntHw [natByte 72, natByte 247, natByte 225] = none ∧
    decodeIntHw [natByte 74, natByte 33, natByte 200] = none ∧
    decodeIntHw [natByte 33, natByte 200] = none := by
  decide

/-! ## 5. Execution: shared step over the canonical state.

    Register writes reuse `mergeRegNarrow` (32-bit zero-upper, 8/16-bit
    partial, 64-bit full) with `regSet`/`ripNach`; TEST writes no register;
    NOT preserves flags exactly; NEG installs the defined `negWf` snapshot.
    Length is checked data (`laengeOk` plus exact-length match). -/

/-- One register-row step; `none` is an explicit refusal. -/
def stepIntHw (d : IntHwDec) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    if d.laenge != 3 then none
    else
      let nach := ripNach s.rip d.laenge
      match d.op with
      | .andRR b dst src =>
        let r := andB b (s.register dst) (s.register src)
        some (schrittRegister s nach (intHwFlagsLogik b r) dst
          (mergeRegNarrow b (s.register dst) r))
      | .orRR b dst src =>
        let r := orB b (s.register dst) (s.register src)
        some (schrittRegister s nach (intHwFlagsLogik b r) dst
          (mergeRegNarrow b (s.register dst) r))
      | .testRR b lhs rhs =>
        let r := andB b (s.register lhs) (s.register rhs)
        some ({ s with rip := nach, flags := intHwFlagsLogik b r })
      | .notR b dst =>
        some (schrittRegister s nach s.flags dst
          (mergeRegNarrow b (s.register dst) (notB b (s.register dst))))
      | .negR b dst =>
        let w := negWf b (s.register dst)
        some (schrittRegister s nach w.2 dst
          (mergeRegNarrow b (s.register dst) w.1))

/-- AND steps through the shared value with the logic snapshot. -/
theorem stepIntHw_and (d : IntHwDec) (s : Zustand) (b : Breite)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = 3) (h : d.op = .andRR b dst src) :
    stepIntHw d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (intHwFlagsLogik b (andB b (s.register dst) (s.register src))) dst
        (mergeRegNarrow b (s.register dst)
          (andB b (s.register dst) (s.register src)))) := by
  unfold stepIntHw
  rw [hok, h, hlen]
  simp

/-- TEST writes no register: only flags and RIP move. -/
theorem stepIntHw_test (d : IntHwDec) (s : Zustand) (b : Breite)
    (lhs rhs : Register) (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = 3) (h : d.op = .testRR b lhs rhs) :
    stepIntHw d s =
      some ({ s with rip := ripNach s.rip d.laenge, flags := intHwFlagsLogik b (andB b (s.register lhs) (s.register rhs)) }) := by
  unfold stepIntHw
  rw [hok, h, hlen]
  simp

/-- NOT preserves flags exactly (no snapshot exists). -/
theorem stepIntHw_not_flags (d : IntHwDec) (s s' : Zustand) (b : Breite)
    (dst : Register) (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = 3) (h : d.op = .notR b dst)
    (hstep : stepIntHw d s = some s') :
    s'.flags = s.flags := by
  have e : stepIntHw d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (mergeRegNarrow b (s.register dst) (notB b (s.register dst)))) := by
    unfold stepIntHw
    rw [hok, h, hlen]
    simp
  rw [e] at hstep
  cases hstep
  rfl

/-- NEG installs the defined snapshot (satisfies `NegGueltig`). -/
theorem stepIntHw_neg_gueltig (d : IntHwDec) (s s' : Zustand) (b : Breite)
    (dst : Register) (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = 3) (h : d.op = .negR b dst)
    (hstep : stepIntHw d s = some s') :
    NegGueltig b (s.register dst) s'.flags := by
  have e : stepIntHw d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (negWf b (s.register dst)).2 dst
        (mergeRegNarrow b (s.register dst)
          (negWf b (s.register dst)).1)) := by
    unfold stepIntHw
    rw [hok, h, hlen]
    simp
  rw [e] at hstep
  cases hstep
  have hg := negWf_gueltig b (s.register dst)
  simp [negWf] at hg ⊢
  exact hg

/-- A wrong consumed length refuses on any state. -/
theorem stepIntHw_laenge_falsch (d : IntHwDec) (s : Zustand)
    (h : d.laenge ≠ 3) (hok : laengeOk d.laenge = true) :
    stepIntHw d s = none := by
  unfold stepIntHw
  rw [hok]
  simp [h]

/-- Register rows never touch memory (adapter for address lane 664). -/
theorem stepIntHw_speicher (d : IntHwDec) (s s' : Zustand)
    (h : stepIntHw d s = some s') : s'.speicher = s.speicher := by
  unfold stepIntHw at h
  by_cases hok : laengeOk d.laenge = true
  · rw [hok] at h
    by_cases hlen : d.laenge != 3
    · simp [hlen] at h
    · simp [hlen] at h
      cases dop : d.op with
      | andRR b dst src =>
        rw [dop] at h
        cases h
        rfl
      | orRR b dst src =>
        rw [dop] at h
        cases h
        rfl
      | testRR b lhs rhs =>
        rw [dop] at h
        cases h
        rfl
      | notR b dst =>
        rw [dop] at h
        cases h
        rfl
      | negR b dst =>
        rw [dop] at h
        cases h
        rfl
  · have h2 : laengeOk d.laenge = false := by
      cases hlen : laengeOk d.laenge with
      | true => simp [hlen] at hok
      | false => rfl
    rw [h2] at h
    cases h

/- CUTS:
    Skeleton only: codec/step/fetch/witnesses are open.
-/

#print axioms intHwWert_routen

end Gabbro.Grammatik.X86
