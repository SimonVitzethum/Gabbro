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
import Grammatik.X86.Byteschritt

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

/-- Decode after REX: opcode 33/9/133 via ModRM, 247 via group F7.
    `f7ok = false` (REX.R set) refuses the group opcode: the R bit would
    extend the digit into an unadmitted row. -/
def decodeIntHwNach (b : Breite) (rBit bBit : Nat) (f7ok : Bool) :
    List Byte → Option (IntHwDec × List Byte)
  | op :: rest =>
    if byteNat op == 33 then decodeIntHwModrm b 33 rBit bBit rest
    else if byteNat op == 9 then decodeIntHwModrm b 9 rBit bBit rest
    else if byteNat op == 133 then decodeIntHwModrm b 133 rBit bBit rest
    else if byteNat op == 247 then
      if f7ok then decodeIntHwF7 b bBit rest else none
    else none
  | [] => none

/-- Top-level decode: REX.W rows are b64, REX W=0 rows are b32;
    anything else (no REX, REX.X, 66 prefix, high-byte regs) refuses. -/
def decodeIntHw : List Byte → Option (IntHwDec × List Byte)
  | r :: rest =>
    match byteNat r with
    | 72 => decodeIntHwNach .b64 0 0 true rest
    | 73 => decodeIntHwNach .b64 0 1 true rest
    | 76 => decodeIntHwNach .b64 1 0 false rest
    | 77 => decodeIntHwNach .b64 1 1 false rest
    | 64 => decodeIntHwNach .b32 0 0 true rest
    | 65 => decodeIntHwNach .b32 0 1 true rest
    | 68 => decodeIntHwNach .b32 1 0 false rest
    | 69 => decodeIntHwNach .b32 1 1 false rest
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

/-! ## 6. Compact immediates: one int32, two encodings.

    ADD/SUB/CMP are b64-only (their AF is DEFINED via add64/sub64, and no
    narrow ADD/SUB flag snapshot exists); AND/OR/XOR admit b64+b32
    (width-correct `logikFlags`). The immediate is one int32 value with
    architectural sign extension; the encoder picks the compact imm8 form
    (0x83) exactly when the value fits in a signed byte, else imm32 (0x81).
    Group-1 digits: ADD /0, OR /1, AND /4, SUB /5, XOR /6, CMP /7; ADC /2
    and SBB /3 refuse (no row claimed). -/

/-- Immediate rows: arithmetic is b64-only, logic is b64/b32. -/
inductive IntHwImm where
  | addI (dst : Register) (imm : BitVec 32)
  | subI (dst : Register) (imm : BitVec 32)
  | cmpI (lhs : Register) (imm : BitVec 32)
  | andI (b : Breite) (dst : Register) (imm : BitVec 32)
  | orI (b : Breite) (dst : Register) (imm : BitVec 32)
  | xorI (b : Breite) (dst : Register) (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- Architectural sign extension of the int32 immediate to a word. -/
def immWort (imm : BitVec 32) : Wort :=
  sext .b32 (BitVec.ofNat 64 imm.toNat)

/-- The immediate fits in a signed byte: the compact form applies. -/
def immPasst8 (imm : BitVec 32) : Bool :=
  decide (-128 ≤ sVal .b32 (BitVec.ofNat 64 imm.toNat) ∧ sVal .b32 (BitVec.ofNat 64 imm.toNat) < 128)

/-- Sign extension of one immediate byte to int32 (0x83 form). -/
def imm8Erweitern (n : Nat) : BitVec 32 :=
  if n ≥ 128 then BitVec.ofNat 32 (0xFFFFFF00 + n) else BitVec.ofNat 32 n

/-- The imm8 form round-trips through sign extension on fitting values:
    -1 (0xFF) extends to 0xFFFFFFFF. -/
theorem probe_imm8_neg1 : imm8Erweitern 255 = 0xFFFFFFFF := by
  decide

/-- The imm8 form keeps small positives: 1 extends to 1. -/
theorem probe_imm8_pos1 : imm8Erweitern 1 = 1 := by
  decide

/-- Group-1 ModRM digit of an immediate row. -/
def immDigit : IntHwImm → Nat
  | .addI _ _ => 0
  | .orI _ _ _ => 1
  | .andI _ _ _ => 4
  | .subI _ _ => 5
  | .xorI _ _ _ => 6
  | .cmpI _ _ => 7

/-- Width gate: arithmetic rows need b64; logic rows take b64/b32.
    A 32-bit ADD/SUB/CMP immediate has no defined flag snapshot and is
    refused by the decoder (OPEN, not silently computed). -/
def immBreiteOk : IntHwImm → Breite → Bool
  | .addI _ _, .b64 => true
  | .subI _ _, .b64 => true
  | .cmpI _ _, .b64 => true
  | .andI b _ _, _ => b == .b64 || b == .b32
  | .orI b _ _, _ => b == .b64 || b == .b32
  | .xorI b _ _, _ => b == .b64 || b == .b32
  | _, _ => false

/-- Canonical encoding: compact imm8 (0x83, 4 bytes) exactly when the
    value fits, else imm32 (0x81, 7 bytes). REX.W for b64, W=0 for b32. -/
def encodeIntHwImm : IntHwImm → List Byte
  | .addI dst imm =>
    if immPasst8 imm then [rexByte 0 (regHigh dst), natByte 131, modrmReg 0 (regLow dst), natByte (imm.toNat % 256)]
    else [rexByte 0 (regHigh dst), natByte 129, modrmReg 0 (regLow dst)] ++ leBytes32 imm
  | .subI dst imm =>
    if immPasst8 imm then [rexByte 0 (regHigh dst), natByte 131, modrmReg 5 (regLow dst), natByte (imm.toNat % 256)]
    else [rexByte 0 (regHigh dst), natByte 129, modrmReg 5 (regLow dst)] ++ leBytes32 imm
  | .cmpI lhs imm =>
    if immPasst8 imm then [rexByte 0 (regHigh lhs), natByte 131, modrmReg 7 (regLow lhs), natByte (imm.toNat % 256)]
    else [rexByte 0 (regHigh lhs), natByte 129, modrmReg 7 (regLow lhs)] ++ leBytes32 imm
  | .andI b dst imm =>
    let rex := match b with | .b64 => rexByte 0 (regHigh dst) | .b32 => natByte (64 + regHigh dst) | _ => natByte 0
    if immPasst8 imm then [rex, natByte 131, modrmReg 4 (regLow dst), natByte (imm.toNat % 256)]
    else [rex, natByte 129, modrmReg 4 (regLow dst)] ++ leBytes32 imm
  | .orI b dst imm =>
    let rex := match b with | .b64 => rexByte 0 (regHigh dst) | .b32 => natByte (64 + regHigh dst) | _ => natByte 0
    if immPasst8 imm then [rex, natByte 131, modrmReg 1 (regLow dst), natByte (imm.toNat % 256)]
    else [rex, natByte 129, modrmReg 1 (regLow dst)] ++ leBytes32 imm
  | .xorI b dst imm =>
    let rex := match b with | .b64 => rexByte 0 (regHigh dst) | .b32 => natByte (64 + regHigh dst) | _ => natByte 0
    if immPasst8 imm then [rex, natByte 131, modrmReg 6 (regLow dst), natByte (imm.toNat % 256)]
    else [rex, natByte 129, modrmReg 6 (regLow dst)] ++ leBytes32 imm

/-- The compact choice fires exactly on fitting values (ADD row). -/
theorem kompakt_add_feuert (dst : Register) (imm : BitVec 32) :
    (encodeIntHwImm (.addI dst imm)).length = 4 ↔ immPasst8 imm = true := by
  unfold encodeIntHwImm
  by_cases h : immPasst8 imm = true
  · simp [h]
  · have hf : immPasst8 imm = false := by
      cases he : immPasst8 imm with
      | true => simp [he] at h
      | false => rfl
    simp [hf, length_leBytes32]

/-- Pinned compact bytes: `add rax, 1` is REX.W, 83, C0, 01. -/
theorem pin_add_kompakt :
    encodeIntHwImm (.addI .rax 1) =
      [natByte 72, natByte 131, natByte 192, natByte 1] := by
  decide

/-- Pinned wide bytes: `add rax, 256` needs the imm32 form. -/
theorem pin_add_weit :
    encodeIntHwImm (.addI .rax 256) =
      [natByte 72, natByte 129, natByte 192,
       natByte 0, natByte 1, natByte 0, natByte 0] := by
  decide

/-- Pinned compact bytes: `cmp rax, -1` signs through one byte. -/
theorem pin_cmp_neg1 :
    encodeIntHwImm (.cmpI .rax 0xFFFFFFFF) =
      [natByte 72, natByte 131, natByte 248, natByte 255] := by
  decide

/-! ## 7. Immediate decoder: both compact and wide forms.

    Parses REX (W selects b64/b32), opcode (129 wide / 131 compact),
    mod=3 ModRM digit and the immediate bytes. ADC /2 and SBB /3 refuse;
    32-bit ADD/SUB/CMP refuse (no narrow arithmetic flag snapshot);
    b8/b16 logic rows refuse (no codec row). -/

/-- Decoded immediate row with consumed length (7 wide, 4 compact). -/
structure IntHwImmDec where
  op : IntHwImm
  laenge : Nat
  deriving DecidableEq, Repr

/-- Expected length of an immediate row: 4 exactly when compact fires. -/
def immDecLaenge : IntHwImm → Nat
  | .addI _ imm => if immPasst8 imm then 4 else 7
  | .subI _ imm => if immPasst8 imm then 4 else 7
  | .cmpI _ imm => if immPasst8 imm then 4 else 7
  | .andI _ _ imm => if immPasst8 imm then 4 else 7
  | .orI _ _ imm => if immPasst8 imm then 4 else 7
  | .xorI _ _ imm => if immPasst8 imm then 4 else 7

/-- Decode one group-1 ModRM byte with its immediate tail at width `b`.
    `wide = true` reads imm32 (opcode 129), else one sign-extended byte
    (opcode 131). Length 7 wide, 4 compact. -/
def decodeIntHwImmModrm (b : Breite) (wide : Bool) (bBit : Nat) :
    List Byte → Option (IntHwImmDec × List Byte)
  | m :: rest =>
    let digit := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeReg (bBit * 8 + rm) with
      | some rd =>
        match digit, b, wide with
        | 0, .b64, true =>
          match parseLe32 rest with
          | some (imm, rest') => some (⟨.addI rd imm, 7⟩, rest')
          | none => none
        | 0, .b64, false =>
          match rest with
          | i :: rest' => some (⟨.addI rd (imm8Erweitern (byteNat i)), 4⟩, rest')
          | [] => none
        | 5, .b64, true =>
          match parseLe32 rest with
          | some (imm, rest') => some (⟨.subI rd imm, 7⟩, rest')
          | none => none
        | 5, .b64, false =>
          match rest with
          | i :: rest' => some (⟨.subI rd (imm8Erweitern (byteNat i)), 4⟩, rest')
          | [] => none
        | 7, .b64, true =>
          match parseLe32 rest with
          | some (imm, rest') => some (⟨.cmpI rd imm, 7⟩, rest')
          | none => none
        | 7, .b64, false =>
          match rest with
          | i :: rest' => some (⟨.cmpI rd (imm8Erweitern (byteNat i)), 4⟩, rest')
          | [] => none
        | 4, _, true =>
          match parseLe32 rest with
          | some (imm, rest') => some (⟨.andI b rd imm, 7⟩, rest')
          | none => none
        | 4, _, false =>
          match rest with
          | i :: rest' => some (⟨.andI b rd (imm8Erweitern (byteNat i)), 4⟩, rest')
          | [] => none
        | 1, _, true =>
          match parseLe32 rest with
          | some (imm, rest') => some (⟨.orI b rd imm, 7⟩, rest')
          | none => none
        | 1, _, false =>
          match rest with
          | i :: rest' => some (⟨.orI b rd (imm8Erweitern (byteNat i)), 4⟩, rest')
          | [] => none
        | 6, _, true =>
          match parseLe32 rest with
          | some (imm, rest') => some (⟨.xorI b rd imm, 7⟩, rest')
          | none => none
        | 6, _, false =>
          match rest with
          | i :: rest' => some (⟨.xorI b rd (imm8Erweitern (byteNat i)), 4⟩, rest')
          | [] => none
        | _, _, _ => none
      | none => none
    else none
  | [] => none

/-- Decode after REX at width `b`: 129 is the wide form, 131 compact. -/
def decodeIntHwImmNach (b : Breite) (bBit : Nat) :
    List Byte → Option (IntHwImmDec × List Byte)
  | op :: rest =>
    if byteNat op == 129 then decodeIntHwImmModrm b true bBit rest
    else if byteNat op == 131 then decodeIntHwImmModrm b false bBit rest
    else none
  | [] => none

/-- Top-level immediate decode. REX.W rows decode at b64 with the full
    six-op set; REX W=0 rows decode logic rows at b32 only (digits 0/5/7
    refuse there: no 32-bit arithmetic flag snapshot). REX.R rows refuse:
    the R bit would extend the group digit. The decoder also refuses
    b8/b16 logic digits by width mismatch at step time. -/
def decodeIntHwImm : List Byte → Option (IntHwImmDec × List Byte)
  | r :: rest =>
    match byteNat r with
    | 72 => decodeIntHwImmNach .b64 0 rest
    | 73 => decodeIntHwImmNach .b64 1 rest
    | 64 => decodeIntHwImmNach .b32 0 rest
    | 65 => decodeIntHwImmNach .b32 1 rest
    | _ => none
  | [] => none

/-- Guard: a decoded logic row at b8/b16 is never admitted to the step. -/
def immDecBreiteOk : IntHwImm → Bool
  | .addI _ _ => true
  | .subI _ _ => true
  | .cmpI _ _ => true
  | .andI b _ _ => b == .b64 || b == .b32
  | .orI b _ _ => b == .b64 || b == .b32
  | .xorI b _ _ => b == .b64 || b == .b32

/-- Pinned decode: compact `add rax, 1` (4 bytes). -/
theorem pin_imm_add_kompakt_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 192, natByte 1] =
      some ((⟨.addI .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned decode: wide `add rax, 256` (7 bytes). -/
theorem pin_imm_add_weit_dekode :
    decodeIntHwImm [natByte 72, natByte 129, natByte 192,
      natByte 0, natByte 1, natByte 0, natByte 0] =
      some ((⟨.addI .rax 256, 7⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned decode: compact `cmp rax, -1` (sign extension at decode). -/
theorem pin_imm_cmp_neg1_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 248, natByte 255] =
      some ((⟨.cmpI .rax 0xFFFFFFFF, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned decode: 32-bit compact `and eax, 1` (zero-upper row). -/
theorem pin_imm_and32_dekode :
    decodeIntHwImm [natByte 64, natByte 131, natByte 224, natByte 1] =
      some ((⟨.andI .b32 .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Planted immediate refusals: ADC digit /2, 32-bit ADD digit /0,
    REX.R row, truncated wide tail, truncated compact tail, no REX. -/
theorem sonde_imm_verweigert :
    decodeIntHwImm [natByte 72, natByte 131, natByte 208, natByte 1] = none ∧
    decodeIntHwImm [natByte 64, natByte 131, natByte 192, natByte 1] = none ∧
    decodeIntHwImm [natByte 76, natByte 131, natByte 192, natByte 1] = none ∧
    decodeIntHwImm [natByte 72, natByte 129, natByte 192, natByte 1] = none ∧
    decodeIntHwImm [natByte 72, natByte 131, natByte 192] = none ∧
    decodeIntHwImm [natByte 129, natByte 192, natByte 1, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-! ## 8. Immediate execution: defined flags, no silent narrowing.

    ADD/SUB reuse add64/sub64 (AF DEFINED via afAdd/afSub); CMP writes no
    register; b64 logic reuses and64/or64/xor64; b32 logic reuses the
    width-correct `logikFlags` with the zero-upper merge. b8/b16 logic
    steps refuse (`immDecBreiteOk`); 32-bit arithmetic never reaches the
    step (refused at decode). -/

/-- One immediate step; `none` is an explicit refusal. -/
def stepIntHwImm (d : IntHwImmDec) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    if d.laenge != immDecLaenge d.op then none
    else if !immDecBreiteOk d.op then none
    else
      let nach := ripNach s.rip d.laenge
      match d.op with
      | .addI dst imm =>
        let r := add64 (s.register dst) (immWort imm)
        some (schrittRegister s nach r.2 dst r.1)
      | .subI dst imm =>
        let r := sub64 (s.register dst) (immWort imm)
        some (schrittRegister s nach r.2 dst r.1)
      | .cmpI lhs imm =>
        let r := sub64 (s.register lhs) (immWort imm)
        some ({ s with rip := nach, flags := r.2 })
      | .andI b dst imm =>
        let r := andB b (s.register dst) (immWort imm)
        some (schrittRegister s nach (intHwFlagsLogik b r) dst
          (mergeRegNarrow b (s.register dst) r))
      | .orI b dst imm =>
        let r := orB b (s.register dst) (immWort imm)
        some (schrittRegister s nach (intHwFlagsLogik b r) dst
          (mergeRegNarrow b (s.register dst) r))
      | .xorI b dst imm =>
        let r := xorB b (s.register dst) (immWort imm)
        some (schrittRegister s nach (intHwFlagsLogik b r) dst
          (mergeRegNarrow b (s.register dst) r))

/-- ADD-imm defines AF (the nibble carry, not none). -/
theorem stepImm_add_af (d : IntHwImmDec) (s s' : Zustand)
    (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .addI dst imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.flags.af = some (afAdd (s.register dst) (immWort imm)) := by
  have e : stepIntHwImm d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (add64 (s.register dst) (immWort imm)).2 dst
        (add64 (s.register dst) (immWort imm)).1) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  exact add64_af _ _

/-- CMP-imm writes no register at all. -/
theorem stepImm_cmp_reg (d : IntHwImmDec) (s s' : Zustand)
    (lhs : Register) (imm : BitVec 32) (q : Register)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .cmpI lhs imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.register q = s.register q := by
  have e : stepIntHwImm d s =
      some ({ s with rip := ripNach s.rip d.laenge, flags := (sub64 (s.register lhs) (immWort imm)).2 }) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  rfl

/-- b64 AND-imm flags agree with the register-row snapshot. -/
theorem stepImm_and64_eq_reg (d : IntHwImmDec) (s s' : Zustand)
    (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .andI .b64 dst imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.flags = (and64 (s.register dst) (immWort imm)).2 ∧
    s'.register dst = andB .b64 (s.register dst) (immWort imm) := by
  have e : stepIntHwImm d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (intHwFlagsLogik .b64 (andB .b64 (s.register dst) (immWort imm))) dst
        (mergeRegNarrow .b64 (s.register dst)
          (andB .b64 (s.register dst) (immWort imm)))) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  constructor
  · rw [schrittRegister_flags]
    simp [intHwFlagsLogik, logikFlags, negB_b64, andB_b64, and64]
  · have hr : ∀ (f : Flags) (v : Wort),
        (schrittRegister s (ripNach s.rip d.laenge) f dst v).register dst
          = v :=
      fun f v => regSet_gleich s.register dst v
    rw [hr, mergeRegNarrow_b64, andB_b64]

/-- Immediate steps never touch memory (adapter for address lane 664). -/
theorem stepImm_speicher (d : IntHwImmDec) (s s' : Zustand)
    (h : stepIntHwImm d s = some s') : s'.speicher = s.speicher := by
  unfold stepIntHwImm at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases dop : d.op with
        | addI dst imm =>
          rw [dop] at h
          cases h
          rfl
        | subI dst imm =>
          rw [dop] at h
          cases h
          rfl
        | cmpI lhs imm =>
          rw [dop] at h
          cases h
          rfl
        | andI b dst imm =>
          rw [dop] at h
          cases h
          rfl
        | orI b dst imm =>
          rw [dop] at h
          cases h
          rfl
        | xorI b dst imm =>
          rw [dop] at h
          cases h
          rfl

/-! ## 9. Fetched-byte paths from actual executable memory.

    Fetch mirrors `fetchDekodiert`: decode the ACTUAL fetched window with
    the independent decoder, then check consumed-length consistency,
    the length guard and execute permission of the consumed prefix.
    A forged `IntHwDec` can never inject an instruction. -/

/-- Fetch and decode a register row from actual memory. -/
def fetchIntHw (s : Zustand) : Option (IntHwDec × List Byte) :=
  match decodeIntHw (geholt s) with
  | none => none
  | some p =>
    if p.1.laenge + p.2.length == (geholt s).length &&
        laengeOk p.1.laenge && ausfuehrbarN s.speicher s.rip p.1.laenge
    then some p
    else none

/-- Fetch and decode an immediate row from actual memory. -/
def fetchIntHwImm (s : Zustand) : Option (IntHwImmDec × List Byte) :=
  match decodeIntHwImm (geholt s) with
  | none => none
  | some p =>
    if p.1.laenge + p.2.length == (geholt s).length &&
        laengeOk p.1.laenge && ausfuehrbarN s.speicher s.rip p.1.laenge
    then some p
    else none

/-- One register-row byte step from actual memory. -/
def intHwByteschritt (s : Zustand) : ByteAusgang :=
  match fetchIntHw s with
  | none => .verweigert
  | some (d, _) =>
    match stepIntHw d s with
    | none => .verweigert
    | some s' => .weiter s'

/-- One immediate byte step from actual memory. -/
def intHwImmByteschritt (s : Zustand) : ByteAusgang :=
  match fetchIntHwImm s with
  | none => .verweigert
  | some (d, _) =>
    match stepIntHwImm d s with
    | none => .verweigert
    | some s' => .weiter s'

/-- A successful register fetch decodes to the admitted instruction:
    length equation, length guard and execute permission all hold. -/
theorem fetchIntHw_erfolg (s : Zustand) (d : IntHwDec) (rest : List Byte)
    (h : fetchIntHw s = some (d, rest)) :
    decodeIntHw (geholt s) = some (d, rest) ∧
      d.laenge + rest.length = (geholt s).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN s.speicher s.rip d.laenge = true := by
  have e : fetchIntHw s =
      match decodeIntHw (geholt s) with
      | none => (none : Option (IntHwDec × List Byte))
      | some p =>
        if p.1.laenge + p.2.length == (geholt s).length &&
            laengeOk p.1.laenge &&
            ausfuehrbarN s.speicher s.rip p.1.laenge
        then some p else none := rfl
  rw [e] at h
  cases hdec : decodeIntHw (geholt s) with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : (p.1.laenge + p.2.length == (geholt s).length &&
        laengeOk p.1.laenge &&
        ausfuehrbarN s.speicher s.rip p.1.laenge) = true
    · simp only [hz, if_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨⟨hsum, hlen⟩, hexe⟩ := hz
      have hsum' : d.laenge + rest.length = (geholt s).length := hsum
      exact ⟨rfl, hsum', hlen, hexe⟩
    · simp [hz] at h

/-- A successful immediate fetch decodes to the admitted instruction. -/
theorem fetchIntHwImm_erfolg (s : Zustand) (d : IntHwImmDec)
    (rest : List Byte) (h : fetchIntHwImm s = some (d, rest)) :
    decodeIntHwImm (geholt s) = some (d, rest) ∧
      d.laenge + rest.length = (geholt s).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN s.speicher s.rip d.laenge = true := by
  have e : fetchIntHwImm s =
      match decodeIntHwImm (geholt s) with
      | none => (none : Option (IntHwImmDec × List Byte))
      | some p =>
        if p.1.laenge + p.2.length == (geholt s).length &&
            laengeOk p.1.laenge &&
            ausfuehrbarN s.speicher s.rip p.1.laenge
        then some p else none := rfl
  rw [e] at h
  cases hdec : decodeIntHwImm (geholt s) with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : (p.1.laenge + p.2.length == (geholt s).length &&
        laengeOk p.1.laenge &&
        ausfuehrbarN s.speicher s.rip p.1.laenge) = true
    · simp only [hz, if_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨⟨hsum, hlen⟩, hexe⟩ := hz
      have hsum' : d.laenge + rest.length = (geholt s).length := hsum
      exact ⟨rfl, hsum', hlen, hexe⟩
    · simp [hz] at h

/-! ## 10. Branch/validator adapters: TEST/CMP feed `bedingung`.

    TEST sets ZF exactly when the shared AND value is zero; CMP sets the
    signed-less condition exactly from the shared SUB value. Consumers
    (branch lane, validator) read flags only through these equations. -/

/-- Word equality test reads the decidable equality (bridge for branch
    consumers: `==` and `decide` agree on words). -/
theorem wort_beq_decide (w : Wort) : (w == 0) = decide (w = 0) := by
  cases h : decide (w = 0) with
  | true =>
    have heq : w = 0 := of_decide_eq_true h
    simp [heq]
  | false =>
    have hne : w ≠ 0 := of_decide_eq_false h
    exact beq_eq_false_iff_ne.mpr hne

/-- TEST zero-flag reads the shared AND value (adapter for branch lane). -/
theorem inthw_test_zf (b : Breite) (x y : Wort) :
    bedingung .e (intHwFlagsLogik b (andB b x y)) = decide (andB b x y = 0) := by
  simp only [bedingung, intHwFlagsLogik, logikFlags, zfTest]
  exact wort_beq_decide _

/-- CMP signed-less reads the shared SUB value (adapter for branch lane). -/
theorem inthw_cmp_l (x y : Wort) :
    bedingung .l (sub64 x y).2 = ((sfTest (x - y) != ofSub (sfTest x) (sfTest y) (sfTest (x - y)))) := by
  simp [bedingung, sub64]

/-- CMP equal reads ZF of the shared SUB value. -/
theorem inthw_cmp_e (x y : Wort) :
    bedingung .e (sub64 x y).2 = decide (x - y = 0) := by
  simp only [bedingung, sub64, zfTest]
  exact wort_beq_decide _

/- CUTS:
    Skeleton only: codec/step/fetch/witnesses are open.
-/

#print axioms intHwWert_routen

end Gabbro.Grammatik.X86
