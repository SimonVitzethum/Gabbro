/-
  File:      Grammatik/X86/Wort.lean
  Subject:   Integer arithmetic and architectural flags over the canonical words.

  Lane 270 (wave A): helpers over the REAL canonical `Wort` (BitVec 64) from
  `Grammatik/X86/Typen.lean` -- low-width modular arithmetic, sign/zero
  extension, 64-bit ADD/SUB/XOR results with defined CF/OF/SF/ZF/PF/AF flags,
  and the 16 `Bedingung` tests. No independent register, instruction or state
  types are created here. ADD/SUB AF is defined (`some`); XOR AF is `none`
  (architecturally undefined, and `none` means undefined, never false).
  Parity is EVEN parity of the low byte. Signed overflow (OF) is kept distinct
  from unsigned carry (CF) by construction: CF is computed from `toNat`,
  OF from the sign bits.

  No source correspondence is claimed here; the bridge (lane 277) must still
  preserve source range and fault semantics.
-/
import Grammatik.X86.Typen

namespace Gabbro.Grammatik.X86

/-- Width mask: exactly the low `b.bits` bits set. -/
def maske : Breite → Wort
  | .b8 => 0xFF
  | .b16 => 0xFFFF
  | .b32 => 0xFFFFFFFF
  | .b64 => 0xFFFFFFFFFFFFFFFF

/-- Truncation to a pilot width: high bits cleared, low bits kept. -/
def trunc (b : Breite) (w : Wort) : Wort := w &&& maske b

/-! ## 1. Low-width modular arithmetic (pilot `Breite` widths only).

    Every operation truncates to the named width, so results are modular at
    that width. Helpers take a `Breite` (four architectural widths); there is
    no accidental zero-width or arbitrary-`n` word anywhere in this file. -/

/-- Modular addition at width `b`. -/
def addB (b : Breite) (x y : Wort) : Wort := trunc b (x + y)

/-- Modular subtraction at width `b`. -/
def subB (b : Breite) (x y : Wort) : Wort := trunc b (x - y)

/-- Bitwise xor at width `b` (truncated; xor cannot carry, but the mask keeps
    the width contract uniform). -/
def xorB (b : Breite) (x y : Wort) : Wort := trunc b (x ^^^ y)

/-- Zero extension is truncation: the value of the low `b.bits` bits as a word. -/
def zext (b : Breite) (w : Wort) : Wort := trunc b w

/-- The sign bit position of width `b` (7, 15, 31, 63). -/
def signBit : Breite → Nat
  | .b8 => 7
  | .b16 => 15
  | .b32 => 31
  | .b64 => 63

/-- Sign extension of the low `b.bits` bits into a full word: the upper bits
    repeat the sign bit. Computed from `toNat`, so no decoder API is needed. -/
def sext (b : Breite) (w : Wort) : Wort :=
  let lo := (trunc b w).toNat
  if lo.testBit (signBit b) then
    BitVec.ofNat 64 (lo + (2 ^ 64 - 2 ^ b.bits))
  else
    BitVec.ofNat 64 lo

/-! ## 2. Sign, zero and parity tests (computable `Bool` helpers).

    All tests read the canonical word through `toNat`/`testBit`, so no
    decoder API is needed. `parityEven` is EVEN parity of the low byte,
    matching the architectural meaning of PF. -/

/-- Sign bit of the truncated value at width `b`. -/
def negB (b : Breite) (w : Wort) : Bool :=
  (trunc b w).toNat.testBit (signBit b)

/-- 64-bit sign test: the top bit of the word. -/
def sfTest (w : Wort) : Bool := w.toNat.testBit 63

/-- 64-bit zero test. -/
def zfTest (w : Wort) : Bool := w == 0

/-- One bit of a natural number as `0`/`1`. -/
def bitAt (n i : Nat) : Nat := if n.testBit i then 1 else 0

/-- Population count of the low byte. -/
def popCount8 (n : Nat) : Nat :=
  bitAt n 0 + bitAt n 1 + bitAt n 2 + bitAt n 3 +
  bitAt n 4 + bitAt n 5 + bitAt n 6 + bitAt n 7

/-- Even parity of the low byte (architectural PF meaning). -/
def parityEven (w : Wort) : Bool := popCount8 (w.toNat % 256) % 2 == 0

/-! ## 3. Carry, borrow, signed overflow and auxiliary carry.

    CF is computed from `toNat` (unsigned range), OF purely from the three
    sign bits, so the two can never be confused by construction. AF is the
    carry out of bit 3 (nibble boundary), as `some` for ADD/SUB. -/

/-- Unsigned carry out of bit 63 for `x + y`. -/
def cfAdd (x y : Wort) : Bool := decide (2 ^ 64 ≤ x.toNat + y.toNat)

/-- Borrow for `x - y` (CF set means a borrow occurred). -/
def cfSub (x y : Wort) : Bool := decide (x.toNat < y.toNat)

/-- Signed overflow for addition from the operand and result signs:
    equal operand signs with a differing result sign. -/
def ofAdd (sx sy sr : Bool) : Bool := (sx == sy) && (sr != sx)

/-- Signed overflow for subtraction from the operand and result signs:
    differing operand signs with a result sign differing from the lhs. -/
def ofSub (sx sy sr : Bool) : Bool := (sx != sy) && (sr != sx)

/-- Auxiliary carry out of bit 3 for addition (nibble boundary). -/
def afAdd (x y : Wort) : Bool := decide (16 ≤ x.toNat % 16 + y.toNat % 16)

/-- Auxiliary borrow out of bit 3 for subtraction (nibble boundary). -/
def afSub (x y : Wort) : Bool := decide (x.toNat % 16 < y.toNat % 16)

/-! ## 4. The three exported 64-bit operations.

    Each returns the modular result word together with the architectural
    flags. ADD/SUB define AF (`some`); XOR leaves AF undefined (`none`,
    which means undefined, never false). XOR clears CF and OF. -/

/-- 64-bit ADD with architectural flags; AF is defined. -/
def add64 (x y : Wort) : Wort × Flags :=
  let r := x + y
  (r, Flags.mk (cfAdd x y) (parityEven r) (some (afAdd x y))
    (zfTest r) (sfTest r) (ofAdd (sfTest x) (sfTest y) (sfTest r)))

/-- 64-bit SUB with architectural flags; CF is the borrow; AF is defined. -/
def sub64 (x y : Wort) : Wort × Flags :=
  let r := x - y
  (r, Flags.mk (cfSub x y) (parityEven r) (some (afSub x y))
    (zfTest r) (sfTest r) (ofSub (sfTest x) (sfTest y) (sfTest r)))

/-- 64-bit XOR with architectural flags; CF/OF cleared, AF undefined. -/
def xor64 (x y : Wort) : Wort × Flags :=
  let r := x ^^^ y
  (r, Flags.mk false (parityEven r) none
    (zfTest r) (sfTest r) false)

/-! ## 5. The 16 architectural condition tests.

    Standard Intel mapping: `b`/`ae` read CF, `e`/`ne` read ZF, `be`/`a`
    combine them, `s`/`ns` read SF, `p`/`np` read PF, `o`/`no` read OF,
    and the signed comparisons combine SF, OF and ZF. -/

/-- The 16 `Bedingung` tests over a flag snapshot. -/
def bedingung : Bedingung → Flags → Bool
  | .o, f => f.of
  | .no, f => !f.of
  | .b, f => f.cf
  | .ae, f => !f.cf
  | .e, f => f.zf
  | .ne, f => !f.zf
  | .be, f => (f.cf || f.zf)
  | .a, f => (!f.cf && !f.zf)
  | .s, f => f.sf
  | .ns, f => !f.sf
  | .p, f => f.pf
  | .np, f => !f.pf
  | .l, f => (f.sf != f.of)
  | .ge, f => (f.sf == f.of)
  | .le, f => (f.zf || (f.sf != f.of))
  | .g, f => (!f.zf && (f.sf == f.of))

/-! ## 6. Generic lemmas: result values and flag meanings.

    Each lemma is proved from the definitions above (plus the toolchain's
    `BitVec.toNat_*` facts); every premise is used. The `decide` tactic
    appears only in §7, for finite concrete probes. -/

/-- The ADD result is the modular sum. -/
theorem add64_wert (x y : Wort) :
    (add64 x y).1.toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  simp [add64, BitVec.toNat_add]

/-- ADD carry means the unsigned sum leaves 64 bits. -/
theorem add64_cf (x y : Wort) :
    (add64 x y).2.cf = true ↔ 2 ^ 64 ≤ x.toNat + y.toNat := by
  simp [add64, cfAdd]

/-- ADD overflow is decided by the three sign bits alone. -/
theorem add64_of (x y : Wort) :
    (add64 x y).2.of =
      ((sfTest x == sfTest y) && (sfTest (x + y) != sfTest x)) := by
  simp [add64, ofAdd]

/-- The SUB result is the modular difference. -/
theorem sub64_wert (x y : Wort) :
    (sub64 x y).1.toNat = ((2 ^ 64 - y.toNat) + x.toNat) % 2 ^ 64 := by
  simp [sub64, BitVec.toNat_sub]

/-- SUB carry means a borrow: the lhs is unsigned-smaller. -/
theorem sub64_cf (x y : Wort) :
    (sub64 x y).2.cf = true ↔ x.toNat < y.toNat := by
  simp [sub64, cfSub]

/-- SUB overflow is decided by the three sign bits alone. -/
theorem sub64_of (x y : Wort) :
    (sub64 x y).2.of =
      ((sfTest x != sfTest y) && (sfTest (x - y) != sfTest x)) := by
  simp [sub64, ofSub]

/-- The XOR result is the bitwise xor (no carry exists). -/
theorem xor64_wert (x y : Wort) :
    (xor64 x y).1.toNat = x.toNat ^^^ y.toNat := by
  simp [xor64, BitVec.toNat_xor]

/-- XOR always clears CF. -/
theorem xor64_cf (x y : Wort) : (xor64 x y).2.cf = false := by
  simp [xor64]

/-- XOR always clears OF. -/
theorem xor64_of (x y : Wort) : (xor64 x y).2.of = false := by
  simp [xor64]

/-- XOR leaves AF undefined (`none`, never false). -/
theorem xor64_af (x y : Wort) : (xor64 x y).2.af = none := by
  simp [xor64]

/-- ADD sign reads the result top bit. -/
theorem add64_sf (x y : Wort) : (add64 x y).2.sf = sfTest (x + y) := by
  simp [add64]

/-- ADD zero reads the result word. -/
theorem add64_zf (x y : Wort) : (add64 x y).2.zf = zfTest (x + y) := by
  simp [add64]

/-- ADD parity reads the result low byte. -/
theorem add64_pf (x y : Wort) : (add64 x y).2.pf = parityEven (x + y) := by
  simp [add64]

/-- ADD defines AF (the nibble carry). -/
theorem add64_af (x y : Wort) : (add64 x y).2.af = some (afAdd x y) := by
  simp [add64]

/-- SUB sign reads the result top bit. -/
theorem sub64_sf (x y : Wort) : (sub64 x y).2.sf = sfTest (x - y) := by
  simp [sub64]

/-- SUB zero reads the result word. -/
theorem sub64_zf (x y : Wort) : (sub64 x y).2.zf = zfTest (x - y) := by
  simp [sub64]

/-- SUB parity reads the result low byte. -/
theorem sub64_pf (x y : Wort) : (sub64 x y).2.pf = parityEven (x - y) := by
  simp [sub64]

/-- SUB defines AF (the nibble borrow). -/
theorem sub64_af (x y : Wort) : (sub64 x y).2.af = some (afSub x y) := by
  simp [sub64]

/-- XOR sign reads the result top bit. -/
theorem xor64_sf (x y : Wort) : (xor64 x y).2.sf = sfTest (x ^^^ y) := by
  simp [xor64]

/-- XOR zero reads the result word. -/
theorem xor64_zf (x y : Wort) : (xor64 x y).2.zf = zfTest (x ^^^ y) := by
  simp [xor64]

/-- XOR parity reads the result low byte. -/
theorem xor64_pf (x y : Wort) : (xor64 x y).2.pf = parityEven (x ^^^ y) := by
  simp [xor64]

/-! ## 7. The condition table as equations.

    Direct readings by `rfl`; lane 272 rewrites jumps with these. -/

theorem bedingung_o (f : Flags) : bedingung .o f = f.of := by rfl
theorem bedingung_no (f : Flags) : bedingung .no f = !f.of := by rfl
theorem bedingung_b (f : Flags) : bedingung .b f = f.cf := by rfl
theorem bedingung_ae (f : Flags) : bedingung .ae f = !f.cf := by rfl
theorem bedingung_e (f : Flags) : bedingung .e f = f.zf := by rfl
theorem bedingung_ne (f : Flags) : bedingung .ne f = !f.zf := by rfl
theorem bedingung_be (f : Flags) : bedingung .be f = (f.cf || f.zf) := by rfl
theorem bedingung_a (f : Flags) : bedingung .a f = (!f.cf && !f.zf) := by rfl
theorem bedingung_s (f : Flags) : bedingung .s f = f.sf := by rfl
theorem bedingung_ns (f : Flags) : bedingung .ns f = !f.sf := by rfl
theorem bedingung_p (f : Flags) : bedingung .p f = f.pf := by rfl
theorem bedingung_np (f : Flags) : bedingung .np f = !f.pf := by rfl
theorem bedingung_l (f : Flags) : bedingung .l f = (f.sf != f.of) := by rfl
theorem bedingung_ge (f : Flags) : bedingung .ge f = (f.sf == f.of) := by rfl
theorem bedingung_le (f : Flags) : bedingung .le f = (f.zf || (f.sf != f.of)) := by rfl
theorem bedingung_g (f : Flags) : bedingung .g f = (!f.zf && (f.sf == f.of)) := by rfl

/-! ## 8. Narrow widths: masks and truncation.

    `trunc`/`addB`/`subB`/`xorB`/`zext` never see an accidental zero-width
    word: every helper takes a `Breite` (four architectural widths), and the
    mask value pins the width. -/

/-- Each width mask holds exactly the low `b.bits` bits. -/
theorem maske_nat (b : Breite) : (maske b).toNat = 2 ^ b.bits - 1 := by
  cases b <;> decide

/-- The 64-bit mask is the all-ones word. -/
theorem maske_b64 : maske .b64 = BitVec.allOnes 64 := by
  decide

/-- Truncation at full width is the identity. -/
theorem trunc_b64 (w : Wort) : trunc .b64 w = w := by
  simp only [trunc, maske_b64, BitVec.and_allOnes]

/-- Full-width modular arithmetic is plain machine arithmetic. -/
theorem addB_b64 (x y : Wort) : addB .b64 x y = x + y := by
  simp [addB, trunc_b64]

/-- Full-width modular subtraction is plain machine subtraction. -/
theorem subB_b64 (x y : Wort) : subB .b64 x y = x - y := by
  simp [subB, trunc_b64]

/-- Full-width xor is plain machine xor. -/
theorem xorB_b64 (x y : Wort) : xorB .b64 x y = x ^^^ y := by
  simp [xorB, trunc_b64]

/-- Zero extension at full width is the identity. -/
theorem zext_b64 (w : Wort) : zext .b64 w = w := by
  simp [zext, trunc_b64]

/-! ## 9. Concrete boundary probes.

    Finite concrete examples only (`decide`): unsigned carry without
    signed overflow, signed overflow without carry, the signed extremes,
    zero, even/odd parity, sign extension and a borrow. -/

/-- `0xFF..FF + 1`: carry out, no signed overflow, result zero. -/
theorem probe_add_carry_no_overflow :
    (add64 0xFFFFFFFFFFFFFFFF 1).1 = 0 ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.cf = true ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.of = false := by
  decide

/-- `0x7FF..FF + 1`: signed overflow into the sign bit, no carry. -/
theorem probe_add_overflow_no_carry :
    (add64 0x7FFFFFFFFFFFFFFF 1).1 = 0x8000000000000000 ∧
    (add64 0x7FFFFFFFFFFFFFFF 1).2.cf = false ∧
    (add64 0x7FFFFFFFFFFFFFFF 1).2.of = true := by
  decide

/-- `42 - 42`: zero result, ZF set, no borrow. -/
theorem probe_sub_zero :
    (sub64 42 42).1 = 0 ∧ (sub64 42 42).2.zf = true ∧
    (sub64 42 42).2.cf = false := by
  decide

/-- `0 - 1`: borrow out, all-ones result. -/
theorem probe_sub_borrow :
    (sub64 0 1).1 = 0xFFFFFFFFFFFFFFFF ∧
    (sub64 0 1).2.cf = true := by
  decide

/-- Parity: zero/two/eight low bits are even, one low bit is odd. -/
theorem probe_parity :
    parityEven 0 = true ∧ parityEven 0x03 = true ∧
    parityEven 0x01 = false ∧ parityEven 0xFF = true := by
  decide

/-- Sign extension: `0xFF` fills, `0x7F` keeps, 16-bit `0x8000` fills. -/
theorem probe_sext :
    sext .b8 0xFF = 0xFFFFFFFFFFFFFFFF ∧ sext .b8 0x7F = 0x7F ∧
    sext .b16 0x8000 = 0xFFFFFFFFFFFF8000 := by
  decide

/-- `x ^^^ x`: zero result, ZF set, AF stays undefined. -/
theorem probe_xor_self :
    (xor64 0xDEADBEEF 0xDEADBEEF).1 = 0 ∧
    (xor64 0xDEADBEEF 0xDEADBEEF).2.zf = true ∧
    (xor64 0xDEADBEEF 0xDEADBEEF).2.af = none := by
  decide

/-- Condition probe: after `1 - 2`, signed less holds, greater does not,
    and the unsigned borrow makes `b` hold and `a` fail. -/
theorem probe_bedingung_lt :
    let f := (sub64 1 2).2
    bedingung .l f = true ∧ bedingung .g f = false ∧
    bedingung .b f = true ∧ bedingung .a f = false := by
  decide

/- CUTS:
   No instruction execution, decoder, encoding, memory/state transition,
   TSO bridge, source correspondence, ABI/loader theorem, cost transfer or
   final-image acceptance is proved here. Flag helpers cover only the three
   64-bit operations above; narrow widths have modular arithmetic, masks,
   sign/zero extension and tests, but no narrow flag snapshots. Only AF is
   modelled as possibly undefined (`none` means undefined, never false);
   all other flags of these three operations are defined. The nibble AF
   model, the even-parity reading of PF and the 16-entry condition table
   are stated, not verified against hardware. The bridge (lane 277) must
   still preserve source range and fault semantics.
-/

#print axioms add64_wert
#print axioms add64_cf
#print axioms add64_of
#print axioms sub64_wert
#print axioms sub64_cf
#print axioms sub64_of
#print axioms xor64_wert
#print axioms trunc_b64
#print axioms maske_nat
#print axioms probe_add_carry_no_overflow
#print axioms probe_bedingung_lt

end Gabbro.Grammatik.X86
