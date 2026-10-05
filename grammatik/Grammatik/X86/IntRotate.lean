/-
  File:      Grammatik/X86/IntRotate.lean
  Subject:   Rotate family (ROL/ROR/RCL/RCR) connected to the coherent
             machine and the unified byte dispatcher.

  Lane 1273: lifts a new rotate value core (single-bit iteration over
  Nat, widths 8/16/32/64) into register and memory forms for opcodes
  D0/D1/D2/D3/C0/C1 with digits 0 to 3, count sources by-1/by-CL/by-imm8,
  SDM count masking, CF/OF-only flag effects, a `HwAdapter` over
  `HwMaschine`/`HwSchritt` (register path only; memory forms are TSO
  events, never the register plug), and a reached two-core witness.
  No new machine, no redefined evaluator, no silicon proof beyond
  self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.NarrowOps
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.HardwareExecution
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- The four rotate operations; the Group-2 extension digit is the
    opcode: ROL is /0, ROR is /1, RCL is /2, RCR is /3. -/
inductive RotOp where
  | rol | ror | rcl | rcr
  deriving DecidableEq, Repr

/-- Operation back from a Group-2 extension digit. -/
def feldRotOp : Nat → Option RotOp
  | 0 => some .rol | 1 => some .ror | 2 => some .rcl | 3 => some .rcr
  | _ => none

/-- Digit of an operation. -/
def rotOpFeld : RotOp → Nat
  | .rol => 0 | .ror => 1 | .rcl => 2 | .rcr => 3

/-- Decoding inverts the digit on every operation. -/
theorem feldRotOp_rotOpFeld (o : RotOp) :
    feldRotOp (rotOpFeld o) = some o := by
  cases o <;> rfl

/-! ## 1. Value core: single-bit rotation iterated over Nat.

    Counts reuse the architectural mask (`schiebeZaehler` from
    `Ganzzahl.lean`: five bits below 64, six at 64). ROL and ROR turn
    the masked count modulo the width; RCL and RCR turn it modulo
    width-plus-one (the carry is the extra bit). A zero effective
    count rotates nothing. Values are Nat iterations of one-bit
    steps, so the inverse laws below go by induction. -/

/-- Masked rotate count: the reused architectural mask. -/
def rotMaske (b : Breite) (c : Nat) : Nat := schiebeZaehler b c

/-- Effective ROL and ROR count: masked count modulo the width. -/
def rotEff (b : Breite) (c : Nat) : Nat := rotMaske b c % b.bits

/-- Effective RCL and RCR count: masked count modulo width plus one. -/
def rclEff (b : Breite) (c : Nat) : Nat := rotMaske b c % (b.bits + 1)

/-- One rotate-left step on a `bits`-bit value. -/
def rol1Nat (n bits : Nat) : Nat :=
  (n * 2) % 2 ^ bits + n / 2 ^ (bits - 1)

/-- One rotate-right step on a `bits`-bit value. -/
def ror1Nat (n bits : Nat) : Nat :=
  n / 2 + n % 2 * 2 ^ (bits - 1)

/-- ROL of `k` single steps over a `bits`-bit value. -/
def rolNat (n bits : Nat) : Nat → Nat
  | 0 => n % 2 ^ bits
  | k + 1 => rol1Nat (rolNat n bits k) bits

/-- ROR of `k` single steps over a `bits`-bit value. -/
def rorNat (n bits : Nat) : Nat → Nat
  | 0 => n % 2 ^ bits
  | k + 1 => ror1Nat (rorNat n bits k) bits

/-- One rotate-through-carry-left step on a `(bits+1)`-bit value. -/
def rcl1Nat (v bits : Nat) : Nat :=
  (v * 2) % 2 ^ (bits + 1) + v / 2 ^ bits

/-- One rotate-through-carry-right step. -/
def rcr1Nat (v bits : Nat) : Nat :=
  v / 2 + v % 2 * 2 ^ bits

/-- RCL of `k` single steps over a `(bits+1)`-bit value. -/
def rclNat (v bits : Nat) : Nat → Nat
  | 0 => v % 2 ^ (bits + 1)
  | k + 1 => rcl1Nat (rclNat v bits k) bits

/-- RCR of `k` single steps over a `(bits+1)`-bit value. -/
def rcrNat (v bits : Nat) : Nat → Nat
  | 0 => v % 2 ^ (bits + 1)
  | k + 1 => rcr1Nat (rcrNat v bits k) bits

/-- ROL value at width `b`: truncated rotate by the effective count. -/
def rolB (b : Breite) (x : Wort) (c : Nat) : Wort :=
  BitVec.ofNat 64 (rolNat (trunc b x).toNat b.bits (rotEff b c))

/-- ROR value at width `b`. -/
def rorB (b : Breite) (x : Wort) (c : Nat) : Wort :=
  BitVec.ofNat 64 (rorNat (trunc b x).toNat b.bits (rotEff b c))

/-- RCL value with incoming carry: the low width bits of the rotated
    extended value, with the new carry beside it. -/
def rclB (b : Breite) (x : Wort) (cf : Bool) (c : Nat) : Wort × Bool :=
  let v := rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat)
    b.bits (rclEff b c)
  (BitVec.ofNat 64 (v % 2 ^ b.bits), decide (v / 2 ^ b.bits = 1))

/-- RCR value with incoming carry. -/
def rcrB (b : Breite) (x : Wort) (cf : Bool) (c : Nat) : Wort × Bool :=
  let v := rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat)
    b.bits (rclEff b c)
  (BitVec.ofNat 64 (v % 2 ^ b.bits), decide (v / 2 ^ b.bits = 1))

/-- Narrow counts wrap every 32 (the reused five-bit mask period). -/
theorem rotMaske_periode_schmal (b : Breite) (c : Nat)
    (h : b ≠ .b64) : rotMaske b (c + 32) = rotMaske b c := by
  unfold rotMaske
  exact schiebeZaehler_periode_schmal b c h

/-- Pinned counts: `0x81 ROL by 1` is `0x03`, `0x01 ROR by 1` is `0x80`,
    RCL of `0xFF` through set carry by 1 is `0xFF` with carry set,
    RCR of `0x01` through clear carry by 1 is `0x00` with carry set. -/
theorem probe_rot_werte :
    rolB .b8 0x81 1 = 0x03 ∧ rorB .b8 0x01 1 = 0x80 ∧
    rclB .b8 0xFF true 1 = (0xFF, true) ∧
    rcrB .b8 0x01 false 1 = (0x00, true) := by
  decide

/-! ## 2. Single-step inverses at every width.

    One right step undoes one left step on values below the modulus,
    and conversely; the through-carry pair is the same fact on the
    extended `(bits+1)`-bit value. All arithmetic is symbolic in
    `bits` (no giant literals), closed by `omega` over atoms. -/

/-- Exact shape of one ROL step: twice the low part plus the high bit. -/
theorem rol1Nat_char (n bits : Nat) (hb : 1 ≤ bits) :
    rol1Nat n bits =
      2 * (n % 2 ^ (bits - 1)) + n / 2 ^ (bits - 1) := by
  obtain ⟨b', rfl⟩ : ∃ b', bits = b' + 1 := ⟨bits - 1, by omega⟩
  have hM : 2 ^ b' * 2 = 2 ^ (b' + 1) := (Nat.pow_succ 2 b').symm
  have hqr : 2 ^ b' * (n / 2 ^ b') + n % 2 ^ b' = n :=
    Nat.div_add_mod n _
  have h1 : n * 2 = (2 ^ b' * (n / 2 ^ b') + n % 2 ^ b') * 2 := by
    rw [hqr]
  have h2 : (2 ^ b' * (n / 2 ^ b') + n % 2 ^ b') * 2 =
      (2 ^ b' * 2) * (n / 2 ^ b') + (n % 2 ^ b') * 2 := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (n / 2 ^ b') 2,
      ← Nat.mul_assoc]
  have h3 : (2 ^ b' * 2) * (n / 2 ^ b') + (n % 2 ^ b') * 2 =
      2 * (n % 2 ^ b') + (n / 2 ^ b') * 2 ^ (b' + 1) := by
    rw [hM, Nat.mul_comm (2 ^ (b' + 1)) _, Nat.mul_comm (n % 2 ^ b') 2,
      Nat.add_comm]
  have hmod : (n * 2) % 2 ^ (b' + 1) = 2 * (n % 2 ^ b') := by
    rw [h1, h2, h3, Nat.add_mul_mod_self_right]
    have hr : n % 2 ^ b' < 2 ^ b' :=
      Nat.mod_lt _ (Nat.pow_pos (show (0 : Nat) < 2 by decide))
    have hlt : 2 * (n % 2 ^ b') < 2 ^ (b' + 1) := by omega
    exact Nat.mod_eq_of_lt hlt
  unfold rol1Nat
  simp only [Nat.add_sub_cancel]
  rw [hmod]

/-- One ROR step undoes one ROL step below the modulus. -/
theorem ror1Nat_rol1Nat (n bits : Nat) (hb : 1 ≤ bits)
    (hn : n < 2 ^ bits) :
    ror1Nat (rol1Nat n bits) bits = n := by
  obtain ⟨b', rfl⟩ : ∃ b', bits = b' + 1 := ⟨bits - 1, by omega⟩
  have hqr : 2 ^ b' * (n / 2 ^ b') + n % 2 ^ b' = n :=
    Nat.div_add_mod n _
  have hq2 : n / 2 ^ b' < 2 := by
    have hM : 2 ^ b' * 2 = 2 ^ (b' + 1) := Nat.pow_succ 2 b'
    cases Nat.lt_or_ge (n / 2 ^ b') 2 with
    | inl h => exact h
    | inr h =>
      have hle : 2 ^ b' * 2 ≤ 2 ^ b' * (n / 2 ^ b') :=
        Nat.mul_le_mul_left _ h
      omega
  have hchar : rol1Nat n (b' + 1) = 2 * (n % 2 ^ b') + n / 2 ^ b' := by
    have h := rol1Nat_char n (b' + 1) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  have hd : (2 * (n % 2 ^ b') + n / 2 ^ b') / 2 = n % 2 ^ b' := by
    rw [Nat.add_comm (2 * (n % 2 ^ b')) _,
      Nat.add_mul_div_left _ _ (show (0 : Nat) < 2 by decide),
      Nat.div_eq_of_lt hq2, Nat.zero_add]
  have hm : (2 * (n % 2 ^ b') + n / 2 ^ b') % 2 = n / 2 ^ b' := by omega
  have hror : ror1Nat (2 * (n % 2 ^ b') + n / 2 ^ b') (b' + 1) =
      n % 2 ^ b' + (n / 2 ^ b') * 2 ^ b' := by
    unfold ror1Nat
    simp only [Nat.add_sub_cancel]
    rw [hd, hm]
  rw [hchar, hror, Nat.mul_comm (n / 2 ^ b') (2 ^ b')]
  omega

/-- Exact shape of one ROR step: high-bit multiple plus the high part. -/
theorem ror1Nat_char (n bits : Nat) :
    ror1Nat n bits =
      (n % 2) * 2 ^ (bits - 1) + n / 2 := by
  unfold ror1Nat
  rw [Nat.add_comm]

/-- One ROL step undoes one ROR step below the modulus. -/
theorem rol1Nat_ror1Nat (n bits : Nat) (hb : 1 ≤ bits)
    (hn : n < 2 ^ bits) :
    rol1Nat (ror1Nat n bits) bits = n := by
  obtain ⟨b', rfl⟩ : ∃ b', bits = b' + 1 := ⟨bits - 1, by omega⟩
  have hM : 2 ^ b' * 2 = 2 ^ (b' + 1) := Nat.pow_succ 2 b'
  have hqr : 2 ^ b' * (n / 2 ^ b') + n % 2 ^ b' = n :=
    Nat.div_add_mod n _
  have hHpos : 0 < 2 ^ b' :=
    Nat.pow_pos (show (0 : Nat) < 2 by decide)
  have hhalf : n / 2 < 2 ^ b' := by omega
  have hmod2 : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have hchar : ror1Nat n (b' + 1) = (n % 2) * 2 ^ b' + n / 2 := by
    have h := ror1Nat_char n (b' + 1)
    simpa only [Nat.add_sub_cancel] using h
  have hlow : ((n % 2) * 2 ^ b' + n / 2) % 2 ^ b' = n / 2 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hhalf]
  have hhigh : ((n % 2) * 2 ^ b' + n / 2) / 2 ^ b' = n % 2 := by
    rw [Nat.add_comm ((n % 2) * 2 ^ b') (n / 2),
      Nat.add_mul_div_right _ _ hHpos,
      Nat.div_eq_of_lt hhalf, Nat.zero_add]
  have hrol : rol1Nat ((n % 2) * 2 ^ b' + n / 2) (b' + 1) =
      2 * (n / 2) + n % 2 := by
    have h := rol1Nat_char ((n % 2) * 2 ^ b' + n / 2) (b' + 1)
      (by omega)
    simpa only [Nat.add_sub_cancel, hlow, hhigh] using h
  rw [hchar, hrol]
  exact Nat.div_add_mod n 2

/- CUTS (checkpoint: value core only):
    Proved here: rotate operation digits, Nat value core for ROL/ROR
    and RCL/RCR with architectural count masking, single-step
    inverses in both directions, and pinned values.
    NOT proved here, and not claimed:
    - Iterated inverses, word-level identities, flag effects,
      decode/encode, family step, dispatcher, machine adapter,
      TSO memory events and the joint witness are OPEN.
    - No hardware correspondence: stated executable semantics with
      self-consistency only, not x86 truth.
-/

#print axioms feldRotOp_rotOpFeld
#print axioms probe_rot_werte
#print axioms rol1Nat_char
#print axioms ror1Nat_rol1Nat
#print axioms ror1Nat_char
#print axioms rol1Nat_ror1Nat

end Gabbro.Grammatik.X86
