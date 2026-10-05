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

/-- ROL of `k` single steps over a `bits`-bit value, innermost
    step first (so the ROR inverse below unfolds the outer step). -/
def rolNat (n bits : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => rolNat (rol1Nat n bits) bits k

/-- ROR of `k` single steps over a `bits`-bit value, outermost step
    first (matching the ROL form above from the other side). -/
def rorNat (n bits : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => ror1Nat (rorNat n bits k) bits

/-- One rotate-through-carry-left step on a `(bits+1)`-bit value. -/
def rcl1Nat (v bits : Nat) : Nat :=
  (v * 2) % 2 ^ (bits + 1) + v / 2 ^ bits

/-- One rotate-through-carry-right step. -/
def rcr1Nat (v bits : Nat) : Nat :=
  v / 2 + v % 2 * 2 ^ bits

/-- RCL of `k` single steps over a `(bits+1)`-bit value, innermost
    step first (so the RCR inverse below unfolds the outer step). -/
def rclNat (v bits : Nat) : Nat → Nat
  | 0 => v
  | k + 1 => rclNat (rcl1Nat v bits) bits k

/-- RCR of `k` single steps over a `(bits+1)`-bit value, outermost
    step first. -/
def rcrNat (v bits : Nat) : Nat → Nat
  | 0 => v
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

/-- The top bit of a value below twice a power of two is below two. -/
theorem divTopBit_lt_two (n b' : Nat) (hn : n < 2 ^ (b' + 1)) :
    n / 2 ^ b' < 2 := by
  have hM : 2 ^ b' * 2 = 2 ^ (b' + 1) := Nat.pow_succ 2 b'
  have hqr : 2 ^ b' * (n / 2 ^ b') + n % 2 ^ b' = n :=
    Nat.div_add_mod n _
  cases Nat.lt_or_ge (n / 2 ^ b') 2 with
  | inl h => exact h
  | inr h =>
    have hle : 2 ^ b' * 2 ≤ 2 ^ b' * (n / 2 ^ b') :=
      Nat.mul_le_mul_left _ h
    omega

/-- Exact shape of one RCL step. -/
theorem rcl1Nat_char (v bits : Nat) :
    rcl1Nat v bits = 2 * (v % 2 ^ bits) + v / 2 ^ bits := by
  have hM : 2 ^ bits * 2 = 2 ^ (bits + 1) := Nat.pow_succ 2 bits
  have hqr : 2 ^ bits * (v / 2 ^ bits) + v % 2 ^ bits = v :=
    Nat.div_add_mod v _
  have e : v * 2 =
      2 * (v % 2 ^ bits) + (v / 2 ^ bits) * 2 ^ (bits + 1) := by
    have h1 : v * 2 =
        (2 ^ bits * (v / 2 ^ bits) + v % 2 ^ bits) * 2 := by rw [hqr]
    have h2 : (2 ^ bits * (v / 2 ^ bits) + v % 2 ^ bits) * 2 =
        (2 ^ bits * 2) * (v / 2 ^ bits) + (v % 2 ^ bits) * 2 := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (v / 2 ^ bits) 2,
        ← Nat.mul_assoc]
    have h3 : (2 ^ bits * 2) * (v / 2 ^ bits) + (v % 2 ^ bits) * 2 =
        2 * (v % 2 ^ bits) + (v / 2 ^ bits) * 2 ^ (bits + 1) := by
      rw [hM, Nat.mul_comm (2 ^ (bits + 1)) _,
        Nat.mul_comm (v % 2 ^ bits) 2, Nat.add_comm]
    rw [h1, h2, h3]
  have hmod : (v * 2) % 2 ^ (bits + 1) = 2 * (v % 2 ^ bits) := by
    rw [e, Nat.add_mul_mod_self_right]
    have hr : v % 2 ^ bits < 2 ^ bits :=
      Nat.mod_lt _ (Nat.pow_pos (show (0 : Nat) < 2 by decide))
    have hlt : 2 * (v % 2 ^ bits) < 2 ^ (bits + 1) := by omega
    exact Nat.mod_eq_of_lt hlt
  unfold rcl1Nat
  rw [hmod]

/-- Exact shape of one RCR step. -/
theorem rcr1Nat_char (v bits : Nat) :
    rcr1Nat v bits = (v % 2) * 2 ^ bits + v / 2 := by
  unfold rcr1Nat
  rw [Nat.add_comm]

/-- One RCR step undoes one RCL step below the extended modulus. -/
theorem rcr1Nat_rcl1Nat (v bits : Nat) (hv : v < 2 ^ (bits + 1)) :
    rcr1Nat (rcl1Nat v bits) bits = v := by
  have hqr : 2 ^ bits * (v / 2 ^ bits) + v % 2 ^ bits = v :=
    Nat.div_add_mod v _
  have hq2 : v / 2 ^ bits < 2 := divTopBit_lt_two v bits hv
  have hchar : rcl1Nat v bits = 2 * (v % 2 ^ bits) + v / 2 ^ bits :=
    rcl1Nat_char v bits
  have hd : (2 * (v % 2 ^ bits) + v / 2 ^ bits) / 2 = v % 2 ^ bits := by
    rw [Nat.add_comm (2 * (v % 2 ^ bits)) _,
      Nat.add_mul_div_left _ _ (show (0 : Nat) < 2 by decide),
      Nat.div_eq_of_lt hq2, Nat.zero_add]
  have hm : (2 * (v % 2 ^ bits) + v / 2 ^ bits) % 2 = v / 2 ^ bits := by
    omega
  have hrcr : rcr1Nat (2 * (v % 2 ^ bits) + v / 2 ^ bits) bits =
      v % 2 ^ bits + (v / 2 ^ bits) * 2 ^ bits := by
    unfold rcr1Nat
    rw [hd, hm]
  rw [hchar, hrcr, Nat.mul_comm (v / 2 ^ bits) (2 ^ bits)]
  omega

/-- One RCL step undoes one RCR step below the extended modulus. -/
theorem rcl1Nat_rcr1Nat (v bits : Nat) (hv : v < 2 ^ (bits + 1)) :
    rcl1Nat (rcr1Nat v bits) bits = v := by
  have hHpos : 0 < 2 ^ bits :=
    Nat.pow_pos (show (0 : Nat) < 2 by decide)
  have hhalf : v / 2 < 2 ^ bits := by
    have hM : 2 ^ bits * 2 = 2 ^ (bits + 1) := Nat.pow_succ 2 bits
    omega
  have hchar : rcr1Nat v bits = (v % 2) * 2 ^ bits + v / 2 := rcr1Nat_char v bits
  have hlow : ((v % 2) * 2 ^ bits + v / 2) % 2 ^ bits = v / 2 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hhalf]
  have hhigh : ((v % 2) * 2 ^ bits + v / 2) / 2 ^ bits = v % 2 := by
    rw [Nat.add_comm ((v % 2) * 2 ^ bits) (v / 2),
      Nat.add_mul_div_right _ _ hHpos,
      Nat.div_eq_of_lt hhalf, Nat.zero_add]
  have hrcl : rcl1Nat ((v % 2) * 2 ^ bits + v / 2) bits =
      2 * (v / 2) + v % 2 := by
    have h := rcl1Nat_char ((v % 2) * 2 ^ bits + v / 2) bits
    simpa only [hlow, hhigh] using h
  rw [hchar, hrcl]
  exact Nat.div_add_mod v 2

/-! ## 3. Iterated inverses.

    ROR undoes ROL and RCR undoes RCL over any step count, by
    induction: the left operations peel their innermost step first,
    the right operations their outermost step, so each successor
    case meets the single-step inverse exactly once. -/

/-- A low bit times a power of two stays below twice that power. -/
theorem modTwo_mul_pow_le (n b' : Nat) : (n % 2) * 2 ^ b' ≤ 2 ^ b' := by
  cases Nat.lt_or_ge (n % 2) 1 with
  | inl h =>
    have h0 : n % 2 = 0 := by omega
    rw [h0, Nat.zero_mul]
    exact Nat.zero_le _
  | inr h =>
    have h1 : n % 2 = 1 := by omega
    rw [h1, Nat.one_mul]
    exact Nat.le_refl _
theorem rol1Nat_lt (n bits : Nat) (hb : 1 ≤ bits) (hn : n < 2 ^ bits) :
    rol1Nat n bits < 2 ^ bits := by
  obtain ⟨b', rfl⟩ : ∃ b', bits = b' + 1 := ⟨bits - 1, by omega⟩
  have hM : 2 ^ b' * 2 = 2 ^ (b' + 1) := Nat.pow_succ 2 b'
  have hchar : rol1Nat n (b' + 1) = 2 * (n % 2 ^ b') + n / 2 ^ b' := by
    have h := rol1Nat_char n (b' + 1) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  have hr : n % 2 ^ b' < 2 ^ b' :=
    Nat.mod_lt _ (Nat.pow_pos (show (0 : Nat) < 2 by decide))
  have hq2 : n / 2 ^ b' < 2 := divTopBit_lt_two n b' hn
  rw [hchar]
  omega

/-- One ROR step keeps values below the modulus. -/
theorem ror1Nat_lt (n bits : Nat) (hb : 1 ≤ bits) (hn : n < 2 ^ bits) :
    ror1Nat n bits < 2 ^ bits := by
  obtain ⟨b', rfl⟩ : ∃ b', bits = b' + 1 := ⟨bits - 1, by omega⟩
  have hM : 2 ^ b' * 2 = 2 ^ (b' + 1) := Nat.pow_succ 2 b'
  have hchar : ror1Nat n (b' + 1) = (n % 2) * 2 ^ b' + n / 2 := by
    have h := ror1Nat_char n (b' + 1)
    simpa only [Nat.add_sub_cancel] using h
  rw [hchar]
  have hP : (n % 2) * 2 ^ b' ≤ 2 ^ b' := modTwo_mul_pow_le n b'
  have hf : n / 2 < 2 ^ b' := by omega
  omega

/-- One RCL step keeps values below the extended modulus. -/
theorem rcl1Nat_lt (v bits : Nat) (hv : v < 2 ^ (bits + 1)) :
    rcl1Nat v bits < 2 ^ (bits + 1) := by
  have hM : 2 ^ bits * 2 = 2 ^ (bits + 1) := Nat.pow_succ 2 bits
  have hchar : rcl1Nat v bits = 2 * (v % 2 ^ bits) + v / 2 ^ bits :=
    rcl1Nat_char v bits
  have hr : v % 2 ^ bits < 2 ^ bits :=
    Nat.mod_lt _ (Nat.pow_pos (show (0 : Nat) < 2 by decide))
  have hq2 : v / 2 ^ bits < 2 := divTopBit_lt_two v bits hv
  rw [hchar]
  omega

/-- One RCR step keeps values below the extended modulus. -/
theorem rcr1Nat_lt (v bits : Nat) (hv : v < 2 ^ (bits + 1)) :
    rcr1Nat v bits < 2 ^ (bits + 1) := by
  have hM : 2 ^ bits * 2 = 2 ^ (bits + 1) := Nat.pow_succ 2 bits
  have hchar : rcr1Nat v bits = (v % 2) * 2 ^ bits + v / 2 :=
    rcr1Nat_char v bits
  rw [hchar]
  have hP : (v % 2) * 2 ^ bits ≤ 2 ^ bits := modTwo_mul_pow_le v bits
  have hf : v / 2 < 2 ^ bits := by omega
  omega

/-- Iterated ROR keeps values below the modulus. -/
theorem rorNat_lt (n bits k : Nat) (hb : 1 ≤ bits)
    (hn : n < 2 ^ bits) :
    rorNat n bits k < 2 ^ bits := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    show ror1Nat (rorNat n bits k) bits < 2 ^ bits
    exact ror1Nat_lt _ _ hb (ih n hn)

/-- Iterated ROL keeps values below the modulus. -/
theorem rolNat_lt (n bits k : Nat) (hb : 1 ≤ bits)
    (hn : n < 2 ^ bits) :
    rolNat n bits k < 2 ^ bits := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    show rolNat (rol1Nat n bits) bits k < 2 ^ bits
    exact ih _ (rol1Nat_lt n bits hb hn)

/-- Iterated RCR keeps values below the extended modulus. -/
theorem rcrNat_lt (v bits k : Nat) (hv : v < 2 ^ (bits + 1)) :
    rcrNat v bits k < 2 ^ (bits + 1) := by
  induction k generalizing v with
  | zero => exact hv
  | succ k ih =>
    show rcr1Nat (rcrNat v bits k) bits < 2 ^ (bits + 1)
    exact rcr1Nat_lt _ _ (ih v hv)

/-- Iterated RCL keeps values below the extended modulus. -/
theorem rclNat_lt (v bits k : Nat) (hv : v < 2 ^ (bits + 1)) :
    rclNat v bits k < 2 ^ (bits + 1) := by
  induction k generalizing v with
  | zero => exact hv
  | succ k ih =>
    show rclNat (rcl1Nat v bits) bits k < 2 ^ (bits + 1)
    exact ih _ (rcl1Nat_lt v bits hv)

/-- ROR undoes ROL over any step count. -/
theorem rorNat_rolNat (n bits k : Nat) (hb : 1 ≤ bits)
    (hn : n < 2 ^ bits) :
    rorNat (rolNat n bits k) bits k = n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have h1 : rol1Nat n bits < 2 ^ bits := rol1Nat_lt n bits hb hn
    simp only [rolNat, rorNat]
    rw [ih _ h1]
    exact ror1Nat_rol1Nat _ _ hb hn

/-- ROL undoes ROR over any step count. -/
theorem rolNat_rorNat (n bits k : Nat) (hb : 1 ≤ bits)
    (hn : n < 2 ^ bits) :
    rolNat (rorNat n bits k) bits k = n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hmb : rorNat n bits k < 2 ^ bits := rorNat_lt n bits k hb hn
    simp only [rolNat, rorNat]
    rw [rol1Nat_ror1Nat _ _ hb hmb]
    exact ih _ hn

/-- RCR undoes RCL over any step count. -/
theorem rcrNat_rclNat (v bits k : Nat) (hv : v < 2 ^ (bits + 1)) :
    rcrNat (rclNat v bits k) bits k = v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    have h1 : rcl1Nat v bits < 2 ^ (bits + 1) := rcl1Nat_lt v bits hv
    simp only [rclNat, rcrNat]
    rw [ih _ h1]
    exact rcr1Nat_rcl1Nat _ _ hv

/-- RCL undoes RCR over any step count. -/
theorem rclNat_rcrNat (v bits k : Nat) (hv : v < 2 ^ (bits + 1)) :
    rclNat (rcrNat v bits k) bits k = v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    have hmb : rcrNat v bits k < 2 ^ (bits + 1) := rcrNat_lt v bits k hv
    simp only [rclNat, rcrNat]
    rw [rcl1Nat_rcr1Nat _ _ hmb]
    exact ih _ hv

/-! ## 4. Word level: identities and inverses over truncated words.

    Truncation of a small `ofNat` word is exact, so the Nat inverses
    above lift to words: ROL and ROR invert each other, RCL and RCR
    invert each other through the carry, and a zero effective count
    is the truncated identity. -/

/-- A truncated word fits its width (reused `narrowTruncMod`). -/
theorem trunc_toNat_lt (b : Breite) (x : Wort) :
    (trunc b x).toNat < 2 ^ b.bits := by
  rw [narrowTruncMod]
  exact Nat.mod_lt _ (Nat.pow_pos (show (0 : Nat) < 2 by decide))

/-- Every width is positive. -/
theorem breite_pos (b : Breite) : 1 ≤ b.bits := by
  cases b <;> decide

/-- Truncating a small `ofNat` word is exact. -/
theorem trunc_ofNat_lt (b : Breite) (m : Nat) (hm : m < 2 ^ b.bits) :
    trunc b (BitVec.ofNat 64 m) = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  unfold trunc
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hmask : (maske b).toNat = 2 ^ b.bits - 1 := by cases b <;> decide
  rw [hmask, narrowMaskMod]
  have h64 : m < 2 ^ 64 := by
    cases b with
    | b8 => omega
    | b16 => omega
    | b32 => omega
    | b64 => exact hm
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hm]

/-- An `ofNat` word reads back its truncated value. -/
theorem trunc_ofNat_toNat (b : Breite) (x : Wort) :
    BitVec.ofNat 64 (trunc b x).toNat = trunc b x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have h64 : (trunc b x).toNat < 2 ^ 64 := by
    have h := trunc_toNat_lt b x
    cases b with
    | b8 => omega
    | b16 => omega
    | b32 => omega
    | b64 => exact h
  rw [Nat.mod_eq_of_lt h64]

/-- A zero effective ROL count is the truncated identity. -/
theorem rolB_null (b : Breite) (x : Wort) (c : Nat)
    (h : rotEff b c = 0) :
    rolB b x c = trunc b x := by
  unfold rolB
  rw [h]
  have h0 : rolNat (trunc b x).toNat b.bits 0 = (trunc b x).toNat := rfl
  rw [h0]
  exact trunc_ofNat_toNat b x

/-- A zero effective ROR count is the truncated identity. -/
theorem rorB_null (b : Breite) (x : Wort) (c : Nat)
    (h : rotEff b c = 0) :
    rorB b x c = trunc b x := by
  unfold rorB
  rw [h]
  have h0 : rorNat (trunc b x).toNat b.bits 0 = (trunc b x).toNat := rfl
  rw [h0]
  exact trunc_ofNat_toNat b x

/-- Rotate by the width is the identity (the masked count turns
    modulo the width to zero at every width). -/
theorem rolB_breite_ident (b : Breite) (x : Wort) :
    rolB b x b.bits = trunc b x := by
  apply rolB_null
  unfold rotEff rotMaske
  cases b <;> decide

/-- Rotate right by the width is the identity. -/
theorem rorB_breite_ident (b : Breite) (x : Wort) :
    rorB b x b.bits = trunc b x := by
  apply rorB_null
  unfold rotEff rotMaske
  cases b <;> decide

/-- A zero effective RCL count keeps value and carry. -/
theorem rclB_null (b : Breite) (x : Wort) (cf : Bool) (c : Nat)
    (h : rclEff b c = 0) :
    rclB b x cf c = (trunc b x, cf) := by
  unfold rclB
  rw [h]
  have h0 : rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat)
      b.bits 0 = cf.toNat * 2 ^ b.bits + (trunc b x).toNat := rfl
  rw [h0]
  have hn := trunc_toNat_lt b x
  have hcf : cf.toNat ≤ 1 := by cases cf <;> decide
  have hmod : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) % 2 ^ b.bits =
      (trunc b x).toNat := by
    have e : cf.toNat * 2 ^ b.bits + (trunc b x).toNat =
        (trunc b x).toNat + cf.toNat * 2 ^ b.bits := by
      rw [Nat.add_comm]
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]
  have hdiv : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) / 2 ^ b.bits =
      cf.toNat := by
    have hHpos : 0 < 2 ^ b.bits :=
      Nat.pow_pos (show (0 : Nat) < 2 by decide)
    rw [Nat.add_comm (cf.toNat * 2 ^ b.bits) _,
      Nat.add_mul_div_right _ _ hHpos, Nat.div_eq_of_lt hn,
      Nat.zero_add]
  have hcfback : decide ((cf.toNat * 2 ^ b.bits +
      (trunc b x).toNat) / 2 ^ b.bits = 1) = cf := by
    cases cf <;> rw [hdiv] <;> rfl
  simp only [hmod, hcfback]
  rw [trunc_ofNat_toNat b x]

/-- ROR undoes ROL at the word level. -/
theorem rol_ror_inverse (b : Breite) (x : Wort) (c : Nat) :
    rorB b (rolB b x c) c = trunc b x := by
  have hn := trunc_toNat_lt b x
  have hb := breite_pos b
  have hbound : rolNat (trunc b x).toNat b.bits (rotEff b c) < 2 ^ b.bits :=
    rolNat_lt _ _ _ hb hn
  have hinv := rorNat_rolNat (trunc b x).toNat b.bits (rotEff b c) hb hn
  unfold rorB rolB
  have htr : trunc b (BitVec.ofNat 64
      (rolNat (trunc b x).toNat b.bits (rotEff b c))) =
      BitVec.ofNat 64 (rolNat (trunc b x).toNat b.bits (rotEff b c)) :=
    trunc_ofNat_lt b _ hbound
  rw [htr]
  have hto : (BitVec.ofNat 64
      (rolNat (trunc b x).toNat b.bits (rotEff b c))).toNat =
      rolNat (trunc b x).toNat b.bits (rotEff b c) := by
    rw [BitVec.toNat_ofNat]
    have h64 : rolNat (trunc b x).toNat b.bits (rotEff b c) < 2 ^ 64 := by
      have hle : 2 ^ b.bits ≤ 2 ^ 64 := by
        cases b <;> decide
      omega
    exact Nat.mod_eq_of_lt h64
  rw [hto, hinv]
  exact trunc_ofNat_toNat b x

/-- ROL undoes ROR at the word level. -/
theorem ror_rol_inverse (b : Breite) (x : Wort) (c : Nat) :
    rolB b (rorB b x c) c = trunc b x := by
  have hn := trunc_toNat_lt b x
  have hb := breite_pos b
  have hbound : rorNat (trunc b x).toNat b.bits (rotEff b c) < 2 ^ b.bits :=
    rorNat_lt _ _ _ hb hn
  have hinv := rolNat_rorNat (trunc b x).toNat b.bits (rotEff b c) hb hn
  unfold rolB rorB
  have htr : trunc b (BitVec.ofNat 64
      (rorNat (trunc b x).toNat b.bits (rotEff b c))) =
      BitVec.ofNat 64 (rorNat (trunc b x).toNat b.bits (rotEff b c)) :=
    trunc_ofNat_lt b _ hbound
  rw [htr]
  have hto : (BitVec.ofNat 64
      (rorNat (trunc b x).toNat b.bits (rotEff b c))).toNat =
      rorNat (trunc b x).toNat b.bits (rotEff b c) := by
    rw [BitVec.toNat_ofNat]
    have h64 : rorNat (trunc b x).toNat b.bits (rotEff b c) < 2 ^ 64 := by
      have hle : 2 ^ b.bits ≤ 2 ^ 64 := by
        cases b <;> decide
      omega
    exact Nat.mod_eq_of_lt h64
  rw [hto, hinv]
  exact trunc_ofNat_toNat b x

/-- A truncated `ofNat` word reads back its value. -/
theorem trunc_ofNat_toNat' (b : Breite) (m : Nat)
    (hm : m < 2 ^ b.bits) :
    (trunc b (BitVec.ofNat 64 m)).toNat = m := by
  rw [trunc_ofNat_lt b m hm, BitVec.toNat_ofNat]
  have hle : 2 ^ b.bits ≤ 2 ^ 64 := by
    cases b <;> decide
  have h64 : m < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt h64

/-- The decided top bit reads back as the quotient below twice. -/
theorem decide_div_eq_toNat (v H : Nat) (hv : v < H * 2) :
    (decide (v / H = 1)).toNat = v / H := by
  have hqr : H * (v / H) + v % H = v := Nat.div_add_mod v H
  have hle : H * (v / H) ≤ v := by
    have h := Nat.le_add_right (H * (v / H)) (v % H)
    rw [hqr] at h
    exact h
  cases Nat.lt_or_ge (v / H) 2 with
  | inl h =>
    cases Nat.lt_or_ge (v / H) 1 with
    | inl h0 =>
      have h00 : v / H = 0 :=
        Nat.le_antisymm (Nat.le_of_lt_succ h0) (Nat.zero_le _)
      have e0 : (decide ((0 : Nat) = 1)).toNat = 0 := rfl
      rw [h00, e0]
    | inr h1 =>
      have h11 : v / H = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h) h1
      have e1 : (decide ((1 : Nat) = 1)).toNat = 1 := rfl
      rw [h11, e1]
  | inr h =>
    have hge : H * 2 ≤ H * (v / H) := Nat.mul_le_mul_left _ h
    have hX : H * (v / H) < H * (v / H) :=
      Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le hv hge)
    exact absurd hX (Nat.lt_irrefl _)

/-- Word and carry rejoin below twice the width. -/
theorem split_roundtrip_nat (W H : Nat) (hW : W < H * 2) :
    (decide (W / H = 1)).toNat * H + W % H = W := by
  have hcf1n : (decide (W / H = 1)).toNat = W / H :=
    decide_div_eq_toNat W H hW
  rw [hcf1n]
  have hqr := Nat.div_add_mod W H
  rw [Nat.mul_comm (W / H) H]
  exact hqr

/-- A zero effective RCR count keeps value and carry. -/
theorem rcrB_null (b : Breite) (x : Wort) (cf : Bool) (c : Nat)
    (h : rclEff b c = 0) :
    rcrB b x cf c = (trunc b x, cf) := by
  unfold rcrB
  rw [h]
  have h0 : rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat)
      b.bits 0 = cf.toNat * 2 ^ b.bits + (trunc b x).toNat := rfl
  rw [h0]
  have hn := trunc_toNat_lt b x
  have hmod : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) % 2 ^ b.bits =
      (trunc b x).toNat := by
    have e : cf.toNat * 2 ^ b.bits + (trunc b x).toNat =
        (trunc b x).toNat + cf.toNat * 2 ^ b.bits := by
      rw [Nat.add_comm]
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]
  have hdiv : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) / 2 ^ b.bits =
      cf.toNat := by
    have hHpos : 0 < 2 ^ b.bits :=
      Nat.pow_pos (show (0 : Nat) < 2 by decide)
    rw [Nat.add_comm (cf.toNat * 2 ^ b.bits) _,
      Nat.add_mul_div_right _ _ hHpos, Nat.div_eq_of_lt hn,
      Nat.zero_add]
  have hcfback : decide ((cf.toNat * 2 ^ b.bits +
      (trunc b x).toNat) / 2 ^ b.bits = 1) = cf := by
    cases cf <;> rw [hdiv] <;> rfl
  simp only [hmod, hcfback]
  rw [trunc_ofNat_toNat b x]

/-- RCR undoes RCL through the carry at the word level. -/
theorem rcl_rcr_inverse (b : Breite) (x : Wort) (cf : Bool) (c : Nat) :
    rcrB b (rclB b x cf c).1 (rclB b x cf c).2 c = (trunc b x, cf) := by
  have hn : (trunc b x).toNat < 2 ^ b.bits := trunc_toNat_lt b x
  have hHpos : 0 < 2 ^ b.bits :=
    Nat.pow_pos (show (0 : Nat) < 2 by decide)
  have hM : 2 ^ b.bits * 2 = 2 ^ (b.bits + 1) := Nat.pow_succ 2 b.bits
  have hV : cf.toNat * 2 ^ b.bits + (trunc b x).toNat < 2 ^ (b.bits + 1) := by
    have hcf1 : cf.toNat * 2 ^ b.bits ≤ 2 ^ b.bits := by
      cases cf with
      | true =>
        have e : (true : Bool).toNat = 1 := rfl
        rw [e, Nat.one_mul]
        exact Nat.le_refl _
      | false =>
        have e : (false : Bool).toNat = 0 := rfl
        rw [e, Nat.zero_mul]
        exact Nat.zero_le _
    omega
  have hV1 : rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
      (rclEff b c) < 2 ^ (b.bits + 1) :=
    rclNat_lt _ _ _ hV
  have hinv := rcrNat_rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat)
    b.bits (rclEff b c) hV
  have hw1 : (rclB b x cf c).1 = BitVec.ofNat 64
      (rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) % 2 ^ b.bits) := rfl
  have hcf1 : (rclB b x cf c).2 = decide
      (rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) / 2 ^ b.bits = 1) := rfl
  rw [hw1, hcf1]
  have hlow : (trunc b (BitVec.ofNat 64
      (rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) % 2 ^ b.bits))).toNat =
      rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) % 2 ^ b.bits :=
    trunc_ofNat_toNat' b _ (Nat.mod_lt _ hHpos)
  have hrebuild : (decide
        (rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
          (rclEff b c) / 2 ^ b.bits = 1)).toNat * 2 ^ b.bits +
      (trunc b (BitVec.ofNat 64
        (rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
          (rclEff b c) % 2 ^ b.bits))).toNat =
      rclNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) := by
    rw [hlow]
    exact split_roundtrip_nat _ _ hV1
  unfold rcrB
  simp only [hrebuild]
  rw [hinv]
  have hmod : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) % 2 ^ b.bits =
      (trunc b x).toNat := by
    have e : cf.toNat * 2 ^ b.bits + (trunc b x).toNat =
        (trunc b x).toNat + cf.toNat * 2 ^ b.bits := by
      rw [Nat.add_comm]
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]
  have hdiv : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) / 2 ^ b.bits =
      cf.toNat := by
    rw [Nat.add_comm (cf.toNat * 2 ^ b.bits) _,
      Nat.add_mul_div_right _ _ hHpos, Nat.div_eq_of_lt hn,
      Nat.zero_add]
  rw [hmod]
  cases cf with
  | true =>
    rw [hdiv]
    have e1 : (decide ((true.toNat : Nat) = 1)) = true := rfl
    rw [e1, trunc_ofNat_toNat b x]
  | false =>
    rw [hdiv]
    have e0 : (decide ((false.toNat : Nat) = 1)) = false := rfl
    rw [e0, trunc_ofNat_toNat b x]

/-- RCL undoes RCR through the carry at the word level. -/
theorem rcr_rcl_inverse (b : Breite) (x : Wort) (cf : Bool) (c : Nat) :
    rclB b (rcrB b x cf c).1 (rcrB b x cf c).2 c = (trunc b x, cf) := by
  have hn : (trunc b x).toNat < 2 ^ b.bits := trunc_toNat_lt b x
  have hHpos : 0 < 2 ^ b.bits :=
    Nat.pow_pos (show (0 : Nat) < 2 by decide)
  have hM : 2 ^ b.bits * 2 = 2 ^ (b.bits + 1) := Nat.pow_succ 2 b.bits
  have hV : cf.toNat * 2 ^ b.bits + (trunc b x).toNat < 2 ^ (b.bits + 1) := by
    have hcf1 : cf.toNat * 2 ^ b.bits ≤ 2 ^ b.bits := by
      cases cf with
      | true =>
        have e : (true : Bool).toNat = 1 := rfl
        rw [e, Nat.one_mul]
        exact Nat.le_refl _
      | false =>
        have e : (false : Bool).toNat = 0 := rfl
        rw [e, Nat.zero_mul]
        exact Nat.zero_le _
    omega
  have hV1 : rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
      (rclEff b c) < 2 ^ (b.bits + 1) :=
    rcrNat_lt _ _ _ hV
  have hinv := rclNat_rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat)
    b.bits (rclEff b c) hV
  have hw1 : (rcrB b x cf c).1 = BitVec.ofNat 64
      (rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) % 2 ^ b.bits) := rfl
  have hcf1 : (rcrB b x cf c).2 = decide
      (rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) / 2 ^ b.bits = 1) := rfl
  rw [hw1, hcf1]
  have hlow : (trunc b (BitVec.ofNat 64
      (rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) % 2 ^ b.bits))).toNat =
      rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) % 2 ^ b.bits :=
    trunc_ofNat_toNat' b _ (Nat.mod_lt _ hHpos)
  have hrebuild : (decide
        (rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
          (rclEff b c) / 2 ^ b.bits = 1)).toNat * 2 ^ b.bits +
      (trunc b (BitVec.ofNat 64
        (rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
          (rclEff b c) % 2 ^ b.bits))).toNat =
      rcrNat (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) b.bits
        (rclEff b c) := by
    rw [hlow]
    exact split_roundtrip_nat _ _ hV1
  unfold rclB
  simp only [hrebuild]
  rw [hinv]
  have hmod : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) % 2 ^ b.bits =
      (trunc b x).toNat := by
    have e : cf.toNat * 2 ^ b.bits + (trunc b x).toNat =
        (trunc b x).toNat + cf.toNat * 2 ^ b.bits := by
      rw [Nat.add_comm]
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]
  have hdiv : (cf.toNat * 2 ^ b.bits + (trunc b x).toNat) / 2 ^ b.bits =
      cf.toNat := by
    rw [Nat.add_comm (cf.toNat * 2 ^ b.bits) _,
      Nat.add_mul_div_right _ _ hHpos, Nat.div_eq_of_lt hn,
      Nat.zero_add]
  rw [hmod]
  cases cf with
  | true =>
    rw [hdiv]
    have e1 : (decide ((true.toNat : Nat) = 1)) = true := rfl
    rw [e1, trunc_ofNat_toNat b x]
  | false =>
    rw [hdiv]
    have e0 : (decide ((false.toNat : Nat) = 1)) = false := rfl
    rw [e0, trunc_ofNat_toNat b x]

/-! ## 5. Flag effects: CF pinned, OF at masked count one, rest kept.

    CF is the last bit rotated out (ROL: the wrapped low bit, ROR:
    the sign bit, RCL and RCR: the new carry). OF is defined only
    for a masked count of one and stays free otherwise (the `getD`
    idiom of `schiebErlaubt`, never invented false). SF, ZF, AF and
    PF are unaffected (kept from the incoming snapshot), and a zero
    effective count changes no flag at all. The executable snapshot
    keeps the incoming OF bit where the architecture leaves it
    undefined (one admissible member, documented, not hardware
    truth). -/

/-- Defined rotate evidence: value, carry out, optional overflow. -/
structure RotNachweis where
  ergebnis : Wort
  trag : Bool
  ueberlauf : Option Bool

/-- Defined evidence of one rotate: value from §1 and §4, carry out,
    overflow exactly at a masked count of one. -/
def rotNachweis (o : RotOp) (b : Breite) (x : Wort) (cfAlt : Bool)
    (c : Nat) : RotNachweis :=
  match o with
  | .rol =>
    let r := rolB b x c
    let cf := r.toNat.testBit 0
    ⟨r, cf, if rotMaske b c = 1 then some (negB b r != cf) else none⟩
  | .ror =>
    let r := rorB b x c
    let cf := negB b r
    ⟨r, cf, if rotMaske b c = 1 then
      some (negB b r != r.toNat.testBit (b.bits - 2)) else none⟩
  | .rcl =>
    let p := rclB b x cfAlt c
    ⟨p.1, p.2, if rotMaske b c = 1 then some (negB b p.1 != p.2)
      else none⟩
  | .rcr =>
    let p := rcrB b x cfAlt c
    ⟨p.1, p.2, if rotMaske b c = 1 then some (negB b x != p.2)
      else none⟩

/-- The evidence carries the §1 and §4 value. -/
theorem rotNachweis_wert (o : RotOp) (b : Breite) (x : Wort)
    (cfAlt : Bool) (c : Nat) :
    (match o with
      | .rol => (rotNachweis .rol b x cfAlt c).ergebnis = rolB b x c
      | .ror => (rotNachweis .ror b x cfAlt c).ergebnis = rorB b x c
      | .rcl => (rotNachweis .rcl b x cfAlt c).ergebnis = (rclB b x cfAlt c).1
      | .rcr => (rotNachweis .rcr b x cfAlt c).ergebnis = (rcrB b x cfAlt c).1) := by
  cases o <;> rfl

/-- Overflow evidence is defined exactly at a masked count of one. -/
theorem rotNachweis_ueberlauf (o : RotOp) (b : Breite) (x : Wort)
    (cfAlt : Bool) (c : Nat) :
    (rotMaske b c = 1 →
      (rotNachweis o b x cfAlt c).ueberlauf ≠ none) ∧
    (rotMaske b c ≠ 1 →
      (rotNachweis o b x cfAlt c).ueberlauf = none) := by
  cases o with
  | rol =>
    unfold rotNachweis
    constructor <;> intro hcond <;> simp [hcond]
  | ror =>
    unfold rotNachweis
    constructor <;> intro hcond <;> simp [hcond]
  | rcl =>
    unfold rotNachweis
    constructor <;> intro hcond <;> simp [hcond]
  | rcr =>
    unfold rotNachweis
    constructor <;> intro hcond <;> simp [hcond]

/-- A zero effective count rotates nothing (per operation kind). -/
def rotLeer (o : RotOp) (b : Breite) (c : Nat) : Bool :=
  match o with
  | .rol | .ror => decide (rotEff b c = 0)
  | .rcl | .rcr => decide (rclEff b c = 0)

/-- Validity of a rotate flag snapshot against the incoming flags:
    a zero effective count keeps every flag; otherwise CF is pinned
    to the evidence, SF, ZF, AF and PF are kept, and OF is pinned
    exactly at a masked count of one (free otherwise). -/
def RotGueltig (o : RotOp) (b : Breite) (n : RotNachweis) (c : Nat)
    (vor nach : Flags) : Prop :=
  if rotLeer o b c then nach = vor
  else nach.cf = n.trag ∧ nach.sf = vor.sf ∧ nach.zf = vor.zf ∧
    nach.af = vor.af ∧ nach.pf = vor.pf ∧
    (rotMaske b c = 1 → nach.of = n.ueberlauf.getD nach.of) ∧
    (n.ueberlauf = none → rotMaske b c ≠ 1)

/-- The executable flag snapshot: nothing on a zero count, else the
    evidence with the incoming OF bit where undefined. -/
def rotFlags (o : RotOp) (b : Breite) (x : Wort) (cfAlt : Bool)
    (vor : Flags) (c : Nat) : Flags :=
  if rotLeer o b c then vor
  else
    let n := rotNachweis o b x cfAlt c
    { cf := n.trag, pf := vor.pf, af := vor.af, zf := vor.zf,
      sf := vor.sf, of := n.ueberlauf.getD vor.of }

/-- A zero effective count keeps every flag. -/
theorem rotFlags_null (o : RotOp) (b : Breite) (x : Wort)
    (cfAlt : Bool) (vor : Flags) (c : Nat) (h : rotLeer o b c = true) :
    rotFlags o b x cfAlt vor c = vor := by
  unfold rotFlags
  rw [if_pos h]

/-- The snapshot satisfies its validity relation. -/
theorem rotFlags_gueltig (o : RotOp) (b : Breite) (x : Wort)
    (cfAlt : Bool) (vor : Flags) (c : Nat) :
    RotGueltig o b (rotNachweis o b x cfAlt c) c vor
      (rotFlags o b x cfAlt vor c) := by
  unfold RotGueltig rotFlags
  by_cases hleer : rotLeer o b c = true
  · rw [if_pos hleer, if_pos hleer]
  · rw [if_neg hleer, if_neg hleer]
    have hue := rotNachweis_ueberlauf o b x cfAlt c
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro h1
      have hne : (rotNachweis o b x cfAlt c).ueberlauf ≠ none :=
        hue.1 h1
      cases hueb : (rotNachweis o b x cfAlt c).ueberlauf with
      | some v =>
        simp only [hueb, Option.getD_some]
      | none => exact absurd hueb hne
    · intro hnone hcon
      exact hue.1 hcon hnone

/-- Pinned flag snapshots: ROL carries the wrapped bit out with the
    sign-change overflow, ROR carries the sign out, RCL and RCR carry
    the new through-carry with their one-count overflow rows. -/
theorem probe_rot_flags :
    (rotNachweis .rol .b8 0x81 false 1).trag = true ∧
    (rotNachweis .rol .b8 0x81 false 1).ueberlauf = some true ∧
    (rotNachweis .ror .b8 0x01 false 1).trag = true ∧
    (rotNachweis .ror .b8 0x01 false 1).ueberlauf = some true ∧
    (rotNachweis .rcl .b8 0xFF true 1).trag = true ∧
    (rotNachweis .rcl .b8 0xFF true 1).ueberlauf = some false ∧
    (rotNachweis .rcr .b8 0x01 false 1).trag = true ∧
    (rotNachweis .rcr .b8 0x01 false 1).ueberlauf = some true ∧
    (rotNachweis .rol .b8 0x81 false 2).ueberlauf = none ∧
    rotFlags .rol .b8 0x81 false zeugeFlags 0 = zeugeFlags := by
  decide

/- CUTS (checkpoint: value core only):    Proved here: rotate operation digits, Nat value core for ROL/ROR
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
