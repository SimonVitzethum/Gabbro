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

/-! ## 6. Canonical bytes: decode, encode, round trips, refusals.

    Opcodes D0 (byte, by one), D1 (wide, by one), D2 (byte, by CL),
    D3 (wide, by CL), C0 (byte, imm8) and C1 (wide, imm8) with
    digits 0 to 3 for ROL, ROR, RCL and RCR. The 66h prefix selects
    16 bits, REX.W selects 64, otherwise 32 (byte forms take no 66h
    and no REX.W). REX.R would rewrite the extension digit and
    REX.X has no SIB to extend, so both refuse; LOCK refuses.
    ModRM mod 3 is register-direct, mod 2 is base plus disp32 (the
    pilot canonical memory shape, with the SIB byte where the pilot
    has one); modes 0 and 1 refuse. The decoder parses bytes, never
    encode-equality. -/

/-- Count source: by one, by CL, or by an 8-bit immediate. -/
inductive RotQuelle where
  | eins | cl | imm8 (n : Nat)
  deriving DecidableEq, Repr

/-- Operand: register-direct or base-plus-displacement memory. -/
inductive RotOperand where
  | reg (dst : Register)
  | mem (base : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- One rotate form: operation, width, count source, operand. -/
structure RotForm where
  op : RotOp
  breite : Breite
  quelle : RotQuelle
  operand : RotOperand
  deriving DecidableEq, Repr

/-- A decoded rotate instruction with its consumed length. -/
structure RotDecodiert where
  befehl : RotForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- Parsed prefix: 16-bit override, REX bits, consumed length. -/
structure RotPraefix where
  op16 : Bool
  w : Nat
  r : Nat
  x : Nat
  b : Nat
  n : Nat
  deriving DecidableEq, Repr

/-- Prefix parse after an optional REX byte position: at most one
    REX follows (LOCK refuses, anything else takes no prefix). -/
def rotNimmRex (op16 : Bool) (n : Nat) :
    List Byte → Option (RotPraefix × List Byte)
  | [] => none
  | b1 :: rest =>
    if byteNat b1 == 240 then none
    else if byteNat b1 / 16 == 4 then
      let q := byteNat b1 - 64
      some (⟨op16, q / 8, q / 4 % 2, q / 2 % 2, q % 2, n + 1⟩, rest)
    else some (⟨op16, 0, 0, 0, 0, n⟩, b1 :: rest)

/-- Prefix parse: at most one 66h then at most one REX. LOCK
    refuses; a lone prefix byte is truncation. -/
def rotNimmPraefix : List Byte → Option (RotPraefix × List Byte)
  | [] => none
  | b1 :: rest =>
    if byteNat b1 == 240 then none
    else if byteNat b1 == 102 then rotNimmRex true 1 rest
    else rotNimmRex false 0 (b1 :: rest)

/-- Width from the prefix: byte forms take no 66h and no REX.W,
    wide forms take 16 bits on 66h, 64 on REX.W, else 32. -/
def rotBreite (is8 : Bool) (p : RotPraefix) : Option Breite :=
  if is8 then
    if p.op16 then none
    else if p.w == 1 then none
    else some .b8
  else
    if p.op16 then some .b16
    else if p.w == 1 then some .b64
    else some .b32

/-- ModRM body after an admitted prefix and width: register-direct
    or disp32 memory (with the pilot SIB byte), operation digit 0
    to 3, every other mode or digit refuses. Returns the operation,
    the operand, the ModRM tail length and the rest. -/
def rotModrm (p : RotPraefix) :
    List Byte → Option (RotOp × RotOperand × Nat × List Byte)
  | [] => none
  | m :: rest =>
    match feldRotOp (byteNat m / 8 % 8) with
    | none => none
    | some o =>
      if byteNat m / 64 == 3 then
        match codeReg (p.b * 8 + byteNat m % 8) with
        | some dst => some (o, .reg dst, 1, rest)
        | none => none
      else if byteNat m / 64 == 2 then
        let rm := byteNat m % 8
        if rm == 4 then
          match rest with
          | sib :: rest2 =>
            if byteNat sib == 36 then
              match parseLe32 rest2 with
              | some (d, rest3) =>
                match codeReg (p.b * 8 + rm) with
                | some base => some (o, .mem base d, 6, rest3)
                | none => none
              | none => none
            else none
          | [] => none
        else
          match parseLe32 rest with
          | some (d, rest2) =>
            match codeReg (p.b * 8 + rm) with
            | some base => some (o, .mem base d, 5, rest2)
            | none => none
          | none => none
      else none

/-- Group decode for the by-one and by-CL opcodes: REX.R would
    rewrite the digit and REX.X has no SIB, so both refuse. -/
def rotGruppe (p : RotPraefix) (is8 : Bool) (q : RotQuelle) :
    List Byte → Option (RotDecodiert × List Byte)
  | bs =>
    if p.r == 1 || p.x == 1 then none
    else match rotBreite is8 p with
    | none => none
    | some b =>
      match rotModrm p bs with
      | some (o, operand, ml, rest) =>
        some (⟨⟨o, b, q, operand⟩, p.n + 1 + ml⟩, rest)
      | none => none

/-- Group decode for the imm8 opcodes: one immediate byte follows
    the ModRM tail. -/
def rotGruppeImm (p : RotPraefix) (is8 : Bool) :
    List Byte → Option (RotDecodiert × List Byte)
  | bs =>
    if p.r == 1 || p.x == 1 then none
    else match rotBreite is8 p with
    | none => none
    | some b =>
      match rotModrm p bs with
      | some (o, operand, ml, ib :: rest) =>
        some (⟨⟨o, b, .imm8 (byteNat ib), operand⟩, p.n + 2 + ml⟩, rest)
      | _ => none

/-- Opcode dispatch after the prefix: D0 through D3 and C0, C1;
    anything else refuses without touching later bytes. -/
def rotNachOpcode (p : RotPraefix) :
    List Byte → Option (RotDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    let n := byteNat op
    if n == 208 then rotGruppe p true .eins rest
    else if n == 209 then rotGruppe p false .eins rest
    else if n == 210 then rotGruppe p true .cl rest
    else if n == 211 then rotGruppe p false .cl rest
    else if n == 192 then rotGruppeImm p true rest
    else if n == 193 then rotGruppeImm p false rest
    else none

/-- Full decode: prefix then opcode, ModRM and immediate. -/
def decodeRot : List Byte → Option (RotDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match rotNimmPraefix (b :: rest) with
    | none => none
    | some (p, tail) => rotNachOpcode p tail

/-- Group opcode byte of a width and count source. -/
def rotOpcode (b : Breite) (q : RotQuelle) : Nat :=
  match b, q with
  | .b8, .eins => 208
  | .b8, .cl => 210
  | .b8, .imm8 _ => 192
  | .b16, .eins => 209
  | .b16, .cl => 211
  | .b16, .imm8 _ => 193
  | .b32, .eins => 209
  | .b32, .cl => 211
  | .b32, .imm8 _ => 193
  | .b64, .eins => 209
  | .b64, .cl => 211
  | .b64, .imm8 _ => 193

/-- Canonical prefix bytes of a width over a register: 66h for 16
    bits, REX.W for 64, REX.B where the code needs it. -/
def rotPraefixBytes (b : Breite) (r : Register) : List Byte :=
  match b with
  | .b8 => if regHigh r == 0 then [] else [natByte (64 + regHigh r)]
  | .b16 => [natByte 102] ++
      (if regHigh r == 0 then [] else [natByte (64 + regHigh r)])
  | .b32 => if regHigh r == 0 then [] else [natByte (64 + regHigh r)]
  | .b64 => [natByte (72 + regHigh r)]

/-- Immediate tail of a count source (one byte or nothing). -/
def rotImmTail : RotQuelle → List Byte
  | .imm8 n => [natByte n]
  | _ => []

/-- SIB tail of a base register (the pilot byte where needed). -/
def rotSibTail (base : Register) : List Byte :=
  if regLow base == 4 then [natByte 36] else []

/-- Canonical bytes of one rotate form. -/
def rotEncode : RotForm → List Byte
  | ⟨o, b, q, .reg dst⟩ =>
    rotPraefixBytes b dst ++ [natByte (rotOpcode b q),
      natByte (192 + 8 * rotOpFeld o + regLow dst)] ++ rotImmTail q
  | ⟨o, b, q, .mem base d⟩ =>
    rotPraefixBytes b base ++ [natByte (rotOpcode b q),
      natByte (128 + 8 * rotOpFeld o + regLow base)] ++
      rotSibTail base ++ leBytes32 d ++ rotImmTail q

/-- Decoded length of one rotate form. -/
def rotLaenge : RotForm → Nat
  | ⟨_, b, q, .reg dst⟩ =>
    (rotPraefixBytes b dst).length + 2 + (rotImmTail q).length
  | ⟨_, b, q, .mem base _⟩ =>
    (rotPraefixBytes b base).length + 2 +
      (rotSibTail base).length + 4 + (rotImmTail q).length

/-- The encoding is exactly the decoded length. -/
theorem rotEncode_laenge (f : RotForm) :
    (rotEncode f).length = rotLaenge f := by
  cases f with
  | mk o b q operand =>
    cases b <;> cases q <;> cases operand with
    | reg dst => cases dst <;> rfl
    | mem base d => cases base <;> rfl

/-- A canonical prefix is at most two bytes. -/
theorem rotPraefixBytes_len (b : Breite) (r : Register) :
    (rotPraefixBytes b r).length ≤ 2 := by
  cases b <;> cases r <;> decide

/-- An immediate tail is at most one byte. -/
theorem rotImmTail_len (q : RotQuelle) :
    (rotImmTail q).length ≤ 1 := by
  cases q with
  | eins => exact Nat.zero_le _
  | cl => exact Nat.zero_le _
  | imm8 n => exact Nat.le_refl _

/-- A SIB tail is at most one byte. -/
theorem rotSibTail_len (base : Register) :
    (rotSibTail base).length ≤ 1 := by
  cases base <;> decide

/-- Every rotate encoding fits the 1 to 15 instruction bound. -/
theorem rotEncode_len_ok (f : RotForm) :
    1 ≤ (rotEncode f).length ∧ (rotEncode f).length ≤ 15 := by
  rw [rotEncode_laenge]
  cases f with
  | mk o b q operand =>
    cases operand with
    | reg dst =>
      have hp := rotPraefixBytes_len b dst
      have hi := rotImmTail_len q
      simp only [rotLaenge]
      omega
    | mem base d =>
      have hp := rotPraefixBytes_len b base
      have hs := rotSibTail_len base
      have hi := rotImmTail_len q
      simp only [rotLaenge]
      omega

/-- The decoded length passes the length guard. -/
theorem rotLaenge_ok (f : RotForm) :
    laengeOk (rotLaenge f) = true := by
  cases f with
  | mk o b q operand =>
    cases b <;> cases q <;> cases operand with
    | reg dst => cases dst <;> rfl
    | mem base d => cases base <;> rfl

/-! ## 7. Round trips, pins and planted refusals.

    Decoding inverts encoding with the suffix: register forms
    generically (immediate forms over a byte premise), memory forms
    through the little-endian displacement. Shift digits, foreign
    modes, LOCK, stray REX bits and truncations refuse by name. -/

/-- Round trip for by-one register forms, over any suffix. -/
theorem rotRoundtrip_reg_eins (o : RotOp) (b : Breite) (dst : Register)
    (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, b, .eins, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, b, .eins, .reg dst⟩,
        rotLaenge ⟨o, b, .eins, .reg dst⟩⟩, suffix) := by
  cases o <;> cases b <;> cases dst <;> rfl

/-- Round trip for by-CL register forms, over any suffix. -/
theorem rotRoundtrip_reg_cl (o : RotOp) (b : Breite) (dst : Register)
    (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, b, .cl, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, b, .cl, .reg dst⟩,
        rotLaenge ⟨o, b, .cl, .reg dst⟩⟩, suffix) := by
  cases o <;> cases b <;> cases dst <;> rfl

/-- Round trip for immediate register forms over a byte premise,
    8-bit width. -/
theorem rotRoundtrip_reg_imm8 (o : RotOp) (dst : Register)
    (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b8, .imm8 n, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, .b8, .imm8 n, .reg dst⟩,
        rotLaenge ⟨o, .b8, .imm8 n, .reg dst⟩⟩, suffix) := by
  cases o <;> cases dst <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotLaenge, (byteNat_natByte_of_lt n h)]

/-- Round trip for immediate register forms over a byte premise,
    16-bit width. -/
theorem rotRoundtrip_reg_imm16 (o : RotOp) (dst : Register)
    (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b16, .imm8 n, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, .b16, .imm8 n, .reg dst⟩,
        rotLaenge ⟨o, .b16, .imm8 n, .reg dst⟩⟩, suffix) := by
  cases o <;> cases dst <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotLaenge, (byteNat_natByte_of_lt n h)]

/-- Round trip for immediate register forms over a byte premise,
    32-bit width. -/
theorem rotRoundtrip_reg_imm32 (o : RotOp) (dst : Register)
    (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b32, .imm8 n, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, .b32, .imm8 n, .reg dst⟩,
        rotLaenge ⟨o, .b32, .imm8 n, .reg dst⟩⟩, suffix) := by
  cases o <;> cases dst <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotLaenge, (byteNat_natByte_of_lt n h)]

/-- Round trip for immediate register forms over a byte premise,
    64-bit width. -/
theorem rotRoundtrip_reg_imm64 (o : RotOp) (dst : Register)
    (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b64, .imm8 n, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, .b64, .imm8 n, .reg dst⟩,
        rotLaenge ⟨o, .b64, .imm8 n, .reg dst⟩⟩, suffix) := by
  cases o <;> cases dst <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotLaenge, (byteNat_natByte_of_lt n h)]

/-! ## 7b. Memory round trips through the displacement.

    Register and memory share the ModRM layer; memory adds the
    little-endian disp32 (and the pilot SIB byte) parsed back by
    `parseLe32_cons`. One theorem per width and count source keeps
    each command inside the heartbeat budget. -/

/-- Round trip for by-one memory forms, 8-bit width. -/
theorem rotRoundtrip_mem_eins8 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b8, .eins, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b8, .eins, .mem base d⟩,
        rotLaenge ⟨o, .b8, .eins, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-one memory forms, 16-bit width. -/
theorem rotRoundtrip_mem_eins16 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b16, .eins, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b16, .eins, .mem base d⟩,
        rotLaenge ⟨o, .b16, .eins, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-one memory forms, 32-bit width. -/
theorem rotRoundtrip_mem_eins32 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b32, .eins, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b32, .eins, .mem base d⟩,
        rotLaenge ⟨o, .b32, .eins, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-one memory forms, 64-bit width. -/
theorem rotRoundtrip_mem_eins64 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b64, .eins, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b64, .eins, .mem base d⟩,
        rotLaenge ⟨o, .b64, .eins, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-CL memory forms, 8-bit width. -/
theorem rotRoundtrip_mem_cl8 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b8, .cl, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b8, .cl, .mem base d⟩,
        rotLaenge ⟨o, .b8, .cl, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-CL memory forms, 16-bit width. -/
theorem rotRoundtrip_mem_cl16 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b16, .cl, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b16, .cl, .mem base d⟩,
        rotLaenge ⟨o, .b16, .cl, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-CL memory forms, 32-bit width. -/
theorem rotRoundtrip_mem_cl32 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b32, .cl, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b32, .cl, .mem base d⟩,
        rotLaenge ⟨o, .b32, .cl, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for by-CL memory forms, 64-bit width. -/
theorem rotRoundtrip_mem_cl64 (o : RotOp) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b64, .cl, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b64, .cl, .mem base d⟩,
        rotLaenge ⟨o, .b64, .cl, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppe, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons]

/-- Round trip for immediate memory forms, 8-bit width. -/
theorem rotRoundtrip_mem_imm8 (o : RotOp) (base : Register)
    (d : BitVec 32) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b8, .imm8 n, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b8, .imm8 n, .mem base d⟩,
        rotLaenge ⟨o, .b8, .imm8 n, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons, (byteNat_natByte_of_lt n h)]

/-- Round trip for immediate memory forms, 16-bit width. -/
theorem rotRoundtrip_mem_imm16 (o : RotOp) (base : Register)
    (d : BitVec 32) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b16, .imm8 n, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b16, .imm8 n, .mem base d⟩,
        rotLaenge ⟨o, .b16, .imm8 n, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons, (byteNat_natByte_of_lt n h)]

/-- Round trip for immediate memory forms, 32-bit width. -/
theorem rotRoundtrip_mem_imm32 (o : RotOp) (base : Register)
    (d : BitVec 32) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b32, .imm8 n, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b32, .imm8 n, .mem base d⟩,
        rotLaenge ⟨o, .b32, .imm8 n, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons, (byteNat_natByte_of_lt n h)]

/-- Round trip for immediate memory forms, 64-bit width. -/
theorem rotRoundtrip_mem_imm64 (o : RotOp) (base : Register)
    (d : BitVec 32) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeRot (rotEncode ⟨o, .b64, .imm8 n, .mem base d⟩ ++ suffix) =
      some (⟨⟨o, .b64, .imm8 n, .mem base d⟩,
        rotLaenge ⟨o, .b64, .imm8 n, .mem base d⟩⟩, suffix) := by
  cases o <;> cases base <;>
    simp [rotEncode, decodeRot, rotNimmPraefix, rotNimmRex,
      rotNachOpcode, rotGruppeImm, rotModrm, rotBreite, feldRotOp,
      rotOpFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      rotOpcode, rotImmTail, rotSibTail, rotLaenge, leBytes32,
      parseLe32_cons, (byteNat_natByte_of_lt n h)]

/-- Pinned bytes: ROL r/m8 by one over rax. -/
theorem pin_rot_rol8_eins :    decodeRot [natByte 208, natByte 192] =
      some ((⟨⟨.rol, .b8, .eins, .reg .rax⟩, 2⟩ : RotDecodiert), []) := by
  decide

/-- Pinned bytes: ROR r9 by CL at 64 bits. -/
theorem pin_rot_ror64_cl :
    decodeRot [natByte 73, natByte 211, natByte 201] =
      some ((⟨⟨.ror, .b64, .cl, .reg .r9⟩, 3⟩ : RotDecodiert), []) := by
  decide

/-- Pinned bytes: RCL edx by imm8 5 at 16 bits. -/
theorem pin_rot_rcl16_imm :
    decodeRot [natByte 102, natByte 193, natByte 210, natByte 5] =
      some ((⟨⟨.rcl, .b16, .imm8 5, .reg .rdx⟩, 4⟩ : RotDecodiert),
        []) := by
  decide

/-- Pinned bytes: RCR dword at rbx plus 16 by one. -/
theorem pin_rot_rcr32_mem :
    decodeRot [natByte 209, natByte 155, natByte 16, natByte 0,
      natByte 0, natByte 0] =
      some ((⟨⟨.rcr, .b32, .eins,
        .mem .rbx (BitVec.ofNat 32 16)⟩, 6⟩ : RotDecodiert), []) := by
  decide

/-- Pinned bytes: ROL r8 by one at 64 bits. -/
theorem pin_rot_rol64_weit :
    decodeRot [natByte 73, natByte 209, natByte 192] =
      some ((⟨⟨.rol, .b64, .eins, .reg .r8⟩, 3⟩ : RotDecodiert), []) := by
  decide

/-- Planted refusal: LOCK stays refused. -/
theorem rot_nichts_lock :
    decodeRot [natByte 240, natByte 209, natByte 192] = none := by
  decide

/-- Planted refusal: the shift digit stays a shift row, not a rotate. -/
theorem rot_nichts_digit_vier :
    decodeRot [natByte 208, natByte 224] = none := by
  decide

/-- Planted refusal: mod 0 is no canonical rotate memory. -/
theorem rot_nichts_modus_null :
    decodeRot [natByte 209, natByte 0] = none := by
  decide

/-- Planted refusal: mod 1 is no canonical rotate memory. -/
theorem rot_nichts_modus_eins :
    decodeRot [natByte 209, natByte 64] = none := by
  decide

/-- Planted refusal: 66h selects no byte form. -/
theorem rot_nichts_sechzehn_bei_byte :
    decodeRot [natByte 102, natByte 208, natByte 192] = none := by
  decide

/-- Planted refusal: REX.W promotes no byte form. -/
theorem rot_nichts_rex_w_bei_byte :
    decodeRot [natByte 72, natByte 208, natByte 192] = none := by
  decide

/-- Planted refusal: REX.R would rewrite the extension digit. -/
theorem rot_nichts_rex_r :
    decodeRot [natByte 76, natByte 209, natByte 192] = none := by
  decide

/-- Planted refusal: REX.X has no SIB to extend here. -/
theorem rot_nichts_rex_x :
    decodeRot [natByte 66, natByte 209, natByte 192] = none := by
  decide

/-- Planted refusal: an unknown opcode refuses. -/
theorem rot_nichts_unbekannt : decodeRot [natByte 255] = none := by
  decide

/-- Planted refusal: the empty input decodes to nothing. -/
theorem rot_nichts_leer : decodeRot [] = none := rfl

/-- Planted refusal: an opcode without ModRM is truncated. -/
theorem rot_nichts_opcode_allein :
    decodeRot [natByte 209] = none := by
  decide

/-- Planted refusal: an imm8 form without its byte is truncated. -/
theorem rot_nichts_imm_kurz :
    decodeRot [natByte 193, natByte 224] = none := by
  decide

/-! ## 8. Family step: register forms execute, memory forms refuse.

    The register path installs the §5 snapshot with the
    architectural merge (`mergeRegNarrow`: 8/16-bit merging,
    32-bit zero-extension, 64-bit whole); a zero effective count
    advances RIP with flags untouched; memory never moves here
    (register plug only). Memory forms refuse: their values live
    beside the step through the same evidence, carried to bytes
    by `rotMemIssue` in §11, never by the register plug. -/

/-- Raw count of a form in a state: one, the low CL byte, or the
    immediate. -/
def rotZaehler (f : RotForm) (s : Zustand) : Nat :=
  match f.quelle with
  | .eins => 1
  | .cl => (s.register .rcx).toNat % 256
  | .imm8 n => n

/-- Family outcome: the successor state or explicit refusal.
    Rotates take no fault: there is no halt arm. -/
inductive RotErgebnis where
  | ok : Zustand → RotErgebnis
  | verweigert : RotErgebnis

/-- One family step: refuse on bad or mismatched length; memory
    forms refuse (register plug only); a zero effective count
    advances RIP with flags untouched; otherwise the evidence
    value merged with the §5 snapshot. -/
def rotSchritt (d : RotDecodiert) (s : Zustand) : RotErgebnis :=
  match laengeOk d.laenge with
  | false => .verweigert
  | true =>
    if d.laenge == rotLaenge d.befehl then
      match d.befehl.operand with
      | .mem _ _ => .verweigert
      | .reg dst =>
        let c := rotZaehler d.befehl s
        let n := rotNachweis d.befehl.op d.befehl.breite
          (s.register dst) s.flags.cf c
        let nach := ripNach s.rip d.laenge
        if rotLeer d.befehl.op d.befehl.breite c then
          .ok ({ s with rip := nach })
        else
          .ok (schrittRegister s nach
            (rotFlags d.befehl.op d.befehl.breite (s.register dst)
              s.flags.cf s.flags c)
            dst (mergeRegNarrow d.befehl.breite (s.register dst)
              n.ergebnis))
    else .verweigert

/-- Register success: merged value, snapshot flags, advanced RIP. -/
theorem rot_reg_erfolg (d : RotDecodiert) (s : Zustand) (dst : Register)
    (hok : laengeOk d.laenge = true)
    (hlen : (d.laenge == rotLaenge d.befehl) = true)
    (hop : d.befehl.operand = .reg dst)
    (hne : rotLeer d.befehl.op d.befehl.breite (rotZaehler d.befehl s) =
      false) :
    rotSchritt d s = .ok (schrittRegister s (ripNach s.rip d.laenge)
      (rotFlags d.befehl.op d.befehl.breite (s.register dst) s.flags.cf
        s.flags (rotZaehler d.befehl s))
      dst (mergeRegNarrow d.befehl.breite (s.register dst)
        (rotNachweis d.befehl.op d.befehl.breite (s.register dst)
          s.flags.cf (rotZaehler d.befehl s)).ergebnis)) := by
  unfold rotSchritt
  simp [hok, hlen, hop, hne]

/-- Zero-count success: RIP advances, flags and registers kept. -/
theorem rot_leer_rip (d : RotDecodiert) (s : Zustand) (dst : Register)
    (hok : laengeOk d.laenge = true)
    (hlen : (d.laenge == rotLaenge d.befehl) = true)
    (hop : d.befehl.operand = .reg dst)
    (hle : rotLeer d.befehl.op d.befehl.breite (rotZaehler d.befehl s) =
      true) :
    rotSchritt d s = .ok ({ s with rip := ripNach s.rip d.laenge }) := by
  unfold rotSchritt
  simp [hok, hlen, hop, hle]

/-- A memory operand refuses the register step. -/
theorem rot_mem_verweigert (d : RotDecodiert) (s : Zustand)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : (d.laenge == rotLaenge d.befehl) = true)
    (hop : d.befehl.operand = .mem base disp) :
    rotSchritt d s = .verweigert := by
  unfold rotSchritt
  simp [hok, hlen, hop]

/-- A bad decode length refuses every rotate form. -/
theorem rot_laenge_misslungen (d : RotDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) :
    rotSchritt d s = .verweigert := by
  unfold rotSchritt
  simp [h]

/-- A mismatched length refuses (checked data, never trusted). -/
theorem rot_laenge_falsch (d : RotDecodiert) (s : Zustand)
    (hok : laengeOk d.laenge = true)
    (h : (d.laenge == rotLaenge d.befehl) = false) :
    rotSchritt d s = .verweigert := by
  unfold rotSchritt
  simp [hok, h]

/-- A successful rotate step leaves canonical memory alone. -/
theorem rotSchritt_speicher (d : RotDecodiert) (s s' : Zustand)
    (h : rotSchritt d s = .ok s') :
    s'.speicher = s.speicher := by
  by_cases hok : laengeOk d.laenge = true
  · by_cases hlen : (d.laenge == rotLaenge d.befehl) = true
    · cases hop : d.befehl.operand with
      | reg dst =>
        by_cases hle : rotLeer d.befehl.op d.befehl.breite
            (rotZaehler d.befehl s) = true
        · have e := rot_leer_rip d s dst hok hlen hop hle
          rw [e] at h
          cases h
          rfl
        · have hleF : rotLeer d.befehl.op d.befehl.breite
              (rotZaehler d.befehl s) = false := by
            cases hb : rotLeer d.befehl.op d.befehl.breite
                (rotZaehler d.befehl s) with
            | true => exact absurd hb hle
            | false => rfl
          have e := rot_reg_erfolg d s dst hok hlen hop hleF
          rw [e] at h
          cases h
          exact schrittRegister_speicher _ _ _ _ _
      | mem base disp =>
        have e := rot_mem_verweigert d s base disp hok hlen hop
        rw [e] at h
        cases h
    · have hlenF : (d.laenge == rotLaenge d.befehl) = false := by
        cases hb : (d.laenge == rotLaenge d.befehl) with
        | true => exact absurd hb hlen
        | false => rfl
      have e := rot_laenge_falsch d s hok hlenF
      rw [e] at h
      cases h
  · have hokF : laengeOk d.laenge = false := by
      cases hb : laengeOk d.laenge with
      | true => exact absurd hb hok
      | false => rfl
    have e := rot_laenge_misslungen d s hokF
    rw [e] at h
    cases h

/-! ## 8b. Memory values through the same evidence.

    A memory form over an explicitly loaded word installs exactly
    the evidence the register path installs, merged for writeback;
    a zero effective count installs nothing. `rotMemIssue` carries
    the merged bytes as TSO events (see §11); the register plug
    never sees them. -/

/-- One memory-form rotate over an explicitly loaded word. -/
def rotMemNachweis (d : RotDecodiert) (s : Zustand)
    (w : Wort) : Option (Wort × Flags) :=
  match d.befehl.operand with
  | .reg _ => none
  | .mem _ _ =>
    if d.laenge == rotLaenge d.befehl then
      let c := rotZaehler d.befehl s
      let n := rotNachweis d.befehl.op d.befehl.breite w s.flags.cf c
      if rotLeer d.befehl.op d.befehl.breite c then none
      else some (mergeRegNarrow d.befehl.breite w n.ergebnis,
        rotFlags d.befehl.op d.befehl.breite w s.flags.cf s.flags c)
    else none

/-- A register operand is no memory form. -/
theorem rotMemNachweis_reg_nichts (d : RotDecodiert) (s : Zustand)
    (w : Wort) (dst : Register)
    (hop : d.befehl.operand = .reg dst) :
    rotMemNachweis d s w = none := by
  unfold rotMemNachweis
  simp [hop]

/-- Memory success: merged value with the snapshot flags. -/
theorem rot_mem_erfolg (d : RotDecodiert) (s : Zustand) (w : Wort)
    (base : Register) (disp : BitVec 32)
    (hlen : (d.laenge == rotLaenge d.befehl) = true)
    (hop : d.befehl.operand = .mem base disp)
    (hne : rotLeer d.befehl.op d.befehl.breite (rotZaehler d.befehl s) =
      false) :
    rotMemNachweis d s w = some (mergeRegNarrow d.befehl.breite w
      (rotNachweis d.befehl.op d.befehl.breite w s.flags.cf
        (rotZaehler d.befehl s)).ergebnis,
      rotFlags d.befehl.op d.befehl.breite w s.flags.cf s.flags
        (rotZaehler d.befehl s)) := by
  unfold rotMemNachweis
  simp [hop, hlen, hne]

/-- Issue the low bytes of a word as TSO events, oldest first. -/
def rotIssueKette (s : TSOZustand) (c : Nat)
    (l : List TSOEintrag) : Option TSOZustand :=
  match l with
  | [] => some s
  | e :: rest =>
    match issueByte s c e.addr e.wert with
    | none => none
    | some s' => rotIssueKette s' c rest

/-- A memory rotate result enters the TSO buffer byte by byte;
    canonical memory moves only at drain, never here. -/
def rotMemIssue (s : TSOZustand) (c : Nat) (a : Adresse) (b : Breite)
    (v : Wort) : Option TSOZustand :=
  rotIssueKette s c (List.take b.bytes (wortEintraege a v))

/-! ## 9. Unified dispatcher: the accepted chain first.

    The dispatcher runs the unified `decodeExt` first and the
    rotate decoder only where it refuses: no pilot or extension
    form is shadowed, overlapping shift rows keep their unified
    arm, new rotate rows take the rotate arm. -/

/-- Unified dispatcher instruction: the accepted unified chain
    first, the rotate family only where it refuses. -/
inductive RotHwInstr where
  | ext : ExtInstr → RotHwInstr
  | rot : RotDecodiert → RotHwInstr
  deriving DecidableEq, Repr

/-- Dispatcher: the unified decoder first, the rotate decoder only
    where the unified chain refuses. No pilot form is shadowed. -/
def decodeRotHw : List Byte → Option (RotHwInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match decodeRot bs with
      | some (d, rest) => some (.rot d, rest)
      | none => none

/-- Consumed length of one dispatcher instruction. -/
def rotHwLen : RotHwInstr → Nat
  | .ext i => extLen i
  | .rot d => d.laenge

/-- The dispatcher agrees with the unified chain wherever it
    accepts: no pilot or extension form is shadowed. -/
theorem decodeRotHw_prefers_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeRotHw bs = some (.ext i, rest) := by
  unfold decodeRotHw
  rw [h]

/-- Where the unified chain refuses, a covered rotate row is taken. -/
theorem decodeRotHw_rot (bs : List Byte) (d : RotDecodiert)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeRot bs = some (d, rest)) :
    decodeRotHw bs = some (.rot d, rest) := by
  unfold decodeRotHw
  rw [h1, h2]

/-- Where both chains refuse, the dispatcher refuses. -/
theorem decodeRotHw_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeRot bs = none) :
    decodeRotHw bs = none := by
  unfold decodeRotHw
  rw [h1, h2]

/-! ## 9b. No shadowing: the unified chain refuses the new rows.

    The rotate rows below are refused by the whole unified chain,
    so the rotate arm takes them exactly once; the overlapping
    shift row keeps its unified arm. -/

theorem ext_weist_rotrol8_zurueck :
    decodeExt [natByte 208, natByte 192] = none := by
  decide

theorem ext_weist_rotror64_zurueck :
    decodeExt [natByte 73, natByte 211, natByte 201] = none := by
  decide

theorem ext_weist_rotrcl16_zurueck :
    decodeExt [natByte 102, natByte 193, natByte 210, natByte 5] = none := by
  decide

theorem ext_weist_rotmem32_zurueck :
    decodeExt [natByte 209, natByte 155, natByte 16, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

theorem ext_weist_rotrol64_zurueck :
    decodeExt [natByte 73, natByte 209, natByte 192] = none := by
  decide

/-! ## 9c. Dispatcher pins: new rows take the rotate arm.

    The pilot row goes through unchanged, overlapping shift rows
    keep the unified arm, planted refusals stay refused. -/

/-- Pin: the pilot row goes through unchanged. -/
theorem pin_rotHw_pilot_ret :
    decodeRotHw (encode .ret) =
      some (.ext (.pilot ⟨.ret, 1⟩), []) :=
  decodeRotHw_prefers_ext _ _ _ pin_ext_pilot_ret

/-- Pin: the 8-bit ROL row takes the rotate arm. -/
theorem pin_rotHw_rol8 :
    decodeRotHw [natByte 208, natByte 192] =
      some (.rot (⟨⟨.rol, .b8, .eins, .reg .rax⟩, 2⟩ : RotDecodiert),
        []) :=
  decodeRotHw_rot _ _ _ ext_weist_rotrol8_zurueck pin_rot_rol8_eins

/-- Pin: the 64-bit ROR-by-CL row takes the rotate arm. -/
theorem pin_rotHw_ror64 :
    decodeRotHw [natByte 73, natByte 211, natByte 201] =
      some (.rot (⟨⟨.ror, .b64, .cl, .reg .r9⟩, 3⟩ : RotDecodiert),
        []) :=
  decodeRotHw_rot _ _ _ ext_weist_rotror64_zurueck pin_rot_ror64_cl

/-- Pin: the 16-bit RCL-imm row takes the rotate arm. -/
theorem pin_rotHw_rcl16 :
    decodeRotHw [natByte 102, natByte 193, natByte 210, natByte 5] =
      some (.rot (⟨⟨.rcl, .b16, .imm8 5, .reg .rdx⟩, 4⟩ : RotDecodiert),
        []) :=
  decodeRotHw_rot _ _ _ ext_weist_rotrcl16_zurueck pin_rot_rcl16_imm

/-- Pin: the 32-bit RCR memory row takes the rotate arm. -/
theorem pin_rotHw_rcr32 :
    decodeRotHw [natByte 209, natByte 155, natByte 16, natByte 0,
      natByte 0, natByte 0] =
      some (.rot (⟨⟨.rcr, .b32, .eins,
        .mem .rbx (BitVec.ofNat 32 16)⟩, 6⟩ : RotDecodiert), []) :=
  decodeRotHw_rot _ _ _ ext_weist_rotmem32_zurueck
    pin_rot_rcr32_mem

/-- Pin: the overlapping shift row keeps the unified arm. -/
theorem pin_rotHw_ext_shift :
    decodeRotHw [natByte 72, natByte 193, natByte 224, natByte 1] =
      some (.ext (.shift ⟨.imm .shl .rax 1, 4⟩), []) := by
  apply decodeRotHw_prefers_ext
  decide

/-- Planted refusal: LOCK stays refused through the dispatcher. -/
theorem rotHw_nichts_lock :
    decodeRotHw [natByte 240, natByte 209, natByte 192] = none := by
  apply decodeRotHw_nichts
  · decide
  · exact rot_nichts_lock

/-! ## 10. Machine adapter: the rotate family on the coherent machine.

    The producer plug instantiates `HwAdapter RotDecodiert`: a
    successful register step re-embeds core data over the shared
    memory; memory forms, traps and refusals admit no successor
    state. The machine outcome reuses the accepted `HwRegAusgang`
    (success re-embeds, refusal is `verweigert`); rotates take no
    fault, so `halt` never occurs. -/

/-- The rotate plug: one checked rotate event step on the coherent
    machine. `none` = memory form, trap or refusal, never a silent
    successor. -/
def adapterRot : HwAdapter RotDecodiert :=
  ⟨fun m c d =>
    match rotSchritt d (projZustand m c) with
    | .ok s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | .verweigert => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterRot_wf (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterRot).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterRot at h
  simp only at h
  cases hsch : rotSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | verweigert =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the family step
    succeeds, with the successor core data re-embedded. -/
theorem adapterRot_ok (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) (s' : Zustand)
    (h : rotSchritt d (projZustand m c) = .ok s') :
    (adapterRot).schritt m c d =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterRot
  simp only [h]

/-- The successor core sees the family successor registers over
    the shared memory. -/
theorem adapterRot_proj (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) (s' : Zustand)
    (h : rotSchritt d (projZustand m c) = .ok s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne c).register =
      s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem = m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := rotSchritt_speicher d (projZustand m c) s' h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- A bad decode length admits no adapter step. -/
theorem adapterRot_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : RotDecodiert)
    (h : laengeOk d.laenge = false) :
    (adapterRot).schritt m c d = none := by
  have hstep := rot_laenge_misslungen d (projZustand m c) h
  unfold adapterRot
  simp only [hstep]

/-- A memory operand admits no adapter step: memory forms are TSO
    events (§8b, §11), never the register plug. -/
theorem adapterRot_verweigert_bei_mem (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) (base : Register) (disp : BitVec 32)
    (hop : d.befehl.operand = .mem base disp) :
    (adapterRot).schritt m c d = none := by
  have hstep : rotSchritt d (projZustand m c) = .verweigert := by
    cases hok : laengeOk d.laenge with
    | false => exact rot_laenge_misslungen d (projZustand m c) hok
    | true =>
      cases hlen : (d.laenge == rotLaenge d.befehl) with
      | true =>
        exact rot_mem_verweigert d (projZustand m c) base disp hok hlen hop
      | false => exact rot_laenge_falsch d (projZustand m c) hok hlen
  unfold adapterRot
  simp only [hstep]

/-- One rotate machine step on core `c`: the family step on the
    core projection, re-embedded on success. -/
def rotHwRegSchritt (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) : HwRegAusgang :=
  match rotSchritt d (projZustand m c) with
  | .ok s' => .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
  | .verweigert => .verweigert

/-- Selection: a successful family step continues on the machine. -/
theorem rotHwRegSchritt_weiter (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) (s' : Zustand)
    (h : rotSchritt d (projZustand m c) = .ok s') :
    rotHwRegSchritt m c d =
      .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  have e : rotHwRegSchritt m c d =
      match rotSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .verweigert => .verweigert := rfl
  rw [e, h]

/-- Selection: family refusal is machine refusal. -/
theorem rotHwRegSchritt_verweigert (m : HwMaschine) (c : Nat)
    (d : RotDecodiert)
    (h : rotSchritt d (projZustand m c) = .verweigert) :
    rotHwRegSchritt m c d = .verweigert := by
  have e : rotHwRegSchritt m c d =
      match rotSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .verweigert => .verweigert := rfl
  rw [e, h]

/-- Rotates never halt: the outcome has no fault arm. -/
theorem rotHwRegSchritt_nie_halt (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) :
    rotHwRegSchritt m c d ≠ .halt := by
  cases h : rotSchritt d (projZustand m c) with
  | ok s' =>
    have e := rotHwRegSchritt_weiter m c d s' h
    rw [e]
    intro hc
    cases hc
  | verweigert =>
    have e := rotHwRegSchritt_verweigert m c d h
    rw [e]
    intro hc
    cases hc

/-- A machine continue preserves well-formedness. -/
theorem rotHwRegSchritt_weiter_wf (m : HwMaschine) (c : Nat)
    (d : RotDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : rotHwRegSchritt m c d = .weiter m') :
    HwWf m' := by
  have e : rotHwRegSchritt m c d =
      match rotSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .verweigert => .verweigert := rfl
  rw [e] at h
  cases hsch : rotSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | verweigert =>
    rw [hsch] at h
    simp only at h
    cases h

/-! ## 11. Joint witness: two cores, family steps, buffered store.

    Core 0 rotates ROL `0x81` by imm8 1 (value `0x03`, carry out,
    one-count overflow); core 1 rotates ROR `0x01` by imm8 1
    (value `0x80`, carry out, one-count overflow); a memory form
    computes its evidence over a loaded word and both result bytes
    issue through `rotMemIssue`, each visible only to its owner by
    forwarding; the drain of core 0 changes actual shared memory
    from 0 to 3. A bad length refuses the machine step and a
    memory operand refuses the adapter beside the run. Every claim
    projects to plain values before `decide` (machines contain
    functions); the general equations pin the full states. -/

/-- Witness registers core 0: ROL source in rax. -/
def rotHwWitReg0 : Register → Wort := fun q =>
  if q = Register.rax then 0x81
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness registers core 1: ROR source in rbx. -/
def rotHwWitReg1 : Register → Wort := fun q =>
  if q = Register.rbx then 0x01
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness cores over the register files: both cores run at 4096. -/
def rotHwWitKern : Nat → HwKern
  | 0 => ⟨rotHwWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨rotHwWitReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon. -/
def rotHwWitStart : HwMaschine :=
  ⟨zeugenSpeicher, rotHwWitKern, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem rotHwWitStart_wf : HwWf rotHwWitStart := by
  intro c f _
  cases f <;> rfl

/-- Core 0 ROLs `0x81` by imm8 1 through the machine outcome. -/
def rotHwOutRol : HwRegAusgang :=
  rotHwRegSchritt rotHwWitStart 0
    ⟨⟨.rol, .b8, .imm8 1, .reg .rax⟩, 3⟩

/-- Core 1 RORs `0x01` by imm8 1 through the machine outcome. -/
def rotHwOutRor : HwRegAusgang :=
  rotHwRegSchritt rotHwWitStart 1
    ⟨⟨.ror, .b8, .imm8 1, .reg .rbx⟩, 3⟩

/-- Read a core register out of a machine outcome. -/
def rotHwRegOut (o : HwRegAusgang) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | .weiter m => some ((m.kerne c).register q)
  | _ => none

/-- Read a core carry out of a machine outcome. -/
def rotHwCfOut (o : HwRegAusgang) (c : Nat) : Option Bool :=
  match o with
  | .weiter m => some ((m.kerne c).flags.cf)
  | _ => none

/-- Read a core overflow out of a machine outcome. -/
def rotHwOfOut (o : HwRegAusgang) (c : Nat) : Option Bool :=
  match o with
  | .weiter m => some ((m.kerne c).flags.of)
  | _ => none

/-- Core 0 result: rax holds `0x03`. -/
theorem rotHw_rol_rax :
    rotHwRegOut rotHwOutRol 0 Register.rax = some 3 := by
  decide

/-- Core 0 carry: the wrapped bit comes out. -/
theorem rotHw_rol_cf :
    rotHwCfOut rotHwOutRol 0 = some true := by
  decide

/-- Core 0 overflow: sign change at count one. -/
theorem rotHw_rol_of :
    rotHwOfOut rotHwOutRol 0 = some true := by
  decide

/-- Core 1 result: rbx holds `0x80`. -/
theorem rotHw_ror_rbx :
    rotHwRegOut rotHwOutRor 1 Register.rbx = some 128 := by
  decide

/-- Core 1 carry: the sign comes out. -/
theorem rotHw_ror_cf :
    rotHwCfOut rotHwOutRor 1 = some true := by
  decide

/-- Core 1 overflow: top two bits differ at count one. -/
theorem rotHw_ror_of :
    rotHwOfOut rotHwOutRor 1 = some true := by
  decide

/-- Witness word for the memory form. -/
def rotHwWitMemW : Wort := BitVec.ofNat 64 0x01020304

/-- Memory form over the loaded word: RCR gives `0x00810182`
    with the incoming flags kept (carry clear, no overflow). -/
theorem rotHw_mem_wert :
    rotMemNachweis
      ⟨⟨.rcr, .b32, .eins, .mem .rbx (BitVec.ofNat 32 16)⟩, 6⟩
      ⟨rotHwWitReg0, zeugeFlags, BitVec.ofNat 64 4096, zeugenSpeicher⟩
      rotHwWitMemW =
      some (BitVec.ofNat 64 0x00810182, zeugeFlags) := by
  decide

/-- Witness data addresses, one per acting core. -/
def rotHwWitAdr0 : Adresse := BitVec.ofNat 64 8192

def rotHwWitAdr1 : Adresse := BitVec.ofNat 64 8200

/-- Witness TSO start: canonical memory, empty buffers. -/
def rotHwWitTso0 : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- Core 0 issues its ROL result byte at its cell. -/
def rotHwWitTso1 : Option TSOZustand :=
  rotMemIssue rotHwWitTso0 0 rotHwWitAdr0 .b8 0x03

/-- Core 1 issues its ROR result byte at its cell. -/
def rotHwWitTso1b : Option TSOZustand :=
  match rotHwWitTso1 with
  | some s => rotMemIssue s 1 rotHwWitAdr1 .b8 0x80
  | none => none

/-- Core 0 observes its own byte (forwarding). -/
def rotHwWitEigen0 : Option (Option Byte) :=
  match rotHwWitTso1b with
  | some s => some (loadByte s 0 rotHwWitAdr0)
  | none => none

/-- Core 1 observes the old byte at core 0's cell. -/
def rotHwWitFremd0 : Option (Option Byte) :=
  match rotHwWitTso1b with
  | some s => some (loadByte s 1 rotHwWitAdr0)
  | none => none

/-- Core 1 observes its own byte (forwarding). -/
def rotHwWitEigen1 : Option (Option Byte) :=
  match rotHwWitTso1b with
  | some s => some (loadByte s 1 rotHwWitAdr1)
  | none => none

/-- Core 0 observes the old byte at core 1's cell. -/
def rotHwWitFremd1 : Option (Option Byte) :=
  match rotHwWitTso1b with
  | some s => some (loadByte s 0 rotHwWitAdr1)
  | none => none

/-- Core 0 drains its oldest entry. -/
def rotHwWitTso2 : Option TSOZustand :=
  match rotHwWitTso1b with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def rotHwWitNachFlush : Option (Option Byte) :=
  match rotHwWitTso2 with
  | some s => some (some (s.mem.bytes rotHwWitAdr0))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def rotHwWitFremdNach : Option (Option Byte) :=
  match rotHwWitTso2 with
  | some s => some (loadByte s 1 rotHwWitAdr0)
  | none => none

/-- The data cells start zeroed. -/
theorem rotHw_anfang_null :
    zeugenSpeicher.bytes rotHwWitAdr0 = BitVec.ofNat 8 0 ∧
    zeugenSpeicher.bytes rotHwWitAdr1 = BitVec.ofNat 8 0 := by
  constructor <;> rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem rotHw_weiterleitung0 :
    rotHwWitEigen0 = some (some (BitVec.ofNat 8 3)) := by
  decide

/-- No foreign forwarding at core 0's cell. -/
theorem rotHw_fremd_alt0 :
    rotHwWitFremd0 = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Forwarding: core 1 reads its own unflushed byte. -/
theorem rotHw_weiterleitung1 :
    rotHwWitEigen1 = some (some (BitVec.ofNat 8 128)) := by
  decide

/-- No foreign forwarding at core 1's cell. -/
theorem rotHw_fremd_alt1 :
    rotHwWitFremd1 = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 3. -/
theorem rotHw_spuelung_aendert_speicher :
    rotHwWitNachFlush = some (some (BitVec.ofNat 8 3)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem rotHw_fremd_neu :
    rotHwWitFremdNach = some (some (BitVec.ofNat 8 3)) := by
  decide

/-- A bad decode length refuses the machine step. -/
theorem rotHw_schlechte_laenge_verweigert :
    rotHwRegSchritt rotHwWitStart 0
      (⟨⟨.rol, .b8, .eins, .reg .rax⟩, 0⟩ : RotDecodiert) =
      .verweigert := by
  have hstep := rot_laenge_misslungen
    (⟨⟨.rol, .b8, .eins, .reg .rax⟩, 0⟩ : RotDecodiert)
    (projZustand rotHwWitStart 0) (by decide)
  exact rotHwRegSchritt_verweigert _ _ _ hstep

/-- A memory operand refuses the adapter step. -/
theorem rotHw_mem_adapter_verweigert :
    (adapterRot).schritt rotHwWitStart 0
      (⟨⟨.rcr, .b32, .eins, .mem .rbx (BitVec.ofNat 32 16)⟩, 6⟩ :
        RotDecodiert) = none :=
  adapterRot_verweigert_bei_mem _ _ _ _ _ rfl

/-- The joint witness: a reached two-core rotate run (ROL on
    core 0, ROR on core 1) beside a memory-form value, two
    owner-only forwarded family bytes and a drain that changes
    actual shared memory from 0 to 3 -- with the halt-free
    outcome, the length refusal, the adapter memory refusal and
    the decode refusals beside it. Non-degenerate: the drain
    changes actual shared memory. -/
theorem rotHw_zeuge :
    rotHwRegOut rotHwOutRol 0 Register.rax = some 3 ∧
      rotHwCfOut rotHwOutRol 0 = some true ∧
      rotHwOfOut rotHwOutRol 0 = some true ∧
      rotHwRegOut rotHwOutRor 1 Register.rbx = some 128 ∧
      rotHwCfOut rotHwOutRor 1 = some true ∧
      rotHwOfOut rotHwOutRor 1 = some true ∧
      rotMemNachweis
        ⟨⟨.rcr, .b32, .eins, .mem .rbx (BitVec.ofNat 32 16)⟩, 6⟩
        ⟨rotHwWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
          zeugenSpeicher⟩
        rotHwWitMemW =
        some (BitVec.ofNat 64 0x00810182, zeugeFlags) ∧
      rotHwWitEigen0 = some (some (BitVec.ofNat 8 3)) ∧
      rotHwWitFremd0 = some (some (BitVec.ofNat 8 0)) ∧
      rotHwWitEigen1 = some (some (BitVec.ofNat 8 128)) ∧
      rotHwWitFremd1 = some (some (BitVec.ofNat 8 0)) ∧
      rotHwWitNachFlush = some (some (BitVec.ofNat 8 3)) ∧
      rotHwWitFremdNach = some (some (BitVec.ofNat 8 3)) ∧
      zeugenSpeicher.bytes rotHwWitAdr0 = BitVec.ofNat 8 0 ∧
      HwWf rotHwWitStart ∧
      rotHwRegSchritt rotHwWitStart 0
        (⟨⟨.rol, .b8, .eins, .reg .rax⟩, 0⟩ : RotDecodiert) =
        .verweigert ∧
      (adapterRot).schritt rotHwWitStart 0
        (⟨⟨.rcr, .b32, .eins, .mem .rbx (BitVec.ofNat 32 16)⟩, 6⟩ :
          RotDecodiert) = none ∧
      decodeRotHw [natByte 240, natByte 209, natByte 192] =
        none := by
  refine ⟨rotHw_rol_rax, rotHw_rol_cf, rotHw_rol_of,
    rotHw_ror_rbx, rotHw_ror_cf, rotHw_ror_of, rotHw_mem_wert,
    rotHw_weiterleitung0, rotHw_fremd_alt0, rotHw_weiterleitung1,
    rotHw_fremd_alt1, rotHw_spuelung_aendert_speicher,
    rotHw_fremd_neu, rotHw_anfang_null.1, rotHwWitStart_wf,
    rotHw_schlechte_laenge_verweigert, rotHw_mem_adapter_verweigert,
    rotHw_nichts_lock⟩

/- CUTS:
    Proved here: the rotate family ROL, ROR, RCL and RCR by 1, by
    CL and by imm8 connected to the coherent machine and the
    unified byte dispatcher --
    - §0-§1: operation digits 0 to 3, Nat value core with the
      architectural count mask (five bits below 64, six at 64,
      RCL and RCR modulo width plus one) and pinned values;
    - §2-§3: exact single-step shapes, single-step inverses both
      ways, range preservation and iterated inverses over any
      step count;
    - §4: word-level zero-count and by-width identities, ROL and
      ROR inversion, RCL and RCR inversion through the carry, with
      exact truncation bridges;
    - §5: CF pinned to the last rotated-out bit, OF defined only
      at a masked count of one (free otherwise, never invented
      false), SF, ZF, AF and PF kept, zero effective count keeps
      every flag, with the executable snapshot and its validity
      proof;
    - §6-§7: canonical prefix, ModRM and immediate codec for D0,
      D1, D2, D3, C0 and C1 with register and disp32 memory
      forms, encoder length identity and bounds, generic register
      and memory round trips with the suffix, pinned SDM byte
      rows and named planted refusals;
    - §8: the family step with per-arm equations (register forms
      execute with the architectural merge, zero count advances
      RIP only, memory forms and bad lengths refuse), generic
      memory preservation, memory-form values through the same
      evidence and the TSO issue chain;
    - §9: the extension-first dispatcher with no-shadowing pins,
      pilot preservation, shift overlap keeping the unified arm
      and LOCK refusal;
    - §10: the `HwAdapter RotDecodiert` plug with
      well-formedness preservation and exact agreement, memory
      refusal for memory operands, and the `HwRegAusgang`
      outcome (rotates never halt);
    - §11: a reached two-core run (ROL on core 0, ROR on core 1)
      beside a memory-form value, two owner-only forwarded
      family bytes and a drain that changes actual shared memory
      from 0 to 3, with length, adapter and decode refusals
      beside it.
    NOT proved here, and not claimed:
    - No hardware correspondence: encodings are stated canonical
      bytes with self-consistency only (round trips, pins), not
      x86 truth. Named silicon assumptions: the 5 and 6 bit
      count masks with REX.W, the RCL and RCR modulo width plus
      one, CF as the last rotated-out bit, OF defined only at a
      masked count of one (ROL sign change, ROR top-bit pair,
      RCL sign change, RCR original sign), SF, ZF, AF and PF
      unaffected, count 0 changing no flag, 8 and 16-bit merging
      with 32-bit zero-extension, opcodes D0, D1, D2, D3, C0 and
      C1 with digits 0 to 3. Provenance for the rows is the
      accepted ShiftCodec layering (shared group opcodes with
      disjoint digits) and the report; silicon re-check against
      the supplied SDM extracts stays open.
    - Canonical-subset refusals, each named: mod 0 and mod 1
      memory (disp32 mod 2 only, the pilot shape), the ah, bh,
      ch and dh high-byte registers (low bytes only), 66h and
      REX.W on byte forms, REX.R over the digit, REX.X without
      SIB, LOCK everywhere.
    - No source, IR, ABI, loader, entry or budget link, no
      per-access target-to-W and GX simulation, no whole-word
      atomicity beyond byte drains, no timing or power claim.
    - Multi-byte drain-to-`writeBreite` agreement for memory
      rotates stays open (`rotMemIssue` issues the family bytes;
      only single-byte forwarding and drain are pinned).
    - The family is connected at the dispatcher and adapter
      level only: rotate forms are not in `decodeExt` and
      `stepExt`, and no W to GX bridge is claimed.
-/

#print axioms feldRotOp_rotOpFeld
#print axioms rotMaske_periode_schmal
#print axioms probe_rot_werte
#print axioms rol1Nat_char
#print axioms ror1Nat_rol1Nat
#print axioms ror1Nat_char
#print axioms rol1Nat_ror1Nat
#print axioms divTopBit_lt_two
#print axioms rcl1Nat_char
#print axioms rcr1Nat_char
#print axioms rcr1Nat_rcl1Nat
#print axioms rcl1Nat_rcr1Nat
#print axioms modTwo_mul_pow_le
#print axioms rol1Nat_lt
#print axioms ror1Nat_lt
#print axioms rcl1Nat_lt
#print axioms rcr1Nat_lt
#print axioms rorNat_lt
#print axioms rolNat_lt
#print axioms rcrNat_lt
#print axioms rclNat_lt
#print axioms rorNat_rolNat
#print axioms rolNat_rorNat
#print axioms rcrNat_rclNat
#print axioms rclNat_rcrNat
#print axioms trunc_toNat_lt
#print axioms breite_pos
#print axioms trunc_ofNat_lt
#print axioms trunc_ofNat_toNat
#print axioms rolB_null
#print axioms rorB_null
#print axioms rolB_breite_ident
#print axioms rorB_breite_ident
#print axioms rclB_null
#print axioms rol_ror_inverse
#print axioms ror_rol_inverse
#print axioms trunc_ofNat_toNat'
#print axioms decide_div_eq_toNat
#print axioms split_roundtrip_nat
#print axioms rcrB_null
#print axioms rcl_rcr_inverse
#print axioms rcr_rcl_inverse
#print axioms rotNachweis_wert
#print axioms rotNachweis_ueberlauf
#print axioms rotFlags_null
#print axioms rotFlags_gueltig
#print axioms probe_rot_flags
#print axioms rotEncode_laenge
#print axioms rotPraefixBytes_len
#print axioms rotImmTail_len
#print axioms rotSibTail_len
#print axioms rotEncode_len_ok
#print axioms rotLaenge_ok
#print axioms rotRoundtrip_reg_eins
#print axioms rotRoundtrip_reg_cl
#print axioms rotRoundtrip_reg_imm8
#print axioms rotRoundtrip_reg_imm16
#print axioms rotRoundtrip_reg_imm32
#print axioms rotRoundtrip_reg_imm64
#print axioms rotRoundtrip_mem_eins8
#print axioms rotRoundtrip_mem_eins16
#print axioms rotRoundtrip_mem_eins32
#print axioms rotRoundtrip_mem_eins64
#print axioms rotRoundtrip_mem_cl8
#print axioms rotRoundtrip_mem_cl16
#print axioms rotRoundtrip_mem_cl32
#print axioms rotRoundtrip_mem_cl64
#print axioms rotRoundtrip_mem_imm8
#print axioms rotRoundtrip_mem_imm16
#print axioms rotRoundtrip_mem_imm32
#print axioms rotRoundtrip_mem_imm64
#print axioms pin_rot_rol8_eins
#print axioms pin_rot_ror64_cl
#print axioms pin_rot_rcl16_imm
#print axioms pin_rot_rcr32_mem
#print axioms pin_rot_rol64_weit
#print axioms rot_nichts_lock
#print axioms rot_nichts_digit_vier
#print axioms rot_nichts_modus_null
#print axioms rot_nichts_modus_eins
#print axioms rot_nichts_sechzehn_bei_byte
#print axioms rot_nichts_rex_w_bei_byte
#print axioms rot_nichts_rex_r
#print axioms rot_nichts_rex_x
#print axioms rot_nichts_unbekannt
#print axioms rot_nichts_leer
#print axioms rot_nichts_opcode_allein
#print axioms rot_nichts_imm_kurz
#print axioms rot_reg_erfolg
#print axioms rot_leer_rip
#print axioms rot_mem_verweigert
#print axioms rot_laenge_misslungen
#print axioms rot_laenge_falsch
#print axioms rotSchritt_speicher
#print axioms rotMemNachweis_reg_nichts
#print axioms rot_mem_erfolg
#print axioms decodeRotHw_prefers_ext
#print axioms decodeRotHw_rot
#print axioms decodeRotHw_nichts
#print axioms ext_weist_rotrol8_zurueck
#print axioms ext_weist_rotror64_zurueck
#print axioms ext_weist_rotrcl16_zurueck
#print axioms ext_weist_rotmem32_zurueck
#print axioms ext_weist_rotrol64_zurueck
#print axioms pin_rotHw_pilot_ret
#print axioms pin_rotHw_rol8
#print axioms pin_rotHw_ror64
#print axioms pin_rotHw_rcl16
#print axioms pin_rotHw_rcr32
#print axioms pin_rotHw_ext_shift
#print axioms rotHw_nichts_lock
#print axioms adapterRot_wf
#print axioms adapterRot_ok
#print axioms adapterRot_proj
#print axioms adapterRot_verweigert_bei_laenge
#print axioms adapterRot_verweigert_bei_mem
#print axioms rotHwRegSchritt_weiter
#print axioms rotHwRegSchritt_verweigert
#print axioms rotHwRegSchritt_nie_halt
#print axioms rotHwRegSchritt_weiter_wf
#print axioms rotHwWitStart_wf
#print axioms rotHw_rol_rax
#print axioms rotHw_rol_cf
#print axioms rotHw_rol_of
#print axioms rotHw_ror_rbx
#print axioms rotHw_ror_cf
#print axioms rotHw_ror_of
#print axioms rotHw_mem_wert
#print axioms rotHw_anfang_null
#print axioms rotHw_weiterleitung0
#print axioms rotHw_fremd_alt0
#print axioms rotHw_weiterleitung1
#print axioms rotHw_fremd_alt1
#print axioms rotHw_spuelung_aendert_speicher
#print axioms rotHw_fremd_neu
#print axioms rotHw_schlechte_laenge_verweigert
#print axioms rotHw_mem_adapter_verweigert
#print axioms rotHw_zeuge

end Gabbro.Grammatik.X86
