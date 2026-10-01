/-
  File:      Grammatik/X86/Vektor.lean
  Subject:   Packed integer lanes over the canonical x86-64 words (lane 290).

  Packed 128-bit integer words for a future SIMD profile, over the SAME
  canonical vocabulary (`Grammatik/X86/Typen.lean`: `Wort`, `Breite`;
  `Wort.lean`: `addB`/`subB`/`xorB`, `trunc`/`maske`; `Speicher.lean`:
  `read64`/`write64`, frames, read-back). Lanes are 8/16/32/64-bit fields
  of one `BitVec 128`; lane arithmetic is modular at the lane width and
  memory carriage is two ordered canonical 64-bit chunk accesses.

  No XMM register file is created and `Befehl` is not extended: this is the
  data/operation foundation only. SIMD optimisation admission stays refused
  (see `simdFreigabe`) until source correspondence, fault order, tearing,
  concurrent observations and budget transfer are proved. No FP SIMD.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- A packed integer word: 128 bits holding 16/8/4/2 lanes. -/
abbrev Vektor := BitVec 128

/-- Lane count per width: 16 x 8-bit, 8 x 16-bit, 4 x 32-bit, 2 x 64-bit. -/
def laneCount : Breite → Nat
  | .b8 => 16
  | .b16 => 8
  | .b32 => 4
  | .b64 => 2

/-- Horner-packed lane values: lane `i` holds `f i % 2^w`. -/
def vecVal (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f 0 % 2 ^ w) + 2 ^ w * vecVal w (fun i => f (i + 1)) n

/-- One-step unfolding of the Horner packing (definitional). -/
theorem vecVal_succ (w : Nat) (f : Nat → Nat) (n : Nat) :
    vecVal w f (n + 1) = (f 0 % 2 ^ w) + 2 ^ w * vecVal w (fun i => f (i + 1)) n := rfl

/-- Every width packs exactly 128 bits. -/
theorem laneCount_bits (b : Breite) : laneCount b * b.bits = 128 := by
  cases b <;> rfl

/-- Every width has at least one lane. -/
theorem laneCount_pos (b : Breite) : 0 < laneCount b := by
  cases b <;> decide

/-- The lane modulus is positive at every width. -/
theorem laneMod_pos (b : Breite) : 0 < 2 ^ b.bits := by
  cases b <;> decide

/-- Masking the low `k` bits is reduction modulo `2^k`. -/
theorem mask_and_eq_mod (n k : Nat) : (n &&& (2 ^ k - 1)) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-- Canonical truncation is reduction modulo the lane modulus. -/
theorem trunc_nat (b : Breite) (w : Wort) : (trunc b w).toNat = w.toNat % 2 ^ b.bits := by
  cases b with
  | b8 =>
    show (trunc .b8 w).toNat = w.toNat % 2 ^ 8
    have hff : (0xFF : Wort).toNat = 2 ^ 8 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, mask_and_eq_mod]
  | b16 =>
    show (trunc .b16 w).toNat = w.toNat % 2 ^ 16
    have hff : (0xFFFF : Wort).toNat = 2 ^ 16 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, mask_and_eq_mod]
  | b32 =>
    show (trunc .b32 w).toNat = w.toNat % 2 ^ 32
    have hff : (0xFFFFFFFF : Wort).toNat = 2 ^ 32 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, mask_and_eq_mod]
  | b64 =>
    show (trunc .b64 w).toNat = w.toNat % 2 ^ 64
    have hff : (0xFFFFFFFFFFFFFFFF : Wort).toNat = 2 ^ 64 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, mask_and_eq_mod]

/-- Lane `i` of a packed word as a natural below `2^b.bits`. -/
def laneNat (b : Breite) (v : Vektor) (i : Nat) : Nat :=
  (v.toNat / (2 ^ b.bits) ^ i) % 2 ^ b.bits

/-- Lane `i` of a packed word as a canonical word (zero-extended). -/
def laneGet (b : Breite) (v : Vektor) (i : Nat) : Wort :=
  BitVec.ofNat 64 (laneNat b v i)

/-- Pack `laneCount b` lane values (each taken modulo the lane modulus). -/
def vecMk (b : Breite) (f : Nat → Nat) : Vektor :=
  BitVec.ofNat 128 (vecVal b.bits f (laneCount b))

/-- A lane value is below its modulus. -/
theorem laneNat_lt (b : Breite) (v : Vektor) (i : Nat) :
    laneNat b v i < 2 ^ b.bits :=
  Nat.mod_lt _ (laneMod_pos b)

/-- The lane modulus exceeds one at every width. -/
theorem laneMod_gt_one (b : Breite) : 1 < 2 ^ b.bits := by
  cases b <;> decide

/-- A packed value of `n` lanes fits below `(2^w)^n`. -/
theorem vecVal_lt (w n : Nat) (f : Nat → Nat) (hw : 1 < 2 ^ w) :
    vecVal w f n < (2 ^ w) ^ n := by
  induction n generalizing f with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    rw [vecVal_succ]
    have h1 : f 0 % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by omega)
    have ht := ih (fun i => f (i + 1))
    have htle : vecVal w (fun i => f (i + 1)) n + 1 ≤ (2 ^ w) ^ n := by omega
    calc f 0 % 2 ^ w + 2 ^ w * vecVal w (fun i => f (i + 1)) n
        < 2 ^ w + 2 ^ w * vecVal w (fun i => f (i + 1)) n := by omega
      _ = 2 ^ w * (vecVal w (fun i => f (i + 1)) n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        exact Nat.add_comm _ _
      _ ≤ 2 ^ w * (2 ^ w) ^ n := Nat.mul_le_mul (Nat.le_refl _) htle
      _ = (2 ^ w) ^ (n + 1) := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _

/-- Horner projection: lane `j` of a packed value is that lane's value. -/
theorem vecVal_proj (w n j : Nat) (f : Nat → Nat) (hw : 0 < 2 ^ w) (hj : j < n) :
    (vecVal w f n / (2 ^ w) ^ j) % 2 ^ w = f j % 2 ^ w := by
  induction n generalizing f j with
  | zero => omega
  | succ n ih =>
    rw [vecVal_succ]
    cases j with
    | zero => rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_mod]
    | succ j =>
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hw,
        Nat.div_eq_of_lt (Nat.mod_lt _ hw), Nat.zero_add]
      exact ih j (fun i => f (i + 1)) (by omega)

/-- Packing then reading lane `i` returns that lane modulo the modulus. -/
theorem laneGet_mk (b : Breite) (f : Nat → Nat) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecMk b f) i = f i % 2 ^ b.bits := by
  have hbound : vecVal b.bits f (laneCount b) < 2 ^ 128 := by
    have h := vecVal_lt b.bits (laneCount b) f (laneMod_gt_one b)
    rwa [← Nat.pow_mul, Nat.mul_comm b.bits (laneCount b), laneCount_bits] at h
  unfold laneNat vecMk
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  exact vecVal_proj b.bits (laneCount b) i f (laneMod_pos b) hi

/-- Lane-wise modular addition: each lane adds modulo its width. -/
def vecAdd (b : Breite) (x y : Vektor) : Vektor :=
  vecMk b (fun i => laneNat b x i + laneNat b y i)

/-- Lane-wise modular subtraction, wrapping through `2^64` exactly as the
    canonical `BitVec.toNat_sub` representative does. -/
def vecSub (b : Breite) (x y : Vektor) : Vektor :=
  vecMk b (fun i => 2 ^ 64 - laneNat b y i + laneNat b x i)

/-- Lane-wise xor. -/
def vecXor (b : Breite) (x y : Vektor) : Vektor :=
  vecMk b (fun i => (laneNat b x i) ^^^ (laneNat b y i))

/-- Lane-wise and. -/
def vecAnd (b : Breite) (x y : Vektor) : Vektor :=
  vecMk b (fun i => (laneNat b x i) &&& (laneNat b y i))

/-- Lane-wise or. -/
def vecOr (b : Breite) (x y : Vektor) : Vektor :=
  vecMk b (fun i => (laneNat b x i) ||| (laneNat b y i))

/-- Per-lane addition is the modular lane sum. -/
theorem laneNat_add (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecAdd b x y) i = (laneNat b x i + laneNat b y i) % 2 ^ b.bits := by
  unfold vecAdd
  exact laneGet_mk b _ i hi

/-- Per-lane subtraction follows the canonical representative. -/
theorem laneNat_sub (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecSub b x y) i = (2 ^ 64 - laneNat b y i + laneNat b x i) % 2 ^ b.bits := by
  unfold vecSub
  exact laneGet_mk b _ i hi

/-- Per-lane xor is the lane xor. -/
theorem laneNat_xor (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecXor b x y) i = ((laneNat b x i) ^^^ (laneNat b y i)) % 2 ^ b.bits := by
  unfold vecXor
  exact laneGet_mk b _ i hi

/-- Per-lane and is the lane conjunction. -/
theorem laneNat_and (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecAnd b x y) i = ((laneNat b x i) &&& (laneNat b y i)) % 2 ^ b.bits := by
  unfold vecAnd
  exact laneGet_mk b _ i hi

/-- Per-lane or is the lane disjunction. -/
theorem laneNat_or (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecOr b x y) i = ((laneNat b x i) ||| (laneNat b y i)) % 2 ^ b.bits := by
  unfold vecOr
  exact laneGet_mk b _ i hi

/-- Every lane modulus divides `2^64`. -/
theorem laneMod_dvd (b : Breite) : 2 ^ b.bits ∣ 2 ^ 64 := by
  cases b <;> decide

/-- Every lane modulus fits in a word. -/
theorem laneMod_le (b : Breite) : 2 ^ b.bits ≤ 2 ^ 64 := by
  cases b <;> decide

/-- A lane value fits in a word. -/
theorem laneNat_lt64 (b : Breite) (v : Vektor) (i : Nat) : laneNat b v i < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (laneNat_lt b v i) (laneMod_le b)

/-- A lane read as a word carries exactly the lane value. -/
theorem laneGet_toNat (b : Breite) (v : Vektor) (i : Nat) :
    (laneGet b v i).toNat = laneNat b v i := by
  unfold laneGet
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (laneNat_lt64 b v i)]

/-- Canonical modular addition at the lane modulus. -/
theorem addB_nat (b : Breite) (x y : Wort) :
    (addB b x y).toNat = (x.toNat + y.toNat) % 2 ^ b.bits := by
  simp only [addB]
  rw [trunc_nat, BitVec.toNat_add, Nat.mod_mod_of_dvd _ (laneMod_dvd b)]

/-- Canonical modular subtraction at the lane modulus. -/
theorem subB_nat (b : Breite) (x y : Wort) :
    (subB b x y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ b.bits := by
  simp only [subB]
  rw [trunc_nat, BitVec.toNat_sub, Nat.mod_mod_of_dvd _ (laneMod_dvd b)]

/-- Canonical lane xor at the lane modulus. -/
theorem xorB_nat (b : Breite) (x y : Wort) :
    (xorB b x y).toNat = (x.toNat ^^^ y.toNat) % 2 ^ b.bits := by
  simp only [xorB]
  rw [trunc_nat, BitVec.toNat_xor]

/-- Canonical truncation of a conjunction at the lane modulus. -/
theorem trunc_and_nat (b : Breite) (x y : Wort) :
    (trunc b (x &&& y)).toNat = (x.toNat &&& y.toNat) % 2 ^ b.bits := by
  rw [trunc_nat, BitVec.toNat_and]

/-- Canonical truncation of a disjunction at the lane modulus. -/
theorem trunc_or_nat (b : Breite) (x y : Wort) :
    (trunc b (x ||| y)).toNat = (x.toNat ||| y.toNat) % 2 ^ b.bits := by
  rw [trunc_nat, BitVec.toNat_or]

/-- A vector add reads per lane as the canonical modular add: no
    inter-lane carry, by construction through the lane values. -/
theorem laneGet_add (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneGet b (vecAdd b x y) i = addB b (laneGet b x i) (laneGet b y i) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (laneNat b (vecAdd b x y) i)).toNat =
    (addB b (laneGet b x i) (laneGet b y i)).toNat
  rw [BitVec.toNat_ofNat, laneNat_add b x y i hi, addB_nat,
    laneGet_toNat, laneGet_toNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (laneMod_pos b)) (laneMod_le b))]

/-- A vector subtraction reads per lane as the canonical modular subtraction. -/
theorem laneGet_sub (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneGet b (vecSub b x y) i = subB b (laneGet b x i) (laneGet b y i) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (laneNat b (vecSub b x y) i)).toNat =
    (subB b (laneGet b x i) (laneGet b y i)).toNat
  rw [BitVec.toNat_ofNat, laneNat_sub b x y i hi, subB_nat,
    laneGet_toNat, laneGet_toNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (laneMod_pos b)) (laneMod_le b))]

/-- A vector xor reads per lane as the canonical xor. -/
theorem laneGet_xor (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneGet b (vecXor b x y) i = xorB b (laneGet b x i) (laneGet b y i) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (laneNat b (vecXor b x y) i)).toNat =
    (xorB b (laneGet b x i) (laneGet b y i)).toNat
  rw [BitVec.toNat_ofNat, laneNat_xor b x y i hi, xorB_nat,
    laneGet_toNat, laneGet_toNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (laneMod_pos b)) (laneMod_le b))]

/-- A vector and reads per lane as the truncated conjunction. -/
theorem laneGet_and (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneGet b (vecAnd b x y) i = trunc b (laneGet b x i &&& laneGet b y i) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (laneNat b (vecAnd b x y) i)).toNat =
    (trunc b (laneGet b x i &&& laneGet b y i)).toNat
  rw [BitVec.toNat_ofNat, laneNat_and b x y i hi, trunc_and_nat,
    laneGet_toNat, laneGet_toNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (laneMod_pos b)) (laneMod_le b))]

/-- A vector or reads per lane as the truncated disjunction. -/
theorem laneGet_or (b : Breite) (x y : Vektor) (i : Nat) (hi : i < laneCount b) :
    laneGet b (vecOr b x y) i = trunc b (laneGet b x i ||| laneGet b y i) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (laneNat b (vecOr b x y) i)).toNat =
    (trunc b (laneGet b x i ||| laneGet b y i)).toNat
  rw [BitVec.toNat_ofNat, laneNat_or b x y i hi, trunc_or_nat,
    laneGet_toNat, laneGet_toNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (laneMod_pos b)) (laneMod_le b))]

/-- No inter-lane carry: lane `i` of a vector add depends only on the
    lane-`i` inputs; other lanes cannot influence it. -/
theorem vecAdd_allein (b : Breite) (x x' y y' : Vektor) (i : Nat)
    (hx : laneNat b x i = laneNat b x' i) (hy : laneNat b y i = laneNat b y' i)
    (hi : i < laneCount b) :
    laneNat b (vecAdd b x y) i = laneNat b (vecAdd b x' y') i := by
  rw [laneNat_add b x y i hi, laneNat_add b x' y' i hi, hx, hy]

/-- No inter-lane borrow: the same independence for subtraction. -/
theorem vecSub_allein (b : Breite) (x x' y y' : Vektor) (i : Nat)
    (hx : laneNat b x i = laneNat b x' i) (hy : laneNat b y i = laneNat b y' i)
    (hi : i < laneCount b) :
    laneNat b (vecSub b x y) i = laneNat b (vecSub b x' y') i := by
  rw [laneNat_sub b x y i hi, laneNat_sub b x' y' i hi, hx, hy]

/- CUTS:
    Skeleton only: lane accessors, lane operations, memory carriage,
    correctness/no-carry theorems, witnesses and the SIMD refusal are open.
-/

#print axioms vecVal_succ

end Gabbro.Grammatik.X86
