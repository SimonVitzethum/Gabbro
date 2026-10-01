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

/-- Low 64 bits of a packed word. -/
def vLo (v : Vektor) : Wort := BitVec.ofNat 64 (v.toNat % 2 ^ 64)

/-- High 64 bits of a packed word. -/
def vHi (v : Vektor) : Wort := BitVec.ofNat 64 (v.toNat / 2 ^ 64)

/-- Reassemble a packed word from its halves. -/
def vecJoin (lo hi : Wort) : Vektor :=
  BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64)

/-- Splitting then rejoining is the identity. -/
theorem vecJoin_split (v : Vektor) : vecJoin (vLo v) (vHi v) = v := by
  have hlt := v.isLt
  have hdiv : v.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)]
    have hprod : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
    rw [hprod]
    exact hlt
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 128 ((vLo v).toNat + (vHi v).toNat * 2 ^ 64)).toNat = v.toNat
  unfold vLo vHi
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod,
    Nat.mod_eq_of_lt hdiv, Nat.mul_comm _ (2 ^ 64),
    Nat.mod_add_div, Nat.mod_eq_of_lt hlt]

/-- Second chunk address: eight bytes past the base. -/
def vecHiAddr (a : Adresse) : Adresse := addrOff a 8

/-- No-wrap over both eight-byte chunks: sixteen bytes from the base. -/
def OhneUmbruch16 (a : Adresse) : Prop := a.toNat + 16 ≤ 2 ^ 64

/-- Machine address addition is Nat addition below the wrap bound. -/
theorem addrOff_nat (a : Adresse) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    (addrOff a i).toNat = a.toNat + i := by
  unfold addrOff
  have ha := a.isLt
  have hi64 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hi64, Nat.mod_eq_of_lt (by omega)]

/-- Footprint disjointness is symmetric. -/
theorem Disjunkt_symm (a b : Adresse) (h : Disjunkt a b) : Disjunkt b a := by
  intro i j hi hj he
  exact h j i hj hi he.symm

/-- The two eight-byte chunks of one vector access are disjoint. -/
theorem vecChunks_disjoint (a : Adresse) (h : OhneUmbruch16 a) :
    Disjunkt a (vecHiAddr a) := by
  intro i j hi hj he
  unfold OhneUmbruch16 at h
  have e1 := addrOff_nat a i (by omega)
  have e0 : (vecHiAddr a).toNat = a.toNat + 8 := addrOff_nat a 8 (by omega)
  have e2 := addrOff_nat (vecHiAddr a) j (by omega)
  have h2 := congrArg BitVec.toNat he
  rw [e1, e2] at h2
  omega

/-- Store a packed word as two ordered canonical 64-bit chunks: the low
    half first, then the high half eight bytes past the base. -/
def vecWrite (m : Speicher) (a : Adresse) (v : Vektor) : Option Speicher :=
  match write64 m a (vLo v) with
  | none => none
  | some m1 => write64 m1 (vecHiAddr a) (vHi v)

/-- Load a packed word as two ordered canonical 64-bit chunks. -/
def vecRead (m : Speicher) (a : Adresse) : Option Vektor :=
  match read64 m a, read64 m (vecHiAddr a) with
  | some lo, some hi => some (vecJoin lo hi)
  | _, _ => none

/-- A successful vector store preserves all permissions: only bytes change. -/
theorem vecWrite_perm (m m1 m' : Speicher) (a : Adresse) (v : Vektor)
    (h1 : write64 m a (vLo v) = some m1)
    (h2 : write64 m1 (vecHiAddr a) (vHi v) = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  obtain ⟨a1, b1, c1⟩ := write64_erhaelt_berechtigungen m a (vLo v) m1 h1
  obtain ⟨a2, b2, c2⟩ := write64_erhaelt_berechtigungen m1 (vecHiAddr a) (vHi v) m' h2
  exact ⟨by rw [a2, a1], by rw [b2, b1], by rw [c2, c1]⟩

/-- A refused low chunk refuses the whole vector store. -/
theorem vecWrite_verweigert_lo (m : Speicher) (a : Adresse) (v : Vektor)
    (h : schreibbar8 m a = false) : vecWrite m a v = none := by
  unfold vecWrite
  rw [write64_verweigert m a (vLo v) h]

/-- A refused high chunk refuses the whole vector store after the low write. -/
theorem vecWrite_verweigert_hi (m m1 : Speicher) (a : Adresse) (v : Vektor)
    (h1 : write64 m a (vLo v) = some m1)
    (h : schreibbar8 m1 (vecHiAddr a) = false) : vecWrite m a v = none := by
  unfold vecWrite
  rw [h1]
  exact write64_verweigert m1 (vecHiAddr a) (vHi v) h

/-- READ-AFTER-WRITE: two successful chunks read back as the packed word.
    Needs readability at both chunks and no-wrap across both footprints. -/
theorem vecRead_nach_write (m m1 m' : Speicher) (a : Adresse) (v : Vektor)
    (h1 : write64 m a (vLo v) = some m1)
    (h2 : write64 m1 (vecHiAddr a) (vHi v) = some m')
    (hrd1 : lesbar8 m a = true) (hrd2 : lesbar8 m (vecHiAddr a) = true)
    (hno : OhneUmbruch16 a) :
    vecRead m' a = some v := by
  have hle1 : lesbar8 m1 (vecHiAddr a) = true := by
    have h := lesbar8_nach_schreiben m m1 a (vecHiAddr a) (vLo v) h1
    rwa [hrd2] at h
  have rhi := read64_nach_write64 m1 m' (vecHiAddr a) (vHi v) h2 hle1
  have rlo : read64 m' a = some (vLo v) := by
    have base := read64_nach_write64 m m1 a (vLo v) h1 hrd1
    have hframe := read64_rahmen m1 m' (vecHiAddr a) a (vHi v) h2
      (Disjunkt_symm a (vecHiAddr a) (vecChunks_disjoint a hno))
    rw [hframe]
    exact base
  simp only [vecRead, rlo, rhi, vecJoin_split]

/-- A vector store changes nothing outside its two footprints. -/
theorem vecWrite_rahmen (m m1 m' : Speicher) (a x : Adresse) (v : Vektor)
    (h1 : write64 m a (vLo v) = some m1)
    (h2 : write64 m1 (vecHiAddr a) (vHi v) = some m')
    (hau1 : ∀ k : Nat, k < 8 → x ≠ addrOff a k)
    (hau2 : ∀ k : Nat, k < 8 → x ≠ addrOff (vecHiAddr a) k) :
    m'.bytes x = m.bytes x := by
  have e1 := write64_rahmen m m1 a x (vLo v) h1 hau1
  have e2 := write64_rahmen m1 m' (vecHiAddr a) x (vHi v) h2 hau2
  rw [e2, e1]

/-- NO VECTOR ATOMICITY: after the first chunk, memory is observably mixed --
    the low half already carries the new value while the high half still
    carries the old bytes. A concurrent observer may see this state. -/
theorem vecWrite_teilt (m m1 : Speicher) (a : Adresse) (v : Vektor)
    (h1 : write64 m a (vLo v) = some m1)
    (hrd1 : lesbar8 m a = true)
    (hno : OhneUmbruch16 a) :
    read64 m1 a = some (vLo v) ∧
      read64 m1 (vecHiAddr a) = read64 m (vecHiAddr a) := by
  refine ⟨read64_nach_write64 m m1 a (vLo v) h1 hrd1, ?_⟩
  exact read64_rahmen m m1 a (vecHiAddr a) (vLo v) h1
    (vecChunks_disjoint a hno)

/-- Boundary witness: lane 0 overflows (`0xFF + 1` wraps to zero) while
    lane 1 adds independently (`5 + 7 = 12`): no carry crosses lanes. -/
theorem vec_ueberlauf_ohne_uebertrag_b8 :
    laneNat .b8 (vecAdd .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 5 else 0))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 7 else 0))) 0 = 0 ∧
    laneNat .b8 (vecAdd .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 5 else 0))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 7 else 0))) 1 = 12 := by
  decide

/-- Boundary witness at 64-bit lanes: the low lane wraps
    (`0xFFFF..FF + 1` to zero) while the high lane adds independently. -/
theorem vec_ueberlauf_ohne_uebertrag_b64 :
    laneNat .b64 (vecAdd .b64
      (vecMk .b64 (fun i => if i = 0 then 18446744073709551615 else 3))
      (vecMk .b64 (fun i => if i = 0 then 1 else 4))) 0 = 0 ∧
    laneNat .b64 (vecAdd .b64
      (vecMk .b64 (fun i => if i = 0 then 18446744073709551615 else 3))
      (vecMk .b64 (fun i => if i = 0 then 1 else 4))) 1 = 7 := by
  decide

/-- Boundary witness for subtraction: lane 0 borrows and wraps (`0 - 1`
    to `0xFF`) while lane 1 subtracts independently (`5 - 2 = 3`). -/
theorem vec_borg_ohne_uebertrag_b8 :
    laneNat .b8 (vecSub .b8
      (vecMk .b8 (fun i => if i = 0 then 0 else if i = 1 then 5 else 0))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 2 else 0))) 0 = 255 ∧
    laneNat .b8 (vecSub .b8
      (vecMk .b8 (fun i => if i = 0 then 0 else if i = 1 then 5 else 0))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 2 else 0))) 1 = 3 := by
  decide

/-- Boundary witness for xor: lane 0 complements (`0xAA ^^^ 0x55 = 0xFF`)
    while lane 1 cancels to zero. -/
theorem vec_xor_spur_b8 :
    laneNat .b8 (vecXor .b8
      (vecMk .b8 (fun i => if i = 0 then 170 else if i = 1 then 240 else 0))
      (vecMk .b8 (fun i => if i = 0 then 85 else if i = 1 then 240 else 0))) 0 = 255 ∧
    laneNat .b8 (vecXor .b8
      (vecMk .b8 (fun i => if i = 0 then 170 else if i = 1 then 240 else 0))
      (vecMk .b8 (fun i => if i = 0 then 85 else if i = 1 then 240 else 0))) 1 = 0 := by
  decide

/-- Fully permissive memory with zeroed bytes. -/
def vecZeugenSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- A nonzero packed word with distinct halves. -/
def vecZeugenVektor : Vektor :=
  BitVec.ofNat 128 0x100F0E0D0C0B0A090807060504030201

/-- Memory after the low chunk of the witness write at address zero. -/
def vecZeugenM1 : Speicher :=
  { vecZeugenSpeicher with bytes := writeBytes vecZeugenSpeicher 0 (vLo vecZeugenVektor) }

/-- Memory after both chunks of the witness write at address zero. -/
def vecZeugenM2 : Speicher :=
  { vecZeugenM1 with bytes := writeBytes vecZeugenM1 (vecHiAddr 0) (vHi vecZeugenVektor) }

/-- A nonzero vector store goes through two ordered chunk writes, reads
    back, and observably changes memory. -/
theorem vecWrite_read_zeuge :
    ∃ (m m' : Speicher) (a : Adresse) (v : Vektor),
      v ≠ 0 ∧ vecWrite m a v = some m' ∧ read64 m' a = some (vLo v) ∧
        vecRead m' a = some v ∧ m.bytes a ≠ m'.bytes a := by
  have h1 : write64 vecZeugenSpeicher 0 (vLo vecZeugenVektor) = some vecZeugenM1 := by
    unfold write64
    have hc : schreibbar8 vecZeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  have h2 : write64 vecZeugenM1 (vecHiAddr 0) (vHi vecZeugenVektor) = some vecZeugenM2 := by
    unfold write64
    have hc : schreibbar8 vecZeugenM1 (vecHiAddr 0) = true := rfl
    rw [if_pos hc]
    rfl
  have hw : vecWrite vecZeugenSpeicher 0 vecZeugenVektor = some vecZeugenM2 := by
    unfold vecWrite
    rw [h1]
    exact h2
  have hrd1 : lesbar8 vecZeugenSpeicher 0 = true := rfl
  have hrd2 : lesbar8 vecZeugenSpeicher (vecHiAddr 0) = true := rfl
  have hno : OhneUmbruch16 (0 : Adresse) := by
    unfold OhneUmbruch16
    decide
  have hback := vecRead_nach_write vecZeugenSpeicher vecZeugenM1 vecZeugenM2 0
    vecZeugenVektor h1 h2 hrd1 hrd2 hno
  have hlo : read64 vecZeugenM2 0 = some (vLo vecZeugenVektor) := by
    have base := read64_nach_write64 vecZeugenSpeicher vecZeugenM1 0
      (vLo vecZeugenVektor) h1 hrd1
    have hframe := read64_rahmen vecZeugenM1 vecZeugenM2 (vecHiAddr 0) 0
      (vHi vecZeugenVektor) h2
      (Disjunkt_symm 0 (vecHiAddr 0) (vecChunks_disjoint 0 hno))
    rw [hframe]
    exact base
  have hhit : writeBytes vecZeugenSpeicher 0 (vLo vecZeugenVektor) 0 =
      wortByte (vLo vecZeugenVektor) 0 := by
    have h := writeBytesN_hit vecZeugenSpeicher 0 (vLo vecZeugenVektor) 8 0
      (by decide) (by decide)
    rwa [addrOff_null] at h
  have hmiss : ∀ k : Nat, k < 8 → (0 : Adresse) ≠ addrOff (vecHiAddr 0) k := by
    intro k hk hcon
    have e : (addrOff (vecHiAddr 0) k).toNat = 8 + k := by
      have e0 : (vecHiAddr (0 : Adresse)).toNat = 8 := by decide
      have hkk : (vecHiAddr (0 : Adresse)).toNat + k < 2 ^ 64 := by omega
      rw [addrOff_nat _ _ hkk, e0]
    have z : (0 : Adresse).toNat = 0 := by decide
    have hcon2 := congrArg BitVec.toNat hcon
    rw [z, e] at hcon2
    omega
  have hframe : vecZeugenM2.bytes 0 = vecZeugenM1.bytes 0 :=
    writeBytesN_miss vecZeugenM1 (vecHiAddr 0) (vHi vecZeugenVektor) 8 0 hmiss
  have hchg : vecZeugenSpeicher.bytes 0 ≠ vecZeugenM2.bytes 0 := by
    rw [hframe]
    show BitVec.ofNat 8 0 ≠ vecZeugenM1.bytes 0
    have e1 : vecZeugenM1.bytes 0 =
        writeBytes vecZeugenSpeicher 0 (vLo vecZeugenVektor) 0 := rfl
    rw [e1, hhit]
    decide
  exact ⟨vecZeugenSpeicher, vecZeugenM2, 0, vecZeugenVektor,
    by decide, hw, hlo, hback, hchg⟩

/-- SIMD admission: refused until a generic vector correspondence is proved
    covering source correspondence, fault order (IR-VALIDIERUNG §3 item 9a),
    visibility (9b), tearing (9c) and FP control status (9d), concurrent
    observations, and budget transfer. Any admission must edit this
    definition, so it cannot slip in silently. No FP SIMD exists here. -/
def simdFreigabe : Bool := false

/-- No SIMD transformation is admitted on this foundation. -/
theorem simd_gesperrt : simdFreigabe = false := rfl

/- CUTS:
    Data/operation foundation only: packed 128-bit integer words over the
    canonical `Wort`/`Breite` helpers (8/16/32/64 lanes), per-lane modular
    add/sub/bitwise correctness with no inter-lane carry or borrow, and
    memory carriage as two ordered permission-checked canonical 64-bit
    chunk accesses with explicit refusal, read-back, frame and an
    observably mixed intermediate state (no vector atomicity is claimed;
    lane disjointness never implies atomicity or reordering of shared
    operations).
    NOT proved here and required before any SIMD optimisation is admitted:
    source correspondence (lowering to `P`/`exec`), fault order across
    lanes, visibility against concurrent observers, tearing correspondence
    against the per-access TSO bridge table, FP control status (no FP lanes
    are modelled), source call-log preservation (`FolgeG`), budget transfer
    for the two chunk accesses, progress interaction, or decoder/ABI/image
    validation. `simdFreigabe` stays `false` until all of it is proved.
    No XMM register file is created and `Befehl` is untouched.
-/

#print axioms vecVal_succ
#print axioms laneCount_bits
#print axioms laneCount_pos
#print axioms laneMod_pos
#print axioms mask_and_eq_mod
#print axioms trunc_nat
#print axioms laneNat_lt
#print axioms laneMod_gt_one
#print axioms vecVal_lt
#print axioms vecVal_proj
#print axioms laneGet_mk
#print axioms laneNat_add
#print axioms laneNat_sub
#print axioms laneNat_xor
#print axioms laneNat_and
#print axioms laneNat_or
#print axioms laneMod_dvd
#print axioms laneMod_le
#print axioms laneNat_lt64
#print axioms laneGet_toNat
#print axioms addB_nat
#print axioms subB_nat
#print axioms xorB_nat
#print axioms trunc_and_nat
#print axioms trunc_or_nat
#print axioms laneGet_add
#print axioms laneGet_sub
#print axioms laneGet_xor
#print axioms laneGet_and
#print axioms laneGet_or
#print axioms vecAdd_allein
#print axioms vecSub_allein
#print axioms vecJoin_split
#print axioms addrOff_nat
#print axioms Disjunkt_symm
#print axioms vecChunks_disjoint
#print axioms vecWrite_perm
#print axioms vecWrite_verweigert_lo
#print axioms vecWrite_verweigert_hi
#print axioms vecRead_nach_write
#print axioms vecWrite_rahmen
#print axioms vecWrite_teilt
#print axioms vec_ueberlauf_ohne_uebertrag_b8
#print axioms vec_ueberlauf_ohne_uebertrag_b64
#print axioms vec_borg_ohne_uebertrag_b8
#print axioms vec_xor_spur_b8
#print axioms vecWrite_read_zeuge
#print axioms simd_gesperrt

end Gabbro.Grammatik.X86
