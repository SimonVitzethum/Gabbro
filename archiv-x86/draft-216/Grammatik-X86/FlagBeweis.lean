/-
  File:      Grammatik/X86/FlagBeweis.lean
  Subject:   Mathematical carry and signed-overflow characterisation of the
             EXISTING `add64`/`sub64` flag snapshots from `Grammatik/X86/Wort`.

  Lane 285 (wave A): generic mathematical facts over the REAL canonical
  `Wort` (BitVec 64) and the REAL operations `add64`/`sub64` -- a signed
  interpretation `sint` (BitVec.toInt), OF iff the exact signed sum or
  difference leaves [-2^63, 2^63-1], sign-bit readings (SF = negative,
  threshold 2^63 on toNat), unsigned carry/borrow as Nat range facts, and
  low-byte parity facts. No second add/sub function is defined; every
  lemma consumes `add64`/`sub64` (or the shared flag helpers they use).

  No source correspondence is claimed here; physical instruction semantics
  remain named silicon behaviour plus a later bridge (lane 277 owns it).
-/
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Signed interpretation of a word: two's complement value in
    [-2^63, 2^63-1]. The optimiser and the instruction-semantics consumer
    read ranges through this, never through a second adder. -/
def sint (w : Wort) : Int := w.toInt

/-- Every word denotes a value in the signed 64-bit range. -/
theorem sint_mem (w : Wort) :
    -(2 ^ 63 : Int) ≤ sint w ∧ sint w ≤ 2 ^ 63 - 1 := by
  unfold sint
  rw [BitVec.toInt_eq_toNat_bmod]
  have h1 := Int.le_bmod (x := (w.toNat : Int)) (m := 2 ^ 64) (by decide)
  have h2 := Int.bmod_le (x := (w.toNat : Int)) (m := 2 ^ 64) (by decide)
  constructor <;> omega

/-! ## 2. Sign-bit readings.

    `sfTest` is the top bit: it equals `msb`, the `2^63` threshold on
    `toNat`, and negativity of the signed interpretation. -/

/-- The sign test is the most significant bit. -/
theorem sfTest_msb (w : Wort) : sfTest w = w.msb := by
  unfold BitVec.msb sfTest
  rw [BitVec.getMsbD_eq_getLsbD]
  have h0 : decide (0 < 64) = true := rfl
  rw [h0]
  simp only [Bool.true_and]
  have h1 : (64 - 1 - 0 : Nat) = 63 := rfl
  rw [h1]
  rw [← BitVec.testBit_toNat]

/-- The sign test is the `2^63` threshold on the unsigned value. -/
theorem sfTest_toNat (w : Wort) : sfTest w = decide (2 ^ 63 ≤ w.toNat) := by
  rw [sfTest_msb, BitVec.msb_eq_decide]

/-- A set sign bit means a negative signed value. -/
theorem sint_neg_of_msb (w : Wort) (h : w.msb = true) : sint w < 0 := by
  unfold sint
  rw [BitVec.toInt_eq_msb_cond, if_pos h]
  have hlt := w.isLt
  omega

/-- A clear sign bit means a non-negative signed value. -/
theorem sint_nonneg_of_nmsb (w : Wort) (h : w.msb = false) :
    0 ≤ sint w := by
  unfold sint
  rw [BitVec.toInt_eq_msb_cond]
  have hf : ¬ w.msb = true := by simp [h]
  rw [if_neg hf]
  omega

/-- The sign test is negativity of the signed interpretation. -/
theorem sfTest_sint (w : Wort) : sfTest w = decide (sint w < 0) := by
  rw [sfTest_msb]
  cases hm : w.msb
  · have hn : 0 ≤ sint w := sint_nonneg_of_nmsb w hm
    simp [show ¬ sint w < 0 from by omega]
  · have hp : sint w < 0 := sint_neg_of_msb w hm
    simp [hp]

/-! ## 3. Modular wrap of exact signed sums.

    `BitVec.toInt_add`/`toInt_sub` say the wrapped result is the exact
    sum `bmod 2^64`. The three cases below name its value on each range:
    in range it is the identity, above `2^63 - 1` it subtracts `2^64`,
    below `-2^63` it adds `2^64`. The OF proofs consume exactly these. -/

/-- An in-range exact value survives the 64-bit wrap. -/
theorem bmod_in_range (s : Int) (lo : -(2 ^ 63 : Int) ≤ s)
    (hi : s < 2 ^ 63) : s.bmod (2 ^ 64) = s := by
  apply Int.bmod_eq_of_le (by omega) (by omega)

/-- A large exact sum wraps by subtracting `2^64`. -/
theorem bmod_high (s : Int) (lo : (2 ^ 63 : Int) ≤ s)
    (hi : s < 2 ^ 64) : s.bmod (2 ^ 64) = s - 2 ^ 64 := by
  rw [Int.bmod_def]
  have he : s % ((2 ^ 64 : Nat) : Int) = s :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [he, if_neg (by omega)]
  omega

/-- A small exact sum wraps by adding `2^64`. -/
theorem bmod_low (s : Int) (lo : -(2 ^ 64 : Int) ≤ s)
    (hi : s < -(2 ^ 63 : Int)) : s.bmod (2 ^ 64) = s + 2 ^ 64 := by
  rw [Int.bmod_def]
  have he : s % ((2 ^ 64 : Nat) : Int) = s + 2 ^ 64 := by omega
  rw [he, if_pos (by omega)]

/-! ## 4. OF is the exact signed range check for ADD.

    The signed result of `add64` is the exact sum wrapped `bmod 2^64`;
    OF holds exactly when the exact sum leaves [-2^63, 2^63-1]. The proof
    is a sign-bit case analysis over the three wrap cases of §3 -- no
    overflow equivalence is assumed. -/

/-- The signed ADD result is the exact sum wrapped `bmod 2^64`. -/
theorem add64_sint (x y : Wort) :
    sint (add64 x y).1 = (sint x + sint y).bmod (2 ^ 64) := by
  have hval : (add64 x y).1 = x + y := rfl
  rw [hval]
  exact BitVec.toInt_add x y

/-- ADD overflow holds exactly when the exact signed sum is out of range. -/
theorem add64_of_iff (x y : Wort) :
    (add64 x y).2.of = true ↔
      sint x + sint y < -(2 ^ 63 : Int) ∨
        (2 ^ 63 : Int) ≤ sint x + sint y := by
  have hbx := (sint_mem x).1
  have hbx2 := (sint_mem x).2
  have hby := (sint_mem y).1
  have hby2 := (sint_mem y).2
  have hof := add64_of x y
  rw [sfTest_sint x, sfTest_sint y, sfTest_sint (x + y)] at hof
  have hwrap : sint (x + y) = (sint x + sint y).bmod (2 ^ 64) :=
    BitVec.toInt_add x y
  rw [hwrap] at hof
  rw [hof]
  constructor
  · intro htrue
    by_cases hP : sint x + sint y < -(2 ^ 63 : Int)
    · exact Or.inl hP
    · by_cases hQ : (2 ^ 63 : Int) ≤ sint x + sint y
      · exact Or.inr hQ
      · have hlo : -(2 ^ 63 : Int) ≤ sint x + sint y := by omega
        have hhi : sint x + sint y < 2 ^ 63 := by omega
        have hw : (sint x + sint y).bmod (2 ^ 64) = sint x + sint y :=
          bmod_in_range _ hlo hhi
        rw [hw] at htrue
        by_cases ha : sint x < 0 <;> by_cases hb : sint y < 0
        · have hs : sint x + sint y < 0 := by omega
          simp [ha, hb, hs] at htrue
        · simp [ha, hb] at htrue
        · simp [ha, hb] at htrue
        · have hs : ¬ sint x + sint y < 0 := by omega
          simp [ha, hb, hs] at htrue
  · intro hrange
    cases hrange with
    | inl hlo =>
      have hs2 : -(2 ^ 64 : Int) ≤ sint x + sint y := by omega
      have hw := bmod_low _ hs2 hlo
      have ha : sint x < 0 := by omega
      have hb : sint y < 0 := by omega
      have hs : ¬ (sint x + sint y).bmod (2 ^ 64) < 0 := by rw [hw]; omega
      simp [ha, hb, hs]
    | inr hhi =>
      have hs2 : sint x + sint y < 2 ^ 64 := by omega
      have hw := bmod_high _ hhi hs2
      have ha : ¬ sint x < 0 := by omega
      have hb : ¬ sint y < 0 := by omega
      have hs : (sint x + sint y).bmod (2 ^ 64) < 0 := by rw [hw]; omega
      simp [ha, hb, hs]

/-! ## 5. OF is the exact signed range check for SUB.

    Mirror of §4 for the exact difference: OF holds exactly when
    `sint x - sint y` leaves [-2^63, 2^63-1]. -/

/-- The signed SUB result is the exact difference wrapped `bmod 2^64`. -/
theorem sub64_sint (x y : Wort) :
    sint (sub64 x y).1 = (sint x - sint y).bmod (2 ^ 64) := by
  have hval : (sub64 x y).1 = x - y := rfl
  rw [hval]
  exact BitVec.toInt_sub

/-- SUB overflow holds exactly when the exact signed difference is out
    of range. -/
theorem sub64_of_iff (x y : Wort) :
    (sub64 x y).2.of = true ↔
      sint x - sint y < -(2 ^ 63 : Int) ∨
        (2 ^ 63 : Int) ≤ sint x - sint y := by
  have hbx := (sint_mem x).1
  have hbx2 := (sint_mem x).2
  have hby := (sint_mem y).1
  have hby2 := (sint_mem y).2
  have hof := sub64_of x y
  rw [sfTest_sint x, sfTest_sint y, sfTest_sint (x - y)] at hof
  have hwrap : sint (x - y) = (sint x - sint y).bmod (2 ^ 64) :=
    BitVec.toInt_sub
  rw [hwrap] at hof
  rw [hof]
  constructor
  · intro htrue
    by_cases hP : sint x - sint y < -(2 ^ 63 : Int)
    · exact Or.inl hP
    · by_cases hQ : (2 ^ 63 : Int) ≤ sint x - sint y
      · exact Or.inr hQ
      · have hlo : -(2 ^ 63 : Int) ≤ sint x - sint y := by omega
        have hhi : sint x - sint y < 2 ^ 63 := by omega
        have hw : (sint x - sint y).bmod (2 ^ 64) = sint x - sint y :=
          bmod_in_range _ hlo hhi
        rw [hw] at htrue
        by_cases ha : sint x < 0 <;> by_cases hb : sint y < 0
        · simp [ha, hb] at htrue
        · have hs : sint x - sint y < 0 := by omega
          simp [ha, hb, hs] at htrue
        · have hs : ¬ sint x - sint y < 0 := by omega
          simp [ha, hb, hs] at htrue
        · simp [ha, hb] at htrue
  · intro hrange
    cases hrange with
    | inl hlo =>
      have hs2 : -(2 ^ 64 : Int) ≤ sint x - sint y := by omega
      have hw := bmod_low _ hs2 hlo
      have ha : sint x < 0 := by omega
      have hb : ¬ sint y < 0 := by omega
      have hs : ¬ (sint x - sint y).bmod (2 ^ 64) < 0 := by rw [hw]; omega
      simp [ha, hb, hs]
    | inr hhi =>
      have hs2 : sint x - sint y < 2 ^ 64 := by omega
      have hw := bmod_high _ hhi hs2
      have ha : ¬ sint x < 0 := by omega
      have hb : sint y < 0 := by omega
      have hs : (sint x - sint y).bmod (2 ^ 64) < 0 := by rw [hw]; omega
      simp [ha, hb, hs]

/-! ## 6. Range facts for the instruction-semantics/optimiser consumer.

    Cleared OF means the wrapped value IS the exact sum or difference;
    cleared CF/borrow means the unsigned value IS the exact Nat sum or
    difference. Each lemma names the exact value a later stage may use. -/

/-- Without ADD overflow the signed result is the exact sum. -/
theorem add64_sint_eq_of_no_overflow (x y : Wort)
    (h : (add64 x y).2.of = false) :
    sint (add64 x y).1 = sint x + sint y := by
  by_cases hP : sint x + sint y < -(2 ^ 63 : Int)
  · have hc := (add64_of_iff x y).mpr (Or.inl hP)
    simp [hc] at h
  · by_cases hQ : (2 ^ 63 : Int) ≤ sint x + sint y
    · have hc := (add64_of_iff x y).mpr (Or.inr hQ)
      simp [hc] at h
    · have hlo : -(2 ^ 63 : Int) ≤ sint x + sint y := by omega
      have hhi : sint x + sint y < 2 ^ 63 := by omega
      rw [add64_sint, bmod_in_range _ hlo hhi]

/-- Without SUB overflow the signed result is the exact difference. -/
theorem sub64_sint_eq_of_no_overflow (x y : Wort)
    (h : (sub64 x y).2.of = false) :
    sint (sub64 x y).1 = sint x - sint y := by
  by_cases hP : sint x - sint y < -(2 ^ 63 : Int)
  · have hc := (sub64_of_iff x y).mpr (Or.inl hP)
    simp [hc] at h
  · by_cases hQ : (2 ^ 63 : Int) ≤ sint x - sint y
    · have hc := (sub64_of_iff x y).mpr (Or.inr hQ)
      simp [hc] at h
    · have hlo : -(2 ^ 63 : Int) ≤ sint x - sint y := by omega
      have hhi : sint x - sint y < 2 ^ 63 := by omega
      rw [sub64_sint, bmod_in_range _ hlo hhi]

/-- Cleared ADD overflow is the in-range conjunction on the exact sum. -/
theorem add64_of_false_bounds (x y : Wort)
    (h : (add64 x y).2.of = false) :
    -(2 ^ 63 : Int) ≤ sint x + sint y ∧ sint x + sint y < 2 ^ 63 := by
  by_cases hP : sint x + sint y < -(2 ^ 63 : Int)
  · have hc := (add64_of_iff x y).mpr (Or.inl hP)
    simp [hc] at h
  · by_cases hQ : (2 ^ 63 : Int) ≤ sint x + sint y
    · have hc := (add64_of_iff x y).mpr (Or.inr hQ)
      simp [hc] at h
    · exact ⟨by omega, by omega⟩

/-- Cleared SUB overflow is the in-range conjunction on the exact
    difference. -/
theorem sub64_of_false_bounds (x y : Wort)
    (h : (sub64 x y).2.of = false) :
    -(2 ^ 63 : Int) ≤ sint x - sint y ∧ sint x - sint y < 2 ^ 63 := by
  by_cases hP : sint x - sint y < -(2 ^ 63 : Int)
  · have hc := (sub64_of_iff x y).mpr (Or.inl hP)
    simp [hc] at h
  · by_cases hQ : (2 ^ 63 : Int) ≤ sint x - sint y
    · have hc := (sub64_of_iff x y).mpr (Or.inr hQ)
      simp [hc] at h
    · exact ⟨by omega, by omega⟩

/-- Without ADD carry the unsigned result is the exact Nat sum. -/
theorem add64_cf_false_nat (x y : Wort)
    (h : (add64 x y).2.cf = false) :
    (add64 x y).1.toNat = x.toNat + y.toNat := by
  have hlt : x.toNat + y.toNat < 2 ^ 64 := by
    have hneg : ¬ 2 ^ 64 ≤ x.toNat + y.toNat := by
      rw [← add64_cf x y]
      simp [h]
    omega
  rw [add64_wert x y]
  exact Nat.mod_eq_of_lt hlt

/-- With ADD carry the unsigned result is the exact sum minus `2^64`. -/
theorem add64_cf_true_nat (x y : Wort)
    (h : (add64 x y).2.cf = true) :
    (add64 x y).1.toNat = x.toNat + y.toNat - 2 ^ 64 := by
  have hle : 2 ^ 64 ≤ x.toNat + y.toNat := (add64_cf x y).mp h
  have hx := x.isLt
  have hy := y.isLt
  rw [add64_wert x y]
  omega

/-- Without SUB borrow the unsigned result is the exact Nat difference. -/
theorem sub64_no_borrow_nat (x y : Wort)
    (h : (sub64 x y).2.cf = false) :
    (sub64 x y).1.toNat = x.toNat - y.toNat := by
  have hle : y.toNat ≤ x.toNat := by
    have hneg : ¬ x.toNat < y.toNat := by
      rw [← sub64_cf x y]
      simp [h]
    omega
  have hx := x.isLt
  have hy := y.isLt
  rw [sub64_wert x y]
  omega

/-- With SUB borrow the unsigned result is the exact difference plus
    `2^64`. -/
theorem sub64_borrow_nat (x y : Wort)
    (h : (sub64 x y).2.cf = true) :
    (sub64 x y).1.toNat = x.toNat + 2 ^ 64 - y.toNat := by
  have hlt : x.toNat < y.toNat := (sub64_cf x y).mp h
  have hx := x.isLt
  have hy := y.isLt
  rw [sub64_wert x y]
  omega

/-- The ADD sign flag is negativity of the signed result. -/
theorem add64_sf_sint (x y : Wort) :
    (add64 x y).2.sf = decide (sint (add64 x y).1 < 0) := by
  have hval : (add64 x y).1 = x + y := rfl
  rw [add64_sf, hval]
  exact sfTest_sint (x + y)

/-- The SUB sign flag is negativity of the signed result. -/
theorem sub64_sf_sint (x y : Wort) :
    (sub64 x y).2.sf = decide (sint (sub64 x y).1 < 0) := by
  have hval : (sub64 x y).1 = x - y := rfl
  rw [sub64_sf, hval]
  exact sfTest_sint (x - y)

/-! ## 7. Low-byte parity.

    PF reads only the result low byte: `parityEven` factors through the
    low 8 bits, and xoring a value with itself has even parity. -/

/-- Parity reads only the low byte. -/
theorem parityEven_low8 (w : Wort) :
    parityEven w = parityEven (BitVec.ofNat 64 (w.toNat % 256)) := by
  have he : (BitVec.ofNat 64 (w.toNat % 256)).toNat % 256 =
      w.toNat % 256 := by
    rw [BitVec.toNat_ofNat]
    omega
  unfold parityEven
  rw [he]

/-- Zero has even parity. -/
theorem parityEven_zero : parityEven 0 = true := by decide

/-- `x ^^^ x` has even parity. -/
theorem parityEven_xor_self (x : Wort) :
    parityEven (x ^^^ x) = true := by
  rw [BitVec.xor_self]
  exact parityEven_zero

/-- The XOR parity flag of a self-xor is set. -/
theorem xor64_pf_self (x : Wort) : (xor64 x x).2.pf = true := by
  rw [xor64_pf]
  exact parityEven_xor_self x

/-! ## 8. Jointly instantiated boundary witnesses.

    Each witness pins ONE concrete operand pair with its value and all
    four flags jointly, so the CF/OF independence and the signed
    extremes are inhabited, not just stated. -/

/-- Signed values of the boundary words. -/
theorem sint_werte :
    sint (0xFFFFFFFFFFFFFFFF : Wort) = -1 ∧
    sint (0x7FFFFFFFFFFFFFFF : Wort) = 2 ^ 63 - 1 ∧
    sint (0x8000000000000000 : Wort) = -(2 ^ 63 : Int) ∧
    sint (0 : Wort) = 0 ∧ sint (1 : Wort) = 1 := by
  decide

/-- Carry without overflow: `0xFF..FF + 1 = 0`, CF set, OF clear. -/
theorem wit_add_carry_no_overflow :
    (add64 0xFFFFFFFFFFFFFFFF 1).1 = 0 ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.cf = true ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.of = false ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.sf = false ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.zf = true := by
  decide

/-- Overflow without carry: `0x7F..FF + 1 = 0x80..00`, OF set. -/
theorem wit_add_overflow_no_carry :
    (add64 0x7FFFFFFFFFFFFFFF 1).1 = 0x8000000000000000 ∧
    (add64 0x7FFFFFFFFFFFFFFF 1).2.cf = false ∧
    (add64 0x7FFFFFFFFFFFFFFF 1).2.of = true ∧
    (add64 0x7FFFFFFFFFFFFFFF 1).2.sf = true := by
  decide

/-- Signed-min negation overflows: `0 - (-2^63)` is `2^63`,
    out of range, with a borrow. -/
theorem wit_sub_min_negation :
    (sub64 0 0x8000000000000000).1 = 0x8000000000000000 ∧
    (sub64 0 0x8000000000000000).2.cf = true ∧
    (sub64 0 0x8000000000000000).2.of = true ∧
    (sub64 0 0x8000000000000000).2.sf = true := by
  decide

/-- `min - 1` underflows the signed range without a borrow. -/
theorem wit_sub_min_minus_one :
    (sub64 0x8000000000000000 1).1 = 0x7FFFFFFFFFFFFFFF ∧
    (sub64 0x8000000000000000 1).2.cf = false ∧
    (sub64 0x8000000000000000 1).2.of = true ∧
    (sub64 0x8000000000000000 1).2.sf = false := by
  decide

/-- Both flags together: `min + (-1)` wraps to `max` with carry. -/
theorem wit_add_both_flags :
    (add64 0x8000000000000000 0xFFFFFFFFFFFFFFFF).1 =
      0x7FFFFFFFFFFFFFFF ∧
    (add64 0x8000000000000000 0xFFFFFFFFFFFFFFFF).2.cf = true ∧
    (add64 0x8000000000000000 0xFFFFFFFFFFFFFFFF).2.of = true := by
  decide

/-- `min - min` is exact: zero, no borrow, no overflow. -/
theorem wit_sub_min_self :
    (sub64 0x8000000000000000 0x8000000000000000).1 = 0 ∧
    (sub64 0x8000000000000000 0x8000000000000000).2.cf = false ∧
    (sub64 0x8000000000000000 0x8000000000000000).2.of = false ∧
    (sub64 0x8000000000000000 0x8000000000000000).2.zf = true := by
  decide

/-! ## 9. Memory roundtrips of boundary results.

    The boundary values above survive a real store/load roundtrip
    through `write64`/`read64` on a fully permissive store, jointly with
    their flag facts: the flags characterise the values memory holds. -/

/-- Fully permissive store with zeroed bytes. -/
def flagMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- The store after writing the carry-without-overflow result. -/
def flagMemNachAdd : Speicher :=
  { flagMem with bytes := writeBytes flagMem 0 (add64 0xFFFFFFFFFFFFFFFF 1).1 }

/-- The carry-without-overflow result roundtrips through memory. -/
theorem wit_mem_add_carry :
    write64 flagMem 0 (add64 0xFFFFFFFFFFFFFFFF 1).1 =
      some flagMemNachAdd ∧
    read64 flagMemNachAdd 0 = some (add64 0xFFFFFFFFFFFFFFFF 1).1 ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.cf = true ∧
    (add64 0xFFFFFFFFFFFFFFFF 1).2.of = false := by
  have hwr : write64 flagMem 0 (add64 0xFFFFFFFFFFFFFFFF 1).1 =
      some flagMemNachAdd := by
    unfold write64 flagMemNachAdd
    have hc : schreibbar8 flagMem 0 = true := rfl
    rw [if_pos hc]
  exact ⟨hwr, read64_nach_write64 flagMem _ 0 _ hwr rfl,
    by decide, by decide⟩

/-- The store after writing the `min - 1` overflow result. -/
def flagMemNachSub : Speicher :=
  { flagMem with bytes := writeBytes flagMem 0 (sub64 0x8000000000000000 1).1 }

/-- The `min - 1` overflow result roundtrips through memory. -/
theorem wit_mem_sub_overflow :
    write64 flagMem 0 (sub64 0x8000000000000000 1).1 =
      some flagMemNachSub ∧
    read64 flagMemNachSub 0 = some (sub64 0x8000000000000000 1).1 ∧
    (sub64 0x8000000000000000 1).2.cf = false ∧
    (sub64 0x8000000000000000 1).2.of = true := by
  have hwr : write64 flagMem 0 (sub64 0x8000000000000000 1).1 =
      some flagMemNachSub := by
    unfold write64 flagMemNachSub
    have hc : schreibbar8 flagMem 0 = true := rfl
    rw [if_pos hc]
  exact ⟨hwr, read64_nach_write64 flagMem _ 0 _ hwr rfl,
    by decide, by decide⟩

/- CUTS:
    No instruction execution, decoder, encoding, memory/state transition
    beyond the two §9 roundtrips, TSO bridge, source correspondence,
    ABI/loader theorem, cost transfer or final-image acceptance is proved
    here. Flag characterisation covers only the two 64-bit operations
    `add64`/`sub64` (plus the XOR parity facts of §7); narrow widths have
    no flag snapshots here. The even-parity reading of PF and the
    nibble-carry meaning of AF are inherited from `Wort.lean`, stated,
    not verified against hardware. No source/ISA hardware theorem is
    claimed; physical instruction semantics remain named silicon behaviour
    plus a later bridge (lane 277 owns it).
-/

#print axioms sint_mem
#print axioms sfTest_msb
#print axioms sfTest_toNat
#print axioms sint_neg_of_msb
#print axioms sint_nonneg_of_nmsb
#print axioms sfTest_sint
#print axioms bmod_in_range
#print axioms bmod_high
#print axioms bmod_low
#print axioms add64_sint
#print axioms add64_of_iff
#print axioms sub64_sint
#print axioms sub64_of_iff
#print axioms add64_sint_eq_of_no_overflow
#print axioms sub64_sint_eq_of_no_overflow
#print axioms add64_of_false_bounds
#print axioms sub64_of_false_bounds
#print axioms add64_cf_false_nat
#print axioms add64_cf_true_nat
#print axioms sub64_no_borrow_nat
#print axioms sub64_borrow_nat
#print axioms add64_sf_sint
#print axioms sub64_sf_sint
#print axioms parityEven_low8
#print axioms parityEven_zero
#print axioms parityEven_xor_self
#print axioms xor64_pf_self
#print axioms sint_werte
#print axioms wit_add_carry_no_overflow
#print axioms wit_add_overflow_no_carry
#print axioms wit_sub_min_negation
#print axioms wit_sub_min_minus_one
#print axioms wit_add_both_flags
#print axioms wit_sub_min_self
#print axioms wit_mem_add_carry
#print axioms wit_mem_sub_overflow

end Gabbro.Grammatik.X86
