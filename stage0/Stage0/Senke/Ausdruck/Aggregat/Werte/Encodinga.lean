/- Canonical value words, shared by frames, world storage and call boundaries. -/
module
public import Stage0.Senke.Welt.Lay
public import Stage0.Senke.Ausdruck.Aggregat.Layout
public import Stage0.Senke.Ausdruck.Aggregat.Wert
public import Stage0.Senke.Ausdruck.Aggregat.Kopie
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- Concatenated representations occupy consecutive spans without padding gaps. -/
theorem wordsAt_append {m : Runner.Mem} {fp : Runner.W} {base : Nat} (xs ys : List Runner.W) :
    WordsAt m fp base (xs ++ ys) ↔
      WordsAt m fp base xs ∧ WordsAt m fp (base + xs.length) ys := by
  constructor
  · intro words
    constructor
    · intro i hi
      have read := words i (by simp; omega)
      simpa only [List.getElem_append_left hi] using read
    · intro i hi
      have read := words (xs.length + i) (by simp; omega)
      simpa [List.getElem_append_right, Nat.add_assoc] using read
  · intro words i hi
    by_cases left : i < xs.length
    · simpa only [List.getElem_append_left left] using words.1 i left
    · have bound : i - xs.length < ys.length := by simp only [List.length_append] at hi; omega
      have read := words.2 (i - xs.length) bound
      have index : xs.length + (i - xs.length) = i := by omega
      rw [Nat.add_assoc, index] at read
      simpa only [List.getElem_append_right (by omega : xs.length ≤ i)] using read

/-- The payload's distance from the lower bound; a bare arm has offset zero. -/
def sumOff : (c : Option (Int × Int)) → Nutzlast c → Nat
  | none, _ => 0
  | some (lo, _), v => (v.n - lo).toNat

/-- The representation shared by frames, tables and globals. -/
def sumN {cs : List (Option (Int × Int))} (v : Wert D (.sum cs)) : Nat :=
  v.1.val + 256 * sumOff (cs.get v.1) v.2

/-- The number of an option: `-1` for absent, the index otherwise. -/
def optN {n : Int} : Option (Zahl 0 (n - 1)) → Int
  | Option.none => -1
  | Option.some k => k.n

/-- Little-endian two's-complement limbs, sign extended by Euclidean division. -/
def integerEncoding : Nat → Int → List Runner.W
  | 0, _ => []
  | n + 1, v => BitVec.ofInt 64 v :: integerEncoding n (v / 2 ^ 64)

@[simp] theorem integerEncoding_length (n : Nat) (v : Int) :
    (integerEncoding n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [integerEncoding, ih]

theorem integerEncoding_zero (n : Nat) : integerEncoding n 0 = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [integerEncoding, ih, List.replicate_succ]

theorem integerEncoding_negative_one (n : Nat) :
    integerEncoding n (-1) = List.replicate n (BitVec.ofInt 64 (-1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have quotient : (-1 : Int) / 2 ^ 64 = -1 :=
      Int.ediv_eq_neg_one_of_neg_of_le (by decide) (by decide)
    simpa only [integerEncoding, quotient, List.replicate_succ] using congrArg (List.cons (BitVec.ofInt 64 (-1))) ih

/-- Splitting a canonical integer is Euclidean division, independent of its
    source type. Width changes reuse this identity instead of a second encoding. -/
theorem integerEncoding_append (n k : Nat) (z : Int) :
    integerEncoding (n + k) z = integerEncoding n z ++ integerEncoding k (z / 2 ^ (64 * n)) := by
  induction n generalizing z with
  | zero => simp [integerEncoding]
  | succ n ih =>
    simp only [Nat.succ_add, integerEncoding, ih, List.cons_append]
    have denominator : (2 : Int) ^ 64 * 2 ^ (64 * n) = 2 ^ (64 * (n + 1)) := by
      rw [show 64 * (n + 1) = 64 + 64 * n by omega, Int.pow_add]
    rw [Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 2 ^ 64), denominator]

/-- Extra limbs are the sign extension of a value already fitting the source
    span. No new value interpretation is introduced at a widening boundary. -/
theorem integerEncoding_extend {n : Nat} (k : Nat) (z : Int)
    (lower : -(2 ^ (64 * n)) ≤ z) (upper : z < 2 ^ (64 * n)) :
    integerEncoding (n + k) z = integerEncoding n z ++
      List.replicate k (if z < 0 then BitVec.ofInt 64 (-1) else 0) := by
  rw [integerEncoding_append]
  by_cases negative : z < 0
  · rw [if_pos negative, Int.ediv_eq_neg_one_of_neg_of_le negative (by omega), integerEncoding_negative_one]
  · rw [if_neg negative, Int.ediv_eq_zero_of_lt (by omega) upper, integerEncoding_zero]

theorem integerEncoding_take {n k : Nat} (z : Int) (bound : k ≤ n) :
    (integerEncoding n z).take k = integerEncoding k z := by
  induction k generalizing n z with
  | zero => simp [integerEncoding]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [integerEncoding, List.take_succ_cons]
      rw [ih _ (by omega)]

theorem integerEncoding_last {n : Nat} (positive : 0 < n) (z : Int) :
    integerEncoding n z = integerEncoding (n - 1) z ++
      [BitVec.ofInt 64 (z / 2 ^ (64 * (n - 1)))] := by
  have split := integerEncoding_append (n - 1) 1 z
  rw [show n - 1 + 1 = n by omega] at split
  simpa only [integerEncoding, List.append_nil] using split

theorem integerEncoding_top_signed {n : Nat} (positive : 0 < n) (z : Int)
    (lower : -(2 ^ (64 * n - 1)) ≤ z) (upper : z < 2 ^ (64 * n - 1)) :
    -(2 ^ 63) ≤ z / 2 ^ (64 * (n - 1)) ∧
      z / 2 ^ (64 * (n - 1)) < 2 ^ 63 ∧
      (z / 2 ^ (64 * (n - 1)) < 0 ↔ z < 0) := by
  have denominator : (0 : Int) < 2 ^ (64 * (n - 1)) := Int.pow_pos (by decide)
  have capacity : (2 : Int) ^ (64 * n - 1) = 2 ^ 63 * 2 ^ (64 * (n - 1)) := by
    rw [← Int.pow_add, show 63 + 64 * (n - 1) = 64 * n - 1 by omega]
  rw [capacity] at lower upper
  refine ⟨(Int.le_ediv_iff_mul_le denominator).mpr ?_,
    (Int.ediv_lt_iff_lt_mul denominator).mpr upper, ?_⟩
  · simpa only [Int.neg_mul] using lower
  · rw [Int.ediv_lt_iff_lt_mul denominator, Int.zero_mul]

/-- Flatten elements in increasing index order. No pointer or allocation is introduced. -/
def elementEncoding : (n : Nat) → (Fin n → List Runner.W) → List Runner.W
  | 0, _ => []
  | n + 1, f => f ⟨0, by omega⟩ ++ elementEncoding n (fun i => f i.succ)

theorem elementEncoding_length (n width : Nat) (f : Fin n → List Runner.W)
    (hf : ∀ i, (f i).length = width) : (elementEncoding n f).length = n * width := by
  induction n with
  | zero => simp [elementEncoding]
  | succ n ih => simp only [elementEncoding, List.length_append, hf, ih _ (fun i => hf i.succ), Nat.succ_mul]; omega

/-- Selecting an array element keeps its entire contiguous representation. -/
theorem elementEncoding_wordsAt {m : Runner.Mem} {fp : Runner.W} {base n width : Nat}
    (f : Fin n → List Runner.W) (lengths : ∀ i, (f i).length = width)
    (input : WordsAt m fp base (elementEncoding n f)) (j : Fin n) :
    WordsAt m fp (base + j.val * width) (f j) := by
  induction n generalizing base with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    have parts := (wordsAt_append _ _).mp input
    cases j using Fin.cases with
    | zero => simpa using parts.1
    | succ j =>
      have tail := ih (base := base + width) (fun i => f i.succ)
        (fun i => lengths i.succ) (by simpa only [lengths] using parts.2) j
      simpa only [Fin.val_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using tail


end Gabbro.Stage0.Senke
