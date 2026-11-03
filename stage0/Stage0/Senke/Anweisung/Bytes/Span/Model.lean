/- Byte chunks use the same Euclidean divisions as the canonical integer limbs. -/
module
public import Stage0.Senke.Anweisung.Bytes.Code
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

theorem dropBytes_pow (j : Nat) (z : Int) : dropBytes j z = z / 256 ^ j := by
  induction j with
  | zero => simp [dropBytes]
  | succ j ih =>
    simp only [dropBytes, ih, Int.ediv_ediv_of_nonneg (by positivity : (0 : Int) ≤ 256 ^ j),
      Int.pow_succ]

theorem dropBytes_add (j k : Nat) (z : Int) : dropBytes (j + k) z = dropBytes k (dropBytes j z) := by
  induction k with
  | zero => simp [dropBytes]
  | succ k ih => simp only [Nat.add_succ, dropBytes, ih]

theorem bytesZuZahl_append (as bs : List Byte) :
    bytesZuZahl (as ++ bs) = bytesZuZahl as + 256 ^ as.length * bytesZuZahl bs := by
  induction as with
  | nil => simp [bytesZuZahl]
  | cons a as ih =>
    simp only [List.cons_append, bytesZuZahl, ih, List.length_cons, Int.pow_succ]
    ring

theorem dropBytes_bytes (j : Nat) (bs : List Byte) :
    dropBytes j (bytesZuZahl bs) = bytesZuZahl (bs.drop j) := by
  induction j generalizing bs with
  | zero => simp [dropBytes]
  | succ j ih =>
    cases bs with
    | nil => simp [dropBytes_pow, bytesZuZahl]
    | cons b bs =>
      have div : bytesZuZahl (b :: bs) / 256 = bytesZuZahl bs := by
        have := b.lo_le
        have := b.le_hi
        simp only [bytesZuZahl]
        omega
      rw [show j + 1 = 1 + j by omega, dropBytes_add]
      simp only [dropBytes, div, List.drop_succ_cons, ih]

theorem bytesAb_length (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (n : Nat) (p : Int) :
    (σ.bytesAb t f hf n p).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [World.bytesAb, List.length_cons, ih]

theorem bytesAb_drop (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (k n : Nat) (p : Int) :
    (σ.bytesAb t f hf n p).drop k = σ.bytesAb t f hf (n - k) (p + k) := by
  induction k generalizing n p with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp [World.bytesAb]
    | succ n =>
      simp only [World.bytesAb, List.drop_succ_cons, ih, Nat.succ_sub_succ_eq_sub,
        Int.natCast_add, Int.natCast_one]
      congr 1
      omega

theorem bytesAb_take (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (k n : Nat) (p : Int) :
    (σ.bytesAb t f hf n p).take k = σ.bytesAb t f hf (min k n) p := by
  induction k generalizing n p with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [World.bytesAb, List.take_succ_cons, Nat.min_add_add_right, ih]

/-- One read kernel returns exactly the low limb of the remaining byte span. -/
theorem bytes_chunk_word (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (n : Nat) (p : Int) :
    BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf n p)) =
      BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf (min 8 n) p)) := by
  by_cases short : n ≤ 8
  · rw [Nat.min_eq_right short]
  · let bs := σ.bytesAb t f hf n p
    have split := bytesZuZahl_append (bs.take 8) (bs.drop 8)
    rw [List.take_append_drop] at split
    have len : (bs.take 8).length = 8 := by simp [bs, bytesAb_length]; omega
    rw [len] at split
    rw [split, BitVec.ofInt_add, BitVec.ofInt_mul]
    have zero : BitVec.ofInt 64 ((256 : Int) ^ 8) = 0 := by decide
    rw [zero, BitVec.zero_mul, BitVec.add_zero]
    rw [bytesAb_take]

/-- Dropping a complete limb agrees with advancing by one bounded chunk. -/
theorem bytes_chunk_quotient (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (n : Nat) (p : Int) :
    bytesZuZahl (σ.bytesAb t f hf n p) / 2 ^ 64 =
      bytesZuZahl (σ.bytesAb t f hf (n - 8) (p + min 8 n)) := by
  have div := dropBytes_bytes 8 (σ.bytesAb t f hf n p)
  rw [dropBytes_pow, show (256 : Int) ^ 8 = 2 ^ 64 by decide, bytesAb_drop] at div
  by_cases short : n ≤ 8
  · simpa only [Nat.sub_eq_zero_of_le short, World.bytesAb, bytesZuZahl] using div
  · simpa only [Nat.min_eq_left (by omega : 8 ≤ n)] using div

end Gabbro.Stage0.Senke
