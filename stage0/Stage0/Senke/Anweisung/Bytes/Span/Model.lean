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
    change dropBytes j z / 256 = z / 256 ^ (j + 1)
    rw [ih, Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide : (0 : Int) ≤ 256)),
      Int.pow_succ]

theorem dropBytes_add (j k : Nat) (z : Int) : dropBytes (j + k) z = dropBytes k (dropBytes j z) := by
  induction k with
  | zero => simp [dropBytes]
  | succ k ih =>
    change dropBytes (j + k) z / 256 = dropBytes k (dropBytes j z) / 256
    exact congrArg (fun v : Int => v / 256) ih

theorem bytesZuZahl_append (as bs : List Byte) :
    bytesZuZahl (as ++ bs) = bytesZuZahl as + 256 ^ as.length * bytesZuZahl bs := by
  induction as with
  | nil => simp [bytesZuZahl]
  | cons a as ih =>
    simp only [List.cons_append, bytesZuZahl, ih, List.length_cons, Int.pow_succ]
    rw [Int.mul_add, ← Int.add_assoc, ← Int.mul_assoc,
      Int.mul_comm 256 (256 ^ as.length)]

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
      calc
        dropBytes (j + 1) (bytesZuZahl (b :: bs)) =
            dropBytes j (dropBytes 1 (bytesZuZahl (b :: bs))) := by
          rw [Nat.add_comm j 1, dropBytes_add]
        _ = bytesZuZahl ((b :: bs).drop (j + 1)) := by
          change dropBytes j (bytesZuZahl (b :: bs) / 256) = bytesZuZahl (bs.drop j)
          rw [div]
          exact ih bs

/-- Adjacent chunks concatenate to precisely the original machine-G read span. -/
theorem World.bytesAb_append (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (k n : Nat) (p : Int) :
    σ.bytesAb t f hf (k + n) p =
      σ.bytesAb t f hf k p ++ σ.bytesAb t f hf n (p + k) := by
  induction k generalizing p with
  | zero => simp [World.bytesAb]
  | succ k ih =>
    rw [Nat.succ_add]
    have offset : (p + 1) + (k : Int) = p + ((k + 1 : Nat) : Int) := by omega
    have tail := ih (p + 1)
    rw [offset] at tail
    exact congrArg (List.cons _) tail

theorem bytesAb_drop (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (k n : Nat) (p : Int) :
    (σ.bytesAb t f hf n p).drop k = σ.bytesAb t f hf (n - k) (p + k) := by
  induction k generalizing n p with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp [World.bytesAb]
    | succ n =>
      rw [Nat.succ_sub_succ_eq_sub]
      have offset : (p + 1) + (k : Int) = p + ((k + 1 : Nat) : Int) := by omega
      have tail := ih n (p + 1)
      rw [offset] at tail
      exact tail

theorem bytesAb_take (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (k n : Nat) (p : Int) :
    (σ.bytesAb t f hf n p).take k = σ.bytesAb t f hf (min k n) p := by
  induction k generalizing n p with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [Nat.succ_min_succ]
      exact congrArg (List.cons _) (ih n (p + 1))

/-- One read kernel returns exactly the low limb of the remaining byte span. -/
theorem bytes_chunk_word (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (n : Nat) (p : Int) :
    BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf n p)) =
      BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf (min 8 n) p)) := by
  by_cases short : n ≤ 8
  · rw [Nat.min_eq_right short]
  · have chunks : σ.bytesAb t f hf n p =
        σ.bytesAb t f hf 8 p ++ σ.bytesAb t f hf (n - 8) (p + 8) := by
      have total : 8 + (n - 8) = n := by omega
      simpa only [total, show ((8 : Nat) : Int) = (8 : Int) from rfl] using
        (World.bytesAb_append σ t f hf 8 (n - 8) p)
    rw [chunks, bytesZuZahl_append, World.bytesAb_length, BitVec.ofInt_add, BitVec.ofInt_mul]
    have zero : BitVec.ofInt 64 ((256 : Int) ^ 8) = 0#64 := by decide
    rw [zero, BitVec.zero_mul, BitVec.add_zero]
    rw [Nat.min_eq_left (by omega : 8 ≤ n)]

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
