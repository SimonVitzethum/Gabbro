/- Captured wide integers expose bounded byte chunks without truncating their value. -/
module
public import Stage0.Senke.Anweisung.Bytes.Span.Model
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- The unsigned value of one captured canonical limb. -/
def byteLimb (z : Int) (q : Nat) : Zahl 0 (2 ^ 64 - 1) :=
  ⟨(BitVec.ofInt 64 (dropBytes (8 * q) z)).toNat, by omega, by
    have := (BitVec.ofInt 64 (dropBytes (8 * q) z)).isLt
    omega⟩

theorem byteLimb_word (z : Int) (q : Nat) :
    BitVec.ofInt 64 (byteLimb z q).n = BitVec.ofInt 64 (dropBytes (8 * q) z) := by
  simp only [byteLimb, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem integerEncoding_byteLimb : ∀ (w q : Nat) (z : Int) (hq : q < w),
    (integerEncoding w z)[q]'(by simpa only [integerEncoding_length] using hq) =
      BitVec.ofInt 64 (byteLimb z q).n
  | 0, _, _, hq => by omega
  | w + 1, 0, z, _ => by
    rw [byteLimb_word]
    simp only [integerEncoding, List.getElem_cons_zero, Nat.mul_zero, dropBytes]
  | w + 1, q + 1, z, hq => by
    simp only [integerEncoding, List.getElem_cons_succ]
    rw [integerEncoding_byteLimb w q (z / 2 ^ 64) (by omega), byteLimb_word, byteLimb_word,
      dropBytes_pow, dropBytes_pow, Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 2 ^ 64)]
    congr 2
    rw [show 8 * (q + 1) = 8 + 8 * q by omega, Int.pow_add]
    congr 1

/-- A kernel of at most eight bytes sees exactly the bytes of the selected limb.
    The proof enumerates kernel widths only, independently of the full span. -/
theorem zahlZuBytes_limb (k : Nat) (small : k ≤ 8) (z : Int) (q : Nat) :
    zahlZuBytes k (byteLimb z q).n = zahlZuBytes k (dropBytes (8 * q) z) := by
  have mod : (byteLimb z q).n = dropBytes (8 * q) z % 18446744073709551616 := by
    simp only [byteLimb, BitVec.toNat_ofInt]
    omega
  rw [mod]
  match k, small with
  | 0, _ => rfl
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
    simp only [zahlZuBytes, List.cons.injEq, Zahl.mk.injEq, and_true]
    omega

theorem zahlZuBytes_append (k n : Nat) (z : Int) :
    zahlZuBytes (k + n) z = zahlZuBytes k z ++ zahlZuBytes n (dropBytes k z) := by
  induction k generalizing z with
  | zero => simp [zahlZuBytes, dropBytes]
  | succ k ih =>
    simp only [Nat.succ_add, zahlZuBytes, ih, List.cons_append]
    congr 2
    rw [show k + 1 = 1 + k by omega, dropBytes_add]
    rfl

theorem World.schreibBytes_append (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (p : Int) (as bs : List Byte) :
    σ.schreibBytes t f hf Λ p (as ++ bs) =
      (σ.schreibBytes t f hf Λ p as).schreibBytes t f hf Λ (p + as.length) bs := by
  induction as generalizing σ p with
  | nil => simp [World.schreibBytes]
  | cons a as ih =>
    simp only [List.cons_append, World.schreibBytes, ih, List.length_cons,
      Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- The canonical integer span contains every byte chunk of its declared range. -/
theorem byteSpan_capacity (n : Nat) : n ≤ 8 * integerWords 0 (256 ^ n - 1) := by
  let words := integerWords 0 ((256 : Int) ^ n - 1)
  change n ≤ 8 * words
  have high := integerWords_high 0 (256 ^ n - 1)
  rw [if_neg (by decide : ¬(0 : Int) < 0), Nat.sub_zero] at high
  change ((256 : Int) ^ n - 1).toNat < 2 ^ (64 * words) at high
  have power : (256 : Int) ^ n = 2 ^ (8 * n) := by
    rw [show (256 : Int) = 2 ^ 8 by decide, ← Int.pow_mul]
  have positive : (0 : Int) < 256 ^ n := Int.pow_pos (by decide)
  have cast : (((256 : Int) ^ n - 1).toNat : Int) = 256 ^ n - 1 := Int.toNat_of_nonneg (by omega)
  have bound : (((256 : Int) ^ n - 1).toNat : Int) < 2 ^ (64 * words) := by
    have lifted := Int.ofNat_lt.mpr high
    simpa only [Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl] using lifted
  rw [cast, power] at bound
  have natural : 2 ^ (8 * n) ≤ 2 ^ (64 * words) := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl]
    omega
  have exponents := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp natural
  omega

end Gabbro.Stage0.Senke
