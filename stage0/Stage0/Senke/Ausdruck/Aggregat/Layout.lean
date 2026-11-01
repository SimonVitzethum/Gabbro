/- Canonical word widths for copied values and all frame/parameter offsets. -/
import Grammatik.Kern.Semantik.Semantik

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- Number of little-endian words needed for a bounded integer. A signed word and
    an unsigned word share their bit representation; operators select signedness.
    The negative bound includes a sign bit. -/
def integerWords (lo hi : Int) : Nat :=
  max 1 (max (((hi.toNat.log2 + if lo < 0 then 1 else 0) / 64) + 1) (((-lo - 1).toNat.log2 + 1) / 64 + 1))

/-- A sum fits one word: eight tag bits and a 56-bit unsigned payload offset. -/
def sumFits (cs : List (Option (Int × Int))) : Bool :=
  decide (cs.length ≤ 256) && cs.all (fun c => match c with
    | none => true
    | some (lo, hi) => decide (hi - lo < 2 ^ 56))

/-- Largest payload offset, independently of the tag's width. -/
def sumPayloadWords (cs : List (Option (Int × Int))) : Nat :=
  cs.foldl (fun width c => max width (match c with
    | none => 0
    | some (lo, hi) => integerWords 0 (hi - lo))) 0

/-- Canonical width in runner words, including the empty value's zero marker.
    Long strings contain length followed by one word per byte, padded with zero.
    Short strings retain their established packed encoding. -/
def valueWords : Ty → Nat
  | .int lo hi => integerWords lo hi
  | .arr τ n => max 1 (n * valueWords τ)
  | .str n => if n ≤ 1 then 1 else n + 1
  | .opt n => if n ≤ 2 ^ 63 then 1 else 1 + integerWords 0 (n - 1)
  | .sum cs => if sumFits cs then 1 else
      integerWords 0 (cs.length - 1) + sumPayloadWords cs
  | .why n => integerWords 0 (n - 1)
  | _ => 1

/-- The values whose complete encoding is the single word of the established scalar operations. -/
def wordCompatB : Ty → Bool
  | .opt n => decide (n ≤ 2 ^ 63)
  | .sum cs => sumFits cs
  | .arr τ n => match n with
    | 0 => true
    | 1 => wordCompatB τ
    | _ => false
  | .str n => decide (n ≤ 1)
  | _ => true

/-- Result area width; empty returns keep one ABI word. -/
def resultWords : Option Ty → Nat
  | none => 1
  | some τ => valueWords τ

/-- One shared return area carries either the normal value or a reason value.
    The status and all relocated parameters follow the larger complete span. -/
def returnWords (result : Option Ty) (reasons : Nat) : Nat :=
  max (resultWords result) (valueWords (.why reasons))

theorem resultWords_le_returnWords (result : Option Ty) (reasons : Nat) :
    resultWords result ≤ returnWords result reasons := Nat.le_max_left _ _

theorem reasonWords_le_returnWords (result : Option Ty) (reasons : Nat) :
    valueWords (.why reasons) ≤ returnWords result reasons := Nat.le_max_right _ _

/-- Contexts and parameter lists use the same width calculation. -/
def contextWords : List Ty → Nat
  | [] => 0
  | τ :: Γ => contextWords Γ + valueWords τ

@[simp] theorem contextWords_nil : contextWords [] = 0 := rfl
@[simp] theorem contextWords_cons (τ : Ty) (Γ : Ctx) :
    contextWords (τ :: Γ) = contextWords Γ + valueWords τ := rfl

theorem valueWords_pos (τ : Ty) : 0 < valueWords τ := by
  cases τ <;> simp only [valueWords, integerWords] <;> (try split) <;> omega

theorem resultWords_pos (e : Option Ty) : 0 < resultWords e := by
  cases e with
  | none => decide
  | some τ => exact valueWords_pos τ

@[simp] theorem contextWords_replicate (n : Nat) (τ : Ty) :
    contextWords (List.replicate n τ) = n * valueWords τ := by
  induction n with
  | zero => simp [contextWords]
  | succ n ih => simp only [List.replicate_succ, contextWords_cons, ih, Nat.succ_mul]

theorem contextWords_length (Γ : Ctx) : Γ.length ≤ contextWords Γ := by
  induction Γ with
  | nil => exact Nat.le_refl _
  | cons τ Γ ih => have := valueWords_pos τ; simp only [List.length_cons, contextWords_cons]; omega

theorem integerWords_word {lo hi : Int} (hl : -(2 ^ 63) ≤ lo) (hh : hi < 2 ^ 63) :
    integerWords lo hi = 1 := by
  have hp : hi.toNat < 2 ^ 63 := by omega
  have hn : (-lo - 1).toNat < 2 ^ 63 := by omega
  have hpl : hi.toNat.log2 < 63 := by
    by_cases hz : hi.toNat = 0
    · simp [hz]
    · exact (Nat.log2_lt hz).mpr hp
  have hnl : (-lo - 1).toNat.log2 < 63 := by
    by_cases hz : (-lo - 1).toNat = 0
    · simp [hz]
    · exact (Nat.log2_lt hz).mpr hn
  simp only [integerWords]
  split <;> omega

/-- Unsigned scalar ranges retain one word without consuming a sign bit. -/
theorem integerWords_unsigned {lo hi : Int} (hl : 0 ≤ lo) (hh : hi < 2 ^ 64) :
    integerWords lo hi = 1 := by
  have hz : (-lo - 1).toNat = 0 := by omega
  have hp : hi.toNat < 2 ^ 64 := by omega
  have hlog : hi.toNat.log2 < 64 := by
    by_cases hn : hi.toNat = 0
    · simp [hn]
    · exact (Nat.log2_lt hn).mpr hp
  simp only [integerWords, if_neg (by omega : ¬lo < 0), Nat.add_zero, hz]
  have : (0 : Nat).log2 = 0 := rfl
  rw [this]
  omega

/-- The selected width has room for the declared upper bound, including a sign
    bit exactly when the source interval admits negative values. -/
theorem integerWords_high (lo hi : Int) :
    hi.toNat < 2 ^ (64 * integerWords lo hi - if lo < 0 then 1 else 0) := by
  have width : 1 ≤ integerWords lo hi := by unfold integerWords; omega
  have digits : (hi.toNat.log2 + if lo < 0 then 1 else 0) / 64 + 1 ≤ integerWords lo hi := by
    unfold integerWords; omega
  have exponent : hi.toNat.log2 < 64 * integerWords lo hi - if lo < 0 then 1 else 0 := by
    by_cases negative : lo < 0
    · simp only [if_pos negative] at digits ⊢; omega
    · simp only [if_neg negative] at digits ⊢; omega
  by_cases zero : hi.toNat = 0
  · rw [zero]
    exact Nat.two_pow_pos _
  · exact (Nat.log2_lt zero).mp exponent

/-- The negative lower bound fits the signed interpretation of the top limb. -/
theorem integerWords_low (lo hi : Int) :
    (-lo - 1).toNat < 2 ^ (64 * integerWords lo hi - 1) := by
  have width : 1 ≤ integerWords lo hi := by unfold integerWords; omega
  have digits : ((-lo - 1).toNat.log2 + 1) / 64 + 1 ≤ integerWords lo hi := by
    unfold integerWords; omega
  have exponent : (-lo - 1).toNat.log2 < 64 * integerWords lo hi - 1 := by omega
  by_cases zero : (-lo - 1).toNat = 0
  · rw [zero]
    exact Nat.two_pow_pos _
  · exact (Nat.log2_lt zero).mp exponent

theorem integerWords_signed {lo hi z : Int} (negative : lo < 0) (lower : lo ≤ z) (upper : z ≤ hi) :
    -(2 ^ (64 * integerWords lo hi - 1)) ≤ z ∧ z < 2 ^ (64 * integerWords lo hi - 1) := by
  have high := integerWords_high lo hi
  rw [if_pos negative] at high
  have low := integerWords_low lo hi
  have boundHigh : (hi.toNat : Int) < 2 ^ (64 * integerWords lo hi - 1) := by exact_mod_cast high
  have boundLow : ((-lo - 1).toNat : Int) < 2 ^ (64 * integerWords lo hi - 1) := by exact_mod_cast low
  omega

theorem integerWords_nonnegative {lo hi z : Int} (positive : 0 ≤ lo) (lower : lo ≤ z) (upper : z ≤ hi) :
    0 ≤ z ∧ z < 2 ^ (64 * integerWords lo hi) := by
  have high := integerWords_high lo hi
  rw [if_neg (by omega : ¬lo < 0), Nat.sub_zero] at high
  have bound : (hi.toNat : Int) < 2 ^ (64 * integerWords lo hi) := by exact_mod_cast high
  omega

theorem integerWords_range {lo hi z : Int} (lower : lo ≤ z) (upper : z ≤ hi) :
    -(2 ^ (64 * integerWords lo hi)) ≤ z ∧ z < 2 ^ (64 * integerWords lo hi) := by
  by_cases negative : lo < 0
  · have signed := integerWords_signed negative lower upper
    have capacity : (2 : Int) ^ (64 * integerWords lo hi - 1) ≤ 2 ^ (64 * integerWords lo hi) := by
      exact_mod_cast (Nat.pow_le_pow_right (n := 2) (i := 64 * integerWords lo hi - 1) (by decide) (by omega))
    omega
  · have nonnegative := integerWords_nonnegative (by omega : 0 ≤ lo) lower upper
    have capacity : (0 : Int) < 2 ^ (64 * integerWords lo hi) := Int.pow_pos (by decide)
    omega

@[simp] theorem resultWords_vertragVon (D : Deklaration) (f : D.Fn) :
    resultWords (vertragVon D f).erg = resultWords (D.erg f) := rfl

@[simp] theorem returnWords_vertragVon (D : Deklaration) (f : D.Fn) :
    returnWords (vertragVon D f).erg (vertragVon D f).gruende =
      returnWords (D.erg f) (D.gruende f) := rfl

end Gabbro.Stage0.Senke
