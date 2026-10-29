/- Subject: One-byte strings: zero is empty; 256 + byte is nonempty, including a zero byte.
   The explicit length bit makes length, byte access and lexicographic comparison word operations. -/
import Grammatik.Kern.Semantik.Semantik
import Runner.IR.Rahmen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- The string word's unsigned number. Only strings with a maximum of one byte use it. -/
def strN : List (Zahl 0 255) → Nat
  | [] => 0
  | b :: _ => 256 + b.n.toNat

theorem strN_range (bs : List (Zahl 0 255)) : strN bs ≤ 511 := by
  cases bs with
  | nil => simp [strN]
  | cons b _ => have := b.lo_le; have := b.le_hi; simp only [strN]; omega

theorem short_cases {bs : List (Zahl 0 255)} (h : bs.length ≤ 1) :
    bs = [] ∨ ∃ b, bs = [b] := by
  cases bs with
  | nil => exact Or.inl rfl
  | cons b bs =>
    cases bs with
    | nil => exact Or.inr ⟨b, rfl⟩
    | cons _ _ => simp at h

theorem strN_length {n : Nat} (s : {bs : List (Zahl 0 255) // bs.length ≤ n}) (hn : n ≤ 1) :
    (BitVec.ofNat 64 (strN s.1) >>> 8) = BitVec.ofInt 64 (strLenW s).n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hb := strN_range s.1
  rw [Nat.mod_eq_of_lt (by omega)]
  rcases short_cases (Nat.le_trans s.2 hn) with he | ⟨b, he⟩
  · simp [strLenW, he, strN]
  · have := b.lo_le; have := b.le_hi
    simp only [strLenW, he, strN, List.length_cons, List.length_nil]
    simp
    omega

theorem strN_byte {n : Nat} (s : {bs : List (Zahl 0 255) // bs.length ≤ n}) (hn : n ≤ 1) :
    (BitVec.ofNat 64 (strN s.1) &&& 255) = BitVec.ofInt 64 (strGetW s 0).n := by
  apply BitVec.eq_of_toNat_eq
  rw [show (255 : Runner.W) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
    BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hb := strN_range s.1
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [show (2 ^ 8 - 1) % 2 ^ 64 = 255 from rfl]
  rw [show 255 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases short_cases (Nat.le_trans s.2 hn) with he | ⟨b, he⟩
  · simp [strGetW, he, strN]
  · have := b.lo_le; have := b.le_hi
    have hmod : b.n % 2 ^ 64 = b.n := Int.emod_eq_of_lt (by omega) (by omega)
    simp [strGetW, he, strN, BitVec.toNat_ofInt, hmod]
    omega

theorem short_get_other {n : Nat} (s : {bs : List (Zahl 0 255) // bs.length ≤ n}) (hn : n ≤ 1)
    (i : Int) (hi : i ≠ 0) : (strGetW s i).n = 0 := by
  rcases short_cases (Nat.le_trans s.2 hn) with he | ⟨b, he⟩
  · simp [strGetW, he]
  · by_cases hz : 0 ≤ i
    · have ht : 1 ≤ i.toNat := by omega
      have hget : ([b] : List (Zahl 0 255))[i.toNat]? = none := by
        apply List.getElem?_eq_none
        simpa using ht
      simp [strGetW, he, hz, hget]
    · simp [strGetW, hz]

theorem short_eq {n m : Nat} (s : {bs : List (Zahl 0 255) // bs.length ≤ n})
    (t : {bs : List (Zahl 0 255) // bs.length ≤ m}) (hn : n ≤ 1) (hm : m ≤ 1) :
    strEqW s t = decide (strN s.1 = strN t.1) := by
  rcases short_cases (Nat.le_trans s.2 hn) with hs | ⟨a, hs⟩ <;>
    rcases short_cases (Nat.le_trans t.2 hm) with ht | ⟨b, ht⟩
  · simp [strEqW, strN, hs, ht]
  · simp [strEqW, strN, hs, ht]; omega
  · simp [strEqW, strN, hs, ht]
  · have := a.lo_le; have := b.lo_le
    simp [strEqW, strN, hs, ht, Bool.beq_eq_decide_eq]
    omega

theorem short_lt {n m : Nat} (s : {bs : List (Zahl 0 255) // bs.length ≤ n})
    (t : {bs : List (Zahl 0 255) // bs.length ≤ m}) (hn : n ≤ 1) (hm : m ≤ 1) :
    strLtW s t = decide (strN s.1 < strN t.1) := by
  rcases short_cases (Nat.le_trans s.2 hn) with hs | ⟨a, hs⟩ <;>
    rcases short_cases (Nat.le_trans t.2 hm) with ht | ⟨b, ht⟩
  · simp [strLtW, bytesLt, strN, hs, ht]
  · simp [strLtW, bytesLt, strN, hs, ht]; omega
  · simp [strLtW, bytesLt, strN, hs, ht]
  · have := a.lo_le; have := b.lo_le
    simp [strLtW, bytesLt, strN, hs, ht]
    omega
end Gabbro.Stage0.Senke
