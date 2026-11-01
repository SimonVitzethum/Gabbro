/- Subject: Equality of long strings is equality of the first `min n m + 1` words of their encodings. -/
import Stage0.Senke.Ausdruck.Aggregat.StringOps

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable [Runner.IR.Kern] {D : Deklaration} {L : Lay D}

theorem strGetW_n {n : Nat} (w : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Nat) :
    (strGetW w (j : Int)).n = ((w.1.map (·.n))[j]?).getD 0 := by
  simp only [strGetW, Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte]
  rw [List.getElem?_map]
  cases h : w.1[j]? <;> simp

theorem encodeWords_strLong (L : Lay D) {n : Nat} (hn : 2 ≤ n) (w : { bs : List (Zahl 0 255) // bs.length ≤ n }) :
    encodeWords L (.str n) w = BitVec.ofNat 64 w.1.length :: w.1.map (fun b => BitVec.ofInt 64 b.n) ++
      List.replicate (n - w.1.length) (0 : BitVec 64) := by
  simp only [encodeWords, if_neg (show ¬ n ≤ 1 by omega)]

theorem strLong_byte (L : Lay D) {n : Nat} (hn : 2 ≤ n) (w : { bs : List (Zahl 0 255) // bs.length ≤ n })
    (j : Nat) (hj : j < n) :
    (encodeWords L (.str n) w)[j + 1]? = some (BitVec.ofInt 64 (((w.1.map (·.n))[j]?).getD 0)) := by
  rw [encodeWords_strLong L hn, ← strGetW_n]
  exact strBytes_word w j hj

theorem ofInt_byte_inj {x y : Int} (hx : 0 ≤ x) (hx' : x ≤ 255) (hy : 0 ≤ y) (hy' : y ≤ 255)
    (h : BitVec.ofInt 64 x = BitVec.ofInt 64 y) : x = y := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt] at this
  omega

theorem ofNat_len_inj {a b n : Nat} (ha : a ≤ n) (hb : b ≤ n) (hn : n < 2 ^ 63)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem strEq_words_iff {n m : Nat} (hn : 2 ≤ n) (hm : 2 ≤ m) (hn' : n < 2 ^ 63) (hm' : m < 2 ^ 63)
    (s : { bs : List (Zahl 0 255) // bs.length ≤ n }) (t : { bs : List (Zahl 0 255) // bs.length ≤ m }) :
    ((encodeWords L (.str n) s).take (min n m + 1) = (encodeWords L (.str m) t).take (min n m + 1)) ↔
      s.1.map (·.n) = t.1.map (·.n) := by
  have hs := s.2
  have ht := t.2
  have headS : (encodeWords L (.str n) s)[0]? = some (BitVec.ofNat 64 s.1.length) := by
    rw [encodeWords_strLong L hn]; rfl
  have headT : (encodeWords L (.str m) t)[0]? = some (BitVec.ofNat 64 t.1.length) := by
    rw [encodeWords_strLong L hm]; rfl
  constructor
  · intro h
    have hk : ∀ k, k < min n m + 1 → (encodeWords L (.str n) s)[k]? = (encodeWords L (.str m) t)[k]? := by
      intro k hk
      have := congrArg (fun l => l[k]?) h
      simpa only [List.getElem?_take, if_pos hk] using this
    have hlen : s.1.length = t.1.length := by
      have := hk 0 (by omega)
      rw [headS, headT] at this
      exact ofNat_len_inj (by omega) (by omega) (show max n m < 2 ^ 63 by omega) (Option.some.inj this)
    apply List.ext_getElem?
    intro j
    by_cases hj : j < s.1.length
    · have hjt : j < t.1.length := by omega
      have eq := hk (j + 1) (by omega)
      rw [strLong_byte L hn s j (by omega), strLong_byte L hm t j (by omega)] at eq
      have eq' := Option.some.inj eq
      have hsj : (s.1.map (·.n))[j]? = some (s.1[j]).n := by simp [List.getElem?_eq_getElem hj]
      have htj : (t.1.map (·.n))[j]? = some (t.1[j]).n := by simp [List.getElem?_eq_getElem hjt]
      rw [hsj, htj] at eq' ⊢
      simp only [Option.getD_some] at eq'
      have := ofInt_byte_inj (s.1[j]).lo_le (s.1[j]).le_hi (t.1[j]).lo_le (t.1[j]).le_hi eq'
      rw [this]
    · have hjt : ¬ j < t.1.length := by omega
      simp [List.getElem?_eq_none (by simpa using hj : (s.1.map (·.n)).length ≤ j),
        List.getElem?_eq_none (by simpa using hjt : (t.1.map (·.n)).length ≤ j)]
  · intro h
    have hlen : s.1.length = t.1.length := by simpa using congrArg List.length h
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_take, List.getElem?_take]
    by_cases hk : k < min n m + 1
    · simp only [if_pos hk]
      cases k with
      | zero => rw [headS, headT, hlen]
      | succ j =>
        rw [strLong_byte L hn s j (by omega), strLong_byte L hm t j (by omega), h]
    · simp only [if_neg hk]

end Gabbro.Stage0.Senke
