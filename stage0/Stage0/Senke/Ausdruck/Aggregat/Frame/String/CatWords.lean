/- Canonical padded-byte spans and the exact concatenation update. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderScan
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Span
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

def stringBytes (n : Nat) (bs : List (Zahl 0 255)) : List Runner.W :=
  bs.map (fun b => BitVec.ofInt 64 b.n) ++ List.replicate (n - bs.length) 0

@[simp] theorem stringBytes_length {n : Nat} (bs : List (Zahl 0 255)) (h : bs.length ≤ n) :
    (stringBytes n bs).length = n := by simp only [stringBytes, List.length_append,
      List.length_map, List.length_replicate]; omega

theorem stringBytes_get {n : Nat} (bs : List (Zahl 0 255)) (h : bs.length ≤ n)
    (j : Nat) (hj : j < n) :
    (stringBytes n bs)[j]? = some (BitVec.ofInt 64 ((bs[j]?).getD ⟨0, by omega, by omega⟩).n) := by
  have read := strBytes_word (n := n) ⟨bs, h⟩ j hj
  simpa only [List.cons_append, List.getElem?_cons_succ, strGetW,
    Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte, stringBytes] using read

theorem stringSpan_bytes {D : Deklaration} {L : Lay D} {cap n base : Nat}
    {m : Runner.Mem} {fp : Runner.W} (capLong : 2 ≤ cap) (fits : n ≤ cap)
    (v : Wert D (.str cap)) (length : v.1.length ≤ n)
    (span : ValueAt L m fp base (.str cap) v) : WordsAt m fp (base + 1) (stringBytes n v.1) := by
  intro j hj
  have bound : j < n := by simpa only [stringBytes_length v.1 length] using hj
  have read := span.2 (j + 1)
    (by rw [encodeWords_length]; simp only [valueWords, if_neg (show ¬ cap ≤ 1 by omega)]; omega)
  have capGet : (encodeWords L (.str cap) v)[j + 1]? =
      some (BitVec.ofInt 64 (strGetW v (j : Int)).n) := by
    simpa only [encodeWords, if_neg (show ¬ cap ≤ 1 by omega)] using strBytes_word v j (by omega)
  rw [List.getElem?_eq_getElem] at capGet
  have get := stringBytes_get v.1 length j bound
  rw [List.getElem?_eq_getElem hj] at get
  rw [show base + 1 + j = base + (j + 1) by omega, read]
  rw [Option.some.inj capGet, Option.some.inj get]
  rfl

theorem stringCat_encoding {D : Deklaration} (L : Lay D) {n q : Nat} (long : 2 ≤ n + q)
    (vs : Wert D (.str n)) (vt : Wert D (.str q)) :
    encodeWords L (.str (n + q)) (strCatW vs vt) =
      BitVec.ofNat 64 (vs.1.length + vt.1.length) ::
        (vs.1.map (fun b => BitVec.ofInt 64 b.n) ++
          stringBytes q vt.1 ++ List.replicate (n - vs.1.length) 0) := by
  have la := vs.2
  have lb := vt.2
  simp only [encodeWords, if_neg (show ¬ n + q ≤ 1 by omega), strCatW,
    List.length_append, List.map_append, stringBytes, List.cons_append, List.append_assoc]
  rw [List.replicate_append_replicate]
  congr 3
  omega

/-- Overlay the padded second span on the first span's zero padding. The untouched
    prefix and suffix complete the exact canonical concatenation encoding. -/
theorem wordsAt_cat {m m' : Runner.Mem} {fp : Runner.W} {base ptr n q : Nat}
    (as bs : List Runner.W) (la : as.length ≤ n) (lb : bs.length ≤ q)
    (fits : base + n + q ≤ ptr)
    (old : WordsAt m fp base (as ++ List.replicate (n - as.length + q) 0))
    (written : WordsAt m' fp (base + as.length) (bs ++ List.replicate (q - bs.length) 0))
    (kept : ∀ s, s < ptr → (s < base + as.length ∨ base + as.length + q ≤ s) →
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = m.rd64 (slot fp (BitVec.ofNat 64 s))) :
    WordsAt m' fp base (as ++ (bs ++ List.replicate (q - bs.length) 0) ++ List.replicate (n - as.length) 0) := by
  rw [wordsAt_append, wordsAt_append]
  refine ⟨⟨?_, written⟩, ?_⟩
  · intro i hi
    rw [kept (base + i) (by omega) (Or.inl (by omega))]
    have h := old i (by simp only [List.length_append, List.length_replicate]; omega)
    simpa only [List.getElem_append_left hi] using h
  · intro i hi
    have len : (bs ++ List.replicate (q - bs.length) 0).length = q := by
      simp only [List.length_append, List.length_replicate]; omega
    have bound : i < n - as.length := by simpa using hi
    have address : base + (as ++ (bs ++ List.replicate (q - bs.length) 0)).length + i =
        base + (as.length + q + i) := by simp only [List.length_append, len]; omega
    rw [address, kept _ (by omega) (Or.inr (by omega))]
    have index : as.length + q + i < (as ++ List.replicate (n - as.length + q) (0 : Runner.W)).length := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [old _ index]
    simp only [List.getElem_append_right (by omega : as.length ≤ as.length + q + i),
      List.getElem_replicate]

end Gabbro.Stage0.Senke
