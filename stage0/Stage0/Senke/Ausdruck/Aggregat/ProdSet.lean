/- Representation preservation for typed product replacement. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.ProdGet
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- Replacing one field preserves all product representation obligations. -/
theorem ProdValid.set {L : Lay D} {fs : List Ty} {σ : Ty}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs) (x : Wert D σ)
    (valid : ProdValid L fs v) (replacement : ValueValid L σ x) :
    ProdValid L fs (prodSetW i v x) := by
  induction i generalizing v with
  | head => exact ⟨replacement, valid.2⟩
  | tail i ih => exact ⟨valid.1, ih (ProdVal.tl v) valid.2⟩

/-- Replacement changes exactly the selected field's contiguous encoding. -/
theorem encodeProductFields_set_split (L : Lay D) {fs : List Ty} {σ : Ty}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs) (x : Wert D σ) :
    ∃ before after : List Runner.W,
      encodeProductFields L fs v = before ++ encodeWords L σ (prodGetW i v) ++ after ∧
      encodeProductFields L fs (prodSetW i v x) =
        before ++ encodeWords L σ x ++ after ∧
      before.length = productOffset i := by
  induction i generalizing v with
  | head =>
    exact ⟨[], encodeProductFields L _ (ProdVal.tl v), rfl, rfl, rfl⟩
  | @tail σ τ rest i ih =>
    obtain ⟨before, after, old, updated, offset⟩ := ih (ProdVal.tl v)
    refine ⟨encodeWords L τ (ProdVal.hd v) ++ before, after, ?_, ?_, ?_⟩
    · simp only [encodeProductFields_cons, prodGetW]
      rw [old, List.append_assoc, List.append_assoc]
    · simp only [prodSetW, encodeProductFields_cons, ProdVal.hd, ProdVal.tl]
      rw [updated, List.append_assoc, List.append_assoc]
    · simp only [List.length_append, encodeWords_length, productOffset]
      rw [offset]

/-- Exact field writes and preservation of the surrounding words implement replacement. -/
theorem wordsAt_prodSet {L : Lay D} {name : Nat} {fs : List Ty} {σ : Ty}
    {m3 m4 : Runner.Mem} {fp : Runner.W} {d ptr : Nat}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs) (x : Wert D σ)
    (kept : WordsAt m3 fp d (encodeWords L (.prod name fs) v))
    (written : WordsAt m4 fp (d + productOffset i) (encodeWords L σ x))
    (preserved : ∀ s, s < ptr →
      (s < d + productOffset i ∨ d + productOffset i + valueWords σ ≤ s) →
      m4.rd64 (slot fp (BitVec.ofNat 64 s)) = m3.rd64 (slot fp (BitVec.ofNat 64 s)))
    (fits : d + valueWords (.prod name fs) ≤ ptr) :
    WordsAt m4 fp d (encodeWords L (.prod name fs) (prodSetW i v x)) := by
  have nonempty : fs ≠ [] := by cases i <;> simp
  obtain ⟨before, after, old, updated, offset⟩ := encodeProductFields_set_split L i v x
  have old' : encodeWords L (.prod name fs) v =
      before ++ encodeWords L σ (prodGetW i v) ++ after := by
    simpa only [encodeWords, encodeProduct, if_neg nonempty] using old
  have updated' : encodeWords L (.prod name fs) (prodSetW i v x) =
      before ++ encodeWords L σ x ++ after := by
    simpa only [encodeWords, encodeProduct, if_neg nonempty] using updated
  have length := encodeWords_length L (.prod name fs) v
  rw [old'] at length
  simp only [List.length_append, encodeWords_length, offset] at length
  rw [old', wordsAt_append, wordsAt_append] at kept
  rw [updated', wordsAt_append, wordsAt_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k hk
    rw [preserved (d + k) (by omega) (Or.inl (by omega))]
    exact kept.1.1 k hk
  · simpa only [offset] using written
  · intro k hk
    have read := kept.2 k hk
    simp only [List.length_append, encodeWords_length, offset] at read ⊢
    rw [preserved _ (by omega) (Or.inr (by omega))]
    exact read

end Gabbro.Stage0.Senke
