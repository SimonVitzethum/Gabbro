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

end Gabbro.Stage0.Senke
