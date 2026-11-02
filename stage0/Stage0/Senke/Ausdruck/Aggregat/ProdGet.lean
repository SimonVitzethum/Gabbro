/- Static encoding decomposition for typed product projection. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Product
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- The selected field is a contiguous span at its statically computed offset. -/
theorem encodeProductFields_field_split (L : Lay D) {fs : List Ty} {τ : Ty}
    (i : FieldAt fs τ) (v : ProdVal D.Fn D.passt fs) :
    ∃ before after : List Runner.W,
      encodeProductFields L fs v = before ++ encodeWords L τ (prodGetW i v) ++ after ∧
      before.length = productOffset i := by
  induction i with
  | head =>
    exact ⟨[], encodeProductFields L _ (ProdVal.tl v), rfl, rfl⟩
  | @tail τ σ rest i ih =>
    obtain ⟨before, after, split, offset⟩ := ih (ProdVal.tl v)
    refine ⟨encodeWords L σ (ProdVal.hd v) ++ before, after, ?_, ?_⟩
    · simp only [encodeProductFields_cons, prodGetW]
      rw [split, List.append_assoc, List.append_assoc]
    · simp only [List.length_append, encodeWords_length, productOffset]
      rw [offset]

/-- A typed field guarantees that the empty-product marker is absent. -/
theorem encodeProduct_field_split (L : Lay D) {name : Nat} {fs : List Ty} {τ : Ty}
    (i : FieldAt fs τ) (v : ProdVal D.Fn D.passt fs) :
    ∃ before after : List Runner.W,
      encodeWords L (.prod name fs) v = before ++ encodeWords L τ (prodGetW i v) ++ after ∧
      before.length = productOffset i := by
  have nonempty : fs ≠ [] := by
    cases i <;> simp
  simpa only [encodeWords, encodeProduct, if_neg nonempty] using
    encodeProductFields_field_split L i v

end Gabbro.Stage0.Senke
