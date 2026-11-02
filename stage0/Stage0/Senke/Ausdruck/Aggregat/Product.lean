/- Field-list layout for heterogeneous products, with an empty-product marker. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

@[simp] theorem encodeProductFields_nil (L : Lay D) (v : ProdVal D.Fn D.passt []) :
    encodeProductFields L [] v = [] := rfl

@[simp] theorem encodeProductFields_cons (L : Lay D) {τ : Ty} {fs : List Ty}
    (v : ProdVal D.Fn D.passt (τ :: fs)) :
    encodeProductFields L (τ :: fs) v = encodeWords L τ (ProdVal.hd v) ++
      encodeProductFields L fs (ProdVal.tl v) := rfl

theorem encodeProductFields_length (L : Lay D) (fs : List Ty)
    (v : ProdVal D.Fn D.passt fs) :
    (encodeProductFields L fs v).length = productWords fs := by
  induction fs with
  | nil => rfl
  | cons τ fs ih =>
    simp only [encodeProductFields, List.length_append, encodeWords_length, productWords]
    rw [ih]

/-- Every present field occupies at least one word. -/
theorem productWords_pos_of_ne_nil {fs : List Ty} (h : fs ≠ []) :
    0 < productWords fs := by
  cases fs with
  | nil => exact False.elim (h rfl)
  | cons τ rest =>
    have := valueWords_pos τ
    simp only [productWords]
    omega

theorem encodeProduct_length (L : Lay D) (fs : List Ty)
    (v : ProdVal D.Fn D.passt fs) :
    (encodeProduct L fs v).length = max 1 (productWords fs) := by
  unfold encodeProduct
  split
  · next h => subst fs; rfl
  · next h =>
    rw [encodeProductFields_length]
    have := productWords_pos_of_ne_nil h
    omega

theorem productOffset_bound {fs : List Ty} {σ : Ty} (i : FieldAt fs σ) :
    productOffset i + valueWords σ ≤ productWords fs := by
  induction i with
  | head => simp only [productOffset, productWords]; omega
  | tail i ih => simp only [productOffset, productWords]; omega

end Gabbro.Stage0.Senke
