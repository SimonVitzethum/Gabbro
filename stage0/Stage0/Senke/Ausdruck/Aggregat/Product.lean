/- Field-list layout for heterogeneous products, with an empty-product marker. -/
module
public import Grammatik.Kern.Syntax.Typen.Produkt
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- Products concatenate field spans without an empty-value marker. -/
def productWords : List Ty → Nat
  | [] => 0
  | τ :: rest => valueWords τ + productWords rest

/-- Static word offset of a typed field. -/
def productOffset : {fs : List Ty} → {σ : Ty} → FieldAt fs σ → Nat
  | _, _, .head => 0
  | _, _, .tail (τ := τ) i => valueWords τ + productOffset i

/-- Encode fields in declaration order. -/
def encodeProductFields (L : Lay D) : (fs : List Ty) →
    ProdVal D.Fn D.passt fs → List Runner.W
  | [], _ => []
  | τ :: rest, v => encodeWords L τ (ProdVal.hd v) ++
      encodeProductFields L rest (ProdVal.tl v)

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

/-- An empty product carries a zero marker; other products concatenate fields. -/
def encodeProduct (L : Lay D) (fs : List Ty)
    (v : ProdVal D.Fn D.passt fs) : List Runner.W :=
  if fs = [] then [0] else encodeProductFields L fs v

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
