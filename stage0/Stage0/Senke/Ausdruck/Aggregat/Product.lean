/- Field-list layout for heterogeneous products. Not connected until empty spans
   are supported by the canonical frame representation. -/
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
def encodeProduct (L : Lay D) : (fs : List Ty) →
    ProdVal D.Fn D.passt fs → List Runner.W
  | [], _ => []
  | τ :: rest, v => encodeWords L τ (ProdVal.hd v) ++
      encodeProduct L rest (ProdVal.tl v)

@[simp] theorem encodeProduct_nil (L : Lay D) (v : ProdVal D.Fn D.passt []) :
    encodeProduct L [] v = [] := rfl

@[simp] theorem encodeProduct_cons (L : Lay D) {τ : Ty} {fs : List Ty}
    (v : ProdVal D.Fn D.passt (τ :: fs)) :
    encodeProduct L (τ :: fs) v = encodeWords L τ (ProdVal.hd v) ++
      encodeProduct L fs (ProdVal.tl v) := rfl

theorem encodeProduct_length (L : Lay D) (fs : List Ty)
    (v : ProdVal D.Fn D.passt fs) :
    (encodeProduct L fs v).length = productWords fs := by
  induction fs with
  | nil => rfl
  | cons τ fs ih =>
    simp only [encodeProduct, List.length_append, encodeWords_length, productWords]
    rw [ih]

theorem productOffset_bound {fs : List Ty} {σ : Ty} (i : FieldAt fs σ) :
    productOffset i + valueWords σ ≤ productWords fs := by
  induction i with
  | head => simp only [productOffset, productWords]; omega
  | tail i ih => simp only [productOffset, productWords]; omega

end Gabbro.Stage0.Senke
