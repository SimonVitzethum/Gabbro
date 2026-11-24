module

public import Core.Ast.Aggregate.Runtime

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

theorem wertAls_widen (source target : Ty .value) (fits : Fits source target) (value : Wert source) :
    wertAls target ⟨source, value⟩ = some (Wert.widen source target fits value) := by
  cases source with
  | int lo hi =>
      cases target with
      | int lower upper =>
          simp only [Fits] at fits
          have hb : lower ≤ value.wert ∧ value.wert ≤ upper :=
            ⟨Int.le_trans fits.1 value.unten, Int.le_trans value.oben fits.2⟩
          simp only [wertAls, Wert.widen]
          rw [dif_pos hb]
      | _ =>
          simp only [Fits] at fits
          cases fits
  | array el count =>
      cases target with
      | array el' count' =>
          cases count with
          | zero =>
              cases count' with
              | zero => rfl
              | succ n =>
                  simp only [Fits] at fits
                  cases fits
          | succ n =>
              cases count' with
              | zero =>
                  simp only [Fits] at fits
                  cases fits
              | succ m =>
                  cases fits
                  simp only [wertAls]
                  dsimp [Wert.widen, Nat.casesAuxOn, Ty.noConfusion, Nat.Internal.elimOffset]
      | _ =>
          simp only [Fits] at fits
          cases fits
  | text source =>
    cases target with
    | text target =>
      have length : value.bytes.size ≤ target := Nat.le_trans value.bound fits
      simp only [wertAls, dif_pos length, Wert.widen, TextValue.widen]
    | _ =>
      simp only [Fits] at fits
      cases fits
  | _ =>
      cases target with
      | int _ _ =>
          simp only [Fits] at fits
          cases fits
      | array _ _ =>
          simp only [Fits] at fits
          cases fits
      | _ =>
          cases fits <;>
            simp only [wertAls, Wert.widen, dif_pos] <;>
            dsimp [Ty.noConfusion, Ty.product.noConfusion, Ty.record.noConfusion,
              Ty.recordSchema.noConfusion, Ty.sum.noConfusion, Ty.variant.noConfusion,
              Ty.variantSchema.noConfusion]

theorem wertAls_selbst {type : Ty .value} (value : Wert type) :
    wertAls type ⟨type, value⟩ = some value := by
  cases type with
  | int lo hi =>
    have bounds : lo ≤ value.wert ∧ value.wert ≤ hi := ⟨value.unten, value.oben⟩
    simp only [wertAls, dif_pos bounds]
    cases value
    rfl
  | text capacity =>
    simp only [wertAls, dif_pos value.bound]
    cases value
    rfl
  | array element count =>
    cases count with
    | zero =>
      have empty : value = #v[] := by
        apply Vector.ext
        intro i hi
        omega
      cases empty
      rfl
    | succ n => simp only [wertAls, dif_pos rfl, dif_pos trivial] <;> rfl
  | _ => simp only [wertAls, dif_pos rfl, dif_pos trivial] <;> rfl

end Gabbro.Core.Ast.Semantik
