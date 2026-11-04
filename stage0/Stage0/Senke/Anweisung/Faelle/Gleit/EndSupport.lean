module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
@[expose] public section
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
/-- Shrinking locals commutes with the canonical embedding of an ending outcome. -/
theorem floatEnd_schrumpf {l : Bool} {Γ : Ctx} {τ : Ty}
    (o : EndAusgang V l (τ :: Γ)) : o.schrumpf.zuAusgang = o.zuAusgang.schrumpf := by
  cases o <;> rfl
end Gabbro.Stage0.Senke
