module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The residue of a frame, read off its rest. -/
theorem rest_okV {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (h : F.rest.2.2.2.2.okV P (fussOrte P F.f)) : r.okV P (fussOrte P F.f) := by
  rw [hF] at h
  exact h

end Akteur
end Gabbro.Grammatik
