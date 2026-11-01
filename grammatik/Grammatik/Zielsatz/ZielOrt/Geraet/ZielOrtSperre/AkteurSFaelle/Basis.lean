module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- The residue of a frame, read off its rest. -/
theorem rest_okS {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (h : F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f)) :
    r.okS P (fussOrteG P F.f) (sicher P lok F.f) := by
  rw [hF] at h
  exact h

end Akteur
end Gabbro.Grammatik
