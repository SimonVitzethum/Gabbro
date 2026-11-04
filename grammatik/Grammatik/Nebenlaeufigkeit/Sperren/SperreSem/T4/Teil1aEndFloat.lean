module
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Teil1a

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T3

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Stufen

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semH_endeGleit {Λ : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semH S O U passes R (.ende (.float op a b lo hi rest)) σ ρ =
      semH S O U passes R (.ende rest) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  simp only [semH, execEndH, hv, zErgG_schrumpf]

theorem semH_endeGleitLit {Λ : List (Res D)} (q lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semH S O U passes R (.ende (.floatLit q lo hi rest)) σ ρ =
      semH S O U passes R (.ende rest) σ (.cons v ρ) := by
  simp only [semH, execEndH, hv, zErgG_schrumpf]

theorem semH_endeGleitVon {Λ : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semH S O U passes R (.ende (.floatOf e lo hi rest)) σ ρ =
      semH S O U passes R (.ende rest) (σ.lese Λ e.orte) (.cons v ρ) := by
  simp only [semH, execEndH, hv, zErgG_schrumpf]

theorem semH_endeGleitNarrowOk {Λ : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semH S O U passes R (.ende (.floatNarrow e lo hi sonst rest)) σ ρ =
      semH S O U passes R (.ende rest) (σ.lese Λ e.orte) (.cons v ρ) := by
  simp only [semH, execEndH, hv, zErgG_schrumpf]

theorem semH_endeGleitNarrowElse {Λ : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    (semH S O U passes R (.ende (.floatNarrow e lo hi sonst rest)) σ ρ).folgt
      (semH S O U passes R (.ende sonst) (σ.lese Λ e.orte) ρ) := by
  simp only [semH, execEndH, hn, zErgG_schrumpf]
  exact ZErgG.folgt_refl _

end Stufen
end Gabbro.Grammatik
