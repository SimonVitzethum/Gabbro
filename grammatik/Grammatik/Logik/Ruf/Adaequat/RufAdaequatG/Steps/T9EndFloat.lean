/- Part 9 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9Basis
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T8
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section SemSchritt

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem sem_endeGleit {Λ : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semR O passes (.ende rest) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semR O passes (.ende (.float op a b lo hi rest)) σ ρ := by
  simp only [semR, execEnd, hv, endErg_schrumpf]

theorem sem_endeGleitLit {Λ : List (Res D)} (q lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semR O passes (.ende rest) σ (.cons v ρ) =
      semR O passes (.ende (.floatLit q lo hi rest)) σ ρ := by
  simp only [semR, execEnd, hv, endErg_schrumpf]

theorem sem_endeGleitVon {Λ : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semR O passes (.ende rest) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.ende (.floatOf e lo hi rest)) σ ρ := by
  simp only [semR, execEnd, hv, endErg_schrumpf]

theorem sem_endeGleitNarrowOk {Λ : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semR O passes (.ende rest) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.ende (.floatNarrow e lo hi sonst rest)) σ ρ := by
  simp only [semR, execEnd, hv, endErg_schrumpf]

theorem sem_endeGleitNarrowElse {Λ : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semR O passes (.ende sonst) (σ.lese Λ e.orte) ρ =
      semR O passes (.ende (.floatNarrow e lo hi sonst rest)) σ ρ := by
  simp only [semR, execEnd, hn, endErg_schrumpf]

end SemSchritt
end Gabbro.Grammatik
