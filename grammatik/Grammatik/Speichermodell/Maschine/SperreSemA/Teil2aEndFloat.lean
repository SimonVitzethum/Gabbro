module
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil2a

public import Grammatik.Speichermodell.Atomar.AtomarSem
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section StufenA
variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semHA_endeGleit {Λ : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ).x
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semHA S O U A passes R (.ende (.float op a b lo hi rest)) σ ρ =
      semHA S O U A passes R (.ende rest) (leseA A σ Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  simp only [semHA, weiterHA, execEndHA, hv, zErgG_schrumpf]

theorem semHA_endeGleitLit {Λ : List (Res D)} (q lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semHA S O U A passes R (.ende (.floatLit q lo hi rest)) σ ρ =
      semHA S O U A passes R (.ende rest) σ (.cons v ρ) := by
  simp only [semHA, weiterHA, execEndHA, hv, zErgG_schrumpf]

theorem semHA_endeGleitVon {Λ : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (leseA A σ Λ e.orte) e
      (leseA A σ Λ e.orte) ρ).n) = some v) :
    semHA S O U A passes R (.ende (.floatOf e lo hi rest)) σ ρ =
      semHA S O U A passes R (.ende rest) (leseA A σ Λ e.orte) (.cons v ρ) := by
  simp only [semHA, weiterHA, execEndHA, hv, zErgG_schrumpf]

theorem semHA_endeGleitNarrowOk {Λ : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x = some v) :
    semHA S O U A passes R (.ende (.floatNarrow e lo hi sonst rest)) σ ρ =
      semHA S O U A passes R (.ende rest) (leseA A σ Λ e.orte) (.cons v ρ) := by
  simp only [semHA, weiterHA, execEndHA, hv, zErgG_schrumpf]

theorem semHA_endeGleitNarrowElse {Λ : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)  (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x = none) :
    (semHA S O U A passes R (.ende (.floatNarrow e lo hi sonst rest)) σ ρ).folgt
      (semHA S O U A passes R (.ende sonst) (leseA A σ Λ e.orte) ρ) := by
  simp only [semHA, weiterHA, execEndHA, hn, zErgG_schrumpf]
  exact ZErgG.folgt_refl _

end StufenA
end Gabbro.Grammatik
