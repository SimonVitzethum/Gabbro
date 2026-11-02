module

public import Grammatik.Kern.Semantik.Semantik

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A value at an equal type. -/
def Wert.umTyp {τ σ : Ty} (h : τ = σ) (v : Wert D τ) : Wert D σ := h ▸ v

/-- An expression at an equal type. -/
def Expr.umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ) (e : Expr D Γ Λ τ) :
    Expr D Γ Λ σ := h ▸ e

@[simp] theorem Wert.umTyp_rfl {τ : Ty} (v : Wert D τ) : Wert.umTyp rfl v = v := rfl

@[simp] theorem Expr.umTyp_rfl {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    Expr.umTyp rfl e = e := rfl

/-- Down and up again is nothing. -/
@[simp] theorem Wert.umTyp_hin_her {τ σ : Ty} (h : τ = σ) (v : Wert D σ) :
    Wert.umTyp h (Wert.umTyp (D := D) h.symm v) = v := by subst h; rfl

/-- Evaluating a transported expression is transporting its value: the cast does not
    change what is read. -/
@[simp] theorem eval_umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ)
    (e : Expr D Γ Λ τ) (σ₀ w : World D) (ρ : Env D Γ) :
    eval σ₀ (Expr.umTyp h e) w ρ = Wert.umTyp h (eval σ₀ e w ρ) := by
  subst h; rfl

/-- The places a transported expression reads are the places it read. -/
@[simp] theorem orte_umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ)
    (e : Expr D Γ Λ τ) : (Expr.umTyp h e).orte = e.orte := by
  subst h; rfl


end Gabbro.Grammatik
