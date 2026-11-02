module

public import Grammatik.Kern.Semantik.Semantik

public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A value at an equal type. -/
@[expose] def Wert.umTyp {τ σ : Ty} (h : τ = σ) (v : Wert D τ) : Wert D σ := h ▸ v

/-- An expression at an equal type. -/
@[expose] def Expr.umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ) (e : Expr D Γ Λ τ) :
    Expr D Γ Λ σ := h ▸ e

@[simp] theorem Wert.umTyp_rfl {τ : Ty} (v : Wert D τ) : Wert.umTyp rfl v = v := rfl

@[simp] theorem Expr.umTyp_rfl {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    Expr.umTyp rfl e = e := rfl

/-- Two transports are one; a transport along a type equation with itself is nothing. -/
@[simp] theorem Wert.umTyp_umTyp {τ σ ρ : Ty} (h1 : τ = σ) (h2 : σ = ρ) (v : Wert D τ) :
    Wert.umTyp h2 (Wert.umTyp h1 v) = Wert.umTyp (h1.trans h2) v := by subst h1; subst h2; rfl

@[simp] theorem Wert.umTyp_self {τ : Ty} (h : τ = τ) (v : Wert D τ) : Wert.umTyp h v = v := rfl

/-- A number transported away and back keeps its value. -/
theorem Wert.umTyp_umTyp_n {a b : Int} {τ : Ty} (h1 : Ty.int a b = τ) (h2 : τ = Ty.int a b)
    (x : Wert D (.int a b)) : (Wert.umTyp h2 (Wert.umTyp h1 x) : Zahl a b).n = (x : Zahl a b).n := by
  subst h1; rfl

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
