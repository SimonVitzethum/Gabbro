module

public import Grammatik.Kern.Syntax.Zucker

@[expose] public section

/-
  File:       Grammatik/Kern/Syntax/Syntax/ProduktZucker.lean
  Subject:    C01, the field update of a by-value product LOCAL is no statement of its own: `Stmt.assignField`
              (`Zucker.lean`) is `assignVar x (prodSet (var x) i e)`. Here the expansion is checked against
              `execStmt`, and the value laws of a product expression (get after set, a sibling field stays).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Reading a variable right after writing it gives the written value. -/
theorem Env.get_set_same : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ),
    (ρ.set x v).get x = v
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ ρ, .there x, v => Env.get_set_same ρ x v

/-- **The expansion of `p.f = e`** against the statement semantics: the reads of `e` are recorded, and the
    local `p` holds its old value with exactly the field at `i` replaced by the value of `e`. -/
theorem execStmt_assignField {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {r : Nat}
    {fs : List Ty} {σ : Ty} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (x : Var Γ (.prod r fs)) (i : FieldAt fs σ) (e : Expr D Γ Λ σ) (w : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.assignField (V := V) (l := l) x i e) w ρ =
      .ok (w.lese Λ e.orte)
        (ρ.set x (prodSetW i (ρ.get x) (eval (w.lese Λ e.orte) e (w.lese Λ e.orte) ρ))) := by
  show execStmt O passes R (Stmt.assignVar x (Expr.prodSet (Expr.var x) i e)) w ρ = _
  simp only [execStmt, Expr.orte, List.nil_append, eval]

/-- The updated field reads back the new value. -/
theorem assignField_lies {Γ : Ctx} {r : Nat} {fs : List Ty} {σ : Ty} (x : Var Γ (.prod r fs))
    (i : FieldAt fs σ) (ρ : Env D Γ) (v : Wert D σ) :
    prodGetW i ((ρ.set x (prodSetW i (ρ.get x) v)).get x) = v := by
  erw [Env.get_set_same]
  exact prodGetW_prodSetW i (ρ.get x) v

/-- **Frame**: every other field of the local keeps its value. -/
theorem assignField_geschwister {Γ : Ctx} {r : Nat} {fs : List Ty} {σ τ : Ty}
    (x : Var Γ (.prod r fs)) {i : FieldAt fs σ} {j : FieldAt fs τ} (hd : FieldAt.Disj i j)
    (ρ : Env D Γ) (v : Wert D σ) :
    prodGetW j ((ρ.set x (prodSetW i (ρ.get x) v)).get x) = prodGetW j (ρ.get x) := by
  erw [Env.get_set_same]
  exact prodGetW_prodSetW_of_disj hd (ρ.get x) v

/-- Get after set on the product EXPRESSIONS: a replaced field reads back its replacement. -/
theorem eval_prodGet_prodSet {Γ : Ctx} {Λ : List (Res D)} {r : Nat} {fs : List Ty} {ν : Ty}
    (σ₀ σ : World D) (ρ : Env D Γ) (v : Expr D Γ Λ (.prod r fs)) (i : FieldAt fs ν)
    (e : Expr D Γ Λ ν) :
    eval σ₀ (Expr.prodGet (Expr.prodSet v i e) i) σ ρ = eval σ₀ e σ ρ := by
  simp only [eval]
  exact prodGetW_prodSetW i _ _

/-- Frame on the product EXPRESSIONS: reading another field of an updated product reads the original. -/
theorem eval_prodGet_prodSet_geschwister {Γ : Ctx} {Λ : List (Res D)} {r : Nat} {fs : List Ty}
    {ν τ : Ty} (σ₀ σ : World D) (ρ : Env D Γ) (v : Expr D Γ Λ (.prod r fs)) {i : FieldAt fs ν}
    {j : FieldAt fs τ} (hd : FieldAt.Disj i j) (e : Expr D Γ Λ ν) :
    eval σ₀ (Expr.prodGet (Expr.prodSet v i e) j) σ ρ = eval σ₀ (Expr.prodGet v j) σ ρ := by
  simp only [eval]
  exact prodGetW_prodSetW_of_disj hd _ _

/-- A product literal reads back its first field. -/
theorem eval_prodGet_prod_head {Γ : Ctx} {Λ : List (Res D)} {r : Nat} {ν : Ty} {fs : List Ty}
    (σ₀ σ : World D) (ρ : Env D Γ) (a : Expr D Γ Λ ν) (rest : Args D Γ Λ fs) :
    eval σ₀ (Expr.prodGet (Expr.prod r (.cons a rest)) FieldAt.head) σ ρ = eval σ₀ a σ ρ := by
  simp only [eval, evalProd]
  rfl

end Gabbro.Grammatik
