module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T2

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Stufen

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

/-! ### The consuming traversal (`traverse … by consuming`, C11) -/

theorem semV_dannVerbrauch {Λ Λ'' : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.consumeTraverse t member edge inv bound mass body) rest) k) σ ρ =
      semV O passes R (.verbrauch t member edge inv bound mass body
        ((D.count t).toNat + bound.toNat + 1) (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_verbrauchWeiter {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true)
    (σ₂ : World D) (v : Wert D (.index (D.count t))) (b : Bool) (m : Int)
    (hsel : verbrauchSel t member edge (leseB inv σ ρ).1 ρ = (σ₂, some v, b))
    (hm : (eval (σ₂.lese Λ mass.orte) mass (σ₂.lese Λ mass.orte) ρ).n = m) :
    semV O passes R (.verbrauch t member edge inv bound mass body (rest + 1) k) σ ρ =
      semV O passes R (.dann body
        (.verbrauchRest t member edge inv bound mass body rest m k))
        (σ₂.lese Λ mass.orte) (.cons v ρ) := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (verbrauchLauf _ _ (rest + 1) σ ρ) =
    weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest m k)
      (execBlock O passes R body (σ₂.lese Λ mass.orte) (.cons v ρ))
  simp only [verbrauchLauf, hl, Bool.true_eq_false, if_false, hsel]
  cases execBlock O passes R body (σ₂.lese Λ mass.orte) (.cons v ρ) with
  | ok σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
      · simp only [hfall, if_false]
  | next _ σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
      · simp only [hfall, if_false]
  | leave _ σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
        by_cases hc' : (leseB inv (σ'.lese Λ mass.orte) ρ'.tail).2 = true
        · simp only [hc', if_true]
        · simp only [show (leseB inv (σ'.lese Λ mass.orte) ρ'.tail).2 = false from by
            cases h' : (leseB inv (σ'.lese Λ mass.orte) ρ'.tail).2 with
            | false => rfl
            | true => exact absurd h' hc', if_false]
      · simp only [hfall, if_false]
  | zurueck σ' v => rfl
  | why σ' r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem semV_verbrauchLeer {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true)
    (σ₂ : World D)
    (hsel : verbrauchSel t member edge (leseB inv σ ρ).1 ρ = (σ₂, none, false)) :
    semV O passes R (.verbrauch t member edge inv bound mass body (rest + 1) k) σ ρ =
      semV O passes R k σ₂ ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (verbrauchLauf _ _ (rest + 1) σ ρ) =
    weiterZ O passes R k (.ok σ₂ ρ)
  simp only [verbrauchLauf, hl, hsel, Bool.true_eq_false, if_false]

theorem semV_verbrauchFort {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (σ₁ : World D) (hs₁ : σ₁ = σ.lese Λ mass.orte)
    (m' : Int) (hm' : (eval σ₁ mass σ₁ ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor) :
    semV O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      σ (.cons i ρ) =
      semV O passes R (.verbrauch t member edge inv bound mass body rest k) σ₁ ρ := by
  show weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.ok σ (.cons i ρ)) =
    weiterZ O passes R (.verbrauch t member edge inv bound mass body rest k) (.ok σ₁ ρ)
  simp only [weiterZ, hs₁, hm', hfall, if_true, laufA]

theorem semV_leaveVerbrauch {Λ Λx : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (σm : World D) (hsm : σm = σ.lese Λ mass.orte)
    (m' : Int) (hm' : (eval σm mass σm ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
    (hw : wahr? (eval (σm.lese Λ inv.orte) inv (σm.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.dann (.cons (.leave h) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      semV O passes R k ((σm.lese Λ inv.orte)) ρ := by
  rw [semV_dann_cons]
  show weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.leave h σ (.cons i ρ)) = _
  simp only [weiterZ, hsm, hm', hfall, if_true]
  have hl : (leseB inv σm ρ).2 = true := hw
  simp only [hl, if_true]

theorem semV_nextVerbrauch {Λ Λx : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (σm : World D) (hsm : σm = σ.lese Λ mass.orte)
    (m' : Int) (hm' : (eval σm mass σm ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor) :
    semV O passes R (.dann (.cons (.next h) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      semV O passes R (.verbrauch t member edge inv bound mass body rest k) σm ρ := by
  rw [semV_dann_cons]
  show weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.next h σ (.cons i ρ)) = _
  simp only [weiterZ, hsm, hm', hfall, if_true, laufA]

end Stufen
end Gabbro.Grammatik
