module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A consuming selection boundary has fuel and its two reads must pass: the invariant
    holds and an absent minimum means that the domain is empty. -/
def verbrauchKopfPrueft
    (lesen : World D → List (Res D) → List (D.Tab ⊕ D.Glob) → World D)
    {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (rest : Nat) (σ : World D) (ρ : Env D Γ) : Prop :=
  let σ₁ := lesen σ Λ inv.orte
  let σ₂ := lesen σ₁ Λ (member.orte ++ edge.orte)
  0 < rest ∧ wahr? (eval σ₁ inv σ₁ ρ) = true ∧
    (verbrauchWahl (alleIndizes (D.count t))
      (fun i => wahr? (eval σ₂ member σ₂ (.cons i ρ)))
      (fun i j => wahr? (eval σ₂ edge σ₂ (.cons i (.cons j ρ))))
      (fun i j => decide (i.n = j.n)) = none →
      ((alleIndizes (D.count t)).all fun i => !(wahr? (eval σ₂ member σ₂ (.cons i ρ)))) = true)

/-- Every completed consuming round strictly decreases its bounded measure. -/
def verbrauchAbstiegPrueft
    (lesen : World D → List (Res D) → List (D.Tab ⊕ D.Glob) → World D)
    {Γ : Ctx} {Λ : List (Res D)} {bound : Int}
    (mass : Expr D Γ Λ (.int 0 bound)) (vor : Int) (σ : World D) (ρ : Env D Γ) : Prop :=
  let σm := lesen σ Λ mass.orte
  let m := (eval σm mass σm ρ).n
  0 ≤ m ∧ m ≤ bound ∧ m < vor

/-- Abrupt exits decrease the measure too; `leave` also checks the invariant. -/
def verbrauchAbbruchPrueft
    (lesen : World D → List (Res D) → List (D.Tab ⊕ D.Glob) → World D)
    {Γ : Ctx} {Λ : List (Res D)} {bound : Int} (inv : Expr D Γ Λ .bool)
    (mass : Expr D Γ Λ (.int 0 bound)) (vor : Int) (w : Bool) (σ : World D) (ρ : Env D Γ) : Prop :=
  verbrauchAbstiegPrueft lesen mass vor σ ρ ∧
    (w = true → let σ₁ := lesen (lesen σ Λ mass.orte) Λ inv.orte
      wahr? (eval σ₁ inv σ₁ ρ) = true)

/-- The consuming boundary check reads only the footprint `S`: the read worlds `σ₁` (after the
    invariant read) and `σ₂` (after the member and edge reads) may be replaced by worlds that agree
    with them on `S`. -/
theorem verbrauchKopfWerte_gleich {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (rest : Nat) (ρ : Env D Γ)
    {S S' : List (D.Tab ⊕ D.Glob)} (hi : ∀ o ∈ inv.orte, o ∈ S)
    (hm : ∀ o ∈ member.orte, o ∈ S') (he : ∀ o ∈ edge.orte, o ∈ S')
    {σ₁ σ₁' σ₂ σ₂' : World D} (g₁ : GleichAuf S σ₁ σ₁') (g₂ : GleichAuf S' σ₂ σ₂') :
    (0 < rest ∧ wahr? (eval σ₁ inv σ₁ ρ) = true ∧
      (verbrauchWahl (alleIndizes (D.count t))
        (fun i => wahr? (eval σ₂ member σ₂ (.cons i ρ)))
        (fun i j => wahr? (eval σ₂ edge σ₂ (.cons i (.cons j ρ))))
        (fun i j => decide (i.n = j.n)) = none →
        ((alleIndizes (D.count t)).all fun i => !(wahr? (eval σ₂ member σ₂ (.cons i ρ)))) = true)) ↔
    (0 < rest ∧ wahr? (eval σ₁' inv σ₁' ρ) = true ∧
      (verbrauchWahl (alleIndizes (D.count t))
        (fun i => wahr? (eval σ₂' member σ₂' (.cons i ρ)))
        (fun i j => wahr? (eval σ₂' edge σ₂' (.cons i (.cons j ρ))))
        (fun i j => decide (i.n = j.n)) = none →
        ((alleIndizes (D.count t)).all fun i => !(wahr? (eval σ₂' member σ₂' (.cons i ρ)))) = true)) := by
  have ei := eval_gleichAuf inv hi g₁ ρ
  have em := fun i => eval_gleichAuf member hm g₂ (.cons i ρ)
  have ee := fun i j => eval_gleichAuf edge he g₂ (.cons i (.cons j ρ))
  have hf1 : (fun i : Zahl 0 (D.count t - 1) => wahr? (eval σ₂ member σ₂ (Env.cons i ρ))) =
      (fun i => wahr? (eval σ₂' member σ₂' (Env.cons i ρ))) :=
    funext fun i => congrArg wahr? (em i)
  have hf2 : (fun i j : Zahl 0 (D.count t - 1) =>
      wahr? (eval σ₂ edge σ₂ (Env.cons i (Env.cons j ρ)))) =
      (fun i j => wahr? (eval σ₂' edge σ₂' (Env.cons i (Env.cons j ρ)))) :=
    funext fun i => funext fun j => congrArg wahr? (ee i j)
  have hf3 : (fun i : Zahl 0 (D.count t - 1) => !wahr? (eval σ₂ member σ₂ (Env.cons i ρ))) =
      (fun i => !wahr? (eval σ₂' member σ₂' (Env.cons i ρ))) :=
    funext fun i => congrArg (fun b => !b) (congrArg wahr? (em i))
  rw [hf1, hf2, hf3, ei]
  exact Iff.rfl

section Checks

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
  (t : D.Tab) (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)

/-- A failed consuming boundary check predicts the existing loop logic failure. -/
theorem semV_verbrauch_pruefung_falsch (rest : Nat) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (h : ¬ verbrauchKopfPrueft World.lese t member edge inv rest σ ρ) :
    semV O passes R (.verbrauch t member edge inv bound mass body rest k) σ ρ =
      .logik .schleife := by
  classical
  cases rest with
  | zero =>
      simp only [semV, weiterZ, laufA, verbrauchLauf]
      exact weiterZ_logik O passes R k _
  | succ n =>
      have hn : 0 < n + 1 := by omega
      dsimp only [verbrauchKopfPrueft] at h
      have h := fun hp => h ⟨hn, hp⟩
      by_cases hw : wahr? (eval (World.lese σ Λ inv.orte) inv (World.lese σ Λ inv.orte) ρ) = true
      · have hbad := fun hh => h ⟨hw, hh⟩
        obtain ⟨hnone, hkein⟩ := Classical.not_imp.mp hbad
        have hf : ((alleIndizes (D.count t)).all fun i =>
            !(wahr? (eval (World.lese (World.lese σ Λ inv.orte) Λ (member.orte ++ edge.orte))
              member (World.lese (World.lese σ Λ inv.orte) Λ (member.orte ++ edge.orte)) (.cons i ρ)))) = false :=
          Bool.eq_false_iff.mpr hkein
        have hsel : verbrauchSel t member edge (World.lese σ Λ inv.orte) ρ =
            (World.lese (World.lese σ Λ inv.orte) Λ (member.orte ++ edge.orte), none, true) := by
          refine Prod.ext rfl (Prod.ext hnone ?_)
          show (!(alleIndizes (D.count t)).all _) = true
          rw [Bool.not_eq_true']
          exact hf
        simp only [semV, weiterZ, laufA, verbrauchLauf, leseB, hw,
          Bool.true_eq_false, ite_false, hsel]
        exact weiterZ_logik O passes R k _
      · have hf := Bool.eq_false_iff.mpr hw
        simp only [semV, weiterZ, laufA, verbrauchLauf, leseB, hf, ite_true]
        exact weiterZ_logik O passes R k _

/-- A completed round cannot resume without the strict descent. -/
theorem semV_verbrauchRest_falsch (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (h : ¬ verbrauchAbstiegPrueft World.lese mass vor σ ρ) :
    semV O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      σ (.cons i ρ) = .logik .schleife := by
  show weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
    (.ok σ (.cons i ρ)) = _
  dsimp only [verbrauchAbstiegPrueft] at h
  simp only [weiterZ, Env.tail, h, ↓reduceIte]
  exact weiterZ_logik O passes R k _

/-- `leave` and `next` expose the same descent check as normal completion. -/
theorem semV_abbVerbrauch_falsch {Λx : List (Res D)} (rest : Nat) (vor : Int)
    (k : GRest D V l Γ Λ) (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (w : Bool)
    (h : ¬ verbrauchAbbruchPrueft World.lese inv mass vor w σ ρ) :
    semV O passes R (.dann (.cons (abbS rfl w) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semV_dann_cons]
  cases w with
  | false =>
      change weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
        (.next rfl σ (.cons i ρ)) = _
      dsimp only [verbrauchAbbruchPrueft, verbrauchAbstiegPrueft] at h
      have hfall : ¬ (0 ≤ (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ≤ bound ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n < vor) :=
        fun hf => h ⟨hf, fun hw => (Bool.false_ne_true hw).elim⟩
      simp only [weiterZ, Env.tail, hfall, ↓reduceIte]
      exact weiterZ_logik O passes R k _
  | true =>
      change weiterZ O passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
        (.leave rfl σ (.cons i ρ)) = _
      dsimp only [verbrauchAbbruchPrueft, verbrauchAbstiegPrueft] at h
      by_cases hfall : 0 ≤ (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ≤ bound ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n < vor
      · have hinv : ¬ (wahr? (eval (World.lese (World.lese σ Λ mass.orte) Λ inv.orte) inv
            (World.lese (World.lese σ Λ mass.orte) Λ inv.orte) ρ) = true) :=
          fun hw => h ⟨hfall, fun _ => hw⟩
        simp only [weiterZ, Env.tail, hfall, leseB, hinv, ↓reduceIte]
        exact weiterZ_logik O passes R k _
      · simp only [weiterZ, Env.tail, hfall, ↓reduceIte]
        exact weiterZ_logik O passes R k _


end Checks
end Gabbro.Grammatik
