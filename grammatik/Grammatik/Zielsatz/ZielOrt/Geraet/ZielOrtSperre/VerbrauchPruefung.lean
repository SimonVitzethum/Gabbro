module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.T1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.VerbrauchPruefung

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Checks

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
  (t : D.Tab) (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)

/-- A failed consuming boundary check predicts the existing loop logic failure. -/
theorem semH_verbrauch_pruefung_falsch (rest : Nat) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (h : ¬ verbrauchKopfPrueft World.lese t member edge inv rest σ ρ) :
    semH S O U passes R (.verbrauch t member edge inv bound mass body rest k) σ ρ =
      .logik .schleife := by
  classical
  cases rest with
  | zero =>
      simp only [semH, weiterH, laufA, verbrauchLauf]
      exact weiterH_logik S O U passes R k _
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
        simp only [semH, weiterH, laufA, verbrauchLauf, leseB, hw,
          Bool.true_eq_false, ite_false, hsel]
        exact weiterH_logik S O U passes R k _
      · have hf := Bool.eq_false_iff.mpr hw
        simp only [semH, weiterH, laufA, verbrauchLauf, leseB, hf, ite_true]
        exact weiterH_logik S O U passes R k _

/-- A completed round cannot resume without the strict descent. -/
theorem semH_verbrauchRest_falsch (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (h : ¬ verbrauchAbstiegPrueft World.lese mass vor σ ρ) :
    semH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      σ (.cons i ρ) = .logik .schleife := by
  show weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
    (.ok σ (.cons i ρ)) = _
  dsimp only [verbrauchAbstiegPrueft] at h
  simp only [weiterH, Env.tail, h, ↓reduceIte]
  exact weiterH_logik S O U passes R k _

/-- `leave` and `next` expose the same descent check as normal completion. -/
theorem semH_abbVerbrauch_falsch {Λx : List (Res D)} (rest : Nat) (vor : Int)
    (k : GRest D V l Γ Λ) (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (w : Bool)
    (h : ¬ verbrauchAbbruchPrueft World.lese inv mass vor w σ ρ) :
    semH S O U passes R (.dann (.cons (abbS rfl w) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semH_dann_cons]
  cases w with
  | false =>
      change weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
        (.next rfl σ (.cons i ρ)) = _
      dsimp only [verbrauchAbbruchPrueft, verbrauchAbstiegPrueft] at h
      have hfall : ¬ (0 ≤ (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ≤ bound ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n < vor) :=
        fun hf => h ⟨hf, fun hw => (Bool.false_ne_true hw).elim⟩
      simp only [weiterH, Env.tail, hfall, ↓reduceIte]
      exact weiterH_logik S O U passes R k _
  | true =>
      change weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
        (.leave rfl σ (.cons i ρ)) = _
      dsimp only [verbrauchAbbruchPrueft, verbrauchAbstiegPrueft] at h
      by_cases hfall : 0 ≤ (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n ≤ bound ∧
          (eval (World.lese σ Λ mass.orte) mass (World.lese σ Λ mass.orte) ρ).n < vor
      · have hinv : ¬ (wahr? (eval (World.lese (World.lese σ Λ mass.orte) Λ inv.orte) inv
            (World.lese (World.lese σ Λ mass.orte) Λ inv.orte) ρ) = true) :=
          fun hw => h ⟨hfall, fun _ => hw⟩
        simp only [weiterH, Env.tail, hfall, leseB, hinv, ↓reduceIte]
        exact weiterH_logik S O U passes R k _
      · simp only [weiterH, Env.tail, hfall, ↓reduceIte]
        exact weiterH_logik S O U passes R k _


end Checks
end Gabbro.Grammatik
