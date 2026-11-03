module

public import Grammatik.Speichermodell.Atomar.AtomarAkteur
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.VerbrauchPruefung

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Agreement after two consuming-loop reads, including both accumulated footprints. -/
theorem verbrauch_lese2_gleichAuf {T : D.Tab ⊕ D.Glob → Prop}
    {L X₁ X₂ : List (D.Tab ⊕ D.Glob)} {σ W : World D}
    (hg : GleichAuf L σ W) (h₁ : ∀ c ∈ X₁, c ∈ L ∨ T c)
    (h₂ : ∀ c ∈ X₂, c ∈ L ∨ T c) (Λ : List (Res D)) :
    GleichAuf (L ++ X₁) (mischT T X₁ (σ.lese Λ X₁) W.speicher) (W.lese Λ X₁) ∧
    GleichAuf ((L ++ X₁) ++ X₂)
      (mischT T X₂ ((mischT T X₁ (σ.lese Λ X₁) W.speicher).lese Λ X₂) W.speicher)
      ((W.lese Λ X₁).lese Λ X₂) := by
  have g₁ := mischT_gleichAuf hg h₁ Λ Λ
  refine ⟨g₁, ?_⟩
  exact mischT_gleichAuf g₁
    (fun c hc => (h₂ c hc).elim (fun h => Or.inl (List.mem_append_left _ h)) Or.inr) Λ Λ

section Checks

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
  (t : D.Tab) (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)

/-- A failed consuming boundary check predicts the existing loop logic failure. -/
theorem semHA_verbrauch_pruefung_falsch (rest : Nat) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (h : ¬ verbrauchKopfPrueft (leseA A) t member edge inv rest σ ρ) :
    semHA S O U A passes R (.verbrauch t member edge inv bound mass body rest k) σ ρ =
      .logik .schleife := by
  classical
  cases rest with
  | zero =>
      simp only [semHA, weiterHA, laufA, verbrauchLauf]
      exact weiterHA_logik S O U A passes R k _
  | succ n =>
      have hn : 0 < n + 1 := by omega
      dsimp only [verbrauchKopfPrueft] at h
      have h := fun hp => h ⟨hn, hp⟩
      by_cases hw : wahr? (eval ((leseA A) σ Λ inv.orte) inv ((leseA A) σ Λ inv.orte) ρ) = true
      · have hbad := fun hh => h ⟨hw, hh⟩
        simp only [not_imp] at hbad
        obtain ⟨hnone, hkein⟩ := hbad
        have hf : ((alleIndizes (D.count t)).all fun i =>
            !(wahr? (eval ((leseA A) ((leseA A) σ Λ inv.orte) Λ (member.orte ++ edge.orte))
              member ((leseA A) ((leseA A) σ Λ inv.orte) Λ (member.orte ++ edge.orte)) (.cons i ρ)))) = false :=
          Bool.eq_false_iff.mpr hkein
        simp only [semHA, weiterHA, laufA, verbrauchLauf, leseBA, verbrauchSelA, hw,
          Bool.true_eq_false, ite_false, hnone, hf, Bool.not_false]
        exact weiterHA_logik S O U A passes R k _
      · have hf := Bool.eq_false_iff.mpr hw
        simp only [semHA, weiterHA, laufA, verbrauchLauf, leseBA, hf, ite_true]
        exact weiterHA_logik S O U A passes R k _

/-- A completed round cannot resume without the strict descent. -/
theorem semHA_verbrauchRest_falsch (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (h : ¬ verbrauchAbstiegPrueft (leseA A) mass vor σ ρ) :
    semHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      σ (.cons i ρ) = .logik .schleife := by
  show weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
    (.ok σ (.cons i ρ)) = _
  dsimp only [verbrauchAbstiegPrueft] at h
  dsimp only [weiterHA, Env.tail]
  rw [if_neg h]
  exact weiterHA_logik S O U A passes R k _

/-- `leave` and `next` expose the same descent check as normal completion. -/
theorem semHA_abbVerbrauch_falsch {Λx : List (Res D)} (rest : Nat) (vor : Int)
    (k : GRest D V l Γ Λ) (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (w : Bool)
    (h : ¬ verbrauchAbbruchPrueft (leseA A) inv mass vor w σ ρ) :
    semHA S O U A passes R (.dann (.cons (abbS rfl w) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semHA_dann_cons]
  cases w with
  | false =>
      change weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
        (.next rfl σ (.cons i ρ)) = _
      dsimp only [verbrauchAbbruchPrueft, verbrauchAbstiegPrueft] at h
      have hfall : ¬ (0 ≤ (eval ((leseA A) σ Λ mass.orte) mass ((leseA A) σ Λ mass.orte) ρ).n ∧
          (eval ((leseA A) σ Λ mass.orte) mass ((leseA A) σ Λ mass.orte) ρ).n ≤ bound ∧
          (eval ((leseA A) σ Λ mass.orte) mass ((leseA A) σ Λ mass.orte) ρ).n < vor) :=
        fun hf => h ⟨hf, fun hw => Bool.false_ne_true hw⟩
      dsimp only [weiterHA, Env.tail]
      rw [if_neg hfall]
      exact weiterHA_logik S O U A passes R k _
  | true =>
      change weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
        (.leave rfl σ (.cons i ρ)) = _
      dsimp only [verbrauchAbbruchPrueft, verbrauchAbstiegPrueft] at h
      by_cases hfall : 0 ≤ (eval ((leseA A) σ Λ mass.orte) mass ((leseA A) σ Λ mass.orte) ρ).n ∧
          (eval ((leseA A) σ Λ mass.orte) mass ((leseA A) σ Λ mass.orte) ρ).n ≤ bound ∧
          (eval ((leseA A) σ Λ mass.orte) mass ((leseA A) σ Λ mass.orte) ρ).n < vor
      · have hinv : ¬ (wahr? (eval ((leseA A) ((leseA A) σ Λ mass.orte) Λ inv.orte) inv
            ((leseA A) ((leseA A) σ Λ mass.orte) Λ inv.orte) ρ) = true) :=
          fun hw => h ⟨hfall, fun _ => hw⟩
        dsimp only [weiterHA, Env.tail]
        rw [if_pos hfall]
        dsimp only [leseBA]
        rw [if_neg hinv]
        exact weiterHA_logik S O U A passes R k _
      · dsimp only [weiterHA, Env.tail]
        rw [if_neg hfall]
        exact weiterHA_logik S O U A passes R k _


end Checks
end Gabbro.Grammatik
