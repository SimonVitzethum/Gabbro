import Grammatik.Zielsatz.Einbettung.Lauf

/-!
  File:      Grammatik/Zielsatz/Einbettung/Schleifen.lean
  Subject:   The three loop drivers beside their images (stage E2c, part 3).

  `traverseLauf`, `retryLauf` and `foreverLauf` take the body and the boundary check as
  functions. When the body of `D` (for every map `Φ` that repeats the keys) runs beside its image
  and the boundary check does too, the whole loop does: by induction over the indices or the
  passes, the keys growing at every pass.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

section Schleifen

variable (hZ : E.Rueck) {V : Vertrag D} {Γ Γ' : Ctx}

/-- A body of `D` beside a body of `D'`, for every map that repeats the keys. -/
def KoerperSim {l : Bool} {Δ Δ' : Ctx}
    (schritt : Phi D D' → World D → Env D Δ → Ausgang V l Δ)
    (schritt' : World D' → Env D' Δ' → Ausgang (E.vertragE V) l Δ') : Prop :=
  ∀ (M : Keys D D') (σ : World D) (σ' : World D') (ρ : Env D Δ) (ρ' : Env D' Δ'),
    E.Inv hZ M σ σ' → E.EnvR hZ ρ ρ' →
    ∃ (M₁ : Keys D D') (o : Ausgang V l Δ), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → schritt Φ σ ρ = o) ∧ E.AusRel hZ M₁ o (schritt' σ' ρ')

/-- A boundary check of `D` beside one of `D'`. -/
def PruefSim (pruef : Phi D D' → World D → Env D Γ → World D × Bool)
    (pruef' : World D' → Env D' Γ' → World D' × Bool) : Prop :=
  ∀ (M : Keys D D') (σ : World D) (σ' : World D') (ρ : Env D Γ) (ρ' : Env D' Γ'),
    E.Inv hZ M σ σ' → E.EnvR hZ ρ ρ' →
    ∃ (M₁ : Keys D D') (σ₁ : World D) (b : Bool), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → pruef Φ σ ρ = (σ₁, b)) ∧ E.Inv hZ M₁ σ₁ (pruef' σ' ρ').1 ∧
      (pruef' σ' ρ').2 = b

variable {hZ}

theorem logikRel_schleife : LogikRel (D := D) (D' := D') .schleife .schleife := fun _ h => by cases h

/-- **`traverse` beside its image.** -/
theorem traverse_sim {l : Bool} {τ τ' : Ty}
    (schritt : Phi D D' → World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (schritt' : World D' → Env D' (τ' :: Γ') → Ausgang (E.vertragE V) true (τ' :: Γ'))
    (pruef : Phi D D' → World D → Env D Γ → World D × Bool)
    (pruef' : World D' → Env D' Γ' → World D' × Bool)
    (hs : E.KoerperSim hZ schritt schritt') (hi : E.PruefSim hZ pruef pruef')
    (f : Wert D τ → Wert D' τ') (hf : ∀ k, ∃ h : τ' = E.tyE τ, E.VRel hZ τ k (castW h (f k)))
    (ks : List (Wert D τ)) (ks' : List (Wert D' τ')) (hks : ks' = ks.map f) :
      E.KoerperSim hZ (l := l) (fun Φ => traverseLauf (schritt Φ) (pruef Φ) ks)
        (traverseLauf schritt' pruef' ks') := by
  subst hks
  induction ks with
  | nil =>
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, b, hs1, hΦ1, hI1, hb⟩ := hi M σ σ' ρ ρ' h hρ
      refine ⟨M₁, if b = true then .ok σ₁ ρ else .logik .schleife, hs1, fun Φ hP => ?_, ?_⟩
      · simp only [traverseLauf, hΦ1 Φ hP]
      · simp only [List.map_nil, traverseLauf, hb]
        cases b
        · exact ⟨logikRel_schleife, hI1.keyOk E⟩
        · exact ⟨hI1, hρ⟩
  | cons k ks ih =>
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, b, hs1, hΦ1, hI1, hb⟩ := hi M σ σ' ρ ρ' h hρ
      cases b
      · refine ⟨M₁, .logik .schleife, hs1, fun Φ hP => by simp only [traverseLauf, hΦ1 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte], ?_⟩
        simp only [List.map_cons, traverseLauf, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
        exact ⟨logikRel_schleife, hI1.keyOk E⟩
      · obtain ⟨M₂, o₁, hs2, hΦ2, hR2⟩ := hs M₁ σ₁ (pruef' σ' ρ').1 (.cons k ρ) (.cons (f k) ρ') hI1
          ⟨hf k, hρ⟩
        generalize hsch : schritt' (pruef' σ' ρ').1 (.cons (f k) ρ') = o₁' at hR2
        have h12 := teil_trans hs1 hs2
        rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
        rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
        simp only [AusRel] at hR2 <;> (try exact hR2.elim)
        · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih _ _ _ _ _ hR2.1 (E.envR_tail hZ _ _ hR2.2)
          refine ⟨M₃, o, teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            exact hΦ3 Φ hP
          · simp only [List.map_cons, traverseLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR3
        · refine ⟨M₂, .zurueck σ₂ v, h12, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [List.map_cons, traverseLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .why σ₂ r, h12, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [List.map_cons, traverseLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · obtain ⟨M₃, σ₃, b₃, hs3, hΦ3, hI3, hb3⟩ := hi M₂ σ₂ σ₂' ρ₂.tail ρ₂'.tail hR2.1
            (E.envR_tail hZ _ _ hR2.2)
          refine ⟨M₃, if b₃ = true then .ok σ₃ ρ₂.tail else .logik .schleife,
            teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), hΦ3 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [List.map_cons, traverseLauf, hb, hsch, hb3, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            cases b₃
            · exact ⟨logikRel_schleife, hI3.keyOk E⟩
            · exact ⟨hI3, E.envR_tail hZ _ _ hR2.2⟩
        · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih _ _ _ _ _ hR2.1 (E.envR_tail hZ _ _ hR2.2)
          refine ⟨M₃, o, teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            exact hΦ3 Φ hP
          · simp only [List.map_cons, traverseLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR3
        · refine ⟨M₂, .logik e, h12, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [List.map_cons, traverseLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .hardware e, h12, fun Φ hP => ?_, ?_⟩
          · simp only [traverseLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [List.map_cons, traverseLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2

/-- **`retry` beside its image.** -/
theorem retry_sim {l : Bool}
    (schritt : Phi D D' → World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D' → Env D' Γ' → Ausgang (E.vertragE V) true Γ')
    (bis : Phi D D' → World D → Env D Γ → World D × Bool)
    (bis' : World D' → Env D' Γ' → World D' × Bool)
    (ueber : Phi D D' → World D → Env D Γ → Ausgang V l Γ)
    (ueber' : World D' → Env D' Γ' → Ausgang (E.vertragE V) l Γ')
    (hs : E.KoerperSim hZ schritt schritt') (hi : E.PruefSim hZ bis bis') (hu : E.KoerperSim hZ ueber ueber') :
    ∀ n : Nat, E.KoerperSim hZ (fun Φ => retryLauf (schritt Φ) (bis Φ) (ueber Φ) n)
      (retryLauf schritt' bis' ueber' n) := by
  intro n
  induction n with
  | zero =>
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, b, hs1, hΦ1, hI1, hb⟩ := hi M σ σ' ρ ρ' h hρ
      cases b
      · obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := hu M₁ σ₁ (bis' σ' ρ').1 ρ ρ' hI1 hρ
        refine ⟨M₂, o, teil_trans hs1 hs2, fun Φ hP => ?_, ?_⟩
        · simp only [retryLauf, hΦ1 Φ (passt_teil hP hs2), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          exact hΦ2 Φ hP
        · simp only [retryLauf, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
      · refine ⟨M₁, .ok σ₁ ρ, hs1, fun Φ hP => by simp only [retryLauf, hΦ1 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte], ?_⟩
        simp only [retryLauf, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
        exact ⟨hI1, hρ⟩
  | succ n ih =>
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, b, hs1, hΦ1, hI1, hb⟩ := hi M σ σ' ρ ρ' h hρ
      cases b
      · obtain ⟨M₂, o₁, hs2, hΦ2, hR2⟩ := hs M₁ σ₁ (bis' σ' ρ').1 ρ ρ' hI1 hρ
        generalize hsch : schritt' (bis' σ' ρ').1 ρ' = o₁' at hR2
        have h12 := teil_trans hs1 hs2
        rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
        rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
        simp only [AusRel] at hR2 <;> (try exact hR2.elim)
        · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih _ _ _ _ _ hR2.1 hR2.2
          refine ⟨M₃, o, teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            exact hΦ3 Φ hP
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR3
        · refine ⟨M₂, .zurueck σ₂ v, h12, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .why σ₂ r, h12, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .ok σ₂ ρ₂, h12, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih _ _ _ _ _ hR2.1 hR2.2
          refine ⟨M₃, o, teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            exact hΦ3 Φ hP
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR3
        · refine ⟨M₂, .logik e, h12, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .hardware e, h12, fun Φ hP => ?_, ?_⟩
          · simp only [retryLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [retryLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
      · refine ⟨M₁, .ok σ₁ ρ, hs1, fun Φ hP => by simp only [retryLauf, hΦ1 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte], ?_⟩
        simp only [retryLauf, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
        exact ⟨hI1, hρ⟩

/-- **`forever` beside its image.** -/
theorem forever_sim {l : Bool} (a : D.Annahme) (a' : D'.Annahme)
    (schritt : Phi D D' → World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D' → Env D' Γ' → Ausgang (E.vertragE V) true Γ')
    (pruef : Phi D D' → World D → Env D Γ → World D × Bool)
    (pruef' : World D' → Env D' Γ' → World D' × Bool)
    (hs : E.KoerperSim hZ schritt schritt') (hi : E.PruefSim hZ pruef pruef') :
    ∀ n : Nat, E.KoerperSim hZ (l := l) (fun Φ => foreverLauf a (schritt Φ) (pruef Φ) n)
      (foreverLauf a' schritt' pruef' n) := by
  intro n
  induction n with
  | zero =>
      intro M σ σ' ρ ρ' h hρ
      exact ⟨M, .hardware (.fortschritt a), teil_refl M, fun _ _ => rfl, trivial⟩
  | succ n ih =>
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, b, hs1, hΦ1, hI1, hb⟩ := hi M σ σ' ρ ρ' h hρ
      cases b
      · refine ⟨M₁, .logik .schleife, hs1, fun Φ hP => by simp only [foreverLauf, hΦ1 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte], ?_⟩
        simp only [foreverLauf, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
        exact ⟨logikRel_schleife, hI1.keyOk E⟩
      · obtain ⟨M₂, o₁, hs2, hΦ2, hR2⟩ := hs M₁ σ₁ (pruef' σ' ρ').1 ρ ρ' hI1 hρ
        generalize hsch : schritt' (pruef' σ' ρ').1 ρ' = o₁' at hR2
        have h12 := teil_trans hs1 hs2
        rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
        rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
        simp only [AusRel] at hR2 <;> (try exact hR2.elim)
        · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih _ _ _ _ _ hR2.1 hR2.2
          refine ⟨M₃, o, teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            exact hΦ3 Φ hP
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR3
        · refine ⟨M₂, .zurueck σ₂ v, h12, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .why σ₂ r, h12, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .ok σ₂ ρ₂, h12, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih _ _ _ _ _ hR2.1 hR2.2
          refine ⟨M₃, o, teil_trans h12 hs3, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3)),
              hΦ2 Φ (passt_teil hP hs3), Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            exact hΦ3 Φ hP
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR3
        · refine ⟨M₂, .logik e, h12, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2
        · refine ⟨M₂, .hardware e, h12, fun Φ hP => ?_, ?_⟩
          · simp only [foreverLauf, hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
          · simp only [foreverLauf, hb, hsch, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]; exact hR2

end Schleifen

end Einbettung

end Gabbro.Grammatik.Einbettung
