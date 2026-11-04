module
public import Grammatik.Zielsatz.Einbettung.Lauf
public import Grammatik.Zielsatz.Einbettung.Schleifena
@[expose] public section


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

/-! ## Consuming runs beside their images -/

section Verbrauch

variable {hZ}

/-- **`traverse … by consuming` beside its image.** Each round re-selects
    in the post-body world on both sides; selection, measure and invariant
    transport by hypothesis. By induction on the fuel; every failing check
    is `.logik .schleife` on both sides. -/
theorem verbrauch_sim {l : Bool} (t : D.Tab) (bound : Int)
    (schritt : Phi D D' → World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (schritt' : World D' → Env D' (.index (D'.count (E.tab t)) :: Γ') →
      Ausgang (E.vertragE V) true (.index (D'.count (E.tab t)) :: Γ'))
    (pruef : Phi D D' → World D → Env D Γ → World D × Bool)
    (pruef' : World D' → Env D' Γ' → World D' × Bool)
    (sel : Phi D D' → World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (sel' : World D' → Env D' Γ' →
      World D' × Option (Wert D' (.index (D'.count (E.tab t)))) × Bool)
    (massW : Phi D D' → World D → Env D Γ → World D × Int)
    (massW' : World D' → Env D' Γ' → World D' × Int)
    (hs : E.KoerperSim hZ schritt schritt') (hi : E.PruefSim hZ pruef pruef')
    (f : Wert D (.index (D.count t)) → Wert D' (.index (D'.count (E.tab t))))
    (hf : ∀ k, ∃ h : (.index (D'.count (E.tab t))) = E.tyE (.index (D.count t)),
      E.VRel hZ _ k (castW h (f k)))
    (hsel : E.SelSim hZ t sel sel' f) (hm : E.MassSim hZ massW massW') :
    ∀ fuel : Nat, E.KoerperSim hZ (l := l)
      (fun Φ => verbrauchLauf t (schritt Φ) (pruef Φ) (sel Φ) (massW Φ) bound fuel)
      (verbrauchLauf (E.tab t) schritt' pruef' sel' massW' bound fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro M σ σ' ρ ρ' h hρ
      refine ⟨M, .logik .schleife, teil_refl M, fun Φ _ => by simp only [verbrauchLauf], ?_⟩
      simp only [verbrauchLauf]
      exact ⟨logikRel_schleife, h.keyOk E⟩
  | succ fuel ih =>
      intro M σ σ' ρ ρ' h hρ
      obtain ⟨M₁, σ₁, b, hs1, hΦ1, hI1, hb⟩ := hi M σ σ' ρ ρ' h hρ
      cases b with
      | false =>
          refine ⟨M₁, .logik .schleife, hs1, fun Φ hP => ?_, ?_⟩
          · simp only [verbrauchLauf, hΦ1 Φ hP, Bool.false_eq_true,
              Bool.true_eq_false, ↓reduceIte]
          · simp only [verbrauchLauf, hb, Bool.false_eq_true,
              Bool.true_eq_false, ↓reduceIte]
            exact ⟨logikRel_schleife, hI1.keyOk E⟩
      | true =>
          obtain ⟨M₂, σ₂, σ₂s, w, b₂, hs2, hΦ2, hsel₂, hI2⟩ :=
            hsel M₁ σ₁ (pruef' σ' ρ').1 ρ ρ' hI1 hρ
          have h12 := teil_trans hs1 hs2
          cases w with
          | none =>
              cases b₂ with
              | false =>
                  refine ⟨M₂, .ok σ₂ ρ, h12, fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP,
                      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_none,
                      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                    exact ⟨hI2, hρ⟩
              | true =>
                  refine ⟨M₂, .logik .schleife, h12, fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP hs2), hΦ2 Φ hP,
                      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_none,
                      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                    exact ⟨logikRel_schleife, hI2.keyOk E⟩
          | some v =>
              obtain ⟨M₂m, σm₀, σm₀', m₀, hsm, hΦm0, hm₀, hIm⟩ :=
                hm M₂ σ₂ σ₂s ρ ρ' hI2 hρ
              have h12m := teil_trans h12 hsm
              obtain ⟨M₃, o₁, hs3, hΦ3, hR3⟩ := hs M₂m σm₀ σm₀'
                (.cons v ρ) (.cons (f v) ρ') hIm ⟨hf v, hρ⟩
              generalize hsch : schritt' σm₀' (.cons (f v) ρ') = o₁' at hR3
              have h13 := teil_trans h12m hs3
              rcases o₁ with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r⟩ |
                  ⟨h₂, σ₂', ρ₂'⟩ | ⟨h₂, σ₂', ρ₂'⟩ | e | e <;>
              rcases o₁' with ⟨σ₂'', ρ₂''⟩ | ⟨σ₂'', v''⟩ | ⟨σ₂'', r''⟩ |
                  ⟨h₂', σ₂'', ρ₂''⟩ | ⟨h₂', σ₂'', ρ₂''⟩ | e' | e' <;>
              simp only [AusRel] at hR3 <;> (try exact hR3.elim)
              · obtain ⟨M₄, σm₁, σm₁', m₁, hs4, hΦm1, hm₁, hI4⟩ :=
                  hm M₃ σ₂' σ₂'' ρ₂'.tail ρ₂''.tail hR3.1
                    (E.envR_tail hZ _ _ hR3.2)
                by_cases hfall : 0 ≤ m₁ ∧ m₁ ≤ bound ∧ m₁ < m₀
                · obtain ⟨M₅, o, hs5, hΦ5, hR5⟩ :=
                    ih M₄ σm₁ σm₁' ρ₂'.tail ρ₂''.tail hI4
                      (E.envR_tail hZ _ _ hR3.2)
                  refine ⟨M₅, o, teil_trans h13 (teil_trans hs4 hs5),
                    fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5))))),
                      hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5)))),
                      hΦm0 Φ (passt_teil hP (teil_trans hs3 (teil_trans hs4 hs5))),
                      hΦ3 Φ (passt_teil hP (teil_trans hs4 hs5)),
                      hΦm1 Φ (passt_teil hP hs5), hfall, Bool.true_eq_false, ↓reduceIte]
                    exact hΦ5 Φ hP
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                      hsch, hm₀, hm₁, hfall, Bool.true_eq_false, ↓reduceIte]
                    exact hR5
                · refine ⟨M₄, .logik .schleife, teil_trans h13 hs4,
                    fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 hs4)))),
                      hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 hs4))),
                      hΦm0 Φ (passt_teil hP (teil_trans hs3 hs4)),
                      hΦ3 Φ (passt_teil hP hs4),
                      hΦm1 Φ hP, hfall, Bool.true_eq_false, ↓reduceIte]
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                      hsch, hm₀, hm₁, hfall, Bool.true_eq_false, ↓reduceIte]
                    exact ⟨logikRel_schleife, hI4.keyOk E⟩
              · refine ⟨M₃, .zurueck σ₂' v', h13, fun Φ hP => ?_, ?_⟩
                · simp only [verbrauchLauf,
                    hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm hs3))),
                    hΦ2 Φ (passt_teil hP (teil_trans hsm hs3)),
                    hΦm0 Φ (passt_teil hP hs3),
                    hΦ3 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                    hsch, hm₀, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                  exact hR3
              · refine ⟨M₃, .why σ₂' r, h13, fun Φ hP => ?_, ?_⟩
                · simp only [verbrauchLauf,
                    hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm hs3))),
                    hΦ2 Φ (passt_teil hP (teil_trans hsm hs3)),
                    hΦm0 Φ (passt_teil hP hs3),
                    hΦ3 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                    hsch, hm₀, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                  exact hR3
              · obtain ⟨M₄, σm₁, σm₁', m₁, hs4, hΦm1, hm₁, hI4⟩ :=
                  hm M₃ σ₂' σ₂'' ρ₂'.tail ρ₂''.tail hR3.1
                    (E.envR_tail hZ _ _ hR3.2)
                by_cases hfall : 0 ≤ m₁ ∧ m₁ ≤ bound ∧ m₁ < m₀
                · obtain ⟨M₅, σ₅, b₅, hs5, hΦ5, hI5, hb₅⟩ :=
                    hi M₄ σm₁ σm₁' ρ₂'.tail ρ₂''.tail hI4
                      (E.envR_tail hZ _ _ hR3.2)
                  cases b₅ with
                  | false =>
                      refine ⟨M₅, .logik .schleife,
                        teil_trans h13 (teil_trans hs4 hs5), fun Φ hP => ?_, ?_⟩
                      · simp only [verbrauchLauf,
                          hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5))))),
                          hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5)))),
                          hΦm0 Φ (passt_teil hP (teil_trans hs3 (teil_trans hs4 hs5))),
                          hΦ3 Φ (passt_teil hP (teil_trans hs4 hs5)),
                          hΦm1 Φ (passt_teil hP hs5),
                          hΦ5 Φ hP, hfall, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                      · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                          hsch, hm₀, hm₁, hfall, hb₅,
                          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                        exact ⟨logikRel_schleife, hI5.keyOk E⟩
                  | true =>
                      refine ⟨M₅, .ok σ₅ ρ₂'.tail,
                        teil_trans h13 (teil_trans hs4 hs5), fun Φ hP => ?_, ?_⟩
                      · simp only [verbrauchLauf,
                          hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5))))),
                          hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5)))),
                          hΦm0 Φ (passt_teil hP (teil_trans hs3 (teil_trans hs4 hs5))),
                          hΦ3 Φ (passt_teil hP (teil_trans hs4 hs5)),
                          hΦm1 Φ (passt_teil hP hs5),
                          hΦ5 Φ hP, hfall, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                      · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                          hsch, hm₀, hm₁, hfall, hb₅,
                          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                        exact ⟨hI5, E.envR_tail hZ _ _ hR3.2⟩
                · refine ⟨M₄, .logik .schleife, teil_trans h13 hs4,
                    fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 hs4)))),
                      hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 hs4))),
                      hΦm0 Φ (passt_teil hP (teil_trans hs3 hs4)),
                      hΦ3 Φ (passt_teil hP hs4),
                      hΦm1 Φ hP, hfall, Bool.true_eq_false, ↓reduceIte]
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                      hsch, hm₀, hm₁, hfall, Bool.true_eq_false, ↓reduceIte]
                    exact ⟨logikRel_schleife, hI4.keyOk E⟩
              · obtain ⟨M₄, σm₁, σm₁', m₁, hs4, hΦm1, hm₁, hI4⟩ :=
                  hm M₃ σ₂' σ₂'' ρ₂'.tail ρ₂''.tail hR3.1
                    (E.envR_tail hZ _ _ hR3.2)
                by_cases hfall : 0 ≤ m₁ ∧ m₁ ≤ bound ∧ m₁ < m₀
                · obtain ⟨M₅, o, hs5, hΦ5, hR5⟩ :=
                    ih M₄ σm₁ σm₁' ρ₂'.tail ρ₂''.tail hI4
                      (E.envR_tail hZ _ _ hR3.2)
                  refine ⟨M₅, o, teil_trans h13 (teil_trans hs4 hs5),
                    fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5))))),
                      hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 (teil_trans hs4 hs5)))),
                      hΦm0 Φ (passt_teil hP (teil_trans hs3 (teil_trans hs4 hs5))),
                      hΦ3 Φ (passt_teil hP (teil_trans hs4 hs5)),
                      hΦm1 Φ (passt_teil hP hs5), hfall, Bool.true_eq_false, ↓reduceIte]
                    exact hΦ5 Φ hP
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                      hsch, hm₀, hm₁, hfall, Bool.true_eq_false, ↓reduceIte]
                    exact hR5
                · refine ⟨M₄, .logik .schleife, teil_trans h13 hs4,
                    fun Φ hP => ?_, ?_⟩
                  · simp only [verbrauchLauf,
                      hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm (teil_trans hs3 hs4)))),
                      hΦ2 Φ (passt_teil hP (teil_trans hsm (teil_trans hs3 hs4))),
                      hΦm0 Φ (passt_teil hP (teil_trans hs3 hs4)),
                      hΦ3 Φ (passt_teil hP hs4),
                      hΦm1 Φ hP, hfall, Bool.true_eq_false, ↓reduceIte]
                  · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                      hsch, hm₀, hm₁, hfall, Bool.true_eq_false, ↓reduceIte]
                    exact ⟨logikRel_schleife, hI4.keyOk E⟩
              · refine ⟨M₃, .logik e, h13, fun Φ hP => ?_, ?_⟩
                · simp only [verbrauchLauf,
                    hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm hs3))),
                    hΦ2 Φ (passt_teil hP (teil_trans hsm hs3)),
                    hΦm0 Φ (passt_teil hP hs3),
                    hΦ3 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                    hsch, hm₀, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                  exact hR3
              · refine ⟨M₃, .hardware e, h13, fun Φ hP => ?_, ?_⟩
                · simp only [verbrauchLauf,
                    hΦ1 Φ (passt_teil hP (teil_trans hs2 (teil_trans hsm hs3))),
                    hΦ2 Φ (passt_teil hP (teil_trans hsm hs3)),
                    hΦm0 Φ (passt_teil hP hs3),
                    hΦ3 Φ hP, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                · simp only [verbrauchLauf, hb, hsel₂, Option.map_some,
                    hsch, hm₀, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                  exact hR3

end Verbrauch

end Einbettung

end Gabbro.Grammatik.Einbettung
