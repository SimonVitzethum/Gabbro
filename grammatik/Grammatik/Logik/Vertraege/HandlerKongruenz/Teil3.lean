/-
  File:      Grammatik/HandlerKongruenz/Teil3.lean
  Subject:   **RUN EQUALITY FOR THE LOOP COMBINATORS UNDER AN ERROR SET** --
              the four loop runners under two handlers that agree on
              disciplined entries or fail early with a first-side mark,
              with the entry discipline threaded through the iterations.

  WHY IT EXISTS. The fused run-equality induction (`Teil4.lean`,
  `Teil5.lean`) reaches loop bodies at worlds the loop itself computed;
  the discipline there is maintained by threading it through the
  iterations, exactly as `traverseLauf_treu` threads the frame. Each lemma
  mirrors its `Teil1.lean` namesake, with the handler premise gated by
  the entry discipline and the discipline carried along.
-/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1
public import Grammatik.Logik.Ruf.Eintritt.RufGleichSchleife
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : vertrag D}

section SchleifenUnter

variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}

/-- A traversing run under two related handlers. -/
theorem traverseLauf_unter (bo : Option Int)
    {l : Bool} {Γ : Ctx} {τ : Ty} {Λ : List (Res D)}
    (body₁ body₂ : Block D V true (τ :: Γ) Λ Λ)
    (inv : World D → Env D Γ → World D × Bool)
    (ih : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), body₁.ScopesOk → body₂.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ body₁ σ ρ) (execBlock O passes R₂ body₂ σ ρ))
    (hT : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), body₁.ScopesOk → HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body₁ σ ρ))
    (hi : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (inv σ ρ).1)
    (hscope₁ : body₁.ScopesOk) (hscope₂ : body₂.ScopesOk) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      AusgangUnter Er
        (traverseLauf (l := l) (fun σ ρ => execBlock O passes R₁ body₁ σ ρ) inv ks σ ρ)
        (traverseLauf (l := l) (fun σ ρ => execBlock O passes R₂ body₂ σ ρ) inv ks σ ρ)
  | [], σ, ρ, _ => by
      simp only [traverseLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact AusgangUnter.refl _
      · rw [if_neg hc, if_neg hc]; exact AusgangUnter.refl _
  | k :: ks, σ, ρ, hh => by
      simp only [traverseLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact AusgangUnter.refl _
      · rw [if_neg hc, if_neg hc]
        have hinv := hi σ ρ hh
        rcases ih (inv σ ρ).1 (.cons k ρ) hscope₁ hscope₂ (hinv.heldB hh) with
        | inl heq =>
            rw [heq]
            cases hx : execBlock O passes R₂ body₂ (inv σ ρ).1 (Env.cons k ρ) with
            | ok σ' ρ' =>
                have hT' := treuAus_ok (hT _ _ hscope₁ (hinv.heldB hh))
                  (by rw [heq, hx]; rfl)
                have g1 := hinv.trans hT'
                exact traverseLauf_unter bo body₁ body₂ inv ih hT hi hscope₁ hscope₂
                  ks σ' ρ'.tail (g1.heldB hh)
            | next hl σ' ρ' =>
                have hT' := treuAus_ok (hT _ _ hscope₁ (hinv.heldB hh))
                  (by rw [heq, hx]; rfl)
                have g1 := hinv.trans hT'
                exact traverseLauf_unter bo body₁ body₂ inv ih hT hi hscope₁ hscope₂
                  ks σ' ρ'.tail (g1.heldB hh)
            | leave hl σ' ρ' => exact AusgangUnter.refl _
            | zurueck σ' v => exact AusgangUnter.refl _
            | why σ' r => exact AusgangUnter.refl _
            | logik e => exact AusgangUnter.refl _
            | hardware e => exact AusgangUnter.refl _
        | inr herr => exact Or.inr ⟨herr.1, by rw [herr.2.1]; cases herr.1 <;> rfl, herr.2.2⟩

/-- A consuming run under two related handlers. -/
theorem verbrauchLauf_unter (bo : Option Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (body₁ body₂ : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (ih : ∀ (σ : World D) (ρ : Env D (.index (D.count t) :: Γ)),
      body₁.ScopesOk → body₂.ScopesOk → HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ body₁ σ ρ) (execBlock O passes R₂ body₂ σ ρ))
    (hT : ∀ (σ : World D) (ρ : Env D (.index (D.count t) :: Γ)), body₁.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body₁ σ ρ))
    (hi : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (inv σ ρ).1)
    (hsel : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (sel σ ρ).1)
    (hmass : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (massW σ ρ).1)
    (hscope₁ : body₁.ScopesOk) (hscope₂ : body₂.ScopesOk) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      AusgangUnter Er
        (verbrauchLauf (l := l) t (fun σ ρ => execBlock O passes R₁ body₁ σ ρ)
          inv sel massW bound fuel σ ρ)
        (verbrauchLauf (l := l) t (fun σ ρ => execBlock O passes R₂ body₂ σ ρ)
          inv sel massW bound fuel σ ρ)
  | 0, _, _, _ => AusgangUnter.refl _
  | n + 1, σ, ρ, hh => by
      simp only [verbrauchLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact AusgangUnter.refl _
      · rw [if_neg hc, if_neg hc]
        have hinv := hi σ ρ hh
        have hselg := hsel (inv σ ρ).1 ρ (hinv.heldB hh)
        generalize heq_sel : sel (inv σ ρ).1 ρ = selected at hselg ⊢
        rcases selected with ⟨σr, w, b⟩
        cases b <;> cases w with
        | none => exact AusgangUnter.refl _
        | some v =>
            simp only
            have hmassg := hmass σr ρ ((hinv.trans hselg).heldB hh)
            generalize heq_mass : massW σr ρ = p1 at hmassg ⊢
            rcases p1 with ⟨σm, m⟩
            simp only
            have gm : Treu V.schreibt V.gschreibt σ σm :=
              (hinv.trans hselg).trans hmassg
            rcases ih σm (.cons v ρ) hscope₁ hscope₂ (gm.heldB hh) with
            | inl heq =>
                rw [heq]
                cases hx : execBlock O passes R₂ body₂ σm (Env.cons v ρ) with
                | ok σ' ρ' =>
                    dsimp only
                    have hT' := treuAus_ok (hT _ _ hscope₁ (gm.heldB hh))
                      (by rw [heq, hx]; rfl)
                    have g1 : Treu V.schreibt V.gschreibt σ σ' := gm.trans hT'
                    have hmassg2 := hmass σ' ρ'.tail (g1.heldB hh)
                    generalize heq_mass2 : massW σ' ρ'.tail = p2 at hmassg2 ⊢
                    rcases p2 with ⟨σm', m'⟩
                    dsimp only
                    by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                    · rw [if_pos hfall, if_pos hfall]
                      have g2 : Treu V.schreibt V.gschreibt σ σm' := g1.trans hmassg2
                      exact verbrauchLauf_unter bo t body₁ body₂ inv sel massW bound
                        ih hT hi hsel hmass hscope₁ hscope₂ n σm' ρ'.tail (g2.heldB hh)
                    · rw [if_neg hfall, if_neg hfall]; exact AusgangUnter.refl _
                | next hl σ' ρ' =>
                    dsimp only
                    have hT' := treuAus_ok (hT _ _ hscope₁ (gm.heldB hh))
                      (by rw [heq, hx]; rfl)
                    have g1 : Treu V.schreibt V.gschreibt σ σ' := gm.trans hT'
                    have hmassg2 := hmass σ' ρ'.tail (g1.heldB hh)
                    generalize heq_mass2 : massW σ' ρ'.tail = p2 at hmassg2 ⊢
                    rcases p2 with ⟨σm', m'⟩
                    dsimp only
                    by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                    · rw [if_pos hfall, if_pos hfall]
                      have g2 : Treu V.schreibt V.gschreibt σ σm' := g1.trans hmassg2
                      exact verbrauchLauf_unter bo t body₁ body₂ inv sel massW bound
                        ih hT hi hsel hmass hscope₁ hscope₂ n σm' ρ'.tail (g2.heldB hh)
                    · rw [if_neg hfall, if_neg hfall]; exact AusgangUnter.refl _
                | leave hl σ' ρ' => simp only; exact AusgangUnter.refl _
                | zurueck σ' v => simp only; exact AusgangUnter.refl _
                | why σ' r => simp only; exact AusgangUnter.refl _
                | logik e => simp only; exact AusgangUnter.refl _
                | hardware e => simp only; exact AusgangUnter.refl _
            | inr herr => exact Or.inr ⟨herr.1, by rw [herr.2.1]; cases herr.1 <;> rfl, herr.2.2⟩

end SchleifenUnter

section SchleifenUnterZwei

variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}

/-- A retry run under two related handlers. -/
theorem retryLauf_unter (bo : Option Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (body₁ body₂ : Block D V true Γ Λ Λ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueber₁ ueber₂ : Block D V l Γ Λ Λ)
    (ih : ∀ (σ : World D) (ρ : Env D Γ), body₁.ScopesOk → body₂.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ body₁ σ ρ) (execBlock O passes R₂ body₂ σ ρ))
    (hT : ∀ (σ : World D) (ρ : Env D Γ), body₁.ScopesOk → HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body₁ σ ρ))
    (ihu : ∀ (σ : World D) (ρ : Env D Γ), ueber₁.ScopesOk → ueber₂.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ ueber₁ σ ρ) (execBlock O passes R₂ ueber₂ σ ρ))
    (hb : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (bis σ ρ).1)
    (hscope₁ : body₁.ScopesOk) (hscope₂ : body₂.ScopesOk)
    (hscope_u1 : ueber₁.ScopesOk) (hscope_u2 : ueber₂.ScopesOk) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      AusgangUnter Er
        (retryLauf (fun σ ρ => execBlock O passes R₁ body₁ σ ρ) bis
          (fun σ ρ => execBlock O passes R₁ ueber₁ σ ρ) n σ ρ)
        (retryLauf (fun σ ρ => execBlock O passes R₂ body₂ σ ρ) bis
          (fun σ ρ => execBlock O passes R₂ ueber₂ σ ρ) n σ ρ)
  | 0, σ, ρ, hh => by
      simp only [retryLauf]
      by_cases hc : (bis σ ρ).2 = true
      · rw [if_pos hc, if_pos hc]
        exact ihu (bis σ ρ).1 ρ hscope_u1 hscope_u2 ((hb σ ρ hh).heldB hh)
      · rw [if_neg hc, if_neg hc]; exact AusgangUnter.refl _
  | n + 1, σ, ρ, hh => by
      simp only [retryLauf]
      by_cases hc : (bis σ ρ).2 = true
      · rw [if_pos hc, if_pos hc]
        exact ihu (bis σ ρ).1 ρ hscope_u1 hscope_u2 ((hb σ ρ hh).heldB hh)
      · rw [if_neg hc, if_neg hc]
        have hinv := hb σ ρ hh
        rcases ih (bis σ ρ).1 ρ hscope₁ hscope₂ (hinv.heldB hh) with
        | inl heq =>
            rw [heq]
            cases hx : execBlock O passes R₂ body₂ (bis σ ρ).1 ρ with
            | ok σ' ρ' =>
                have hT' := treuAus_ok (hT _ _ hscope₁ (hinv.heldB hh))
                  (by rw [heq, hx]; rfl)
                have g1 := hinv.trans hT'
                exact retryLauf_unter bo body₁ body₂ bis ueber₁ ueber₂
                  ih hT ihu hb hscope₁ hscope₂ hscope_u1 hscope_u2
                  n σ' ρ' (g1.heldB hh)
            | next hl σ' ρ' =>
                have hT' := treuAus_ok (hT _ _ hscope₁ (hinv.heldB hh))
                  (by rw [heq, hx]; rfl)
                have g1 := hinv.trans hT'
                exact retryLauf_unter bo body₁ body₂ bis ueber₁ ueber₂
                  ih hT ihu hb hscope₁ hscope₂ hscope_u1 hscope_u2
                  n σ' ρ' (g1.heldB hh)
            | leave hl σ' ρ' => exact AusgangUnter.refl _
            | zurueck σ' v => exact AusgangUnter.refl _
            | why σ' r => exact AusgangUnter.refl _
            | logik e => exact AusgangUnter.refl _
            | hardware e => exact AusgangUnter.refl _
        | inr herr => exact Or.inr ⟨herr.1, by rw [herr.2.1]; cases herr.1 <;> rfl, herr.2.2⟩

/-- A forever run under two related handlers. -/
theorem foreverLauf_unter (bo : Option Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme)
    (body₁ body₂ : Block D V true Γ Λ Λ)
    (inv : World D → Env D Γ → World D × Bool)
    (ih : ∀ (σ : World D) (ρ : Env D Γ), body₁.ScopesOk → body₂.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ body₁ σ ρ) (execBlock O passes R₂ body₂ σ ρ))
    (hT : ∀ (σ : World D) (ρ : Env D Γ), body₁.ScopesOk → HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body₁ σ ρ))
    (hi : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (inv σ ρ).1)
    (hscope₁ : body₁.ScopesOk) (hscope₂ : body₂.ScopesOk) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      AusgangUnter Er
        (foreverLauf (l := l) a (fun σ ρ => execBlock O passes R₁ body₁ σ ρ) inv n σ ρ)
        (foreverLauf (l := l) a (fun σ ρ => execBlock O passes R₂ body₂ σ ρ) inv n σ ρ)
  | 0, _, _, _ => AusgangUnter.refl _
  | n + 1, σ, ρ, hh => by
      simp only [foreverLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact AusgangUnter.refl _
      · rw [if_neg hc, if_neg hc]
        have hinv := hi σ ρ hh
        rcases ih (inv σ ρ).1 ρ hscope₁ hscope₂ (hinv.heldB hh) with
        | inl heq =>
            rw [heq]
            cases hx : execBlock O passes R₂ body₂ (inv σ ρ).1 ρ with
            | ok σ' ρ' =>
                have hT' := treuAus_ok (hT _ _ hscope₁ (hinv.heldB hh))
                  (by rw [heq, hx]; rfl)
                have g1 := hinv.trans hT'
                exact foreverLauf_unter bo a body₁ body₂ inv ih hT hi
                  hscope₁ hscope₂ n σ' ρ' (g1.heldB hh)
            | next hl σ' ρ' =>
                have hT' := treuAus_ok (hT _ _ hscope₁ (hinv.heldB hh))
                  (by rw [heq, hx]; rfl)
                have g1 := hinv.trans hT'
                exact foreverLauf_unter bo a body₁ body₂ inv ih hT hi
                  hscope₁ hscope₂ n σ' ρ' (g1.heldB hh)
            | leave hl σ' ρ' => exact AusgangUnter.refl _
            | zurueck σ' v => exact AusgangUnter.refl _
            | why σ' r => exact AusgangUnter.refl _
            | logik e => exact AusgangUnter.refl _
            | hardware e => exact AusgangUnter.refl _
        | inr herr => exact Or.inr ⟨herr.1, by rw [herr.2.1]; cases herr.1 <;> rfl, herr.2.2⟩

end SchleifenUnterZwei
end Gabbro.Grammatik
