/-
  File:      Grammatik/RufGleichSchleife.lean
  Subject:   **RUN EQUALITY FOR THE LOOP COMBINATORS** -- the four loop
              runners (`traverseLauf`, `verbrauchLauf`, `retryLauf`,
              `foreverLauf`) under two handlers that agree wherever the
              entry discipline holds.

  WHY IT EXISTS. The joint run-equality induction (`RufGleichStmt.lean`,
  `RufGleichEnd.lean`) reaches loop bodies at worlds the loop itself
  computed; the discipline there is maintained by threading it through the
  iterations, exactly as `traverseLauf_treu` and friends thread the frame.
  Each lemma below mirrors its `HandlerKongruenz` namesake, with the error
  set empty (equality, not agreement-or-error) and the discipline carried
  along: the body equality comes from the caller, the next iteration's
  discipline from the `Treu` fact about the first handler's body run.
-/
module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- Extract `Treu` from a `TreuAusgang` at a normal outcome. -/
theorem treuAus_ok {W : D.Tab → Bool} {G : D.Glob → Bool} {l : Bool} {Γ : Ctx}
    {σ σ1 : World D} {ρ1 : Env D Γ} {o : Ausgang V l Γ}
    (h : TreuAusgang W G σ o) (heq : o = Ausgang.ok σ1 ρ1) : Treu W G σ σ1 := by
  have h2 := h σ1 (by rw [heq]; rfl)
  simpa [heq] using h2

/-- Extract `Treu` from a `TreuAusgang` at a `next` outcome. -/
theorem treuAus_next {W : D.Tab → Bool} {G : D.Glob → Bool} {Γ : Ctx}
    {σ σ1 : World D} {ρ1 : Env D Γ} {o : Ausgang V true Γ} {hl : true = true}
    (h : TreuAusgang W G σ o) (heq : o = Ausgang.next hl σ1 ρ1) : Treu W G σ σ1 := by
  have h2 := h σ1 (by rw [heq]; rfl)
  simpa [heq] using h2

section SchleifenGleich

variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- A traversing run under two handlers that agree on disciplined entries:
    mirror of `traverseLauf_kongruent`, with the discipline threaded. -/
theorem traverseLauf_gleich (bo : Option Int)
    {l : Bool} {Γ : Ctx} {τ : Ty} {Λ : List (Res D)}
    (body : Block D V true (τ :: Γ) Λ Λ)
    (inv : World D → Env D Γ → World D × Bool)
    (ih : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), body.ScopesOk → HeldB bo Λ σ.haelt →
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (hT : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), body.ScopesOk → HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body σ ρ))
    (hi : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (inv σ ρ).1)
    (hscope_body : body.ScopesOk) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      traverseLauf (l := l) (fun σ ρ => execBlock O passes R₁ body σ ρ) inv ks σ ρ =
      traverseLauf (l := l) (fun σ ρ => execBlock O passes R₂ body σ ρ) inv ks σ ρ
  | [], σ, ρ, _ => by
      simp only [traverseLauf]
  | k :: ks, σ, ρ, hh => by
      simp only [traverseLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc]
      · rw [if_neg hc]
        have hinv := hi σ ρ hh
        have heq := ih (inv σ ρ).1 (.cons k ρ) hscope_body (hinv.heldB hh)
        rw [heq]
        cases hx : execBlock O passes R₂ body (inv σ ρ).1 (Env.cons k ρ) with
        | ok σ' ρ' =>
            have hT' := treuAus_ok (hT _ _ hscope_body (hinv.heldB hh))
              (by rw [heq, hx])
            have g1 := hinv.trans hT'
            exact traverseLauf_gleich bo body inv ih hT hi hscope_body
              ks σ' ρ'.tail (g1.heldB hh)
        | next hl σ' ρ' =>
            have hT' := treuAus_next (hT _ _ hscope_body (hinv.heldB hh))
              (by rw [heq, hx])
            have g1 := hinv.trans hT'
            exact traverseLauf_gleich bo body inv ih hT hi hscope_body
              ks σ' ρ'.tail (g1.heldB hh)
        | leave hl σ' ρ' => rfl
        | zurueck σ' v => rfl
        | why σ' r => rfl
        | logik e => rfl
        | hardware e => rfl

/-- A consuming run under two agreeing handlers: mirror of
    `verbrauchLauf_kongruent`, with the discipline threaded. Selection,
    measure and invariant worlds are linked by `generalize`, as in
    `verbrauchLauf_treu`. -/
theorem verbrauchLauf_gleich (bo : Option Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (ih : ∀ (σ : World D) (ρ : Env D (.index (D.count t) :: Γ)), body.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (hT : ∀ (σ : World D) (ρ : Env D (.index (D.count t) :: Γ)), body.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body σ ρ))
    (hi : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (inv σ ρ).1)
    (hsel : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (sel σ ρ).1)
    (hmass : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (massW σ ρ).1)
    (hscope_body : body.ScopesOk) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      verbrauchLauf (l := l) t (fun σ ρ => execBlock O passes R₁ body σ ρ)
        inv sel massW bound fuel σ ρ =
      verbrauchLauf (l := l) t (fun σ ρ => execBlock O passes R₂ body σ ρ)
        inv sel massW bound fuel σ ρ
  | 0, _, _, _ => rfl
  | n + 1, σ, ρ, hh => by
      simp only [verbrauchLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc]
      · rw [if_neg hc]
        have hinv := hi σ ρ hh
        have hselg := hsel (inv σ ρ).1 ρ (hinv.heldB hh)
        generalize heq_sel : sel (inv σ ρ).1 ρ = selected at hselg ⊢
        rcases selected with ⟨σr, w, b⟩
        cases b <;> cases w with
        | none => rfl
        | some v =>
            simp only
            have hmassg := hmass σr ρ ((hinv.trans hselg).heldB hh)
            generalize heq_mass : massW σr ρ = p1 at hmassg ⊢
            rcases p1 with ⟨σm, m⟩
            simp only
            have gm : Treu V.schreibt V.gschreibt σ σm :=
              (hinv.trans hselg).trans hmassg
            have heq := ih σm (.cons v ρ) hscope_body (gm.heldB hh)
            rw [heq]
            cases hx : execBlock O passes R₂ body σm (Env.cons v ρ) with
            | ok σ' ρ' =>
                dsimp only
                have hT' := treuAus_ok (hT _ _ hscope_body (gm.heldB hh))
                  (by rw [heq, hx])
                have g1 : Treu V.schreibt V.gschreibt σ σ' := gm.trans hT'
                have hmassg2 := hmass σ' ρ'.tail (g1.heldB hh)
                generalize heq_mass2 : massW σ' ρ'.tail = p2 at hmassg2 ⊢
                rcases p2 with ⟨σm', m'⟩
                dsimp only
                by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                · rw [if_pos hfall]
                  have g2 : Treu V.schreibt V.gschreibt σ σm' := g1.trans hmassg2
                  exact verbrauchLauf_gleich bo t body inv sel massW bound
                    ih hT hi hsel hmass hscope_body n σm' ρ'.tail (g2.heldB hh)
                · rw [if_neg hfall] <;> rfl
            | next hl σ' ρ' =>
                dsimp only
                have hT' := treuAus_next (hT _ _ hscope_body (gm.heldB hh))
                  (by rw [heq, hx])
                have g1 : Treu V.schreibt V.gschreibt σ σ' := gm.trans hT'
                have hmassg2 := hmass σ' ρ'.tail (g1.heldB hh)
                generalize heq_mass2 : massW σ' ρ'.tail = p2 at hmassg2 ⊢
                rcases p2 with ⟨σm', m'⟩
                dsimp only
                by_cases hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
                · rw [if_pos hfall]
                  have g2 : Treu V.schreibt V.gschreibt σ σm' := g1.trans hmassg2
                  exact verbrauchLauf_gleich bo t body inv sel massW bound
                    ih hT hi hsel hmass hscope_body n σm' ρ'.tail (g2.heldB hh)
                · rw [if_neg hfall] <;> rfl
            | leave hl σ' ρ' => simp only
            | zurueck σ' v => simp only
            | why σ' r => simp only
            | logik e => simp only
            | hardware e => simp only

end SchleifenGleich

section SchleifenGleichZwei

variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- A retry run under two agreeing handlers: mirror of
    `retryLauf_kongruent`, with the discipline threaded. -/
theorem retryLauf_gleich (bo : Option Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (body : Block D V true Γ Λ Λ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueber : Block D V l Γ Λ Λ)
    (ih : ∀ (σ : World D) (ρ : Env D Γ), body.ScopesOk → HeldB bo Λ σ.haelt →
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (hT : ∀ (σ : World D) (ρ : Env D Γ), body.ScopesOk → HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body σ ρ))
    (ihu : ∀ (σ : World D) (ρ : Env D Γ), ueber.ScopesOk → HeldB bo Λ σ.haelt →
      execBlock O passes R₁ ueber σ ρ = execBlock O passes R₂ ueber σ ρ)
    (hb : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (bis σ ρ).1)
    (hscope_body : body.ScopesOk) (hscope_ueber : ueber.ScopesOk) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      retryLauf (fun σ ρ => execBlock O passes R₁ body σ ρ) bis
        (fun σ ρ => execBlock O passes R₁ ueber σ ρ) n σ ρ =
      retryLauf (fun σ ρ => execBlock O passes R₂ body σ ρ) bis
        (fun σ ρ => execBlock O passes R₂ ueber σ ρ) n σ ρ
  | 0, σ, ρ, hh => by
      simp only [retryLauf]
      by_cases hc : (bis σ ρ).2 = true
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact ihu (bis σ ρ).1 ρ hscope_ueber ((hb σ ρ hh).heldB hh)
  | n + 1, σ, ρ, hh => by
      simp only [retryLauf]
      by_cases hc : (bis σ ρ).2 = true
      · rw [if_pos hc]
      · rw [if_neg hc]
        have hinv := hb σ ρ hh
        have heq := ih (bis σ ρ).1 ρ hscope_body (hinv.heldB hh)
        rw [heq]
        cases hx : execBlock O passes R₂ body (bis σ ρ).1 ρ with
        | ok σ' ρ' =>
            have hT' := treuAus_ok (hT _ _ hscope_body (hinv.heldB hh))
              (by rw [heq, hx])
            have g1 := hinv.trans hT'
            exact retryLauf_gleich bo body bis ueber ih hT ihu hb
              hscope_body hscope_ueber n σ' ρ' (g1.heldB hh)
        | next hl σ' ρ' =>
            have hT' := treuAus_next (hT _ _ hscope_body (hinv.heldB hh))
              (by rw [heq, hx])
            have g1 := hinv.trans hT'
            exact retryLauf_gleich bo body bis ueber ih hT ihu hb
              hscope_body hscope_ueber n σ' ρ' (g1.heldB hh)
        | leave hl σ' ρ' => rfl
        | zurueck σ' v => rfl
        | why σ' r => rfl
        | logik e => rfl
        | hardware e => rfl

/-- A forever run under two agreeing handlers: mirror of
    `foreverLauf_kongruent`, with the discipline threaded. -/
theorem foreverLauf_gleich (bo : Option Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme)
    (body : Block D V true Γ Λ Λ)
    (inv : World D → Env D Γ → World D × Bool)
    (ih : ∀ (σ : World D) (ρ : Env D Γ), body.ScopesOk → HeldB bo Λ σ.haelt →
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (hT : ∀ (σ : World D) (ρ : Env D Γ), body.ScopesOk → HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R₁ body σ ρ))
    (hi : ∀ (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      Treu V.schreibt V.gschreibt σ (inv σ ρ).1)
    (hscope_body : body.ScopesOk) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      foreverLauf (l := l) a (fun σ ρ => execBlock O passes R₁ body σ ρ) inv n σ ρ =
      foreverLauf (l := l) a (fun σ ρ => execBlock O passes R₂ body σ ρ) inv n σ ρ
  | 0, _, _, _ => rfl
  | n + 1, σ, ρ, hh => by
      simp only [foreverLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc]
      · rw [if_neg hc]
        have hinv := hi σ ρ hh
        have heq := ih (inv σ ρ).1 ρ hscope_body (hinv.heldB hh)
        rw [heq]
        cases hx : execBlock O passes R₂ body (inv σ ρ).1 ρ with
        | ok σ' ρ' =>
            have hT' := treuAus_ok (hT _ _ hscope_body (hinv.heldB hh))
              (by rw [heq, hx])
            have g1 := hinv.trans hT'
            exact foreverLauf_gleich bo a body inv ih hT hi hscope_body
              n σ' ρ' (g1.heldB hh)
        | next hl σ' ρ' =>
            have hT' := treuAus_next (hT _ _ hscope_body (hinv.heldB hh))
              (by rw [heq, hx])
            have g1 := hinv.trans hT'
            exact foreverLauf_gleich bo a body inv ih hT hi hscope_body
              n σ' ρ' (g1.heldB hh)
        | leave hl σ' ρ' => rfl
        | zurueck σ' v => rfl
        | why σ' r => rfl
        | logik e => rfl
        | hardware e => rfl

end SchleifenGleichZwei
end Gabbro.Grammatik
