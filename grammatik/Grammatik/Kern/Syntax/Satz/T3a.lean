module
public import Grammatik.Kern.Syntax.Satz.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Schleifen
variable {W : D.Tab → Bool} {G : D.Glob → Bool} {Λ : List (Res D)} {bo : Option Int}

theorem traverseLauf_gut (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hh σ' h
      simp only [traverseLauf] at h ⊢
      by_cases hc : (inv σ ρ).snd = true <;>
        simp only [hc, ite_true, ite_false, Bool.false_eq_true] at h ⊢
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hi σ ρ hh
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | cons k ks ih =>
      intro σ ρ hh σ' h
      simp only [traverseLauf] at h ⊢
      by_cases hc : (inv σ ρ).snd = false <;>
        simp only [hc, ite_true, ite_false] at h ⊢
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ hh
        have hstep := hs (inv σ ρ).1 (.cons k ρ) (hinv.heldB hh)
        cases hs1 : schritt (inv σ ρ).1 (.cons k ρ) with
        | ok σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (GutAusgang.vor g1 (ih σ1 ρ1.tail (g1.heldB hh))) σ' h
        | next _ σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (GutAusgang.vor g1 (ih σ1 ρ1.tail (g1.heldB hh))) σ' h
        | leave _ σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          by_cases hc1 : (inv σ1 ρ1.tail).snd = true <;>
            simp only [hc1, ite_true, ite_false, Ausgang.welt, Option.some.injEq,
              reduceCtorEq] at h ⊢
          subst h; exact g1.trans (hi σ1 ρ1.tail (g1.heldB hh))
        | zurueck σ1 v =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRetV (hstep _ rfl)
        | why σ1 r =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRetV (hstep _ rfl)
        | logik e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h
        | hardware e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h

/-- **Frame of a consuming run** (`traverse … by consuming`, C11): like
    `traverseLauf_gut`, by induction on the fuel. Selection, measure and
    invariant reads are premises (`hsel`, `hmass`, `hi`); every failing
    check is `.logik .schleife`, which carries no world. -/
theorem verbrauchLauf_gut (t : D.Tab)
    (schritt : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (inv σ ρ).1)
    (hsel : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (sel σ ρ).1)
    (hmass : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (massW σ ρ).1) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ
        (verbrauchLauf (l := l) t schritt inv sel massW bound fuel σ ρ) := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ ρ _ σ' h
      simp only [verbrauchLauf, Ausgang.welt, reduceCtorEq] at h
  | succ n ih =>
      intro σ ρ hh
      have hl : ∀ {σ0 : World D} (e : Logik D),
          GutAusgang (V := V) (l := l) (Γ := Γ) W G σ0 (.logik e) := by
        intro σ0 e σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      have hw : ∀ {σ0 : World D} (e : Hardware D),
          GutAusgang (V := V) (l := l) (Γ := Γ) W G σ0 (.hardware e) := by
        intro σ0 e σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      have hok : ∀ {σ0 σ1 : World D} (ρ0 : Env D Γ), Gut W G σ0 σ1 →
          GutAusgang (V := V) (l := l) W G σ0 (.ok σ1 ρ0) := by
        intro σ0 σ1 ρ0 hg σ' h
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hg
      rw [verbrauchLauf]
      by_cases hc : (inv σ ρ).snd = false
      · rw [if_pos hc]; exact hl _
      rw [if_neg hc]
      have hinv := hi σ ρ hh
      have hselg := hsel (inv σ ρ).1 ρ (hinv.heldB hh)
      generalize hsel_eq : sel (inv σ ρ).1 ρ = selected at hselg ⊢
      rcases selected with ⟨σr, _ | k, b⟩
      · have gsel : Gut W G σ σr := hinv.trans hselg
        cases b
        · exact hok ρ gsel
        · exact hl _
      have gsel : Gut W G σ σr := hinv.trans hselg
      dsimp only
      have hmassg := hmass σr ρ (gsel.heldB hh)
      generalize hm1 : massW σr ρ = p1 at hmassg ⊢
      rcases p1 with ⟨σm, m⟩
      dsimp only
      have gm : Gut W G σ σm := gsel.trans hmassg
      have hstep := hs σm (.cons k ρ) (gm.heldB hh)
      generalize hs1 : schritt σm (.cons k ρ) = o at hstep ⊢
      cases o with
      | ok σ1 ρ1 =>
        dsimp only
        have g1 : Gut W G σ σ1 := gm.trans (hstep σ1 rfl)
        have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
        generalize hm2 : massW σ1 ρ1.tail = p2 at hmassg2 ⊢
        rcases p2 with ⟨σm', m'⟩
        dsimp only
        by_cases hf : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
        · rw [if_pos hf]
          have g2 : Gut W G σ σm' := g1.trans hmassg2
          exact GutAusgang.vor g2 (ih σm' ρ1.tail (g2.heldB hh))
        · rw [if_neg hf]; exact hl _
      | next _ σ1 ρ1 =>
        dsimp only
        have g1 : Gut W G σ σ1 := gm.trans (hstep σ1 rfl)
        have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
        generalize hm2 : massW σ1 ρ1.tail = p2 at hmassg2 ⊢
        rcases p2 with ⟨σm', m'⟩
        dsimp only
        by_cases hf : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
        · rw [if_pos hf]
          have g2 : Gut W G σ σm' := g1.trans hmassg2
          exact GutAusgang.vor g2 (ih σm' ρ1.tail (g2.heldB hh))
        · rw [if_neg hf]; exact hl _
      | leave _ σ1 ρ1 =>
        dsimp only
        have g1 : Gut W G σ σ1 := gm.trans (hstep σ1 rfl)
        have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
        generalize hm2 : massW σ1 ρ1.tail = p2 at hmassg2 ⊢
        rcases p2 with ⟨σm', m'⟩
        dsimp only
        by_cases hf : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
        · rw [if_pos hf]
          have g2 : Gut W G σ σm' := g1.trans hmassg2
          by_cases hc1 : (inv σm' ρ1.tail).snd = true
          · rw [if_pos hc1]
            exact hok _ (g2.trans (hi σm' ρ1.tail (g2.heldB hh)))
          · rw [if_neg hc1]; exact hl _
        · rw [if_neg hf]; exact hl _
      | zurueck σ1 v =>
        intro σ' h
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact gm.transRetV (hstep _ rfl)
      | why σ1 r =>
        intro σ' h
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact gm.transRetV (hstep _ rfl)
      | logik e => exact hl e
      | hardware e => exact hw e


theorem retryLauf_gut (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hb : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (bis σ ρ).1)
    (hu : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ hh σ' h
      simp only [retryLauf] at h ⊢
      by_cases hc : (bis σ ρ).snd = true <;>
        simp only [hc, ite_true, ite_false] at h ⊢
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ hh
      · exact (GutAusgang.vor (hb σ ρ hh) (hu _ ρ ((hb σ ρ hh).heldB hh))) σ' h
  | succ n ih =>
      intro σ ρ hh σ' h
      simp only [retryLauf] at h ⊢
      by_cases hc : (bis σ ρ).snd = true <;>
        simp only [hc, ite_true, ite_false] at h ⊢
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ hh
      · have hinv := hb σ ρ hh
        have hstep := hs (bis σ ρ).1 ρ (hinv.heldB hh)
        cases hs1 : schritt (bis σ ρ).1 ρ with
        | ok σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (GutAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | next _ σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (GutAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | leave _ σ1 ρ1 =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.trans (hstep _ rfl)
        | zurueck σ1 v =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRetV (hstep _ rfl)
        | why σ1 r =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRetV (hstep _ rfl)
        | logik e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h
        | hardware e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h

theorem foreverLauf_gut (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _ σ' h; simp only [Ausgang.welt, foreverLauf, reduceCtorEq] at h
  | succ n ih =>
      intro σ ρ hh σ' h
      simp only [foreverLauf] at h ⊢
      by_cases hc : (inv σ ρ).snd = false <;>
        simp only [hc, ite_true, ite_false] at h ⊢
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ hh
        have hstep := hs (inv σ ρ).1 ρ (hinv.heldB hh)
        cases hs1 : schritt (inv σ ρ).1 ρ with
        | ok σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (GutAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | next _ σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (GutAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | leave _ σ1 ρ1 =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.trans (hstep _ rfl)
        | zurueck σ1 v =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRetV (hstep _ rfl)
        | why σ1 r =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRetV (hstep _ rfl)
        | logik e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h
        | hardware e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h

end Schleifen
end Gabbro.Grammatik
