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
      intro σ ρ hh σ' h
      simp only [verbrauchLauf] at h ⊢
      split at h ⊢
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ hh
        have hselg := hsel (inv σ ρ).1 ρ (hinv.heldB hh)
        split at h ⊢
        · rename_i σr hsel_eq
          simp only [Ausgang.welt, Option.some.injEq] at h
          subst h
          have hselr : Gut W G (inv σ ρ).1 σr := by
            rw [hsel_eq] at hselg
            exact hselg
          exact hinv.trans hselr
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · rename_i σr k hsel_eq
          have hselr : Gut W G (inv σ ρ).1 σr := by
            rw [hsel_eq] at hselg
            exact hselg
          have gsel : Gut W G σ σr := hinv.trans hselr
          have hmassg := hmass σr ρ (gsel.heldB hh)
          have hstep := hs (massW σr ρ).1 (.cons k ρ)
            ((gsel.trans hmassg).heldB hh)
          split at h ⊢
          · rename_i σ1 ρ1 hstep_eq
            simp only [hstep_eq] at hstep
            have g1 : Gut W G σ σ1 :=
              (gsel.trans hmassg).trans (hstep σ1 rfl)
            have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
            split at h ⊢
            · have g2 : Gut W G σ (massW σ1 ρ1.tail).1 :=
                g1.trans hmassg2
              exact (GutAusgang.vor g2 (ih (massW σ1 ρ1.tail).1 ρ1.tail
                (g2.heldB hh))) σ' h
            · simp only [Ausgang.welt, reduceCtorEq] at h
          · rename_i σ1 ρ1 hstep_eq
            simp only [hstep_eq] at hstep
            have g1 : Gut W G σ σ1 :=
              (gsel.trans hmassg).trans (hstep σ1 rfl)
            have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
            split at h ⊢
            · have g2 : Gut W G σ (massW σ1 ρ1.tail).1 :=
                g1.trans hmassg2
              exact (GutAusgang.vor g2 (ih (massW σ1 ρ1.tail).1 ρ1.tail
                (g2.heldB hh))) σ' h
            · simp only [Ausgang.welt, reduceCtorEq] at h
          · rename_i σ1 ρ1 hstep_eq
            simp only [hstep_eq] at hstep
            have g1 : Gut W G σ σ1 :=
              (gsel.trans hmassg).trans (hstep σ1 rfl)
            have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
            split at h ⊢
            · split at h ⊢
              · simp only [Ausgang.welt, Option.some.injEq] at h
                subst h
                have h3 := hi (massW σ1 ρ1.tail).1 ρ1.tail
                  ((g1.trans hmassg2).heldB hh)
                exact g1.trans (hmassg2.trans h3)
              · simp only [Ausgang.welt, reduceCtorEq] at h
            · simp only [Ausgang.welt, reduceCtorEq] at h
          · rename_i σ1 v hstep_eq
            simp only [hstep_eq] at hstep
            simp only [Ausgang.welt, Option.some.injEq] at h ⊢
            subst h
            exact (gsel.trans hmassg).transRetV
              (hstep _ rfl)
          · rename_i σ1 r hstep_eq
            simp only [hstep_eq] at hstep
            simp only [Ausgang.welt, Option.some.injEq] at h ⊢
            subst h
            exact (gsel.trans hmassg).transRetV
              (hstep _ rfl)
          · simp only [Ausgang.welt, reduceCtorEq] at h
          · simp only [Ausgang.welt, reduceCtorEq] at h

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
