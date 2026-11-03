module
public import Grammatik.Kern.Syntax.Satz

public import Grammatik.Logik.Vertraege.RahmenTreu.Grundlagen

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Schleifen
variable {W : D.Tab → Bool} {G : D.Glob → Bool}

theorem traverseLauf_treu (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, Treu W G σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ σ' h
      simp only [traverseLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hi σ ρ
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | cons k ks ih =>
      intro σ ρ σ' h
      simp only [traverseLauf] at h
      split at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ
        have hstep := hs (inv σ ρ).1 (.cons k ρ)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          split at h <;> simp only [Ausgang.welt, Option.some.injEq, reduceCtorEq] at h
          subst h; exact g1.trans (hi σ1 ρ1.tail)
        · rename_i σ1 v hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · simp only [Ausgang.welt, reduceCtorEq] at h

/-- Frame of a consuming run: like `traverseLauf_treu`, by induction on
    the fuel. Selection, measure and invariant reads are premises; every
    failing check is `.logik .schleife`, which carries no world. -/
theorem verbrauchLauf_treu (t : D.Tab)
    (schritt : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, Treu W G σ (inv σ ρ).1)
    (hsel : ∀ σ ρ, Treu W G σ (sel σ ρ).1)
    (hmass : ∀ σ ρ, Treu W G σ (massW σ ρ).1) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ
        (verbrauchLauf (l := l) t schritt inv sel massW bound fuel σ ρ) := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ ρ σ' h
      simp only [verbrauchLauf, Ausgang.welt, reduceCtorEq] at h
  | succ n ih =>
      intro σ ρ σ' h
      simp only [verbrauchLauf] at h ⊢
      split at h ⊢
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ
        have hselg := hsel (inv σ ρ).1 ρ
        split at h ⊢
        · rename_i σr hsel_eq
          simp only [Ausgang.welt, Option.some.injEq] at h
          subst h
          have hselr : Treu W G (inv σ ρ).1 σr := by
            rw [hsel_eq] at hselg
            exact hselg
          exact hinv.trans hselr
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · rename_i σr k hsel_eq
          have hselr : Treu W G (inv σ ρ).1 σr := by
            rw [hsel_eq] at hselg
            exact hselg
          have gsel : Treu W G σ σr := hinv.trans hselr
          have hmassg := hmass σr ρ
          have hstep := hs (massW σr ρ).1 (.cons k ρ)
          split at h ⊢
          · rename_i σ1 ρ1 hstep_eq
            simp only [hstep_eq] at hstep
            have g1 : Treu W G σ σ1 :=
              (gsel.trans hmassg).trans (hstep σ1 rfl)
            have hmassg2 := hmass σ1 ρ1.tail
            split at h ⊢
            · have g2 : Treu W G σ (massW σ1 ρ1.tail).1 :=
                g1.trans hmassg2
              exact (TreuAusgang.vor g2 (ih (massW σ1 ρ1.tail).1 ρ1.tail)) σ' h
            · simp only [Ausgang.welt, reduceCtorEq] at h
          · rename_i σ1 ρ1 hstep_eq
            simp only [hstep_eq] at hstep
            have g1 : Treu W G σ σ1 :=
              (gsel.trans hmassg).trans (hstep σ1 rfl)
            have hmassg2 := hmass σ1 ρ1.tail
            split at h ⊢
            · have g2 : Treu W G σ (massW σ1 ρ1.tail).1 :=
                g1.trans hmassg2
              exact g2.trans (ih (massW σ1 ρ1.tail).1 ρ1.tail σ' h)
            · simp only [Ausgang.welt, reduceCtorEq] at h
          · rename_i σ1 ρ1 hstep_eq
            simp only [hstep_eq] at hstep
            have g1 : Treu W G σ σ1 :=
              (gsel.trans hmassg).trans (hstep σ1 rfl)
            have hmassg2 := hmass σ1 ρ1.tail
            split at h ⊢
            · split at h ⊢
              · simp only [Ausgang.welt, Option.some.injEq] at h
                subst h
                have h3 := hi (massW σ1 ρ1.tail).1 ρ1.tail
                exact g1.trans (hmassg2.trans h3)
              · simp only [Ausgang.welt, reduceCtorEq] at h
            · simp only [Ausgang.welt, reduceCtorEq] at h
          · rename_i σ1 v hstep_eq
            simp only [hstep_eq] at hstep
            simp only [Ausgang.welt, Option.some.injEq] at h ⊢
            subst h
            exact (gsel.trans hmassg).transRet
              (hstep _ rfl)
          · rename_i σ1 r hstep_eq
            simp only [hstep_eq] at hstep
            simp only [Ausgang.welt, Option.some.injEq] at h ⊢
            subst h
            exact (gsel.trans hmassg).transRet
              (hstep _ rfl)
          · simp only [Ausgang.welt, reduceCtorEq] at h
          · simp only [Ausgang.welt, reduceCtorEq] at h

theorem retryLauf_treu (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hb : ∀ σ ρ, Treu W G σ (bis σ ρ).1)
    (hu : ∀ σ ρ, TreuAusgang W G σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ σ' h
      simp only [retryLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ
      · exact (hb σ ρ).trans (hu _ ρ σ' h)
  | succ n ih =>
      intro σ ρ σ' h
      simp only [retryLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ
      · have hinv := hb σ ρ
        have hstep := hs (bis σ ρ).1 ρ
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · simp only [Ausgang.welt, reduceCtorEq] at h

theorem foreverLauf_treu (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, Treu W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ σ' h; simp only [Ausgang.welt, foreverLauf, reduceCtorEq] at h
  | succ n ih =>
      intro σ ρ σ' h
      simp only [foreverLauf] at h
      split at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ
        have hstep := hs (inv σ ρ).1 ρ
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · simp only [Ausgang.welt, reduceCtorEq] at h

end Schleifen

/-! ## 5. The two premises: the hardware and the handler -/

/-- **The hardware's half of the frame** (H1, the first two conjuncts of
    `GutO`): an axiom keeps the frame of its declared `effects` and leaves
    the held locks alone. The trace SHAPE of `GutO` is not needed here. -/
def TreuO (O : Orakel D) : Prop :=
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt

theorem gutO_treuO {O : Orakel D} (hO : GutO O) : TreuO O :=
  fun a σ ρ => ⟨(hO a σ ρ).1, (hO a σ ρ).2.1⟩

/-- **The handler's half**, WITHOUT the `HeldB` premise of `GutR`. A completed
    call keeps the frame; EITHER exit may release the scopes the callee
    unwound (`TreuRet`), never more. Unlike `GutR` there is no held-lock
    premise, so a release can never be collapsed back to an equality — it is
    carried explicitly on both channels. -/
def TreuR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ σ', (R f σ ρ).welt = some σ' →
    match (R f σ ρ) with
    | .ok _ _ => TreuRet (D.schreibt f) (D.gschreibt f) σ σ'
    | .why _ _ => TreuRet (D.schreibt f) (D.gschreibt f) σ σ'
    | .logik _ => True
    | .hardware _ => True

/-! ## 6. THE INDUCTION over the whole grammar -/

section Rumpf
variable (O : Orakel D)

theorem axiomAntwort_treu (hO : TreuO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    Treu (D.aschreibt a) (D.agschreibt a) σ (axiomAntwort O a σ ρ).1 := by
  simp only [axiomAntwort]
  exact ⟨(hO a (σ.fragt (.inl a)) ρ).1, (hO a (σ.fragt (.inl a)) ρ).2⟩

variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : TreuR R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

end Rumpf

end Gabbro.Grammatik
