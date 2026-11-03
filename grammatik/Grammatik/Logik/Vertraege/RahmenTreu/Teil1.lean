module
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}


/-! ## 4. The three loop combinators -/

section Schleifen
variable {W : D.Tab → Bool} {G : D.Glob → Bool}

theorem traverseLauf_treu (bo : Option Int) (Λ : List (Res D))
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Treu W G σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      HeldB bo Λ σ.haelt →
      TreuAusgang W G σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hh
      rw [traverseLauf]
      by_cases hc : (inv σ ρ).snd = true
      · rw [if_pos hc]; intro σ' h
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hi σ ρ hh
      · rw [if_neg hc]; intro σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
  | cons k ks ih =>
      intro σ ρ hh
      rw [traverseLauf]
      by_cases hc : (inv σ ρ).snd = false
      · rw [if_pos hc]; intro σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      rw [if_neg hc]
      have hinv := hi σ ρ hh
      have hstep := hs (inv σ ρ).1 (.cons k ρ) (hinv.heldB hh)
      generalize hs1 : schritt (inv σ ρ).1 (.cons k ρ) = o at hstep ⊢
      cases o with
      | ok σ1 ρ1 =>
        have g1 := hinv.trans (hstep σ1 rfl)
        exact TreuAusgang.vor g1 (ih σ1 ρ1.tail (g1.heldB hh))
      | next _ σ1 ρ1 =>
        have g1 := hinv.trans (hstep σ1 rfl)
        exact TreuAusgang.vor g1 (ih σ1 ρ1.tail (g1.heldB hh))
      | leave _ σ1 ρ1 =>
        have g1 := hinv.trans (hstep σ1 rfl)
        dsimp only
        by_cases hc1 : (inv σ1 ρ1.tail).snd = true
        · rw [if_pos hc1]; intro σ' h
          simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact g1.trans (hi σ1 ρ1.tail (g1.heldB hh))
        · rw [if_neg hc1]; intro σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      | zurueck σ1 v =>
        intro σ' h; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact hinv.transRet (hstep _ rfl)
      | why σ1 r =>
        intro σ' h; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact hinv.transRet (hstep _ rfl)
      | logik e => intro σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      | hardware e => intro σ' h; simp only [Ausgang.welt, reduceCtorEq] at h

/-- Frame of a consuming run: like `traverseLauf_treu`, by induction on
    the fuel. Selection, measure and invariant reads are premises; every
    failing check is `.logik .schleife`, which carries no world. -/
theorem verbrauchLauf_treu (bo : Option Int) (Λ : List (Res D)) (t : D.Tab)
    (schritt : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Treu W G σ (inv σ ρ).1)
    (hsel : ∀ σ ρ, HeldB bo Λ σ.haelt → Treu W G σ (sel σ ρ).1)
    (hmass : ∀ σ ρ, HeldB bo Λ σ.haelt → Treu W G σ (massW σ ρ).1) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ),
      HeldB bo Λ σ.haelt →
      TreuAusgang W G σ
        (verbrauchLauf (l := l) t schritt inv sel massW bound fuel σ ρ) := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ ρ _ σ' h
      simp only [verbrauchLauf, Ausgang.welt, reduceCtorEq] at h
  | succ n ih =>
      intro σ ρ hh
      have hl : ∀ {σ0 : World D} (e : Logik D),
          TreuAusgang (V := V) (l := l) (Γ := Γ) W G σ0 (.logik e) := by
        intro σ0 e σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      have hw : ∀ {σ0 : World D} (e : Hardware D),
          TreuAusgang (V := V) (l := l) (Γ := Γ) W G σ0 (.hardware e) := by
        intro σ0 e σ' h; simp only [Ausgang.welt, reduceCtorEq] at h
      have hok : ∀ {σ0 σ1 : World D} (ρ0 : Env D Γ), Treu W G σ0 σ1 →
          TreuAusgang (V := V) (l := l) W G σ0 (.ok σ1 ρ0) := by
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
      · have gsel : Treu W G σ σr := hinv.trans hselg
        cases b
        · exact hok ρ gsel
        · exact hl _
      have gsel : Treu W G σ σr := hinv.trans hselg
      dsimp only
      have hmassg := hmass σr ρ (gsel.heldB hh)
      generalize hm1 : massW σr ρ = p1 at hmassg ⊢
      rcases p1 with ⟨σm, m⟩
      dsimp only
      have gm : Treu W G σ σm := gsel.trans hmassg
      have hstep := hs σm (.cons k ρ) (gm.heldB hh)
      generalize hs1 : schritt σm (.cons k ρ) = o at hstep ⊢
      cases o with
      | ok σ1 ρ1 =>
        dsimp only
        have g1 : Treu W G σ σ1 := gm.trans (hstep σ1 rfl)
        have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
        generalize hm2 : massW σ1 ρ1.tail = p2 at hmassg2 ⊢
        rcases p2 with ⟨σm', m'⟩
        dsimp only
        by_cases hf : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
        · rw [if_pos hf]
          have g2 : Treu W G σ σm' := g1.trans hmassg2
          exact TreuAusgang.vor g2 (ih σm' ρ1.tail (g2.heldB hh))
        · rw [if_neg hf]; exact hl _
      | next _ σ1 ρ1 =>
        dsimp only
        have g1 : Treu W G σ σ1 := gm.trans (hstep σ1 rfl)
        have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
        generalize hm2 : massW σ1 ρ1.tail = p2 at hmassg2 ⊢
        rcases p2 with ⟨σm', m'⟩
        dsimp only
        by_cases hf : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
        · rw [if_pos hf]
          have g2 : Treu W G σ σm' := g1.trans hmassg2
          exact TreuAusgang.vor g2 (ih σm' ρ1.tail (g2.heldB hh))
        · rw [if_neg hf]; exact hl _
      | leave _ σ1 ρ1 =>
        dsimp only
        have g1 : Treu W G σ σ1 := gm.trans (hstep σ1 rfl)
        have hmassg2 := hmass σ1 ρ1.tail (g1.heldB hh)
        generalize hm2 : massW σ1 ρ1.tail = p2 at hmassg2 ⊢
        rcases p2 with ⟨σm', m'⟩
        dsimp only
        by_cases hf : 0 ≤ m' ∧ m' ≤ bound ∧ m' < m
        · rw [if_pos hf]
          have g2 : Treu W G σ σm' := g1.trans hmassg2
          by_cases hc1 : (inv σm' ρ1.tail).snd = true
          · rw [if_pos hc1]
            exact hok _ (g2.trans (hi σm' ρ1.tail (g2.heldB hh)))
          · rw [if_neg hc1]; exact hl _
        · rw [if_neg hf]; exact hl _
      | zurueck σ1 v =>
        intro σ' h
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact gm.transRet (hstep _ rfl)
      | why σ1 r =>
        intro σ' h
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact gm.transRet (hstep _ rfl)
      | logik e => exact hl e
      | hardware e => exact hw e



theorem retryLauf_treu (bo : Option Int) (Λ : List (Res D))
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → TreuAusgang W G σ (schritt σ ρ))
    (hb : ∀ σ ρ, HeldB bo Λ σ.haelt → Treu W G σ (bis σ ρ).1)
    (hu : ∀ σ ρ, HeldB bo Λ σ.haelt → TreuAusgang W G σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      HeldB bo Λ σ.haelt →
      TreuAusgang W G σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ hh σ' h
      simp only [retryLauf] at h ⊢
      by_cases hc : (bis σ ρ).snd = true <;>
        simp only [hc, ite_true, ite_false] at h ⊢
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ hh
      · exact (TreuAusgang.vor (hb σ ρ hh) (hu _ ρ ((hb σ ρ hh).heldB hh))) σ' h
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
          exact (TreuAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | next _ σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (TreuAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | leave _ σ1 ρ1 =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.trans (hstep _ rfl)
        | zurueck σ1 v =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRet (hstep _ rfl)
        | why σ1 r =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRet (hstep _ rfl)
        | logik e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h
        | hardware e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h


theorem foreverLauf_treu (bo : Option Int) (Λ : List (Res D))
    (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Treu W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      HeldB bo Λ σ.haelt →
      TreuAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
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
          exact (TreuAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | next _ σ1 ρ1 =>
          simp only [hs1] at hstep h ⊢
          have g1 := hinv.trans (hstep σ1 rfl)
          exact (TreuAusgang.vor g1 (ih σ1 ρ1 (g1.heldB hh))) σ' h
        | leave _ σ1 ρ1 =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.trans (hstep _ rfl)
        | zurueck σ1 v =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRet (hstep _ rfl)
        | why σ1 r =>
          simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, Option.some.injEq] at h
          subst h
          simp only [hs1] at hstep ⊢
          exact hinv.transRet (hstep _ rfl)
        | logik e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h
        | hardware e => simp only [hs1, Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true, Ausgang.welt, reduceCtorEq] at h


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

/-- **The handler's half**: the frame and the held locks under the callee-entry
    discipline (`HeldB`, as in `GutR`). A normal return keeps the frame and every
    held lock (`Treu`), while a propagated reason may release the scopes the
    callee unwound (`TreuRet` over the callee residual and floor), never more.
    The premise-free `TreuRet`-on-both-exits (C11) was too weak to transport call
    continuations (`TreuAusgang.vorRet` was false); the premise-free
    `Treu`-on-`ok` (pre-C11) was false at releasing bodies: collapsing a release
    to an equality needs the entry discipline, which an arbitrary world does
    not meet. -/
def TreuR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt →
    ∀ σ', (R f σ ρ).welt = some σ' →
      match (R f σ ρ) with
      | .ok _ _ => Treu (D.schreibt f) (D.gschreibt f) σ σ'
      | .why _ _ => TreuRet (D.schreibt f) (D.gschreibt f) (D.signatur f).haelt
          (D.signatur f).boden σ σ'
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
