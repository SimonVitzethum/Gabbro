/-
  File:      Grammatik/Nichtinterferenz/Lokal.lean
  Subject:   THE FLOW CHECK OVER THE SYNTAX, AND THE LOCALITY OF ONE LEAF --
             `nS`/`nB`/`nE` (every read inside a carrier set `S`, every
             axiom admitted), the residue form `GRest.nR`, agreement of two
             worlds on a carrier set (`WRel`), the oracle condition
             (`OrakelTreu`), and the relational leaf lemma `blatt_rel`: a
             leaf whose reads lie in `S`, run in two worlds that agree on
             `T ⊇ S` (and on the trace), ends in two outcomes of the same
             shape, with equal environments and values, equal traces and
             memories that agree on `T`.
-/
module
public import Grammatik.Nichtinterferenz.LokalBasis
import all Grammatik.Nichtinterferenz.LokalBasis
public import Grammatik.Nichtinterferenz.SchrittTreu
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
/-- **The oracle condition for a carrier set `T`**: every axiom `Ax`
    admits, called in two worlds that agree on `T` (and on the trace),
    answers the same and ends in two worlds that agree on `T` (and on the
    trace). The hardware answers `B`'s questions from `B`'s data only. -/
def OrakelTreu (T : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) (O : Orakel D) : Prop :=
  ∀ a, Ax a = true → ∀ (σ τ : World D) (ρ : Env D (D.aparams a)), WRel T σ τ →
    (O.wirkt a σ ρ).2 = (O.wirkt a τ ρ).2 ∧ WRel T (O.wirkt a σ ρ).1 (O.wirkt a τ ρ).1

/-- The oracle condition read through `axiomAntwort`. -/
theorem axiomAntwort_rel (O : Orakel D) {T : D.Tab ⊕ D.Glob → Bool} {AxT : D.Ax → Bool}
    (hO : OrakelTreu T AxT O) {a : D.Ax} (ha : AxT a = true) {σ τ : World D} (h : WRel T σ τ)
    (x : Env D (D.aparams a)) :
    (axiomAntwort O a σ x).2 = (axiomAntwort O a τ x).2 ∧
      WRel T (axiomAntwort O a σ x).1 (axiomAntwort O a τ x).1 := by
  obtain ⟨e1, e2⟩ := hO a ha (σ.fragt (.inl a)) (τ.fragt (.inl a)) x (h.fragt _)
  simp only [axiomAntwort]
  exact ⟨by rw [e1], e2⟩

/-- The same for a fallible axiom (C-free lane, 2026-09-30): the raw answer is the same, so is
    its decoding. -/
theorem axiomAntwortSonst_rel (O : Orakel D) {T : D.Tab ⊕ D.Glob → Bool} {AxT : D.Ax → Bool}
    (hO : OrakelTreu T AxT O) {a : D.Ax} (ha : AxT a = true) {σ τ : World D} (h : WRel T σ τ)
    (x : Env D (D.aparams a)) :
    (axiomAntwortSonst O a σ x).2 = (axiomAntwortSonst O a τ x).2 ∧
      WRel T (axiomAntwortSonst O a σ x).1 (axiomAntwortSonst O a τ x).1 := by
  obtain ⟨e1, e2⟩ := hO a ha (σ.fragt (.inl a)) (τ.fragt (.inl a)) x (h.fragt _)
  simp only [axiomAntwortSonst]
  exact ⟨by rw [e1], e2⟩

/-! ## 3. Two outcomes of the same shape -/

/-- Two outcomes of a statement run in two related worlds: the same
    constructor, the same environment/value/reason, equal traces and
    memories agreeing on `T`. -/
def AusRel (T : D.Tab ⊕ D.Glob → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    Ausgang V l Γ → Ausgang V l Γ → Prop
  | .ok σ ρ, .ok σ' ρ' => WRel T σ σ' ∧ ρ = ρ'
  | .zurueck σ v, .zurueck σ' v' => WRel T σ σ' ∧ v = v'
  | .why σ r, .why σ' r' => WRel T σ σ' ∧ r = r'
  | .leave _ σ ρ, .leave _ σ' ρ' => WRel T σ σ' ∧ ρ = ρ'
  | .next _ σ ρ, .next _ σ' ρ' => WRel T σ σ' ∧ ρ = ρ'
  | .logik _, .logik _ => True
  | .hardware _, .hardware _ => True
  | _, _ => False

section Blatt

variable (O : Orakel D) (passes : Nat) {S T : D.Tab ⊕ D.Glob → Bool} {Ax AxT : D.Ax → Bool}

set_option maxHeartbeats 1000000 in
/-- **A leaf is local, relationally.** Its reads in `S ⊆ T`, its axioms in
    `Ax ⊆ AxT` with the oracle faithful on `T`: two related worlds give two
    related outcomes. -/
theorem blatt_rel (hST : ∀ c, S c = true → T c = true) (hAx : ∀ a, Ax a = true → AxT a = true)
    (hO : OrakelTreu T AxT O) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true) (hn : nS S Ax s = true)
    {σ τ : World D} (h : WRel T σ τ) (ρ : Env D Γ) :
    AusRel T (execStmt O passes keinRuf s σ ρ) (execStmt O passes keinRuf s τ ρ) := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨h1.schreibSlot _ _ _ _ _, trivial⟩
  | assignThru p t ht f i e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1.2) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨h1.schreibSlot _ _ _ _ _, trivial⟩
  | assignThruOwn p t ht f i e m s ho he hg hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1.2) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨h1.schreibSlot _ _ _ _ _, trivial⟩
  | assignSlotRef r t ht ho f e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (r.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval r (alle_von hST hn.1) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨h1.schreibSlot _ _ _ _ _, trivial⟩
  | assignGlob g e hw hL =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.eval e (alle_von hST hn) ρ]
      exact ⟨h1.schreibGlob _ _ _, trivial⟩
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨WRel.schreibBytes t f hf Λ _ _ h1, trivial⟩
  | assignVar x e =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.eval e (alle_von hST hn) ρ]
      exact ⟨h1, rfl⟩
  | shift t f hτ i von nach hn' he hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (.inl t :: i.orte)
      have hi := h1.eval i (alle_von hST hn.2) ρ
      have ht : (σ.lese Λ (.inl t :: i.orte)).slots t = (τ.lese Λ (.inl t :: i.orte)).slots t :=
        h1.2 (.inl t) (hST _ hn.1)
      simp only [execStmt]
      rw [hi, ht]
      split
      · exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
      · trivial
  | axiomCall a args hnone hw hg hd hgd =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ args.orte
      have ha := h1.evalArgs args (alle_von hST hn.2) ρ
      obtain ⟨e1, e2⟩ := axiomAntwort_rel O hO (hAx a hn.1) h1
        (evalArgs (τ.lese Λ args.orte) args (τ.lese Λ args.orte) ρ)
      simp only [execStmt]
      rw [ha]
      revert e1 e2
      generalize axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (τ.lese Λ args.orte) args (τ.lese Λ args.orte) ρ) = p₁
      generalize axiomAntwort O a (τ.lese Λ args.orte)
        (evalArgs (τ.lese Λ args.orte) args (τ.lese Λ args.orte) ρ) = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      cases r1 <;> simp only [AusRel] <;> first | exact ⟨e2, trivial⟩ | exact ⟨e2, rfl⟩ | trivial
  | regWrite r hk e =>
      simp only [execStmt, AusRel]
      exact ⟨h.lese Λ e.orte, trivial⟩
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, AusRel]
      exact ⟨h.fragt _, trivial⟩
  | publish g e payload hp hw hL =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.eval e (alle_von hST hn) ρ]
      exact ⟨h1.schreibGlob _ _ _, trivial⟩
  | advances m a h' hs =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | retires m s' h' a =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | ret e hp =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.evalErg e (alle_von hST hn) ρ]
      exact ⟨h1, rfl⟩
  | retScoped e R =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.evalErg e (alle_von hST hn) ρ]
      exact ⟨h1.gibt_foldl R.scopes, rfl⟩
  | retWhy r hp =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | retWhyScoped r R =>
      simp only [execStmt, AusRel]
      exact ⟨h.gibt_foldl R.scopes, trivial⟩
  | leave h' =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | next h' =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | _ => simp only [Stmt.istBlatt, Bool.false_eq_true] at hb

end Blatt

end Gabbro.Grammatik
