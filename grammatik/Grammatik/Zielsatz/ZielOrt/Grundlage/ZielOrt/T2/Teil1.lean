module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Sperren

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A leaf keeps the held locks (`gut_blatt`, `Brav` leg). The firing equation
    is `.ok`, so scoped returns are impossible and the static scope check
    comes from the leaf itself (`scopesOk_of_ok`). -/
theorem blatt_offen (hO : GutO O) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true) (σ : World D)
    (ρ : Env D Γ) (hΛ : HeldIn Λ (offen σ.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes keinRuf s σ ρ = Ausgang.ok σ' ρ') :
    offen σ'.spur = offen σ.spur := by
  have hw : (execStmt O passes keinRuf s σ ρ).welt = some σ' := by rw [hst]; rfl
  have hscope : s.ScopesOk :=
    Stmt.scopesOk_of_ok O passes keinRuf s hleaf σ ρ σ' ρ' hst
  have hG := (Stmt.gut_blatt O passes keinRuf hO s hleaf hscope σ ρ hΛ) σ' hw
  rw [hst] at hG
  exact hG.2.1

/-- Reads keep the held locks. -/
theorem lese_offen (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    offen (σ.lese Λ os).spur = offen σ.spur :=
  lese_haelt σ Λ os

/-- **How one step moves the held locks of the acting thread** on the
    repaired G: they stay; or one lock `L` is added while no other thread
    holds it (`dannLocks`, the only take); or one lock is released that the
    head's static holdings NAME (`freiGib` and the `frei` peels, the
    release markers of an enclosing `locks` of the head frame). The bare
    `gibt` -- a release of ANY held lock at ANY time -- is gone: there is
    no step that releases a lock the head does not name. -/
theorem offen_schrittG (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    offen (M'.faeden f).spur = offen (M.faeden f).spur ∨
    (∃ L, RufFreiG M f L ∧ offen (M'.faeden f).spur = L :: offen (M.faeden f).spur) ∨
    (∃ L : D.Lock, Res.held L ∈ (M.faeden f).kopf.rest.2.2.1 ∧
      offen (M'.faeden f).spur = (offen (M.faeden f).spur).erase L) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        exact Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep)
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf _ hΛ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        exact Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep)
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inl trivial
          | exact Or.inl rfl
          | exact Or.inl (lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiom_offen' hO _ _ _ _ _ ‹axiomAntwort _ _ _ _ = _›]; exact lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiomSonst_offen' hO _ _ _ _ _ ‹axiomAntwortSonst _ _ _ _ = _›]; exact lese_offen _ _ _)
  | g2 hs =>
    cases hs with
    | dannLocks l Γ Λ Λ'' L _ _ _ _ _ _ _ _ hfrei =>
        simp only [rufUpdateG_self]
        exact Or.inr (Or.inl ⟨L, hfrei, rfl⟩)
    | freiGib l Γ Λ L k ρ hhead =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
        rw [hhead]
        exact List.mem_cons_self
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inl trivial
          | exact Or.inl rfl
          | exact Or.inl (lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiom_offen' hO _ _ _ _ _ ‹axiomAntwort _ _ _ _ = _›]; exact lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiomSonst_offen' hO _ _ _ _ _ ‹axiomAntwortSonst _ _ _ _ = _›]; exact lese_offen _ _ _)
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inl trivial
          | exact Or.inl rfl
          | exact Or.inl (lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiom_offen' hO _ _ _ _ _ ‹axiomAntwort _ _ _ _ = _›]; exact lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiomSonst_offen' hO _ _ _ _ _ ‹axiomAntwortSonst _ _ _ _ = _›]; exact lese_offen _ _ _)
  | g4 hs =>
    cases hs with
    | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
        rw [hhead]
        exact (Block.held_iff rest L).mp List.mem_cons_self
    | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
        rw [hhead]
        exact (Block.held_iff rest L).mp List.mem_cons_self
    | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inl trivial
          | exact Or.inl rfl
          | exact Or.inl (lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiom_offen' hO _ _ _ _ _ ‹axiomAntwort _ _ _ _ = _›]; exact lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiomSonst_offen' hO _ _ _ _ _ ‹axiomAntwortSonst _ _ _ _ = _›]; exact lese_offen _ _ _)
  | g5 hs =>
    cases hs with
    | dannExchange _ _ l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [hs₂, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiom _ _ l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiomElseOk _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ r hax =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inl trivial
          | exact Or.inl rfl
          | exact Or.inl (lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiom_offen' hO _ _ _ _ _ ‹axiomAntwort _ _ _ _ = _›]; exact lese_offen _ _ _)
          | (refine Or.inl ?_; rw [axiomSonst_offen' hO _ _ _ _ _ ‹axiomAntwortSonst _ _ _ _ = _›]; exact lese_offen _ _ _)
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ r hax =>
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        rw [axiomSonst_offen' hO _ _ _ _ _ ‹axiomAntwortSonst _ _ _ _ = _›]
        exact lese_offen _ _ _

  | g7 hs =>
    cases hs with
    | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb _ ρ hleave hhead σ' ρ' neu hstep hneu _ σm hsm _ _ _ σ₁ hs₁ _ neu₁ hneu₁ hΛ =>
        simp only [execStmt, Ausgang.leave.injEq] at hstep
        obtain ⟨e, _⟩ := hstep
        subst e hs₁ hsm
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        simp only [lese_offen] <;> rfl
    | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb _ ρ hnext hhead σ' ρ' neu hstep hneu _ σm hsm _ _ _ neum hneum hΛ =>
        simp only [execStmt, Ausgang.next.injEq] at hstep
        obtain ⟨e, _⟩ := hstep
        subst e hsm
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        simp only [lese_offen] <;> rfl
    | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu =>
        simp only [rufUpdateG_self]
        subst σ₁
        exact Or.inl (lese_offen _ _ _)
    | rueckScopedGrund => exact Or.inl (by simp only [rufUpdateG_self])
    | rueckFreigabe ρ a L remaining hhead =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
        rw [hhead]
        exact List.mem_cons_self
    | rueckAntwort ρ a hhead z hantwort =>
        simp only [rufUpdateG_self, rufAntwortG_spur hantwort]
        exact Or.inl rfl
    | _ =>
        simp only [execStmt, Ausgang.leave.injEq, Ausgang.next.injEq] at *
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl ?_
        simp only [lese_offen] <;> rfl

/-- The start trace of a thread holds exactly its start function's
    signature locks. -/
theorem offen_start (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) (L : D.Lock) :
    L ∈ offen ((RufStartG P sp init).faeden t).spur ↔ L ∈ D.haelt (init t).1 := by
  have e : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).spur = startSpur (init t).1
    cases init t
    rfl
  rw [e]
  exact offen_startSpur _ L

/-- **Lock exclusivity on the repaired G.** On every reachable machine, a
    lock held by thread `f` is held by no other thread. Induction over
    reachability with `offen_schrittG`: a lock enters a held set only
    through `dannLocks`, whose `RufFreiG` premise says no other thread holds
    it; at the start, only through the start trace, exclusive by
    `StartExklusiv`. -/
theorem exklusivG (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (h : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ (f g : Faden), f ≠ g → ∀ L : D.Lock,
      L ∈ offen (M.faeden f).spur → L ∉ offen (M.faeden g).spur := by
  induction h with
  | start =>
      intro f g hfg L hLf hLg
      exact hex f g hfg L ((offen_start sp init f L).mp hLf) ((offen_start sp init g L).mp hLg)
  | schritt M M' f0 _ hs ih =>
      intro f g hfg L hLf hLg
      have hfremd : ∀ t, t ≠ f0 → M'.faeden t = M.faeden t :=
        fun t ht => rufSchrittG_fremd hs t ht
      by_cases hf : f = f0
      · subst hf
        have hg : g ≠ f := fun e => hfg e.symm
        rw [hfremd g hg] at hLg
        rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', _, e⟩
        · rw [e] at hLf
          exact ih f g hfg L hLf hLg
        · rw [e] at hLf
          rcases List.mem_cons.mp hLf with rfl | hLf
          · exact hfrei g hg hLg
          · exact ih f g hfg L hLf hLg
        · rw [e] at hLf
          exact ih f g hfg L (List.mem_of_mem_erase hLf) hLg
      · rw [hfremd f hf] at hLf
        by_cases hg : g = f0
        · subst hg
          rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', _, e⟩
          · rw [e] at hLg
            exact ih f g hfg L hLf hLg
          · rw [e] at hLg
            rcases List.mem_cons.mp hLg with rfl | hLg
            · exact hfrei f hf hLf
            · exact ih f g hfg L hLf hLg
          · rw [e] at hLg
            exact ih f g hfg L hLf (List.mem_of_mem_erase hLg)
        · rw [hfremd g hg] at hLg
          exact ih f g hfg L hLf hLg

/-- A G machine seen as a generic machine (only memory and traces are read
    by the merged leaf lemmas). -/
def genAusG (M : RufMaschineG D) : GenMaschine D :=
  ⟨M.speicher, fun g => (M.faeden g).spur, M.lauf, M.start, [], 0⟩

/-- Agreement of two memories on one carrier. -/
def TraegerGleich (s s' : Speicher D) : D.Tab ⊕ D.Glob → Prop
  | .inl t => s.slots t = s'.slots t
  | .inr x => s.globs x = s'.globs x

theorem traegerGleich_refl (s : Speicher D) (c : D.Tab ⊕ D.Glob) : TraegerGleich s s c := by
  cases c <;> rfl

theorem traegerGleich_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h1 : TraegerGleich s s' c) (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c
  · exact h1.trans h2
  · exact h1.trans h2

end Sperren
end Gabbro.Grammatik
