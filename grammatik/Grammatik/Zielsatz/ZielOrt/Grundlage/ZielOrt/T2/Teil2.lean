module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2.Teil2G5
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2.Teil2G6

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Sperren
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely, one step.** A step of thread `u` leaves a carrier `c` alone
    if (a) some lock guarding `c` is not held by `u`, or (b) the signature of
    `u`'s head function does not permit writing `c`. Every writing step
    carries its carrier's guards in the static holdings (`darf`/`gdarf` on
    the write, on `exchange`, on the axiom's declared writes) and the
    signature permission (`hw`, or `RufPasst` for the generalized C08 calls),
    and every writing step now demands `HeldGenau`, so (a) contradicts a
    write; the frame of `gut_blatt` and of the oracle (`GutO`) gives (b). -/
theorem schritt_traeger (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') (c : D.Tab ⊕ D.Glob)
    (hc : (∃ L, Bewacht c L ∧ L ∉ offen (M.faeden u).spur) ∨
      TraegerSchreibt (M.faeden u).kopf.f c = false) :
    TraegerGleich M'.speicher M.speicher c := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
        have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon u) ρ).welt = some σ' := by
          show (execStmt O passes keinRuf s (M.weltVon u) ρ).welt = some σ'
          rw [hstep]; rfl
        have hscope : s.ScopesOk :=
          Stmt.scopesOk_of_ok O passes keinRuf s hleaf (M.weltVon u) ρ σ' ρ' hstep
        have hR := (Stmt.gut_blatt O passes keinRuf hO s hleaf hscope (M.weltVon u) ρ hΛ) σ'
          (by rw [hstep]; rfl)
        rw [hstep] at hR
        cases c with
        | inl t =>
            show σ'.slots t = M.speicher.slots t
            funext k fld
            rcases hc with ⟨L, hB, hfrei⟩ | hW
            · exact blatt_erhaelt_slots O passes hO (genAusG M) u s ρ hleaf σ' hw t L hB hΛ hfrei k fld
            · exact hR.1 t hW k fld
        | inr x =>
            show σ'.globs x = M.speicher.globs x
            rcases hc with ⟨L, hB, hfrei⟩ | hW
            · exact blatt_erhaelt_globs O passes hO (genAusG M) u s ρ hleaf σ' hw x L hB hΛ hfrei
            · exact hR.2 x hW
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
        have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon u) ρ).welt = some σ' := by
          show (execStmt O passes keinRuf s (M.weltVon u) ρ).welt = some σ'
          rw [hstep]; rfl
        have hscope : s.ScopesOk :=
          Stmt.scopesOk_of_ok O passes keinRuf s hleaf (M.weltVon u) ρ σ' ρ' hstep
        have hR := (Stmt.gut_blatt O passes keinRuf hO s hleaf hscope (M.weltVon u) ρ hΛ) σ'
          (by rw [hstep]; rfl)
        rw [hstep] at hR
        cases c with
        | inl t =>
            show σ'.slots t = M.speicher.slots t
            funext k fld
            rcases hc with ⟨L, hB, hfrei⟩ | hW
            · exact blatt_erhaelt_slots O passes hO (genAusG M) u s ρ hleaf σ' hw t L hB hΛ hfrei k fld
            · exact hR.1 t hW k fld
        | inr x =>
            show σ'.globs x = M.speicher.globs x
            rcases hc with ⟨L, hB, hfrei⟩ | hW
            · exact blatt_erhaelt_globs O passes hO (genAusG M) u s ρ hleaf σ' hw x L hB hΛ hfrei
            · exact hR.2 x hW
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwort] at this
          exact this.symm
        have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
        rw [← e] at hfr
        cases c with
        | inl t =>
            show σ₂.slots t = M.speicher.slots t
            have ha : D.aschreibt a t = false := by
              cases hat : D.aschreibt a t with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hd t hat _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hw t hat
                    rw [hW] at this
                    exact Bool.false_ne_true this
            funext k fld
            rw [hfr.1 t ha k fld, hs₁]
            rfl
        | inr x =>
            show σ₂.globs x = M.speicher.globs x
            have ha : D.agschreibt a x = false := by
              cases hax' : D.agschreibt a x with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hgd x hax' _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hg x hax'
                    rw [hW] at this
                    exact Bool.false_ne_true this
            rw [hfr.2 x ha, hs₁]
            rfl
    | endeBindAxiomOpt l Γ Λ e a args he hp hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwort] at this
          exact this.symm
        have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
        rw [← e] at hfr
        cases c with
        | inl t =>
            show σ₂.slots t = M.speicher.slots t
            have ha : D.aschreibt a t = false := by
              cases hat : D.aschreibt a t with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hd t hat _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hp.hw t hat
                    rw [hW] at this
                    exact Bool.false_ne_true this
            funext k fld
            rw [hfr.1 t ha k fld, hs₁]
            rfl
        | inr x =>
            show σ₂.globs x = M.speicher.globs x
            have ha : D.agschreibt a x = false := by
              cases hax' : D.agschreibt a x with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hgd x hax' _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hp.hg x hax'
                    rw [hW] at this
                    exact Bool.false_ne_true this
            rw [hfr.2 x ha, hs₁]
            rfl
    | _ =>
        subst_vars
        exact traegerGleich_refl _ c
  | g2 hs =>
    cases hs with
    | _ =>
        subst_vars
        exact traegerGleich_refl _ c
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t' inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
        rw [hs₁, leave_welt' _ _ _ _ _ _ _ _ hstep]
        exact traegerGleich_refl _ c
    | dannNextTrav l Γ Λ t' inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        exact traegerGleich_refl _ c
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        exact traegerGleich_refl _ c
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        exact traegerGleich_refl _ c
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        exact traegerGleich_refl _ c
    | dannAxiomCallElseOk l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwort] at this
          exact this.symm
        have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
        rw [← e] at hfr
        cases c with
        | inl t =>
            show σ₂.slots t = M.speicher.slots t
            have ha : D.aschreibt a t = false := by
              cases hat : D.aschreibt a t with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hd t hat _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hp.hw t hat
                    rw [hW] at this
                    exact Bool.false_ne_true this
            funext k fld
            rw [hfr.1 t ha k fld, hs₁]
            rfl
        | inr x =>
            show σ₂.globs x = M.speicher.globs x
            have ha : D.agschreibt a x = false := by
              cases hax' : D.agschreibt a x with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hgd x hax' _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hp.hg x hax'
                    rw [hW] at this
                    exact Bool.false_ne_true this
            rw [hfr.2 x ha, hs₁]
            rfl
    | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwort] at this
          exact this.symm
        have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
        rw [← e] at hfr
        cases c with
        | inl t =>
            show σ₂.slots t = M.speicher.slots t
            have ha : D.aschreibt a t = false := by
              cases hat : D.aschreibt a t with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hd t hat _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hp.hw t hat
                    rw [hW] at this
                    exact Bool.false_ne_true this
            funext k fld
            rw [hfr.1 t ha k fld, hs₁]
            rfl
        | inr x =>
            show σ₂.globs x = M.speicher.globs x
            have ha : D.agschreibt a x = false := by
              cases hax' : D.agschreibt a x with
              | false => rfl
              | true =>
                  exfalso
                  rcases hc with ⟨L, hB, hfrei⟩ | hW
                  · have hmem : Res.held L ∈ Λ := by
                      have := hgd x hax' _ hB
                      simpa [Res.von] using this
                    exact hfrei (hΛ L hmem)
                  · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hp.hg x hax'
                    rw [hW] at this
                    exact Bool.false_ne_true this
            rw [hfr.2 x ha, hs₁]
            rfl
    | _ =>
        subst_vars
        exact traegerGleich_refl _ c
  | g4 hs =>
    cases hs with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        exact traegerGleich_refl _ c
    | _ =>
        subst_vars
        exact traegerGleich_refl _ c
  | g5 hs =>
    exact schritt_traeger_g5 hO hs c hc
  | g6 hs =>
    exact schritt_traeger_g6 hO hs c hc
  | g7 hs =>
    cases hs <;> exact traegerGleich_refl _ c

/-- **The rely on reachable machines.** If thread `t` holds a lock `L`
    guarding `c`, a step of any other thread leaves `c` alone. -/
theorem relyG (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (hut : u ≠ t)
    (c : D.Tab ⊕ D.Glob) (L : D.Lock) (hB : Bewacht c L) (hL : L ∈ offen (M.faeden t).spur) :
    TraegerGleich M'.speicher M.speicher c :=
  schritt_traeger hO hs c (Or.inl ⟨L, hB, exklusivG hO sp init hex hr t u (fun e => hut e.symm) L hL⟩)

/-- The table form of the rely (the shape of the earlier `relyG_tab`). -/
theorem relyG_tab (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) {g : Faden}
    (hs : RufSchrittG P O passes M g M') (f : Faden) (hgf : g ≠ f)
    (t : D.Tab) (L : D.Lock) (hB : Sum.inl L ∈ D.braucht t)
    (hL : L ∈ offen (M.faeden f).spur) :
    ∀ (k : Int) (fld : D.Feld t), M'.speicher.slots t k fld = M.speicher.slots t k fld := by
  have h := relyG hO sp init hex hr hs f hgf (.inl t) L hB hL
  intro k fld
  exact congrFun (congrFun h k) fld

end Sperren

end Gabbro.Grammatik
