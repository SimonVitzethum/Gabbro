/- Part 2 of 3 of `ZielOrt` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrt.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Sperren

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A leaf keeps the held locks (`stmt_gut`, `Brav` leg). -/
theorem blatt_offen (hO : GutO O) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true) (σ : World D)
    (ρ : Env D Γ) (hΛ : HeldIn Λ (offen σ.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes keinRuf s σ ρ = Ausgang.ok σ' ρ') :
    offen σ'.spur = offen σ.spur := by
  have hw : (execStmt O passes keinRuf s σ ρ).welt = some σ' := by rw [hst]; rfl
  exact ((Stmt.gut_blatt O passes keinRuf hO s hleaf σ ρ hΛ) σ' hw).2.1

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
    (∃ L, Res.held L ∈ (M.faeden f).kopf.rest.2.2.1 ∧
      offen (M'.faeden f).spur = (offen (M.faeden f).spur).erase L) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep)
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep)
  | dannLocks l Γ Λ Λ'' L _ _ _ _ _ _ _ _ hfrei =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inl ⟨L, hfrei, rfl⟩)
  | freiGib l Γ Λ L k ρ hhead =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
      rw [hhead]
      exact List.mem_cons_self
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
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [hs₂, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ r hax =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
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
      first
        | exact Or.inl trivial
        | exact Or.inl rfl
        | exact Or.inl (lese_offen _ _ _)

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

/-- **The rely, one step.** A step of thread `u` leaves a carrier `c` alone
    if (a) some lock guarding `c` is not held by `u`, or (b) the signature of
    `u`'s head function does not permit writing `c`. Every writing step
    carries its carrier's guards in the static holdings (`darf`/`gdarf` on
    the write, on `exchange`, on the axiom's declared writes) and the
    signature permission (`hw`), and every writing step now demands
    `HeldGenau`, so (a) contradicts a write; the frame of `stmt_gut` and
    of the oracle (`GutO`) gives (b). -/
theorem schritt_traeger (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') (c : D.Tab ⊕ D.Glob)
    (hc : (∃ L, Bewacht c L ∧ L ∉ offen (M.faeden u).spur) ∨
      TraegerSchreibt (M.faeden u).kopf.f c = false) :
    TraegerGleich M'.speicher M.speicher c := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon u) ρ).welt = some σ' := by
        show (execStmt O passes keinRuf s (M.weltVon u) ρ).welt = some σ'
        rw [hstep]; rfl
      have hR := ((Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon u) ρ hΛ) σ'
        (by rw [hstep]; rfl)).1
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
      have hR := ((Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon u) ρ hΛ) σ'
        (by rw [hstep]; rfl)).1
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
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      rw [hs₂, hs₁]
      cases c with
      | inl t => rfl
      | inr x =>
          show (World.storeGlob _ g _).globs x = M.speicher.globs x
          by_cases hgx : x = g
          · subst hgx
            exfalso
            rcases hc with ⟨L, hB, hfrei⟩ | hW
            · have hmem : Res.held L ∈ Λ := by
                have := hL _ hB
                simpa [Res.von] using this
              exact hfrei (hΛ L hmem)
            · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hw
              rw [hW] at this
              exact Bool.false_ne_true this
          · simp only [World.storeGlob, dif_neg hgx]
            rfl
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
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
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
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
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
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
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
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
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
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
  | _ =>
      subst_vars
      exact traegerGleich_refl _ c

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
