module

public import Grammatik.Kern.Syntax.Satz.T3
public import Grammatik.Kern.Syntax.Satz.T4.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Rumpf
variable (O : Orakel D)
variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : GutR R) (hO : GutO O)
include hR hO
set_option linter.unusedSectionVars false

/-! The exact-held-set forms (no extra lock, `HeldGenau`), with their old names. -/

theorem stmt_gut (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt)
    (hscope : s.ScopesOk) (hresid : ResidHeld V Λ) :
    GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ) :=
  stmt_gutB O passes R hR hO none (bodenUnter_none _) s σ ρ (fun _ h => nomatch h) hscope hresid
    (heldB_of_genau none hh)

theorem block_gut (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt)
    (hscope : b.ScopesOk) (hresid : ResidHeld V Λ) :
    GutAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ) :=
  block_gutB O passes R hR hO none (bodenUnter_none _) b σ ρ (fun _ h => nomatch h) hscope hresid
    (heldB_of_genau none hh)

theorem end_gut (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt)
    (hscope : b.ScopesOk) (hresid : ResidHeld V Λ) :
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ) :=
  end_gutB O passes R hR hO none (bodenUnter_none _) b σ ρ (fun _ h => nomatch h) hscope hresid
    (heldB_of_genau none hh)

end Rumpf
/-! ### Der Ruf, bis hinauf zum Programm -/

theorem held_invSicht_aux (L : D.Lock) : ∀ (ts : List (D.Tab ⊕ D.Glob)),
    Res.held L ∈ ts.foldr (fun c acc => (Sum.elim D.braucht D.gbraucht c).map (Res.von D) ++ acc) [] →
    ∃ c ∈ ts, Sum.inl L ∈ Sum.elim D.braucht D.gbraucht c := by
  intro ts
  induction ts with
  | nil => intro h; simp only [List.foldr_nil, List.not_mem_nil] at h
  | cons c ts ih =>
      intro h
      simp only [List.foldr_cons, List.mem_append, List.mem_map] at h
      rcases h with ⟨w, hw, hwL⟩ | h
      · refine ⟨c, List.mem_cons_self, ?_⟩
        cases w with
        | inl M => simp only [Res.von, Res.held.injEq] at hwL; subst hwL; exact hw
        | inr m => obtain ⟨_, _⟩ := m; simp only [Res.von, reduceCtorEq] at hwL
      · obtain ⟨c', hc', hL⟩ := ih h
        exact ⟨c', List.mem_cons_of_mem _ hc', hL⟩

theorem held_invSicht (i : D.Inv) (L : D.Lock) (h : Res.held L ∈ invSicht D i) :
    ∃ c ∈ D.traeger i, Sum.inl L ∈ Sum.elim D.braucht D.gbraucht c :=
  held_invSicht_aux L _ h

/-- Die Invarianten, die ein Rumpf schuldet, liest er unter Sperren, die er haelt (`U003`). -/
theorem heldIn_invarianten (P : Programm D) (f : D.Fn) {h : List D.Lock}
    (hh : HeldIn (Signatur.anfang D (D.signatur f)) h) (i : D.Inv) (hi : schuldet f i = true) :
    HeldIn (invSicht D i) h := by
  intro L hL
  obtain ⟨c, hc, hLc⟩ := held_invSicht i L hL
  have := D.invarianten_gehalten (D.sig f) i hi c hc L hLc
  exact hh L ((held_anfang _ L).mpr this)

theorem gut_foldl_lese {W G} (P : Programm D) (f : D.Fn) :
    ∀ (is : List D.Inv) (σ : World D), (∀ i ∈ is, schuldet f i = true) →
      HeldIn (Signatur.anfang D (D.signatur f)) σ.haelt →
      Gut W G σ (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ) := by
  intro is
  induction is with
  | nil => intro σ _ _; exact Gut.refl _ _ _
  | cons i is ih =>
      intro σ hs hh
      simp only [List.foldl_cons]
      have g1 : Gut W G σ (σ.lese (invSicht D i) (P.invariante i).orte) :=
        gut_lese σ _ _ (P.invariante i).orte_darf
          (heldIn_invarianten P f hh i (hs i List.mem_cons_self))
      exact g1.trans (ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj)) (g1.heldIn hh))

/-- **Rahmen und Spur eines Rufs, bis hinauf zum Programm**: auf jeder Rekursionstiefe haelt
    `rufAt` Rahmen und Spur des Gerufenen -- Induktion ueber die Tiefe, mit `end_gut` fuer
    den Rumpf. Premises are the hardware (H1) -- and, since the held-set
    relaxation (2026-09-13), that every body respects its function's lock
    floor (`StufenOk`, trivial without floors: `stufenOk_ohne`), and, since
    the scoped-return release (C11), that every scoped return spares the
    residual and respects the floor (`ScopesOkProg`). -/
theorem rufAt_gut (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O) (hP : StufenOk P)
    (hS : ScopesOkProg P) :
    ∀ fuel, GutR (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ _ σ' h; simp only [RufAusgang.welt, rufAt, reduceCtorEq] at h
  | succ n ih =>
      intro f σ ρ hh σ' h
      simp only [rufAt] at h
      have g0 : Gut (D.schreibt f) (D.gschreibt f) σ _ :=
        gut_lese σ _ _ (P.requires f).orte_darf hh.heldIn
      split at h
      · simp only [RufAusgang.welt, reduceCtorEq] at h
      · have hb := end_gutB O passes (rufAt P O passes n) ih hO (D.signatur f).boden
          (bodenUnter_refl _) (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (hP f) (by exact hS f)
          (residHeld_anfang (D.signatur f)) (g0.heldB hh)
        split at h
        · rename_i σ2 v hs
          have hbb := hb σ2 (by rw [hs]; rfl); rw [hs] at hbb
          have g2 : Gut (D.schreibt f) (D.gschreibt f) _ σ2 := hbb.toGut_entry (g0.heldB hh)
          have hh2 : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ2.haelt :=
            g2.heldB (g0.heldB hh)
          have g3 : Gut (D.schreibt f) (D.gschreibt f) σ2 _ :=
            gut_lese σ2 (vertragVon D f).ende _ (P.ensures f).orte_darf
              (by intro L hL; exact hh2.heldIn L ((held_anfang _ L).mpr ((held_ende _ L).mp hL)))
          split at h
          · simp only [RufAusgang.welt, reduceCtorEq] at h
          · have g4 := gut_foldl_lese (W := D.schreibt f) (G := D.gschreibt f) P f
              (D.invs.filter (schuldet f)) _
              (fun i hi => (List.mem_filter.mp hi).2) (g3.heldB hh2).heldIn
            split at h
            · simp only [RufAusgang.welt, reduceCtorEq] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
              exact ((g0.trans g2).trans g3).trans g4
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
          have hbb := hb _ (by rw [hs]; rfl); rw [hs] at hbb
          exact g0.transRetV hbb
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp only [RufAusgang.welt, reduceCtorEq] at h
        · simp only [RufAusgang.welt, reduceCtorEq] at h

/-- **Der Satz ueber Rahmen und Spur**: ein Rumpf unter Vertrag `V`, gestartet in einer Welt,
    die haelt, was sein `Λ` nennt, schreibt nur, was `V` nennt, gibt jede Sperre zurueck und
    tut keinen Zugriff ohne die Waechter seines Traegers -- fuer jedes Programm, jede Tiefe,
    jede Welt; die Hardware haelt ihr `effects` (H1). -/
theorem exec_gut (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O) (hP : StufenOk P)
    (hS : ScopesOkProg P)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt)
    (hscope : b.ScopesOk) (hresid : ResidHeld V Λ) :
    GutAusgang V.schreibt V.gschreibt σ (exec P O passes fuel V b σ ρ) :=
  block_gut O passes _ (rufAt_gut P O passes hO hP hS fuel) hO b σ ρ hh hscope hresid


end Gabbro.Grammatik
