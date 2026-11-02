module
public import Grammatik.Kern.Semantik.MaschinenKette.T4
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}
/-- **The witnessed chain from the whole run: identification with real table
    witnesses, no `hlock`, no vacuous discharge.** Over a single-thread
    `PCReach` run with frame-covered leaves, some chain tracks the machine end
    to end: worlds and run by construction (`rfl` at every level, never
    assumed), the UNCONDITIONAL table link for the covered carrier `t₀` plus
    the guard. The `PCReach` derivation routes three ways at once -- each
    `blatt` step closes through the Ziel section-10 witnessed step
    (`hWitSchritt`, the exact `kette_mit_zeugen_schritt` shape: the old-run link
    arrives as the prefix invariant, the new step closes by the firing witness
    `hwit_leaf`), each lock step closes through `kette_bezeugt_schritt_sperre`
    with its frame by `rfl` and its witness from the prefix (`hwit_lock`), and
    counter routing rules out foreign steps (`hsingle_prog`), while
    `pcReach_gen` projects every prefix to `GenErreichbar` for the step.
    Every premise is load-bearing: `hGuardT` / `hCov` feed the seed and the
    leaf step, `hRahmen` feeds the leaf wiring, `hwit_leaf` / `hwit_lock` feed
    the witness legs, `hWitSchritt` closes every leaf, `hsingle_prog` feeds the
    foreign-step discharge, the rest feed the seed, the projections, or the
    conclusion. -/
theorem kette_aus_lauf_bezeugt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (prog : PCProg D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (f : Faden) (code : Faden → D.Fn)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : TraegerSchreibt (code f) (.inl t₀) = true → ∃ i : D.Inv, Sum.inl t₀ ∈ D.traeger i)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hsingle_run : ∀ s ∈ M.lauf, s.faden = f)
    (hRahmen : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true →
      (∀ t, V.schreibt t = true → D.schreibt (code f) t = true) ∧
      (∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true))
    (hEintritt : EintrittPasst (code f) (GenStart sp).start)
    (hSchuld : SchuldnerHaelt (code f))
    (hInvSicht : InvSichtHaelt (code f) (GenStart sp).start)
    -- Witness duties stay posited (scheduler/witness duty, exactly as section 10
    -- books `hneu_wit` / `hwit_old`): per firing (`hwit_leaf`) and per prefix
    -- (`hwit_lock`). Proof-binders inside the two ∀-hypotheses below carry a
    -- `_` prefix: they are leaves of the dependency chain (nothing later refers
    -- to a proof), so the unused-binder linter would flag them; the proposition
    -- is unchanged and application stays positional.
    (hwit_leaf : ∀ (Mx : GenMaschine D) (V : Vertrag D) (l : Bool) (Γ : Ctx)
      (Λ Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (_hΛ : HeldGenau Λ (offen (Mx.spuren f))) (σ' : World D) (neu : List (Ereignis D))
      (_hstep : (execStmt O passes keinRuf s (Mx.weltVon f) ρ).welt = some σ'),
      TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu)
    (hwit_lock : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        Mx.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)))
    (hWitSchritt : ∀ (M M' : GenMaschine D)
      (_hReach : GenErreichbar P O passes (GenStart sp) M)
      (_hReach' : GenErreichbar P O passes (GenStart sp) M')
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (_hΛ : HeldGenau Λ (offen (M.spuren f)))
      (σ' : World D) (neu : List (Ereignis D))
      (_hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
      (_hM'l : M'.lauf = M.lauf ++ genEigen f neu)
      (_hM'w : M'.welten = M.welten ++ [σ'])
      (J : GemeinsamerLauf (D := D) Nb)
      (_hJw : J.welten = M.welten)
      (_hmem : f ∈ J.faeden)
      (_hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
      (_hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
      (_hsingle : ∀ st ∈ M.lauf, st.faden = f)
      (_hGuardT : Sum.inl L ∈ D.braucht t₀)
      (_hCov : ∀ (g : Faden), g ∈ J.faeden →
        TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, Sum.inl t₀ ∈ D.traeger i)
      (_hwit_old : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
        TraegerSchreibt (J.code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
      (_hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
        ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
          Ereignis.zugriff t₀ w Λw hwL ∈ neu),
      ∃ J' : GemeinsamerLauf (D := D) Nb,
        J'.welten = M'.welten ∧
        J'.l = M'.lauf ∧
        f ∈ J'.faeden ∧
        J'.faeden = J.faeden ∧
        J'.code = J.code ∧
        SerialLink Nb J' M'.lauf t₀ ∧
        (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
          L ∈ D.haelt (J'.code g))) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = M.welten ∧
      J.l = M.lauf ∧
      f ∈ J.faeden ∧
      SerialLink Nb J M.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J.faeden → TraegerSchreibt (J.code g) (.inl t₀) = true →
        L ∈ D.haelt (J.code g)) := by
  have key : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      (∀ s ∈ Mx.lauf, s.faden = f) →
      ∃ J : GemeinsamerLauf (D := D) Nb,
        J.welten = Mx.welten ∧
        J.l = Mx.lauf ∧
        f ∈ J.faeden ∧
        J.faeden = [f] ∧
        J.code = code ∧
        SerialLink Nb J Mx.lauf t₀ ∧
        (∀ (g : Faden), g ∈ J.faeden →
          TraegerSchreibt (J.code g) (.inl t₀) = true → L ∈ D.haelt (J.code g)) := by
    intro Mx pcx hx
    induction hx with
    | start =>
      intro _
      obtain ⟨J, hJw, hJl, hmem, hJf, hJcode, hLink, hGuard⟩ :=
        kette_bezeugt_start Nb sp f code t₀ L hGuardT hCov hEintritt hSchuld hInvSicht
      exact ⟨J, hJw, hJl, hmem, hJf, hJcode, hLink, hGuard⟩
    | step Mmid Mend pcmid pcend g hmid hs ih =>
      intro hsrun
      have hReachEnd : GenErreichbar P O passes (GenStart sp) Mend :=
        pcReach_gen P O passes prog (GenStart sp) Mend pcend
          (PCReach.step Mmid Mend pcmid pcend g hmid hs)
      rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
        ⟨L', hself, hrang, hfrei, hpc⟩ | ⟨L', hhaelt, hpc⟩
      · have hact : f = g := by
          by_cases hgf : g = f
          · exact hgf.symm
          · have hempty : prog g = [] := hsingle_prog g hgf
            rw [hempty] at hpc
            simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hpc
        subst hact
        have hmid_single : ∀ s ∈ Mmid.lauf, s.faden = f := by
          intro s hs'
          exact hsrun s (List.mem_append.mpr (Or.inl hs'))
        have hReachMid : GenErreichbar P O passes (GenStart sp) Mmid :=
          pcReach_gen P O passes prog (GenStart sp) Mmid pcmid hmid
        obtain ⟨J, hJw, hJl, hmemJ, hJfJ, hJcodeJ, hLinkJ, hGuardJ⟩ := ih hmid_single
        obtain ⟨hWt, hGt⟩ := hRahmen V l Γ Λ Λ' s hleaf
        have hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true := by
          intro t ht
          rw [hJcodeJ]
          exact hWt t ht
        have hG : ∀ g0, V.gschreibt g0 = true → D.gschreibt (J.code f) g0 = true := by
          intro g0 hg0
          rw [hJcodeJ]
          exact hGt g0 hg0
        have hCovJ : ∀ (g : Faden), g ∈ J.faeden →
            TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, Sum.inl t₀ ∈ D.traeger i := by
          intro g hg hw
          have hmem' : g ∈ ([f] : List Faden) := by
            rw [← hJfJ]
            exact hg
          have hgf : g = f := by simpa using hmem'
          rw [hgf] at hw
          have hw' : TraegerSchreibt (code f) (.inl t₀) = true := by
            rw [hJcodeJ] at hw
            exact hw
          exact hCov hw'
        have hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
            ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
              Ereignis.zugriff t₀ w Λw hwL ∈ neu := by
          intro hw
          have hw' : TraegerSchreibt (code f) (.inl t₀) = true := by
            rw [hJcodeJ] at hw
            exact hw
          exact hwit_leaf Mmid V l Γ Λ Λ' s ρ hΛ σ' neu hstep hw'
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hJ'f, hJ'code, hLink', hGuard'⟩ :=
          hWitSchritt Mmid _ hReachMid hReachEnd V l Γ Λ Λ' s ρ hΛ σ' neu hstep
            rfl rfl J hJw hmemJ hW hG hmid_single hGuardT hCovJ hLinkJ hneu_wit
        refine ⟨J', hJ'w, hJ'l, hmemJ', ?_, ?_, hLink', hGuard'⟩
        · exact hJ'f.trans hJfJ
        · exact hJ'code.trans hJcodeJ
      · have hact : f = g := by
          by_cases hgf : g = f
          · exact hgf.symm
          · have hempty : prog g = [] := hsingle_prog g hgf
            rw [hempty] at hpc
            simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hpc
        subst hact
        have hmid_single : ∀ s ∈ Mmid.lauf, s.faden = f := by
          intro s hs'
          exact hsrun s (List.mem_append.mpr (Or.inl hs'))
        have hReachMid : GenErreichbar P O passes (GenStart sp) Mmid :=
          pcReach_gen P O passes prog (GenStart sp) Mmid pcmid hmid
        obtain ⟨J, hJw, hJl, hmemJ, hJfJ, hJcodeJ, hLinkJ, hGuardJ⟩ := ih hmid_single
        have hFrameLock : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (Mmid.weltVon f)
            (Mmid.speicher.welt (Ereignis.nimmt L' (offen (Mmid.spuren f)) :: Mmid.spuren f)) :=
          ⟨fun t _ k fld => rfl, fun g _ => rfl⟩
        have hwit_new : TraegerSchreibt (J.code f) (.inl t₀) = true →
            ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
              Mmid.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
          intro hw
          have hw' : TraegerSchreibt (code f) (.inl t₀) = true := by
            rw [hJcodeJ] at hw
            exact hw
          exact hwit_lock Mmid pcmid hmid hw'
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hJ'f, hJ'code, hLink', hGuard'⟩ :=
          kette_bezeugt_schritt_sperre P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            [Ereignis.nimmt L' (offen (Mmid.spuren f))]
            (Mmid.speicher.welt (Ereignis.nimmt L' (offen (Mmid.spuren f)) :: Mmid.spuren f))
            rfl rfl
            J hJw hmemJ hFrameLock t₀ L hLinkJ hGuardJ hwit_new hmid_single
        refine ⟨J', hJ'w, hJ'l, hmemJ', ?_, ?_, hLink', hGuard'⟩
        · exact hJ'f.trans hJfJ
        · exact hJ'code.trans hJcodeJ
      · have hact : f = g := by
          by_cases hgf : g = f
          · exact hgf.symm
          · have hempty : prog g = [] := hsingle_prog g hgf
            rw [hempty] at hpc
            simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hpc
        subst hact
        have hmid_single : ∀ s ∈ Mmid.lauf, s.faden = f := by
          intro s hs'
          exact hsrun s (List.mem_append.mpr (Or.inl hs'))
        have hReachMid : GenErreichbar P O passes (GenStart sp) Mmid :=
          pcReach_gen P O passes prog (GenStart sp) Mmid pcmid hmid
        obtain ⟨J, hJw, hJl, hmemJ, hJfJ, hJcodeJ, hLinkJ, hGuardJ⟩ := ih hmid_single
        have hFrameLock : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (Mmid.weltVon f)
            (Mmid.speicher.welt (Ereignis.gibt L' :: Mmid.spuren f)) :=
          ⟨fun t _ k fld => rfl, fun g _ => rfl⟩
        have hwit_new : TraegerSchreibt (J.code f) (.inl t₀) = true →
            ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
              Mmid.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
          intro hw
          have hw' : TraegerSchreibt (code f) (.inl t₀) = true := by
            rw [hJcodeJ] at hw
            exact hw
          exact hwit_lock Mmid pcmid hmid hw'
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hJ'f, hJ'code, hLink', hGuard'⟩ :=
          kette_bezeugt_schritt_sperre P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            [Ereignis.gibt L']
            (Mmid.speicher.welt (Ereignis.gibt L' :: Mmid.spuren f))
            rfl rfl
            J hJw hmemJ hFrameLock t₀ L hLinkJ hGuardJ hwit_new hmid_single
        refine ⟨J', hJ'w, hJ'l, hmemJ', ?_, ?_, hLink', hGuard'⟩
        · exact hJ'f.trans hJfJ
        · exact hJ'code.trans hJcodeJ
  obtain ⟨J, hJw, hJl, hmem, _, _, hLink, hGuard⟩ := key M pc h hsingle_run
  exact ⟨J, hJw, hJl, hmem, hLink, hGuard⟩

#print axioms Gabbro.Grammatik.kette_bezeugt_start
#print axioms Gabbro.Grammatik.kette_bezeugt_schritt_sperre
#print axioms Gabbro.Grammatik.kette_aus_lauf_bezeugt

end Gabbro.Grammatik

/-! ## Seed joint run J0: the hwit fold base, constructed.

    The `hwit_alt_faltung` fold (`Extraktion.lean`, read-only here) takes its
    base from a posited empty joint run `J₀` (`hempty : J₀.schrittFaden = []`,
    `hcode : J₀.code = code`): at `start` the scheduler owes no thread steps,
    so `hwit_leer` discharges the prefix witness duty vacuously. This section
    constructs that seed instead of positing it: `samen_J0` over `GenStart sp`
    with empty thread and step lists, worlds and run by construction, so both
    `hempty` and `hcode` hold by `rfl`, and `samen_J0_hwit_base` is the
    `hwit_leer` duty already instantiated at the seed (the fold base is the
    instance at `run := (GenStart sp).lauf`; the glue instantiates `fn0` and
    rewrites with `samen_J0_code`).

    Read-only reuse, nothing existing moves: `GenStart` (`Maschine.lean`) and
    the empty-run shapes (`Gesittet` / `BeschraenkteVerschraenkung` over `[]`,
    vacuous `hSchritt` / `hPaar` / entry legs) of `kette_aus_maschinenlauf`
    (`Maschine.lean` §14).

    Construction choice, named exactly (not a narrowing of the duty): the seed
    carries a constant code function (`fun _ => fn0`). With empty thread and
    step lists no code value is ever read by the base duty, so any `fn0` the
    glue supplies fits; `hcode` pins it by `rfl`.

    Remainder (booked, not hidden): instantiating the fold (`hwit_alt_faltung`
    at `J₀ := samen_J0`) and the glue live with the read-only consumers
    elsewhere; this section only provides the seed and its properties. -/

namespace Gabbro.Grammatik

variable {D : Deklaration}


end Gabbro.Grammatik
