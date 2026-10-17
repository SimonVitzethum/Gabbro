/- Part 4 of 5 of `MaschinenKette` (split by instrumente/teile/lean-teilen.py; the umbrella `MaschinenKette.lean` imports all parts). -/
import Grammatik.Kern.Semantik.MaschinenKette.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **Witnessed lock step: the chain extends along a memory-framed step and the
    table link stays unconditional.** Same construction as
    `kette_aus_lauf_schritt_rahmen` (same read-only projection theorems, same
    single-thread arithmetic, same new-step frame transfer of `hFrame`); DELTA:
    no non-writer premise anywhere -- old steps inherit from the unconditional
    prefix link `hLinkOld`, the new step reuses the prefix witness `hwit_new`
    (lock events never carry one), the guard rides along from `hGuardOld`
    (same members, same code). Every premise is load-bearing. -/
theorem kette_bezeugt_schritt_sperre
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (neu : List (Ereignis D)) (nach : World D)
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [nach])
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hFrame : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (M.weltVon f) nach)
    (t₀ : D.Tab) (L : D.Lock)
    (hLinkOld : SerialLink Nb J M.lauf t₀)
    (hGuardOld : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → L ∈ D.haelt (J.code g))
    (hwit_new : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)))
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      J'.faeden = J.faeden ∧
      J'.code = J.code ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) := by
  have hlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hReach
  have hLastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  have hfaden : ∀ (i : Nat) (g : Faden) (ei : Ereignis D),
      M'.lauf[i]? = some (Schritt.mk g ei) → g = f := by
    intro i g ei hi
    rw [hM'l] at hi
    by_cases hlt : i < M.lauf.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hsingle _ (List.mem_of_getElem? hi)
    · have hle : M.lauf.length ≤ i := by omega
      rw [List.getElem?_append_right hle] at hi
      exact (gen_eigen_getElem f neu _ _ _ hi).1
  have hGes' : Gesittet M'.lauf := by
    refine ⟨gen_konsistent P O passes hO sp M' hReach',
            gen_gut_obs P O passes hO sp M' hReach',
            gen_ausschluss P O passes hO sp M' hReach', ?_, ?_⟩
    · intro i j g1 g2 m s s' e1 e2 hi hj _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
    · intro i j g1 g2 o e1 e2 hi hj _ _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
  have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
    intro i j g1 g2 e1 e2 hi hj hne
    have h1 := hfaden i g1 e1 hi
    have h2 := hfaden j g2 e2 hj
    exact absurd (h1.trans h2.symm) hne
  have hKette' : M'.welten.length = (J.schrittFaden ++ [f]).length + 1 := by
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp
    omega
  have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach0 : World D),
      (J.schrittFaden ++ [f])[k]? = some g0 → M'.welten[k]? = some vor →
      M'.welten[k + 1]? = some nach0 →
      g0 ∈ J.faeden ∧
        Rahmen (D.schreibt (J.code g0)) (D.gschreibt (J.code g0)) vor nach0 := by
    intro k g0 vor nach0 hk hkv hkn
    rw [hM'w] at hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
        List.getElem?_append_left hlt
      rw [e1] at hk
      have hltM : k < M.welten.length := by omega
      have e2 : (M.welten ++ [nach])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [nach])[k + 1]? = M.welten[k + 1]? :=
        List.getElem?_append_left hltM1
      rw [e3] at hkn
      have hJkn : J.welten[k + 1]? = some nach0 := by rw [hJw]; exact hkn
      exact J.hSchritt k g0 vor nach0 hk hJkv hJkn
    · by_cases heq : k = J.schrittFaden.length
      · subst heq
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk
        have hg0 : g0 = f := (Option.some_inj.mp hk).symm
        have eW : (M.welten ++ [nach])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [nach])[J.schrittFaden.length + 1]? = some nach := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : nach = nach0 := Option.some_inj.mp hkn
        -- The new-step frame transfers `hFrame` across definitionally equal
        -- memories (successor worlds share memory by construction).
        rw [hg0, hvor, ← hnach0]
        refine ⟨hmem, ?_, ?_⟩
        · intro t ht k2 fld
          exact hFrame.1 t ht k2 fld
        · intro g hg
          exact hFrame.2 g hg
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  -- DELTA: the extended chain keeps member, members, and code by construction;
  -- the link below is unconditional for `t₀` (old steps via `hLinkOld`, the new
  -- step via the prefix witness) and the guard rides along from `hGuardOld`.
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, hmem, rfl, rfl, ?_, ?_⟩
  · intro k0 g0 hk0 hwr
    have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
    have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
    by_cases hlt : k0 < J.schrittFaden.length
    · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
        List.getElem?_append_left hlt
      rw [eOld] at hk0'
      -- DELTA: old steps inherit from the unconditional prefix link.
      obtain ⟨j, w, Λe, he, hw⟩ := hLinkOld k0 g0 hk0' hwr0
      have hjlt : j < M.lauf.length := by
        by_cases h : j < M.lauf.length
        · exact h
        · have hle : M.lauf.length ≤ j := by omega
          rw [List.getElem?_eq_none hle] at hw
          simp at hw
      have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λe he)) := by
        rw [hM'l, List.getElem?_append_left hjlt]
        exact hw
      exact ⟨j, w, Λe, he, hw'⟩
    · by_cases heq : k0 = J.schrittFaden.length
      · subst heq
        have hg0 : g0 = f := by
          have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          rw [eNew] at hk0'
          exact (Option.some_inj.mp hk0').symm
        -- DELTA: the new lock step owns no fresh event, so it reuses the prefix
        -- witness, transported into the extended run -- no guard to hide under.
        rw [hg0] at hk0' hwr ⊢
        obtain ⟨j, w, Λe, he, hj⟩ := hwit_new hwr
        have hjlt : j < M.lauf.length := by
          by_cases h : j < M.lauf.length
          · exact h
          · have hle : M.lauf.length ≤ j := by omega
            rw [List.getElem?_eq_none hle] at hj
            simp at hj
        have hj' : M'.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
          rw [hM'l, List.getElem?_append_left hjlt]
          exact hj
        exact ⟨j, w, Λe, he, hj'⟩
      · have hle : J.schrittFaden.length ≤ k0 := by omega
        have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk0'
        simp at hk0'
  · intro g hg hw
    exact hGuardOld g hg hw

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
    (hCov : TraegerSchreibt (code f) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
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
        TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
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
            simp at hpc
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
            TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i := by
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
            simp at hpc
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
            simp at hpc
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
