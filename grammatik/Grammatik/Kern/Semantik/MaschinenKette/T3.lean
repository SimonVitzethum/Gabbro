/- Part 3 of 5 of `MaschinenKette` (split by instrumente/teile/lean-teilen.py; the umbrella `MaschinenKette.lean` imports all parts). -/
import Grammatik.Kern.Semantik.MaschinenKette.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **The chain from the whole run, framed leaves included: identification by
    construction, no `hlock`.** Over a single-thread `PCReach` run with
    frame-covered leaves and table-nonwriting code, some chain tracks the
    machine end to end: worlds and run by construction (`rfl` at every level,
    never assumed), `SerialLink` guarded-vacuous at each new step. The
    `PCReach` derivation routes three ways at once -- each `blatt` step wires
    its firing data through `blatt_rahmen_schritt` (read-only) under the
    contract-to-code covering (`hRahmen`), each lock step closes its frame by
    `rfl`, and counter routing rules out foreign steps (`hsingle_prog`), while
    `pcReach_gen` projects every prefix to `GenErreichbar` for the step.
    Every premise is load-bearing: `hRahmen` feeds the leaf wiring,
    `hsingle_prog` feeds the foreign-step discharge, the rest feed the seed,
    the projections, or the conclusion. -/
theorem kette_aus_lauf_gesamt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (prog : PCProg D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (f : Faden) (code : Faden → D.Fn)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hsingle_run : ∀ s ∈ M.lauf, s.faden = f)
    (hnw_code : ∀ t₀ : D.Tab, TraegerSchreibt (code f) (.inl t₀) = false)
    (hRahmen : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true →
      (∀ t, V.schreibt t = true → D.schreibt (code f) t = true) ∧
      (∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true))
    (hEintritt : EintrittPasst (code f) (GenStart sp).start)
    (hSchuld : SchuldnerHaelt (code f))
    (hInvSicht : InvSichtHaelt (code f) (GenStart sp).start) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = M.welten ∧
      J.l = M.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J M.lauf t₀) := by
  have key : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      (∀ s ∈ Mx.lauf, s.faden = f) →
      ∃ J : GemeinsamerLauf (D := D) Nb,
        J.welten = Mx.welten ∧
        J.l = Mx.lauf ∧
        f ∈ J.faeden ∧
        J.code = code ∧
        (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false) ∧
        (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
          SerialLink Nb J Mx.lauf t₀) := by
    intro Mx pcx hx
    induction hx with
    | start =>
      intro _
      obtain ⟨J, hJw, hJl, hmem, hJcodeJ, hnwJ, hLink⟩ :=
        kette_aus_lauf_start_code Nb sp f code hnw_code hEintritt hSchuld hInvSicht
      exact ⟨J, hJw, hJl, hmem, hJcodeJ, hnwJ, fun t₀ _ => hLink t₀⟩
    | step Mmid Mend pcmid pcend g hmid hs ih =>
      intro hsrun
      have hReachEnd : GenErreichbar P O passes (GenStart sp) Mend :=
        pcReach_gen P O passes prog (GenStart sp) Mend pcend
          (PCReach.step Mmid Mend pcmid pcend g hmid hs)
      rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
        ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
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
        obtain ⟨J, hJw, _, hmemJ, hJcodeJ, hnwJ, hLink⟩ := ih hmid_single
        obtain ⟨hWt, hGt⟩ := hRahmen V l Γ Λ Λ' s hleaf
        have hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true := by
          intro t ht
          rw [hJcodeJ]
          exact hWt t ht
        have hG : ∀ g0, V.gschreibt g0 = true → D.gschreibt (J.code f) g0 = true := by
          intro g0 hg0
          rw [hJcodeJ]
          exact hGt g0 hg0
        have hFrameBlatt : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (Mmid.weltVon f) σ' :=
          blatt_rahmen_schritt O passes hO Mmid f V l Γ Λ Λ' s ρ hΛ σ' hstep
            J.code hW hG
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hJcodeJ', hnwJ', hJ'link⟩ :=
          kette_aus_lauf_schritt_rahmen P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            neu σ'
            rfl rfl
            J code hJcodeJ hJw hmemJ hFrameBlatt hLink hnwJ hmid_single
        exact ⟨J', hJ'w, hJ'l, hmemJ', hJcodeJ', hnwJ', hJ'link⟩
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
        obtain ⟨J, hJw, _, hmemJ, hJcodeJ, hnwJ, hLink⟩ := ih hmid_single
        have hFrameLock : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (Mmid.weltVon f)
            (Mmid.speicher.welt (Ereignis.nimmt L (offen (Mmid.spuren f)) :: Mmid.spuren f)) :=
          ⟨fun t _ k fld => rfl, fun g _ => rfl⟩
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hJcodeJ', hnwJ', hJ'link⟩ :=
          kette_aus_lauf_schritt_rahmen P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            [Ereignis.nimmt L (offen (Mmid.spuren f))]
            (Mmid.speicher.welt (Ereignis.nimmt L (offen (Mmid.spuren f)) :: Mmid.spuren f))
            rfl rfl
            J code hJcodeJ hJw hmemJ hFrameLock hLink hnwJ hmid_single
        exact ⟨J', hJ'w, hJ'l, hmemJ', hJcodeJ', hnwJ', hJ'link⟩
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
        obtain ⟨J, hJw, _, hmemJ, hJcodeJ, hnwJ, hLink⟩ := ih hmid_single
        have hFrameLock : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (Mmid.weltVon f)
            (Mmid.speicher.welt (Ereignis.gibt L :: Mmid.spuren f)) :=
          ⟨fun t _ k fld => rfl, fun g _ => rfl⟩
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hJcodeJ', hnwJ', hJ'link⟩ :=
          kette_aus_lauf_schritt_rahmen P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            [Ereignis.gibt L]
            (Mmid.speicher.welt (Ereignis.gibt L :: Mmid.spuren f))
            rfl rfl
            J code hJcodeJ hJw hmemJ hFrameLock hLink hnwJ hmid_single
        exact ⟨J', hJ'w, hJ'l, hmemJ', hJcodeJ', hnwJ', hJ'link⟩
  obtain ⟨J, hJw, hJl, _, _, _, hJlink⟩ := key M pc h hsingle_run
  exact ⟨J, hJw, hJl, hJlink⟩

#print axioms Gabbro.Grammatik.kette_aus_lauf_start_code
#print axioms Gabbro.Grammatik.kette_aus_lauf_schritt_rahmen
#print axioms Gabbro.Grammatik.kette_aus_lauf_gesamt

end Gabbro.Grammatik

/-! ## Witnessed whole-run iteration: `kette_aus_lauf_bezeugt`

    Closer for the KRITISCH-ranked BEFUND (two checkers): the witnessed
    whole-run iteration is missing. `kette_aus_lauf_voll` / `kette_aus_lauf_gesamt`
    identify the chain over whole `PCReach` runs, but their `SerialLink` is
    guarded-vacuous -- each new step closes by contradiction from the non-writer
    premise, so no level ever exhibits a real witness event. The witnessed step
    (`kette_mit_zeugen_schritt`, `Ziel.lean` section 10) closes ONE framed leaf
    with real table witnesses, but is single-step. The two are unconnected:
    iterating the witnessed step over `PCReach` runs -- replacing `hlock` -- is
    what this section proves.

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `kette_bezeugt_start`: the seed chain with identity and a real guard. The
      `kette_aus_lauf_start_code` construction (same file, read-only) plus
      `J.faeden = [f]` / `J.schrittFaden = []` by construction, the
      UNCONDITIONAL table link (vacuous over the empty step list, never guarded),
      and the guard derived through `wache_aus_schuld` (read-only) from
      `J.hSchuld` plus coverage. No non-writer premise.
    - `kette_bezeugt_schritt_sperre`: the witnessed lock step. Same construction
      as `kette_aus_lauf_schritt_rahmen` (same file, read-only); DELTA: old steps
      inherit from the unconditional prefix link, the new step reuses the prefix
      witness (lock events never carry one), the guard rides along. No
      non-writer premise anywhere.
    - `kette_aus_lauf_bezeugt`: the witnessed chain from the whole run. The
      `kette_aus_lauf_gesamt` induction (same file, read-only: counter routing
      rules out foreign steps, `pcReach_gen` projects every prefix, `hRahmen`
      wires each fired leaf through `blatt_rahmen_schritt`) with leaves closed
      by the Ziel section-10 witnessed step and locks by the lemma above. The
      step enters as the explicit hypothesis `hWitSchritt` with the exact
      `kette_mit_zeugen_schritt` shape (plus two construction identities that
      hold by `rfl` at its literal): `Ziel` imports `MaschinenKette`, so
      importing the step here would cycle; its proof is never duplicated, and a
      `Ziel`-side glue step can discharge the hypothesis with the real theorem.
      Conclusion: chain identification (worlds and run by construction) with the
      UNCONDITIONAL table link plus the guard -- real witnesses along the run.

    Every premise is load-bearing (each feeds the seed, a projection, a frame,
    a witness transport, or the step hypothesis). Witness duties stay posited --
    per firing (`hwit_leaf`: the fired leaf records its access) and per prefix
    (`hwit_lock`: the prefix already records one) -- as scheduler/witness duty,
    exactly as section 10 books `hneu_wit` / `hwit_old`.

    Coverage (exactly): single-thread `PCReach` runs with frame-covered leaves
    over one shared TABLE carrier `t₀` under guard `L`.

    Remainder (booked, not hidden): discharging `hWitSchritt` with the real
    `kette_mit_zeugen_schritt` (`Ziel`-side glue, which can import both files);
    globals -- U003 is table-only, so `gzugriff` witnesses and the global guard
    stay owed; multi-carrier conflicts; multi-thread runs; the witness duties
    themselves (the run really recording the accesses).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Seed chain with identity and a real guard.** Same construction as
    `kette_aus_lauf_start_code` (same read-only premises, same `Gesittet` /
    frame / entry proofs); DELTA: the conclusion -- `J.faeden = [f]` by
    construction (`rfl` at the literal), the UNCONDITIONAL table link (vacuous
    over the empty step list, not guarded-vacuous), and the guard derived
    through `wache_aus_schuld` (read-only) from `J.hSchuld` plus coverage
    `hCov`. Every premise is load-bearing: `hGuardT` / `hCov` feed the guard,
    the rest feed the construction. -/
theorem kette_bezeugt_start (Nb : Nebeneinander) (sp : Speicher D)
    (f : Faden) (code : Faden → D.Fn)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : TraegerSchreibt (code f) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hEintritt : EintrittPasst (code f) (GenStart sp).start)
    (hSchuld : SchuldnerHaelt (code f))
    (hInvSicht : InvSichtHaelt (code f) (GenStart sp).start) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = (GenStart sp).welten ∧
      J.l = (GenStart sp).lauf ∧
      f ∈ J.faeden ∧
      J.faeden = [f] ∧
      J.code = code ∧
      SerialLink Nb J (GenStart sp).lauf t₀ ∧
      (∀ (g : Faden), g ∈ J.faeden → TraegerSchreibt (J.code g) (.inl t₀) = true →
        L ∈ D.haelt (J.code g)) := by
  have hGes : Gesittet ([] : Lauf D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f j
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
      rw [hsp]
      exact konsistent_nil
    · intro f j e he
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
      rw [hsp] at he
      simp at he
    · intro j f L h hi g hne
      simp at hi
    · intro i j f g m s s' ei ej hi hj hm hm'
      simp at hi
    · intro i j f g o ei ej hi hj ht1 ht2 hu
      simp at hi
  have hBeschr : BeschraenkteVerschraenkung (D := D) Nb ([] : Lauf D) := by
    intro i j f g ei ej hi hj hne
    simp at hi
  have hKette0 : (GenStart sp).welten.length = ([] : List Faden).length + 1 := by
    simp [GenStart]
  have hSchritt0 : ∀ (k : Nat) (f' : Faden) (vor nach : World D),
      ([] : List Faden)[k]? = some f' → (GenStart sp).welten[k]? = some vor →
      (GenStart sp).welten[k + 1]? = some nach →
      f' ∈ ([f] : List Faden) ∧
        Rahmen (D.schreibt (code f')) (D.gschreibt (code f')) vor nach := by
    intro k f' vor nach hk _ _
    simp at hk
  have hPaar0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) → ∀ (g : Faden),
      g ∈ ([f] : List Faden) → f' ≠ g → Nb f' g := by
    intro f' hf' g hg' hne
    simp at hf' hg'
    subst hf'
    subst hg'
    exact absurd rfl hne
  have hEintritt0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) →
      EintrittPasst (code f') ((fun _ => (GenStart sp).start) f') := by
    intro f' hf'
    simp at hf'
    subst hf'
    exact hEintritt
  have hSchuld0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) →
      SchuldnerHaelt (code f') := by
    intro f' hf'
    simp at hf'
    subst hf'
    exact hSchuld
  have hInvSicht0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) →
      InvSichtHaelt (code f') ((fun _ => (GenStart sp).start) f') := by
    intro f' hf'
    simp at hf'
    subst hf'
    exact hInvSicht
  have hmem0 : f ∈ ([f] : List Faden) := by simp
  -- DELTA: the identity conjunct (`rfl` at the literal), the unconditional link
  -- (vacuous over `[]`), and the derived guard -- no non-writer premise.
  refine ⟨{ faeden := [f], code := code, eintritt := fun _ => (GenStart sp).start,
            welten := (GenStart sp).welten, schrittFaden := [], l := ([] : Lauf D),
            hKette := hKette0, hSchritt := hSchritt0, hPaar := hPaar0,
            hGesittet := hGes, hBeschraenkt := hBeschr,
            hEintritt := hEintritt0, hSchuld := hSchuld0, hInvSicht := hInvSicht0 },
          rfl, rfl, hmem0, rfl, rfl, ?_, ?_⟩
  · intro k g hk _
    have hk' : ([] : List Faden)[k]? = some g := hk
    simp at hk'
  · intro g hg hw
    have hmem' : g ∈ ([f] : List Faden) := hg
    have hgf : g = f := by simpa using hmem'
    rw [hgf] at hw ⊢
    exact wache_aus_schuld _ _ t₀ L hGuardT _ (List.mem_singleton_self f) hw (hCov hw)


end Gabbro.Grammatik
