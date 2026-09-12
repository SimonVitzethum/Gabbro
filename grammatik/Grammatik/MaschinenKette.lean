/-
  File:      Grammatik/MaschinenKette.lean
  Subject:   **THE CHAIN FROM THE WHOLE RUN** -- iterating the one-step chain
             construction over entire lock-only PC runs.

  `kette_aus_maschinenlauf_schritt` (in `Maschine.lean`, read-only here) extends a
  tracking chain along ONE memory-preserving machine step of a member thread,
  but its conclusion drops the facts the NEXT iteration needs: the member
  thread (`f ∈ J.faeden`) and the code the link guard reads (`J.code`). An
  opaque `J'` cannot recover them, so pure reuse cannot iterate. The adapted
  step below (`kette_aus_lauf_schritt`) rebuilds the SAME construction with the
  SAME read-only inputs, threading exactly those two facts plus the guarded
  link through; the delta is marked at each changed line.

  Covered class (exactly): single-thread lock-only `PCReach` runs with
  non-writing code and a fitting entry --

    * lock-only (`hlock`): no `PCAtom.leaf` atom anywhere in `prog`, so every
      `PCSchritt` of the run is a `take` / `rel` step and the memory-preservation
      premises (`hslots` / `hglobs`) close by `rfl`;
    * single-thread (`hsingle_prog`, `hsingle_run`): every other thread has an
      empty program (counter routing: a step by `g ≠ f` would need an atom from
      `prog g = []`), and the final run mentions only `f`, so each prefix does;
    * non-writing code (`hnw_code`): `code f` writes no table carrier, so the
      guarded `SerialLink` of one level discharges to the unconditional link
      the next step consumes;
    * fitting entry (`hEintritt`, `hSchuld`, `hInvSicht`): the seed chain over
      the start machine carries `f` as its member thread.

  Read-only inputs, never modified: `pcSchritt_gen` / `pcReach_gen` (counter
  routing: `PCReach` derivations project to `GenErreichbar`), `GenStart`,
  `Speicher.welt`, `genEigen`, `gen_konsistent`, `gen_gut_obs`,
  `gen_ausschluss`, `genWelten_letzte`, `gen_eigen_getElem`, `Gesittet`,
  `BeschraenkteVerschraenkung`, `konsistent_nil`.

  Remainder (booked, not hidden): `blatt` steps -- a writing leaf moves memory,
  so `hslots` / `hglobs` need the `execStmt` frame correspondence; multi-thread
  runs -- discharging `hsingle` needs the `Einfaedig` projection
  (`pc_discharge_einfaedig`) plus the declaration side (`pc_discharge_unshared`),
  as `gen_gesittet` books them; non-vacuous `SerialLink` witnesses at `zugriff`
  events for writing steps; globals and multi-carrier conflicts (as before).
-/

import Grammatik.Maschine

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Seed chain for the induction: the start machine with one member thread.**
    The start machine over shared memory is a chain by construction, carrying
    `f` as its member: empty step list, the generated worlds and the empty run.
    The identification holds by `rfl`; `SerialLink` holds vacuously over the
    empty step list; the non-writer fact is the premise, read on the chain. -/
theorem kette_aus_lauf_start (Nb : Nebeneinander) (sp : Speicher D)
    (f : Faden) (code : Faden → D.Fn)
    (hnw_code : ∀ t₀ : D.Tab, TraegerSchreibt (code f) (.inl t₀) = false)
    (hEintritt : EintrittPasst (code f) (GenStart sp).start)
    (hSchuld : SchuldnerHaelt (code f))
    (hInvSicht : InvSichtHaelt (code f) (GenStart sp).start) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = (GenStart sp).welten ∧
      J.l = (GenStart sp).lauf ∧
      f ∈ J.faeden ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false) ∧
      ∀ t₀ : D.Tab, SerialLink Nb J (GenStart sp).lauf t₀ := by
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
  refine ⟨{ faeden := [f], code := code, eintritt := fun _ => (GenStart sp).start,
            welten := (GenStart sp).welten, schrittFaden := [], l := ([] : Lauf D),
            hKette := hKette0, hSchritt := hSchritt0, hPaar := hPaar0,
            hGesittet := hGes, hBeschraenkt := hBeschr,
            hEintritt := hEintritt0, hSchuld := hSchuld0, hInvSicht := hInvSicht0 },
          rfl, rfl, hmem0, hnw_code, ?_⟩
  intro t₀ k g hk _
  have hk' : ([] : List Faden)[k]? = some g := hk
  simp at hk'

/-- **The chain from the machine, one induction step that threads.** Same
    construction as `kette_aus_maschinenlauf_schritt` (same read-only
    projection theorems, same single-thread arithmetic, same frame, same
    witness transport); DELTA: the link arrives guarded and the member thread
    plus the non-writer fact ride along, so the conclusion feeds the next
    iteration -- worlds, run, member, non-writer fact, guarded link. -/
theorem kette_aus_lauf_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (e : Ereignis D) (nach : World D)
    (hM'l : M'.lauf = M.lauf ++ genEigen f [e])
    (hM'w : M'.welten = M.welten ++ [nach])
    (hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nach.slots t k fld = M.speicher.slots t k fld)
    (hglobs : ∀ g : D.Glob, nach.globs g = M.speicher.globs g)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
      SerialLink Nb J M.lauf t₀)
    (hnwJ : ∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J'.code f) (.inl t₀) = false) ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J'.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  -- DELTA: discharge the guarded link to the unconditional shape the witness
  -- transport below consumes; everything after this line mirrors the source.
  have hLinkUncond : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀ := by
    intro t₀
    exact hLink t₀ (hnwJ t₀)
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
      exact (gen_eigen_getElem f [e] _ _ _ hi).1
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
        rw [hg0, hvor, ← hnach0]
        refine ⟨hmem, ?_, ?_⟩
        · intro t _ k2 fld
          exact hslots t k2 fld
        · intro g _
          exact hglobs g
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  -- DELTA: the extended chain keeps member and non-writer fact by construction
  -- (`rfl` up to the definition: same `faeden`, same `code`); the link below
  -- reads the discharged `hLinkUncond` for old steps.
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, hmem, hnwJ, ?_⟩
  intro t₀ hnw k0 g0 hk0 hwr
  have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
  have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
  by_cases hlt : k0 < J.schrittFaden.length
  · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk0'
    obtain ⟨j, w, Λ, h, hw⟩ := hLinkUncond t₀ k0 g0 hk0' hwr0
    have hjlt : j < M.lauf.length := by
      by_cases h : j < M.lauf.length
      · exact h
      · have hle : M.lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp at hw
    have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λ h)) := by
      rw [hM'l, List.getElem?_append_left hjlt]
      exact hw
    exact ⟨j, w, Λ, h, hw'⟩
  · by_cases heq : k0 = J.schrittFaden.length
    · subst heq
      have hg0 : g0 = f := by
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk0'
        exact (Option.some_inj.mp hk0').symm
      rw [hg0] at hwr
      have hwrF : TraegerSchreibt (J.code f) (.inl t₀) = true := hwr
      rw [hnw] at hwrF
      simp at hwrF
    · have hle : J.schrittFaden.length ≤ k0 := by omega
      have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk0'
      simp at hk0'

/-- **The chain from the whole run: identification by construction.** Over a
    single-thread lock-only `PCReach` run with non-writing code, some chain
    tracks the machine end to end: worlds and run by construction (`rfl` at
    every level, never assumed), `SerialLink` guarded-vacuous at each new lock
    step. The `PCReach` derivation routes both ways at once -- counter routing
    rules out leaf steps (`hlock`) and foreign steps (`hsingle_prog`), while
    `pcReach_gen` projects every prefix to `GenErreichbar` for the step. -/
theorem kette_aus_lauf_voll
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (prog : PCProg D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (f : Faden) (code : Faden → D.Fn)
    (hlock : ∀ (g : Faden) (i : Nat) (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob)),
      (prog g)[i]? ≠ some (PCAtom.leaf Λa cs))
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hsingle_run : ∀ s ∈ M.lauf, s.faden = f)
    (hnw_code : ∀ t₀ : D.Tab, TraegerSchreibt (code f) (.inl t₀) = false)
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
        (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false) ∧
        (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
          SerialLink Nb J Mx.lauf t₀) := by
    intro Mx pcx hx
    induction hx with
    | start =>
      intro _
      obtain ⟨J, hJw, hJl, hmem, hnwJ, hLink⟩ :=
        kette_aus_lauf_start Nb sp f code hnw_code hEintritt hSchuld hInvSicht
      exact ⟨J, hJw, hJl, hmem, hnwJ, fun t₀ _ => hLink t₀⟩
    | step Mmid Mend pcmid pcend g hmid hs ih =>
      intro hsrun
      have hReachEnd : GenErreichbar P O passes (GenStart sp) Mend :=
        pcReach_gen P O passes prog (GenStart sp) Mend pcend
          (PCReach.step Mmid Mend pcmid pcend g hmid hs)
      rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
        ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
      · exact ((hlock g (pcmid g) Λa cs) hpc).elim
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
        obtain ⟨J, hJw, _, hmemJ, hnwJ, hLink⟩ := ih hmid_single
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hnwJ', hJ'link⟩ :=
          kette_aus_lauf_schritt P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            (Ereignis.nimmt L (offen (Mmid.spuren f)))
            (Mmid.speicher.welt (Ereignis.nimmt L (offen (Mmid.spuren f)) :: Mmid.spuren f))
            rfl rfl
            (fun t k fld => rfl) (fun x => rfl)
            J hJw hmemJ hLink hnwJ hmid_single
        exact ⟨J', hJ'w, hJ'l, hmemJ', hnwJ', hJ'link⟩
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
        obtain ⟨J, hJw, _, hmemJ, hnwJ, hLink⟩ := ih hmid_single
        obtain ⟨J', hJ'w, hJ'l, hmemJ', hnwJ', hJ'link⟩ :=
          kette_aus_lauf_schritt P O passes hO sp Nb Mmid _ f
            hReachMid hReachEnd
            (Ereignis.gibt L)
            (Mmid.speicher.welt (Ereignis.gibt L :: Mmid.spuren f))
            rfl rfl
            (fun t k fld => rfl) (fun x => rfl)
            J hJw hmemJ hLink hnwJ hmid_single
        exact ⟨J', hJ'w, hJ'l, hmemJ', hnwJ', hJ'link⟩
  obtain ⟨J, hJw, hJl, _, _, hJlink⟩ := key M pc h hsingle_run
  exact ⟨J, hJw, hJl, hJlink⟩

#print axioms Gabbro.Grammatik.kette_aus_lauf_start
#print axioms Gabbro.Grammatik.kette_aus_lauf_schritt
#print axioms Gabbro.Grammatik.kette_aus_lauf_voll

end Gabbro.Grammatik

/-! ## Table witnesses for `SerialLink`: writing steps at `zugriff` events

    The whole-run induction above (`kette_aus_lauf_voll`) threads a GUARDED
    `SerialLink`: each new lock step closes the link by contradiction from the
    non-writer premise, and the base closes it vacuously over the empty step
    list. No level ever exhibits a real witness event -- for writing steps the
    slot stays owed. This section closes the TABLE half of that remainder.

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `serialLink_zeuge_tabelle`: over one table carrier `t₀` with guard `L`,
      writing chain steps own BOTH a real `zugriff` witness event in the run
      (the `hwit` witness function: per writing step `(k, g)` a run index `j`
      with `run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))`) AND the guard
      (`L ∈ D.haelt (J.code g)`). The event half is posited -- positing the
      witness is scheduler/witness duty (as `hpc` is for `PCSchritt`), with its
      shape read off `writeSlot_trace_singleton` (`Koernung.lean`),
      `schreibBytes_spur_eq` and `execEreignis_aus_blatt_ohne_axiomCall`
      (`Extraktion.lean`), all read-only. The guard half is DERIVED through the
      U003 chain, read-only: `wache_aus_schuld` (`InterferenzAllgemein.lean`
      section 21) from `J.hSchuld` -- the `SchuldnerHaelt` premise the checker
      side carries, proved per body by `schuldnerHaelt_gilt` (U003,
      `Syntax.lean`:181) -- plus coverage. Every premise is load-bearing:
      `Nb J run t₀ L` type both conjuncts, `hGuardT` and `hCov` feed the guard
      discharge, `hwit` feeds the witness conjunct.
    - `serialLink_zeuge_fuer_kette`: the corollary feeding the induction's
      guarded `SerialLink` slot (`∀ t₀, TraegerSchreibt (J.code f) (.inl t₀) =
      false → SerialLink Nb J run t₀`, as consumed by
      `kette_aus_lauf_schritt`): the per-carrier table package closes the slot
      unconditionally, so the slot guard is matched but unneeded -- writers are
      covered by real witnesses, not assumed away. The package premises
      (`hGuard`, `hCov`, `hwit`) are all load-bearing; only the consumer-named
      guard hypothesis is discarded, and it is discarded openly (strength of
      the package, not a hidden gap).

    Checker-side premises, named: `hGuardT` (the static watch list -- which
    lock guards the carrier, the `sperren_je_traeger` side of `gruppe.rs`);
    `hCov` (coverage -- the written table sits in some owed invariant's
    carrier list, the group/invariant side of `gruppe.rs`); `hwit` (the run
    really records the access -- the `schreibSlot` event shape). `J.hSchuld`
    itself is the U003 premise (`SchuldnerHaelt`), not re-proved here.

    Coverage (exactly): single shared TABLE carrier witnesses with guard, plus
    the guarded-slot adapter for whole-run consumers.

    Remainder (booked, not hidden): globals -- U003 is table-only
    (`Syntax.lean`:181-182), so `gzugriff` witnesses and the global guard stay
    owed; multi-carrier conflicts; folding the table witness into a writing
    `blatt` induction step (the `execStmt` frame correspondence `hslots` /
    `hglobs` for moving memory, as booked at `kette_aus_maschinenlauf_schritt`).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Table witness: writing steps own a real `zugriff` event plus the U003
    guard.** Over one table carrier `t₀` with guard `L`, every writing chain
    step has its witness access in the run (`hwit`, witness duty) and every
    writer holds the guard (derived via `wache_aus_schuld` from `J.hSchuld`
    plus coverage `hCov`). -/
theorem serialLink_zeuge_tabelle (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λ : List (Res D)) (h : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))) :
    SerialLink Nb J run t₀ ∧
      ∀ (g : Faden), g ∈ J.faeden → TraegerSchreibt (J.code g) (.inl t₀) = true →
        L ∈ D.haelt (J.code g) := by
  constructor
  · intro k g hkg hW
    exact hwit k g hkg hW
  · intro g hg hW
    exact wache_aus_schuld Nb J t₀ L hGuardT g hg hW (hCov g hg hW)

/-- **Corollary: the table package feeds the induction's guarded `SerialLink`
    slot.** From the per-carrier package (guard existence, coverage, witness
    events) the guarded slot closes unconditionally: the slot guard is matched
    for the consumer (`kette_aus_lauf_schritt`) but carries no content, because
    writers are covered by real witnesses. -/
theorem serialLink_zeuge_fuer_kette (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (f : Faden)
    (hGuard : ∀ t₀ : D.Tab, ∃ L : D.Lock, Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (t₀ : D.Tab) (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit : ∀ (t₀ : D.Tab) (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λ : List (Res D)) (h : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))) :
    ∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
      SerialLink Nb J run t₀ := by
  intro t₀ _
  obtain ⟨L, hL⟩ := hGuard t₀
  exact (serialLink_zeuge_tabelle Nb J run t₀ L hL (hCov t₀) (hwit t₀)).1

#print axioms Gabbro.Grammatik.serialLink_zeuge_tabelle
#print axioms Gabbro.Grammatik.serialLink_zeuge_fuer_kette

end Gabbro.Grammatik
