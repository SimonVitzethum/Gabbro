/- Part 4 of 6 of `Ziel` (split by instrumente/teile/lean-teilen.py; the umbrella `Ziel.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Ziel.T3

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- The goal from PC runs through the run induction (q01 consumer wiring):
    the `ziel_nutzer_last_aus_pc` conclusion with the posited `hSpec`
    replaced by the `stabil_aus_lauf` run premises (`hMemAll`, `hSeedAll`,
    `hBlattAll`) plus the explicit `J`↔`M` wiring (`tr`, `htr`, `hJw`,
    `hJsf`), keeping `hForm` (the `hFree` check derives inside). Every
    premise is load-bearing. -/
theorem ziel_nutzer_last_aus_pc_stabil (o : Ausgang V l Γ)
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob)
    (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc)
    (code : D.Marke → Nat)
    (hMSep : PCMarkSep code (Extraktion.progAus P fcode tabs globs))
    (hCSep : PCUnsharedSep (Extraktion.progAus P fcode tabs globs))
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (tr : List Faden)
    (htr : PCSpur P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc tr)
    (hJw : J.welten = M.welten)
    (hJsf : J.schrittFaden = tr)
    (hMemAll : ∀ (g : Faden), g ∈ J.faeden → SpeicherVertrag Pre Post (J.code g))
    (hSeedAll : ∀ (g : Faden), g ∈ J.faeden →
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Pre (J.code g) σ₀) ∧
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Post (J.code g) σ₀))
    (hBlattAll : ∀ (g : Faden), g ∈ J.faeden → ∀ (M₀ : GenMaschine D) (pc₀ : PCStand),
      PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M₀ pc₀ →
      ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren g)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ' →
      σ'.spur = neu ++ M₀.spuren g →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre (J.code g) (M₀.weltVon g) ↔ Pre (J.code g) σ') ∧
        (Post (J.code g) (M₀.weltVon g) ↔ Post (J.code g) σ'))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂)))
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet M.lauf)
    ∧ ((∀ f j, Konsistent (M.lauf.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .why σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ (Marken.Einfaedig (laufProj code M.lauf))
    ∧ (∀ (i j : Nat) (f g : Faden) (carr : D.Tab ⊕ D.Glob) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      (match carr with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) →
      ei.traeger = some carr → ej.traeger = some carr → f = g)
    ∧ (M.welten.length = M.tiefe + 1)
    ∧ (∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut)
    ∧ (∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f)))
    ∧ (HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pc_gesittet P O passes hO (Extraktion.progAus P fcode tabs globs) sp M pc h
      code hMSep hCSep
  · exact ⟨pc_konsistent P O passes hO (Extraktion.progAus P fcode tabs globs) sp M pc h,
      pc_gut_obs P O passes hO (Extraktion.progAus P fcode tabs globs) sp M pc h⟩
  · intro σ hletzte f hf
    have hInv := invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD
      hGuardEx hEntry hReturn hWatch
    exact stabil_aus_lauf P O passes hO (Extraktion.progAus P fcode tabs globs) sp Nb J M
      pc tr htr hJw hJsf Pre Post I hInv hDeck hAb hMemAll hSeedAll hBlattAll
      (interferenceFree_of_invariantForm Nb J I _ hForm hInv) σ hletzte f hf
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o
  · exact pc_discharge_einfaedig code (Extraktion.progAus P fcode tabs globs) M
      (pcReach_markInv P O passes (Extraktion.progAus P fcode tabs globs) sp M pc h)
      hMSep
  · intro i j f g carr ei ej hi hj hsh hti htj
    exact pc_discharge_unshared (Extraktion.progAus P fcode tabs globs) M
      (pcReach_carrierInv P O passes (Extraktion.progAus P fcode tabs globs) sp M pc h)
      hCSep
      i j f g carr ei ej hi hj hsh hti htj
  · exact genWelten_laenge P O passes hO sp M
      (pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc h)
  · exact genWelten_gut P O passes hO sp M
      (pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc h)
  · exact genWelten_letzte P O passes hO sp M
      (pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc h)
  · exact pc_reduktion P O passes hO (Extraktion.progAus P fcode tabs globs) sp M pc h
      code hMSep hCSep
      t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_pc_stabil

end Gabbro.Grammatik

/-! ## 10. The chain with witnesses: folding the witness package into the step (g02, 2026-09-12)

    BEFUND (rank hwit folding, two checkers): the `hwit` premise -- the run
    carries `zugriff` events for every writing chain step -- travels openly:
    e02 (`MaschinenKette.lean`, `serialLink_zeuge_tabelle` plus the
    `serialLink_zeuge_fuer_kette` corollary) proves the table package, but no
    `blatt` step ever consumes it. The framed-leaf chain extension
    (`kette_aus_maschinenlauf_blatt`, `Maschine.lean` §18, read-only here)
    closes its `SerialLink` guarded-vacuous at the new step: a writer owes no
    witness under the guard. `MaschinenKette.lean:466` books exactly this gap:
    folding the table witness into a writing `blatt` induction step.

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `genEigen_wit_index` (list only): an event of `neu` sits in the extended
      run `M.lauf ++ genEigen f neu` at a computed index -- the transport the
      new-step witness below travels on.
    - `kette_mit_zeugen_schritt`: the framed-leaf chain extension WITH
      witnesses. Same construction as `kette_aus_maschinenlauf_blatt` (same
      routing premises, same frame through `blatt_rahmen_schritt`, same
      single-thread arithmetic and projection theorems -- DELTA marked at each
      changed line): the old-run `SerialLink` arrives via the e02 table
      package (`serialLink_zeuge_tabelle`, read-only reuse) from the prefix
      witness duty `hwit_old`, and the new step closes by the step witness
      `hneu_wit` (the fired leaf's `neu` carries the `zugriff` event when the
      code writes the carrier) transported by `genEigen_wit_index` -- instead
      of the guard contradiction. The conclusion is the UNCONDITIONAL table
      link `SerialLink Nb J' M'.lauf t₀` plus the U003 guard, instead of the
      guarded-vacuous slot.
    - `kette_mit_zeugen` / `kette_mit_zeugen_orakel`: the step firing data
      builds the COVERED PC step through the Ziel lifters
      (`pcSchritt_blatt_progAus_ohne_axiomCall`, non-oracle;
      `pcSchritt_blatt_progAus_axiomCall` under `GutO`, oracle -- read-only
      reuse, same file, never widened), so the SAME `neu` feeds the run
      extension (`PCReach` leg), the frame (inside the chain construction),
      and the witness (`SerialLink` leg). The conclusion carries the extended
      chain, its member, the unconditional table link, the guard, and the
      covered run.

    Every premise is load-bearing: each feeds the lifter, the frame, the
    transport, or the package, so deleting any premise breaks elaboration.
    There is no `have _ :=` discard, and no bare `Prop` slot that `False`
    could inhabit (every hypothesis has a fixed shape; the run is owed as
    `PCReach`, the bound as `GutO`).

    Coverage (exactly): one single-thread framed leaf step by a member thread
    over the computed `progAus` program, for one shared TABLE carrier `t₀`
    under guard `L` -- non-oracle leaves (`kette_mit_zeugen`) and `axiomCall`
    leaves under `GutO` (`kette_mit_zeugen_orakel`).

    Remainder (booked, not hidden): globals -- U003 is table-only, so
    `gzugriff` witnesses and the global guard stay owed; multi-carrier
    conflicts; iterating the witnessed step over a whole `PCReach` run
    (replacing the `hlock` premise of `MaschinenKette.kette_aus_lauf_voll`
    with per-step frame plus witness wiring); the prefix witness duty
    (`hwit_old`: the old run's accesses are still posited, as scheduler
    duty, exactly as e02 posits `hwit`); the step witness duty (`hneu_wit`:
    the fired leaf records its access -- the `schreibSlot` event shape).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Witness transport at list level.** An event of `neu` sits in the extended
    run `l ++ genEigen f neu` at index `l.length + i`, where `i` is its index
    in `neu.reverse` (the order `genEigen` maps over). Every premise is
    load-bearing: `he` yields the index, `l`/`f`/`neu` type the conclusion. -/
theorem genEigen_wit_index (l : Lauf D) (f : Faden) (neu : List (Ereignis D))
    (e : Ereignis D) (he : e ∈ neu) :
    ∃ (j : Nat), (l ++ genEigen f neu)[j]? = some (Schritt.mk f e) := by
  have hmem : e ∈ neu.reverse := List.mem_reverse.mpr he
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨l.length + i, ?_⟩
  have hmap : (genEigen f neu)[i]? = some (Schritt.mk f e) := by
    simp only [genEigen, List.getElem?_map, List.getElem?_eq_getElem hi, hget,
      Option.map_some]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  have hsub : l.length + i - l.length = i := by omega
  rw [hsub]
  exact hmap

#print axioms Gabbro.Grammatik.genEigen_wit_index

/-- **The chain with witnesses, one framed leaf step.** A chain tracking `M`
    extends along a fired framed step of a member thread AND the table link
    closes unconditionally for the covered carrier `t₀`: worlds and run by
    construction (`rfl`), order and goodness from the read-only projection
    theorems, ownership and declaration side from the single-thread run, the
    new frame from `blatt_rahmen_schritt` -- and `SerialLink` inherited along
    the old steps from the e02 table package over the prefix witness duty
    (`hwit_old`), plus witnessed (not assumed away) at the new step from the
    step witness (`hneu_wit`) transported by `genEigen_wit_index`. The
    step-level fold of the `MaschinenKette.lean:466` remainder: a writing
    `blatt` step enters the chain induction carrying its witness. Every
    premise is load-bearing. -/
theorem kette_mit_zeugen_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [σ'])
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit_old : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) := by
  -- DELTA: the old-run link arrives via the e02 table package (read-only reuse)
  -- over the prefix witness duty, not as an assumed premise.
  have hLinkOld : SerialLink Nb J M.lauf t₀ :=
    (serialLink_zeuge_tabelle Nb J M.lauf t₀ L hGuardT hCov hwit_old).1
  have hGuardOld : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → L ∈ D.haelt (J.code g) :=
    (serialLink_zeuge_tabelle Nb J M.lauf t₀ L hGuardT hCov hwit_old).2
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
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff]
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff]
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
      have e2 : (M.welten ++ [σ'])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [σ'])[k + 1]? = M.welten[k + 1]? :=
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
        have eW : (M.welten ++ [σ'])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [σ'])[J.schrittFaden.length + 1]? = some σ' := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : σ' = nach0 := Option.some_inj.mp hkn
        rw [hg0, hvor, ← hnach0]
        have hR := blatt_rahmen_schritt O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep
          J.code hW hG
        refine ⟨hmem, ?_, ?_⟩
        · intro t ht k2 fld
          exact hR.1 t ht k2 fld
        · intro g hg
          exact hR.2 g hg
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp only [reduceCtorEq] at hk
  -- DELTA: the extended chain keeps member and code by construction; the link
  -- below is unconditional for `t₀` (witnessed, via `hLinkOld` and `hneu_wit`)
  -- and the guard rides along from the package.
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, hmem, ?_, ?_⟩
  · intro k0 g0 hk0 hwr
    have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
    have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
    by_cases hlt : k0 < J.schrittFaden.length
    · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
        List.getElem?_append_left hlt
      rw [eOld] at hk0'
      -- DELTA: old steps inherit from the packaged link, not an assumed one.
      obtain ⟨j, w, Λe, he, hw⟩ := hLinkOld k0 g0 hk0' hwr0
      have hjlt : j < M.lauf.length := by
        by_cases h : j < M.lauf.length
        · exact h
        · have hle : M.lauf.length ≤ j := by omega
          rw [List.getElem?_eq_none hle] at hw
          simp only [reduceCtorEq] at hw
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
        -- DELTA: the new writing step owns the fired leaf's witness event,
        -- transported from `neu` into the extended run -- no guard to hide under.
        rw [hg0] at hwr
        obtain ⟨w, Λw, hwL, hmem_neu⟩ := hneu_wit hwr
        obtain ⟨j, hj⟩ := genEigen_wit_index M.lauf f neu _ hmem_neu
        refine ⟨j, w, Λw, hwL, ?_⟩
        rw [hg0, hM'l]
        exact hj
      · have hle : J.schrittFaden.length ≤ k0 := by omega
        have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk0'
        simp only [reduceCtorEq] at hk0'
  · intro g hg hWr
    exact hGuardOld g hg hWr

#print axioms Gabbro.Grammatik.kette_mit_zeugen_schritt

/-- **The witnessed step over the computed program, non-oracle leaves.**
    The firing data of a non-oracle leaf builds the covered PC step through
    `pcSchritt_blatt_progAus_ohne_axiomCall` (read-only reuse, same file --
    `hleaf`/`hax`/`hkein_nimmt`/`hpc`/`hΛa`/`hcs` feed exactly that lifter and
    its `PCReach` leg), while the SAME `neu` feeds the witnessed chain
    extension (`kette_mit_zeugen_schritt`, above) with the frame wiring
    (`hW`/`hG`), the prefix witness duty (`hwit_old`), and the step witness
    (`hneu_wit`). The conclusion carries the extended chain, its member, the
    unconditional table link, the guard, and the covered run. Every premise
    is load-bearing. -/
theorem kette_mit_zeugen
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob)
    (sp : Speicher D) (M : GenMaschine D) (pc : PCStand) (f : Faden)
    (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (Extraktion.progAus P fcode tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = Extraktion.stmtTraeger tabs globs s ++ Extraktion.stmtOrte s)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit_old : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu) :
    ∃ (J' : GemeinsamerLauf (D := D) Nb) (M' : GenMaschine D) (pc' : PCStand),
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) ∧
      PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M' pc' := by
  have hSchritt : PCSchritt P O passes (Extraktion.progAus P fcode tabs globs) M pc f
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) :=
    pcSchritt_blatt_progAus_ohne_axiomCall O passes P fcode tabs globs M pc f V l Γ Λ Λ'
      s ρ hleaf hax hΛ σ' neu hstep hneu hkein_nimmt Λa cs hpc hΛa hcs
  have hReach : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc h
  have hPC' : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp)
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) :=
    PCReach.step _ _ _ _ f h hSchritt
  have hReach' : GenErreichbar P O passes (GenStart sp)
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩ :=
    pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) _ _ hPC'
  obtain ⟨J', hJ'w, hJ'l, hmem', hLink', hGuard'⟩ :=
    kette_mit_zeugen_schritt P O passes hO sp Nb M _ f hReach hReach' V l Γ Λ Λ' s ρ
      hΛ σ' neu hstep rfl rfl J hJw hmem hW hG hsingle t₀ L hGuardT hCov hwit_old hneu_wit
  exact ⟨J', _, _, hJ'w, hJ'l, hmem', hLink', hGuard', hPC'⟩

#print axioms Gabbro.Grammatik.kette_mit_zeugen


end Gabbro.Grammatik
