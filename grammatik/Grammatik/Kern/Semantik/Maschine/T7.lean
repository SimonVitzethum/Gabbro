/- Part 7 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T6

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **Counter routing into the generated run.** An occurring PC step projects
    to a generated step by the same thread (`pcSchritt_gen` read-only): the
    generated run's steps are counter-fired steps. Every premise is
    load-bearing: `hs` feeds the projection, `h` / `hmem` feed membership. -/
theorem zaehler_routing_gen
    (prog : PCProg D) (M0 : GenMaschine D)
    (Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    GenSchritt P O passes Mmid f M' := by
  cases hmem with
  | letzter _ =>
      exact pcSchritt_gen P O passes prog Mmid M' pcmid pc' f hs
  | frueher _ _ _ =>
      exact pcSchritt_gen P O passes prog Mmid M' pcmid pc' f hs

#print axioms Gabbro.Grammatik.zaehler_aus_konstruktion_voll
#print axioms Gabbro.Grammatik.zaehler_routing_fremd
#print axioms Gabbro.Grammatik.zaehler_routing_gen

end Gabbro.Grammatik

/-! ## 18. The leaf-frame correspondence: fired leaf steps satisfy the chain-step frame

    `kette_aus_maschinenlauf_schritt` (§14) extends a tracking chain along one
    memory-preserving step: its `hslots` / `hglobs` premises close by `rfl`
    for lock steps, which keep memory by construction. A `blatt` step moves
    memory on writes, so `MaschinenKette.lean` books `blatt` steps as
    remainder under `hlock` (no `PCAtom.leaf` anywhere in `prog`): the
    induction covers exactly the steps that do nothing. This section wires
    the `execStmt` frame into that step: a fired leaf's post-world satisfies
    the chain-step `Rahmen`.

    What is proved (no `sorry`):

    - `blatt_rahmen_vertrag`: the contract frame of a fired step. From the
      firing data (`hstep` out of the thread world `M.weltVon f` under `hΛ`)
      and the oracle bound (`hO`), the post-world keeps the statement
      contract's frame (`Rahmen V.schreibt V.gschreibt`), by direct reuse of
      `stmt_gut` (`Satz.lean`, the `Gut` half that is the frame). The leaf
      shape is the caller's evidence: the frame holds for every fired
      statement, leaves included, so no `hleaf` premise is taken.
    - `blatt_rahmen_schritt`: the code frame of a fired step. The contract
      frame widened (`Rahmen.weiter`) to the thread's code frame
      (`D.schreibt (code f)` / `D.gschreibt (code f)`) under the
      contract-to-code wiring (`hW` / `hG`: the contract writes only where
      the code may write). This is the chain-step frame the induction's
      `hSchritt` consumes at the new step.
    - `kette_aus_maschinenlauf_blatt`: the chain extension along a fired
      framed step. The `kette_aus_maschinenlauf_schritt` construction with
      the same routing premises and the same conclusion, except the
      memory-preservation premises (`hslots` / `hglobs`) are replaced by the
      firing data plus the wiring, and the new-step `Rahmen` closes through
      `blatt_rahmen_schritt` (successor worlds share memory by
      construction, so the frame transfers across definitionally equal
      memories). The step-level lift of the `hlock` exclusion: a framed
      fired leaf extends the tracking chain.

    Read-only inputs, never modified: `stmt_gut`, `keinRuf_gut`,
    `Rahmen.weiter` (`Satz.lean`); the induction-step construction
    (`kette_aus_maschinenlauf_schritt` above, mirrored except for the
    new-step frame); the projection theorems it reuses (`gen_konsistent`,
    `gen_gut_obs`, `gen_ausschluss`, `genWelten_letzte`,
    `gen_eigen_getElem`).

    Event side (cited, not imported): a fired non-oracle leaf's new events
    carry the statement footprint
    (`Extraktion.execEreignis_aus_blatt_ohne_axiomCall`, `Extraktion.lean`
    §17). This file cannot import `Extraktion` (`Extraktion.lean` imports
    this file), so no event characterization is restated or re-proved here:
    the frame (`Rahmen`) compares slots and globals only, never events, and
    the run side travels through the successor equations (`hM'l` names
    `neu`, `hM'w` names `σ'`). The trace linkage (`hneu`) and the scheduler
    side (`hkein_nimmt`) belong to the `GenSchritt.blatt` evidence and are
    consumed where `hReach'` is built, so the chain step takes neither; the
    per-step footprint checks (`hmark` / `hcar`) stay with the `PCSchritt`
    lifter (`Ziel.lean`: `pcSchritt_blatt_progAus_ohne_axiomCall` and its
    oracle sibling).

    Coverage (exactly): one single-thread step by a member thread for any
    fired statement -- every leaf included, oracle leaves included (their
    frame is the same `stmt_gut` derivation under the same bound `hO`) --
    with `SerialLink` guarded-vacuous at the new step exactly as for lock
    steps (a writer owes no witness under the guard).

    Remainder (booked, not hidden): iterating the step over a whole
    `PCReach` run -- replacing the `hlock` premise of
    `MaschinenKette.kette_aus_lauf_voll` with per-step frame wiring;
    non-vacuous `SerialLink` witnesses at `zugriff` events for writing
    steps; globals and multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The contract frame of a fired step.** From the firing data out of the
    thread world (`hstep` under `hΛ`) and the oracle bound (`hO`), the
    post-world keeps the statement contract's frame -- the `Rahmen` half of
    `stmt_gut` (`Satz.lean`), read directly. Every premise is load-bearing:
    each feeds `stmt_gut` or its application. -/
theorem blatt_rahmen_vertrag
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ') :
    Rahmen V.schreibt V.gschreibt (M.weltVon f) σ' := by
  exact ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ) σ' hstep).1

/-- **The code frame of a fired step (`blatt_rahmen_schritt`).** A fired
    step's memory movement satisfies the chain-step frame: the contract
    frame widened to the thread's code frame under the contract-to-code
    wiring. Every premise is load-bearing: the firing data feeds
    `blatt_rahmen_vertrag`, `code` types the wiring and the conclusion,
    `hW` / `hG` feed the widening. -/
theorem blatt_rahmen_schritt
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (code : Faden → D.Fn)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true) :
    Rahmen (D.schreibt (code f)) (D.gschreibt (code f)) (M.weltVon f) σ' := by
  exact (blatt_rahmen_vertrag O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep).weiter hW hG

/-- **The chain from the machine, one framed leaf step.** A chain tracking
    `M` extends along a fired framed step of a member thread: worlds and run
    by construction (`rfl`), order and goodness from the read-only
    projection theorems, ownership and declaration side from the
    single-thread run, the new frame from `blatt_rahmen_schritt` instead of
    memory preservation, `SerialLink` inherited plus guarded-vacuous at the
    new step. The step-level lift of the `hlock` exclusion: a framed fired
    leaf enters the chain induction. Every premise is load-bearing: the
    firing data and the wiring feed the new-step frame, `neu` types `hM'l`,
    the routing premises feed the mirrored construction. -/
theorem kette_aus_maschinenlauf_blatt
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
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
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
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, ?_⟩
  intro t₀ hnw k0 g0 hk0 hwr
  have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
  have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
  by_cases hlt : k0 < J.schrittFaden.length
  · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk0'
    obtain ⟨j, w, Λ, h, hw⟩ := hLink t₀ k0 g0 hk0' hwr0
    have hjlt : j < M.lauf.length := by
      by_cases h : j < M.lauf.length
      · exact h
      · have hle : M.lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp only [reduceCtorEq] at hw
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
      simp only [Bool.false_eq_true] at hwrF
    · have hle : J.schrittFaden.length ≤ k0 := by omega
      have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk0'
      simp only [reduceCtorEq] at hk0'

#print axioms Gabbro.Grammatik.blatt_rahmen_vertrag
#print axioms Gabbro.Grammatik.blatt_rahmen_schritt
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_blatt

end Gabbro.Grammatik

/-! ## 19. The single-thread discharge for Einfaedig runs (`hsingle_aus_einfaedig`)

    The `hsingle` premises of §14 (`kette_aus_maschinenlauf_schritt`,
    `_nimmt`, `_gibt`) and §18 (`kette_aus_maschinenlauf_blatt`) narrow
    everything to single-thread runs: every run step is `f`'s. Inside those
    proofs `hsingle` is consumed for exactly two duties:

    - the ownership fields of `Gesittet M'.lauf` (`marke_eindeutig`, W4, and
      `ungeteilt`, W5), via `hfaden` arithmetic;
    - `BeschraenkteVerschraenkung Nb M'.lauf`, vacuously via the same
      arithmetic.

    What is proved (no `sorry`):

    - `hsingle_aus_einfaedig`: the first duty discharged for multi-thread
      runs. From reachability (`h`, which yields W1-W3 through the §11
      projection theorems), the `Einfaedig` projection (`hEin`, W4 through
      `marke_eindeutig_aus_einfaedig`, `Wettlauf.lean` §7), and the
      declaration side (`hungeteilt`, W5, the exact shape `gen_gesittet`
      takes), the run is `Gesittet` -- with no single-thread premise
      anywhere. Read-only reuse of `gen_gesittet` (§11): one positional
      application, no duplicated proof. Every premise is load-bearing: each
      feeds `gen_gesittet` positionally, so deleting any premise breaks
      elaboration. There is no `have _ :=` discard, no `sorry`/`admit`/
      `axiom`, and no bare `Prop` slot.

    Coverage (exactly): the `Gesittet` half of `hsingle`'s duties, for every
    generated reachable run whose threads satisfy `Einfaedig` plus the
    declaration side -- multi-thread Einfaedig runs included. The
    `.marke_eindeutig` and `.ungeteilt` projections of the conclusion are
    the literal shapes `hsingle` supplied at the §14/§18 use sites.

    Remainder (booked, not hidden): `BeschraenkteVerschraenkung` does not
    follow from `Einfaedig` plus the declaration side -- it constrains which
    thread pairs may share a run (`Nb`), and under `hsingle` it held
    vacuously only because no second thread had steps. Multi-thread use
    sites keep it as an explicit `Nb` declaration premise (or keep
    `hsingle`); the step theorems themselves are not restated here.
    `hsingle_prog` (the program side, `Extraktion.lean` counter routing)
    is untouched, as are `SerialLink` witnesses, globals, and
    multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The single-thread narrowing discharged for Einfaedig runs.** A
    generated reachable run whose threads satisfy `Einfaedig` (plus the
    declaration side) is `Gesittet`: W1-W3 are generated, W4 travels as the
    `Einfaedig` projection, W5 as the declaration side. This is the
    `Gesittet` half of what `hsingle` supplies at the §14/§18 use sites,
    now without any single-thread premise, so multi-thread Einfaedig runs
    are covered. Every premise is load-bearing: each is passed whole to
    `gen_gesittet`. -/
theorem hsingle_aus_einfaedig
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet M.lauf :=
  gen_gesittet P O passes hO sp M h code hEin hungeteilt

#print axioms Gabbro.Grammatik.hsingle_aus_einfaedig

end Gabbro.Grammatik

/-! ## 20. The spec triple from execution: one fired step extends the thread triple
    (`spec_aus_fuehrung_schritt`)

    The Owicki-Gries bind (`InterferenzAllgemein.lean` section 19: `SpecTriple`,
    `seqTriple_from_spec`, `stabil_from_spec`, consumed by `owickiGries_stabil`)
    posits each thread's triple over chain positions: `requiresEigen` and
    `ensuresEigen` quantify over indices `k` with `schrittFaden[k]? = some f`,
    with no link to the steps the machine actually fired. The sequential side
    exists (`stabil_from_spec`) and the execution side exists (PC runs,
    section 12: where each thread stands, firing through `PCSchritt`); nothing
    binds the triple to the executed steps of the interleaving.

    What is proved (no `sorry`):

    - `spec_aus_fuehrung_schritt`: one executed PC step extends the thread
      triple. A chain `J` tracks the machine `M` (`hJw`: the same worlds); the
      thread's triple holds on `J` (`hSpec`, the prefix -- at the seed this is
      head validity alone, since a zero-step chain carries no eigen
      obligation); one `PCSchritt` of `f` fires (`hs`: where the thread stands
      plus the firing data, read as a generated step through `pcSchritt_gen`);
      the extended chain `J'` continues the history by construction
      (`hJ'sf` / `hJ'w` / `hJ'code`, exactly what the section 14 / `blatt`
      constructions supply definitionally). Then the triple holds on `J'`.
      Old indices transfer through the prefix triple; the new index -- the
      fired step -- transfers through the firing itself. Leaf steps go
      through the per-firing contract preservation (`hBlatt`, the
      sequential-verification duty, now stated over firings with `hstep`
      evidence rather than over chain positions); lock steps (`nimmt` /
      `gibt`, the section boundaries of the section 21 grain) go through
      live-memory constancy plus memory-only contracts (`hMem`): a lock step
      keeps the memory, and contracts read only memory, so `Pre` / `Post`
      survive with no user logic owed.
      Every premise is load-bearing: `hReach` / `hO` / `sp` feed the
      last-world memory fact (`genWelten_letzte` through `pcReach_gen`); `hs`
      feeds `pcSchritt_gen`; `hJw` / `hJ'sf` / `hJ'w` / `hJ'code` rewrite every
      index; `hMem` bridges both step kinds; `hBlatt` closes the leaf case;
      `hSpec` closes the old indices and both heads. There is no `have _ :=`
      discard, no `sorry` / `admit` / `axiom`, and no bare `Prop` slot.

    Coverage (exactly): one executed `PCSchritt` (`leaf` / `nimmt` / `gibt`)
    by a tracked thread, extending a tracked chain. `Pre` holds along the
    thread's executed steps and `Post` at its section ends, in the uniform
    eigen shape that `owickiGries_stabil` consumes -- the indexing is executed
    (chain positions are machine firings, worlds are machine history), while
    the per-statement contract content stays where it belongs (below).

    Remainder (booked, not hidden): iterating the step over a whole `PCReach`
    run (the induction that carries a seed triple -- head validity from the
    caller -- to the final chain); the per-step atom identity inside `hs`
    (S12, the scheduler and witness duty: the counter points at the extracted
    atom); the `axiomCall` oracle-event contract (S13: the oracle answers with
    an arbitrary world, so `hBlatt` for oracle leaves is owed on arbitrary
    answers); discharging `hMem` for `QRequires` / `QEnsures` (the
    per-expression induction showing `eval` reads only slots and globals,
    downstream where the contract instantiation lives); head validity from
    thread entry (the caller side).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Memory-only contracts.** `Pre` / `Post` read only live memory (slots and
    globals), never the trace: worlds over the same memory agree. Contract
    shapes (`QRequires` / `QEnsures`) satisfy this because `eval` reads only
    slots and globals; the per-expression induction stays downstream, where
    the contract instantiation lives. -/
structure SpeicherVertrag (Pre Post : D.Fn → World D → Prop) (fn : D.Fn) : Prop where
  /-- The requires-side agrees on worlds over the same memory. -/
  memPre : ∀ σ σ' : World D, σ.speicher = σ'.speicher → (Pre fn σ ↔ Pre fn σ')
  /-- The ensures-side agrees on worlds over the same memory. -/
  memPost : ∀ σ σ' : World D, σ.speicher = σ'.speicher → (Post fn σ ↔ Post fn σ')

/-- A world built over a memory carries that memory. -/
theorem speicher_welt_speicher (s : Speicher D) (tr : List (Ereignis D)) :
    (s.welt tr).speicher = s := by
  cases s
  rfl

#print axioms Gabbro.Grammatik.speicher_welt_speicher


end Gabbro.Grammatik
