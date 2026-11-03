/- Part 7 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
module
public import Grammatik.Kern.Semantik.Maschine.T6
@[expose] public section


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
      `gut_blatt` (`Maschine/T1`, leaf-local so no caller residual is
      needed: the `Gut` half that is the frame). The leaf shape travels as
      `hleaf`; the static scope check as `hscope`.
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

    Read-only inputs, never modified: `gut_blatt`
    (`Maschine/T1`), `Rahmen.weiter` (`Satz.lean`); the induction-step construction
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
    frame is the same `gut_blatt` derivation under the same bound `hO`) --
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
    the plain leaf fact `gutRet_blatt` (`Maschine/T1`, scope-free: the frame
    never needed spare-and-rank), read directly. Every premise is
    load-bearing: each feeds `gutRet_blatt` or its application. -/
theorem blatt_rahmen_vertrag
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ') :
    Rahmen V.schreibt V.gschreibt (M.weltVon f) σ' := by
  exact (Stmt.gutRet_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ.heldIn σ' hstep).1

/-- **The code frame of a fired step (`blatt_rahmen_schritt`).** A fired
    step's memory movement satisfies the chain-step frame: the contract
    frame widened to the thread's code frame under the contract-to-code
    wiring. Every premise is load-bearing: the firing data feeds
    `blatt_rahmen_vertrag`, `code` types the wiring and the conclusion,
    `hW` / `hG` feed the widening. -/
theorem blatt_rahmen_schritt
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (code : Faden → D.Fn)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true) :
    Rahmen (D.schreibt (code f)) (D.gschreibt (code f)) (M.weltVon f) σ' := by
  exact (blatt_rahmen_vertrag O passes hO M f V l Γ Λ Λ' s ρ hleaf hΛ σ' hstep).weiter hW hG

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
    (hleaf : s.istBlatt = true)
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
        have hR := blatt_rahmen_schritt O passes hO M f V l Γ Λ Λ' s ρ hleaf hΛ σ' hstep
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
