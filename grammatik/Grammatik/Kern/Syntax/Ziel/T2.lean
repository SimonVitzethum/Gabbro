/- Part 2 of 6 of `Ziel` (split by instrumente/teile/lean-teilen.py; the umbrella `Ziel.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Ziel.T1

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 8. The goal from discipline: no assumed context, no per-run check (z03, 2026-09-11)

    What §5 still owes, and what this section stops owing. `ziel_nutzer_last`
    takes the strong `hInv : InvariantenKontext` -- the invariant at EVERY chain
    world -- as a premise, and the general `hFree : InterferenceFree` beside it;
    even the §7 invariant variant keeps `hInv` as a premise instead of deriving
    it. This section wires the goal to the derived side:

    * (a) `hInv` is DERIVED, not assumed: `invariantenKontext_aus_disziplin`
      (§21, read-only reuse) folds the per-carrier lemma over all carriers from
      entry (`hEntry` -- the invariant holds at the chain head),
      return-restoration (`hReturn` -- every writing step re-establishes what it
      owes at its end world under the guard), and the single watch premise per
      carrier (`hWatch` -- writing steps hold the guard). The premises are
      restated honestly in the callee's shape. For tables the watch discharges
      from `J.hSchuld` plus coverage (`wache_aus_schuld`, from `SchuldnerHaelt`
      §3 via U003 `Syntax.lean`:181, proved per body by `schuldnerHaelt_gilt`);
      for globals it stays checker-side -- see the §21 scope prose. No `sorry`,
      no `axiom`; `InterferenzAllgemein.lean` is not touched.
    * (b) `hFree` is DERIVED for the covered fragment, not owed per run: the
      sequential-logic leg runs through the §7 invariant variant
      (`ziel_seqLogic_aus_spec_invariantForm`), which takes `hForm :
      InvariantForm` (OWN-LOGIC: exhibit, per thread, the carrier whose
      invariant the contract conjunction coincides with) in place of `hFree`.
      The non-invariant fragment stays booked: assertions over shared carriers
      that are NOT in invariant form still owe `hFree` exactly as §6 books it.
    * (c) The CSL-exact reading travels as its own leg:
      `interferenceFree_wo_frei` (§21, read-only reuse) over one shared table
      carrier -- the standard CSL case -- with the conclusion gated on the guard
      being free at BOTH step worlds (`LockFrei L vor`, `LockFrei L nach`). Its
      premises (carrier `t₀`, guard `L`, frame-locality, guard link, entry,
      return, coverage `hCov`, uniform coincidence `hFormU`) are stated
      separately from the general discipline premises of (a) because the
      corollary takes them separately; `hFormU` (uniform: every thread
      coincides with `t₀`) is stronger than `hForm` (existential per thread)
      and feeds only this leg.

    Every premise below is load-bearing: each occurs in the proof term applied
    to one of the reused lemmas, so deleting any premise breaks elaboration.
    There is no `have _ :=` discard anywhere in the proof. The older variants
    (`ziel_nutzer_last`, `ziel_seqLogic_aus_spec`,
    `ziel_seqLogic_aus_spec_invariantForm`) stand untouched as corollaries and
    steps. -/

/-- The goal from discipline (z03): the `ziel_nutzer_last` conclusion with `hInv`
    derived from entry plus return-restoration plus watch
    (`invariantenKontext_aus_disziplin`, §21), `hFree` replaced by `hForm` for
    the invariant fragment (through the §7 variant
    `ziel_seqLogic_aus_spec_invariantForm`), and the CSL-exact LockFrei-gated
    reading as its own leg (`interferenceFree_wo_frei`, §21). Every premise is
    load-bearing -- each is applied in the proof term below. -/
theorem ziel_nutzer_last_aus_disziplin (o : Ausgang V l Γ)
    (run : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung run voll)
    (hausschluss : ForeignExclusion (D := D) run)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code run))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (carrier : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      run[i]? = some (Schritt.mk f ei) → run[j]? = some (Schritt.mk g ej) →
      ei.traeger = some carrier → ej.traeger = some carrier →
      (match carrier with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hLink : J.l = run)
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
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (t₀ : D.Tab) (L : D.Lock)
    (WcL : D.Tab → Bool) (GcL : D.Glob → Bool)
    (hAbL : HaengtAb WcL GcL (I.inv (.inl t₀)))
    (hFrameTL : ∀ t : D.Tab, WcL t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameGL : ∀ x : D.Glob, GcL x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntryL : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturnL : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hFormU : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      SpecQ Pre Post Nb J f σ ↔ I.inv (.inl t₀) σ)
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet J.l)
    ∧ ((∀ f j, Konsistent (run.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ run.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .why σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ (∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
          J.welten[k + 1]? = some nach →
            LockFrei (D := D) L vor → LockFrei (D := D) L nach →
              (SpecQ Pre Post Nb J f vor ↔ SpecQ Pre Post Nb J f nach)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLink]
    exact bruecke_exec_gesittet run voll hvoll hvers hausschluss code hEin hungeteilt
  · exact lauf_aus_brav run voll hvoll hvers
  · intro σ hletzte f hf
    exact ziel_seqLogic_aus_spec_invariantForm Nb J I Pre Post
      (invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD hGuardEx
        hEntry hReturn hWatch)
      hDeck hAb hSpec hForm σ hletzte f hf
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o
  · intro f hf k g vor nach hgm hne hkg hkv hkn hFreiVor hFreiNach
    exact interferenceFree_wo_frei Nb J I (SpecQ Pre Post Nb J) t₀ L WcL GcL
      hAbL hFrameTL hFrameGL hGuardT hEntryL hReturnL hCov hFormU
      f hf k g vor nach hgm hne hkg hkv hkn hFreiVor hFreiNach

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_disziplin

/-! ## 9. The goal from the machine: no bare run-side links (m02, 2026-09-11)

    What `ziel_nutzer_last` (§5) still owes on the run side, and what this
    section stops owing. The §5 bridge leg proves `Gesittet J.l` by rewriting
    the bare link `hLink : J.l = run` and applying `bruecke_exec_gesittet`,
    which takes the bare cross-thread shapes `hEin` (W4) and `hungeteilt`
    (W5) beside per-thread provenance (`hvoll`) and interleaving (`hvers`).
    This section replaces that whole premise bundle with one machine run:

    * (M) `M : MaschinenLauf D` (m01 `Maschine.lean`, consumed by
      fast-forward to `cd6e549`, file untouched) IS a reachable run: started
      threads (`hvoll`, closed per body by `exec_spur`), scheduler
      interleaving (`hvers`), the scheduler rule (W3, `hausschluss`), the
      single-thread construction (W4, `hEin` over the projected run), and the
      declaration side (W5, `hungeteilt`). There is no other way to build one.
    * (link) `hLink` is gone: the run side needs no equality and no
      `SerialLink` — `M.run` IS the run. The chain side (`J`, kept for the
      sequential-logic leg) is tied to the machine run only through the open
      chain-to-machine wiring booked below; nothing here asserts that link.
    * (W4) `hEin` is gone as a bare shape: W1, W2, and W4 come from
      `w1w2w4_aus_maschine` (grammar side plus construction), and the whole
      bundle from `gesittet_aus_maschine`. Where a `Verlauf` stands behind
      the run, the one-line closer is `einfaedig_aus_verlauf_getragen` (z05,
      `Marken.lean`): a carried projection IS the `hEin` shape — cited, not
      re-proved.
    * (W5) `hungeteilt` is gone as a bare shape: it travels inside `M` and is
      consumed by `gesittet_aus_maschine`, exactly as the bridge books the
      declaration side. The folded-run closer is `ungeteilt_aus_lauf` (z06,
      `Geteilt.lean` §11, narrowed to split-carrier closed-world runs) —
      cited, not re-proved; the run-to-`Bau` wiring across the fold (cut C2)
      stays open.
    * (worlds) Event-to-world is derived, not asserted: `maschinenWelten`
      folds the run's own events onto the start world, with length,
      last-spur, and goodness lemmas. This closes the step the §22 remainder
      books as open ("no event-to-world step semantics is built ... the
      bodies contribute worlds") — closed here for run worlds.
    * (order) Real reduction is derived, not linked: `reduktion_maschine`
      orders two conflicting accesses in `M.run` via `reduktion_seriell`
      with machine-derived `Gesittet` — no chain object, no `SerialLink`
      premise. Narrowing carried explicitly, never widened: single shared
      TABLE carrier (globals stay on the §§13-15 exception track), two
      conflicting accesses at order level (no folded global schedule, no
      observation equality — `mover_nonwriter_past` and `wache_aus_schuld`
      both take a `GemeinsamerLauf`, which the machine does not supply).
    * (discipline) No assumed context: the strong `hInv : InvariantenKontext`
      (the invariant at EVERY chain world) is DERIVED, not assumed, from
      entry (`hEntry`), return-restoration (`hReturn`), and the single watch
      premise per carrier (`hWatch`) via `invariantenKontext_aus_disziplin`
      (§21, read-only reuse) — the §8 discipline package
      (`ziel_nutzer_last_aus_disziplin` shape: `Wc`/`Gc` frame-locality
      `hAbD`, carrier-frame links `hFrameTD`/`hFrameGD`, guard existence
      `hGuardEx`). The r03 fix (2026-09-11): the first §9 cut kept the §5
      `hInv` premise beside the machine legs — a regression against the
      discipline package that rounds legs 1-2 closed.
    * (form) No per-run interference proof for the covered fragment: the
      general `hFree : InterferenceFree` is replaced by `hForm :
      InvariantForm` (OWN-LOGIC: exhibit, per thread, the carrier whose
      invariant the contract conjunction coincides with), consumed through
      the §7 variant `ziel_seqLogic_aus_spec_invariantForm` (read-only
      reuse). Assertions over shared carriers that are NOT in invariant
      form still owe `hFree` exactly as §6 books it — the non-invariant
      fragment stays open, honestly.

    Every premise below is load-bearing: each is passed whole to at least one
    lemma application in the proof term, so deleting any premise breaks
    elaboration. There is no `have _ :=` discard anywhere in the proof. The
    older variants (`ziel_nutzer_last`,
    `ziel_nutzer_last_aus_disziplin`) stand untouched as corollaries and
    steps.

    Remainder (booked, not hidden): the chain-to-machine wiring (`J.welten`
    versus `maschinenWelten M`); the `Verlauf` behind `M.hEin`
    (`Getragen`/`SpurLink` — no sentence reads a `Verlauf` off an `exec`
    outcome); the run-to-`Bau` wiring across the fold (cut C2); shared
    globals, more than two conflicting sections, restoring writers, and
    the non-invariant fragment — assertions over shared carriers NOT in
    invariant form still owe `hFree` exactly as §6 books it (inherited from
    the §22 remainder unchanged). -/

/-- The goal from the machine (m02, r03 rewired): the `ziel_nutzer_last`
    conclusion with the bare run-side links replaced — `hLink`/`hEin`/
    `hungeteilt` are gone, `M : MaschinenLauf D` travels instead, consumed
    by the machine theorems (`gesittet_aus_maschine`,
    `w1w2w4_aus_maschine`, `maschinenWelten_*`, `reduktion_maschine`). The
    sequential-logic leg runs through the §7 invariant variant
    (`ziel_seqLogic_aus_spec_invariantForm`) over the §8 discipline-derived
    context (`invariantenKontext_aus_disziplin`): `hFree` replaced by `hForm`,
    `hInv` derived from entry plus return-restoration plus watch. Probe,
    lowering, and outcome legs are unchanged from §5. Every premise is
    load-bearing. -/
theorem ziel_nutzer_last_aus_maschine (o : Ausgang V l Γ)
    (M : MaschinenLauf D)
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
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂)))
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet M.run)
    ∧ ((∀ f j, Konsistent (M.run.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ M.run.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .why σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ ((maschinenWelten M).length = M.run.length + 1)
    ∧ (((maschinenWelten M).getLast?.map World.spur) =
      some ((M.run.map Schritt.ereignis).reverse ++ M.start.spur))
    ∧ (∀ W ∈ maschinenWelten M, ∀ e ∈ W.spur, e ∈ M.start.spur ∨ e.gut)
    ∧ (HB M.run j₁ j₂ ∨ HB M.run j₂ j₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gesittet_aus_maschine M
  · exact ⟨(w1w2w4_aus_maschine M).1, (w1w2w4_aus_maschine M).2.1⟩
  · intro σ hletzte f hf
    exact ziel_seqLogic_aus_spec_invariantForm Nb J I Pre Post
      (invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD hGuardEx
        hEntry hReturn hWatch)
      hDeck hAb hSpec hForm σ hletzte f hf
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o
  · exact maschinenWelten_laenge M
  · exact maschinenWelten_letzte_spur M
  · exact maschinenWelten_gut M
  · exact reduktion_maschine M t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_maschine

/-! ## 9b. The goal from PC runs: no deprecated fields, no bare shapes (t01, 2026-09-11)

    What `ziel_nutzer_last_aus_maschine` (§9 m02) still owes on the run side, and
    what this section stops owing. The m02 leg proves `Gesittet M.run` from
    `M : MaschinenLauf D` -- the DEPRECATED structure (`Maschine.lean` §§1-5,
    kept byte-identical for its consumer): reachability handed as premises, with
    `hEin` (W4) and `hungeteilt` (W5) as FIELDS. The §12 PC discharge
    (`pc_discharge_einfaedig`, `pc_discharge_unshared`, genuinely proved) is not
    wired in there: no `PCReach`-to-`MaschinenLauf` bridge exists, and §9 takes
    no `PCReach`. This section rewires the goal onto generated PC runs:

    * (run) `h : PCReach P O passes (progAus P fcode tabs globs) (GenStart sp) M pc`
      travels instead of
      `M : MaschinenLauf D` -- a GENERATED run (positions with footprints,
      `Maschine.lean` §12, read-only reuse): every `PCSchritt` is a generated
      step (`pcSchritt_gen`), every PC-reachable machine is generated
      (`pcReach_gen`). There is no other way to build one.
    * (W4) `hEin` is gone as a bare shape AND as a field: the projection premise
      discharges from program text (`pc_discharge_einfaedig`, consumed below as
      its own leg over `pcReach_markInv`), and the whole bundle closes to
      `Gesittet` (`pc_gesittet`, consumed below).
    * (W5) `hungeteilt` is gone as a bare shape AND as a field: the declaration
      side discharges from carrier separation (`pc_discharge_unshared`,
      consumed below as its own leg over `pcReach_carrierInv`, with the
      shared-side hypothesis before the access equations as §12 states it).
    * (order) `pc_reduktion` runs the serial order on the PC run (consumed
      below) -- the same two-access single-carrier fragment as
      `reduktion_maschine`, with `Gesittet` derived from positions, never
      assumed.
    * (worlds) The live-memory history `M.welten` travels instead of the
      constant-memory fold: `genWelten_laenge` (one world per step),
      `genWelten_gut` (good observations), `genWelten_letzte` (the last world
      is a thread world) -- each through the projection (`pcReach_gen`), never
      re-proved. This escapes the NEGATIVE shape
      `maschinenWelten_speicher_gleich` by construction (`gen_welt_speicher_bewegt`
      moves memory on a fireable write; §12 is read, not modified).
    * (discipline, form, probe, lowering, outcome) Unchanged from §§7-8 and §5:
      the sequential-logic leg runs through the §7 invariant variant
      (`ziel_seqLogic_aus_spec_invariantForm`) over the §8 discipline-derived
      context (`invariantenKontext_aus_disziplin`); `hFree` is replaced by
      `hForm` for the covered fragment only.

    The program text is computed, not handed in: `progAus`
    (`Extraktion.lean` §14) flattens each body through the thread-to-function
    map (`fcode`) into its atom sequence, faithfully
    (`progTreue_aus_progAus`: every flattened body atom is program text). The
    goal takes `fcode`/`tabs`/`globs` and a run over
    `progAus P fcode tabs globs` -- there is no `(prog : PCProg D)` premise
    anymore. The per-step footprint checks inside `h` discharge through the
    execution link (`Extraktion.lean` §17): the lifter
    `pcSchritt_blatt_progAus_ohne_axiomCall` below builds a `PCSchritt.leaf`
    over `progAus` from the firing data, discharging `hmark`/`hcar` through
    `execEreignis_aus_blatt_ohne_axiomCall` (every event of a fired non-oracle
    leaf names the statement `Λ` and touches only the written carrier plus
    the `stmtOrte` read hull). What the witness still owes per step is exactly
    the booked remainder: atom identity (S12 -- the counter points at the
    extracted atom: `hpc`, `hΛa`, `hcs`) and the non-oracle shape (`hax`);
    `take`/`rel` steps need only `hpc`. `axiomCall` stays booked (S13): the
    oracle answers with an arbitrary world, so its events carry arbitrary
    marks and carriers. There is exactly one run premise (`h`), and it is
    load-bearing -- it feeds every run-side leg.

    Every premise below is load-bearing: each is passed whole to at least one
    lemma application in the proof term, so deleting any premise breaks
    elaboration. There is no `have _ :=` discard anywhere in the proof, and no
    bare `Prop` slot that `False` could inhabit (every slot has a fixed shape:
    the run is owed as `PCReach ...`, not as `Prop`). The older variants
    (`ziel_nutzer_last`, `ziel_nutzer_last_aus_disziplin`,
    `ziel_nutzer_last_aus_maschine`) stand untouched as corollaries and steps.

    Remainder (booked, not hidden): the scheduling argument (S12 -- proving
    the counter always points at the atom `stmtAtome_blatt_eq` yields for the
    fired statement, per step and per run); the `axiomCall` oracle-event
    contract (S13 -- every oracle event names the statement `Λ` within the
    declared writes plus `args.orte`); the chain-to-machine wiring (`J.welten`
    versus `M.welten`); the run-to-`Bau` wiring across the fold (cut C2);
    shared globals, more than two conflicting sections, restoring writers; and
    the non-invariant fragment -- assertions over shared carriers NOT in
    invariant form still owe `hFree` exactly as §6 books it (inherited from
    the §8 remainder unchanged). -/

/-- One leaf step over the computed program (q02): the firing data of a
    non-oracle leaf (`s`, `ρ`, `hleaf`, `hΛ`, `hstep`, `hneu`,
    `hkein_nimmt`) plus the booked atom identity (`hpc`: the counter points
    at the extracted atom; `hΛa`, `hcs`: that atom IS the statement
    footprint, S12 scheduler/witness duty) build the `PCSchritt.leaf` over
    `Extraktion.progAus P fcode tabs globs`, discharging `hmark`/`hcar`
    through `Extraktion.execEreignis_aus_blatt_ohne_axiomCall` (read-only
    reuse, never widened: `hax` keeps the non-`axiomCall` fragment;
    `axiomCall` stays booked as S13). Every premise is load-bearing: each is
    passed whole to the constructor or to the link. -/
theorem pcSchritt_blatt_progAus_ohne_axiomCall
    (O : Orakel D) (passes : Nat)
    (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (M : GenMaschine D) (pc : PCStand) (f : Faden)
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
    (hcs : cs = Extraktion.stmtTraeger tabs globs s ++ Extraktion.stmtOrte s) :
    PCSchritt P O passes (Extraktion.progAus P fcode tabs globs) M pc f
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) := by
  obtain ⟨hlam, hcar⟩ :=
    Extraktion.execEreignis_aus_blatt_ohne_axiomCall O passes s hleaf hax
      tabs globs (M.weltVon f) ρ σ' neu hstep hneu
  refine PCSchritt.leaf M pc f V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu
    hkein_nimmt Λa cs hpc hΛa ?_ ?_
  · intro e he m st hm
    rcases hlam e he with hl | hl
    · rw [hl, ← hΛa] at hm
      simp only [PCAtom.marks]
      exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩
    · rw [hl] at hm
      exact absurd hm List.not_mem_nil
  · intro e he o ho
    have hmem : o ∈ Extraktion.stmtTraeger tabs globs s ++ Extraktion.stmtOrte s :=
      hcar e he o ho
    simp only [PCAtom.carriers]
    rw [hcs]
    exact hmem

#print axioms Gabbro.Grammatik.pcSchritt_blatt_progAus_ohne_axiomCall


end Gabbro.Grammatik
