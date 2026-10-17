/- Part 3 of 6 of `Ziel` (split by instrumente/teile/lean-teilen.py; the umbrella `Ziel.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Ziel.T2

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- The goal from PC runs (t01, q02 rewired): the `ziel_nutzer_last`
    conclusion with the deprecated run-side bundle replaced -- no
    `MaschinenLauf`, no `hLink`, no `hEin`/`hungeteilt` as bare shapes or
    fields -- and no hand-supplied program: `h : PCReach ...` travels over
    the computed `Extraktion.progAus P fcode tabs globs` (§14; fidelity
    `progTreue_aus_progAus`), whose per-step `hmark`/`hcar` checks the
    witness builds through the lifter `pcSchritt_blatt_progAus_ohne_axiomCall`
    above (execution link §17, non-`axiomCall` fragment only). The run is
    consumed by the PC theorems (`pc_gesittet`, `pc_discharge_einfaedig`,
    `pc_discharge_unshared`, `pc_reduktion`) and the generated-world lemmas
    through the projection (`pcReach_gen`). The sequential-logic leg runs
    through the §7 invariant variant
    (`ziel_seqLogic_aus_spec_invariantForm`) over the §8 discipline-derived
    context (`invariantenKontext_aus_disziplin`): `hFree` replaced by `hForm`,
    `hInv` derived from entry plus return-restoration plus watch. Probe,
    lowering, and outcome legs are unchanged from §5. Every premise is
    load-bearing, and no bare `Prop` slot admits `False` (the run is owed as
    `PCReach ...`, not as `Prop`). -/
theorem ziel_nutzer_last_aus_pc (o : Ausgang V l Γ)
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
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
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
    exact ziel_seqLogic_aus_spec_invariantForm Nb J I Pre Post
      (invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD hGuardEx
        hEntry hReturn hWatch)
      hDeck hAb hSpec hForm σ hletzte f hf
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

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_pc

/-! ## 9b continued. The oracle lifter: `axiomCall` leaves over `progAus` (a02)

    What §9b above leaves booked: the lifter `pcSchritt_blatt_progAus_ohne_axiomCall`
    wires only the non-oracle fragment (the `hax` exclusion); the merged S13 oracle
    characterization (`Extraktion.execEreignis_aus_axiomCall`,
    `Extraktion.hmark_hcar_aus_progAus_axiomCall`, read-only reuse, never widened)
    stands unused. This block wires it in, mirroring the non-oracle lifter exactly.

    * (lifter) `pcSchritt_blatt_progAus_axiomCall` builds a `PCSchritt.leaf` over
      the computed `Extraktion.progAus P fcode tabs globs` from the firing data of
      an `axiomCall` leaf, discharging `hmark`/`hcar` through
      `Extraktion.execEreignis_aus_axiomCall` under the oracle bound
      (`hO : GutO O`). `hO` travels as a named premise (the `dma_inhalt` class:
      a named assumption, never derived here, never an axiom). The leaf shape
      needs no exclusion premise: `hax` is replaced by `hO`.
    * (application) `pcReach_blatt_progAus_axiomCall` extends a covered run
      (`h : PCReach ...`) by one oracle-leaf step through the lifter, so oracle
      leaves are covered wherever the goal consumes `PCReach` -- which is every
      run-side leg of `ziel_nutzer_last_aus_pc` (its `hO` premise already feeds
      `pc_gesittet`, `pc_konsistent`, `pc_gut_obs`, `pc_reduktion`).
    * (narrowing, carried explicitly) The covered class is GutO oracles only:
      the oracle answers with its recorded write events (`axiomSpur`, the
      trace conjunct of `GutO`), over caller domains covering the declared
      writes (`hct`/`hcg`). Atom identity
      (`hpc`, `hΛa`, `hcs`) stays the scheduler/witness duty (S12); `take`/`rel`
      steps need only `hpc`.

    Every premise below is load-bearing: each is passed whole to the link, to
    the constructor, or to the reach step, so deleting any premise breaks
    elaboration. There is no `have _ :=` discard anywhere in the proofs, no
    `sorry`/`admit`/`axiom`, and no bare `Prop` slot that `False` could inhabit
    (the run is owed as `PCReach ...`, the bound as `GutO O`). -/

/-- One oracle-leaf step over the computed program (a02): the firing data of an
    `axiomCall` leaf (`a`, `args`, `h`, `hw`, `hg`, `ρ`, `hΛ`, `hstep`, `hneu`,
    `hkein_nimmt`) under the oracle bound (`hO`) plus the booked atom identity
    (`hpc`: the counter points at the extracted atom; `hΛa`, `hcs`: that atom IS
    the statement footprint, S12 scheduler/witness duty) build the
    `PCSchritt.leaf` over `Extraktion.progAus P fcode tabs globs`, discharging
    `hmark`/`hcar` through `Extraktion.execEreignis_aus_axiomCall` (read-only
    reuse: GutO oracles only, with the domain-completeness premises).
    Every premise is load-bearing: each is passed whole to the link or to the
    constructor. -/
theorem pcSchritt_blatt_progAus_axiomCall
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (M : GenMaschine D) (pc : PCStand) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hct : ∀ t, D.aschreibt a t = true → t ∈ tabs)
    (hcg : ∀ g, D.agschreibt a g = true → g ∈ globs)
    (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (Extraktion.progAus P fcode tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = Extraktion.stmtTraeger tabs globs
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
      Extraktion.stmtOrte
        (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ)) :
    PCSchritt P O passes (Extraktion.progAus P fcode tabs globs) M pc f
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) := by
  obtain ⟨Λe, hmf, hlam, hcar⟩ :=
    Extraktion.execEreignis_aus_axiomCall O passes a args h hw hg hd hgd hO tabs globs
      hct hcg (M.weltVon f) ρ σ' neu hΛ hstep hneu
  refine PCSchritt.leaf M pc f V l Γ Λ Λ
    (Stmt.axiomCall a args h hw hg hd hgd) ρ rfl hΛ σ' neu hstep hneu
    hkein_nimmt Λa cs hpc hΛa ?_ ?_
  · intro e he m st hm
    rcases hlam e he with hL | hLe
    · rw [hL] at hm
      rw [← hΛa] at hm
      simp only [PCAtom.marks]
      exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩
    · rw [hLe] at hm
      exact absurd hm (hmf m st)
  · intro e he o ho
    have hmem : o ∈ Extraktion.stmtTraeger tabs globs
        (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
        Extraktion.stmtOrte
          (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) :=
      hcar e he o ho
    simp only [PCAtom.carriers]
    rw [hcs]
    exact hmem

#print axioms Gabbro.Grammatik.pcSchritt_blatt_progAus_axiomCall

/-- Oracle leaves extend the covered run (a02 application): one `axiomCall` leaf
    step through the oracle lifter extends `PCReach` over the computed program,
    so the `ziel_nutzer_last_aus_pc` run premise (`h : PCReach ...`, which takes
    no leaf-shape premise of its own) covers oracle leaves wherever a witness
    builds them with the lifter above -- under `hO`, with the S12 atom identity
    owed per step exactly as for non-oracle leaves. Every premise is
    load-bearing: `h` feeds the reach step, the rest feed the lifter. -/
theorem pcReach_blatt_progAus_axiomCall
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (sp : Speicher D) (M : GenMaschine D) (pc : PCStand) (f : Faden)
    (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hct : ∀ t, D.aschreibt a t = true → t ∈ tabs)
    (hcg : ∀ g, D.agschreibt a g = true → g ∈ globs)
    (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ) (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (Extraktion.progAus P fcode tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = Extraktion.stmtTraeger tabs globs
      (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
      Extraktion.stmtOrte
        (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ)) :
    PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp)
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) :=
  PCReach.step _ _ _ _ f h
    (pcSchritt_blatt_progAus_axiomCall O passes hO P fcode tabs globs M pc f V l Γ Λ
      a args hh hw hg hd hgd hct hcg ρ hΛ σ' neu hstep hneu hkein_nimmt Λa cs hpc hΛa hcs)

#print axioms Gabbro.Grammatik.pcReach_blatt_progAus_axiomCall

/-! ## 9b continued. The stabil consumer: the run induction feeds the goal (q01, 2026-09-12)

    BEFUND (rank VERDRAHTUNG HOCH, two checkers): `stabil_aus_lauf`
    (`Maschine.lean:3879`) has ZERO consumers -- `ziel_nutzer_last_aus_pc`
    (§9b above) still takes `hSpec` directly. Everything proved lies ready,
    nothing consumes it: the per-thread run induction (`spec_aus_lauf_voll`
    over `PCSpur`, folded per member thread inside `stabil_aus_lauf`) feeds
    `stabil_from_spec`, i.e. `owickiGries_stabil`'s consumer, while the goal
    posits the triples it could derive.

    What this block wires in (variant theorem, the original stands untouched):

    * `ziel_nutzer_last_aus_pc_stabil` concludes the exact
      `ziel_nutzer_last_aus_pc` conclusion (all twelve conjuncts), but its
      sequential-logic leg runs through `stabil_aus_lauf` (read-only reuse,
      `Maschine.lean` not touched) instead of the §7 invariant variant over a
      posited `hSpec`. What `hSpec` became: it is REPLACED by the three run
      premises `stabil_aus_lauf` consumes -- `hMemAll` (memory-only contracts
      per member thread), `hSeedAll` (head validity per member thread from
      thread entry), `hBlattAll` (uniform per-firing preservation over every
      reachable intermediate machine) -- in the exact callee shapes.
    * The `J`↔`M` wiring is carried explicitly as the narrowing it is:
      `tr`/`htr` (the thread trace of the run over the computed `progAus`
      program), `hJw` (`J.welten = M.welten`), `hJsf`
      (`J.schrittFaden = tr`). The spur is no new assumption class:
      `pcSpur_von_reach` (read-only reuse) bridges any `PCReach` derivation
      to its spur, but the spur travels as a premise because `hJsf` names it.
      The `hJw`/`hJsf` shape is exactly what `kette_aus_lauf_bezeugt_closed`
      (§12, read-only reference, NOT applied) supplies for witnessed runs --
      not applied because that corollary narrows to single-thread runs while
      this goal stays two-thread (its last conjunct is the `HB` disjunction
      over `g₁ ≠ g₂`).
    * No §7/§8 regression: `stabil_aus_lauf` owes `hFree`, but the variant
      keeps the `hForm` premise (not `hFree`) and derives the check inside
      via `interferenceFree_of_invariantForm` (read-only reuse) over the
      discipline-derived context -- the same derivation §8 already feeds the
      §7 variant. The invariant fragment stays per-run-check-free; the
      non-invariant fragment stays booked exactly as §9b books it.
    * `hO` (already a premise) now feeds `stabil_aus_lauf` as well as the run
      legs; `prog` is the computed `Extraktion.progAus P fcode tabs globs`
      (no new gift numbers: `P`, `O`, `passes`, `fcode`, `tabs`, `globs`
      already travel).

    Every premise is load-bearing: each is passed whole to a run-side lemma,
    to the discipline derivation, or to the `stabil_aus_lauf` application
    (through `hInv`, which `hForm` shares for the `hFree` derivation), so
    deleting any premise breaks elaboration. There is no `have _ :=`
    discard, no `sorry`/`admit`/`axiom`, and no bare `Prop` slot that
    `False` could inhabit (the run is owed as `PCReach`/`PCSpur`, the wiring
    as equations over them).

    Remainder (booked, not hidden): discharging `hJw`/`hJsf` per program
    (the chain-to-machine wiring -- §12 closes it for witnessed
    single-thread runs); discharging `hBlattAll` per leaf (execution link)
    and `hMemAll` per contract (the instantiation side); head validity from
    thread entry (caller side, `hSeedAll` shape). -/


end Gabbro.Grammatik
