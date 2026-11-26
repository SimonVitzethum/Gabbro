/-
  File:      Core/Fortschritt/SperrAnnahmeE1.lean
  Subject:   ACCEPTANCE OF THE TICKET UNIT (PERFECT-MODEL §3.2, step M5): `E_1` is
              accepted — authority over empty footprints, the outside rule, flow over
              all-high labels, open bounds, no blockade, the isolation row over the
              single-domain table, empty clause and guard tables, and no lock owner on
              any ideal run (the ticket rule never takes). Plus the admissible fair run
              data for the waiting-bound witness.
-/
module

public import Core.Fortschritt.SperrFair
public import Core.Katalog.Start

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The ticket form meets the authority obligation: both plans have empty footprints. -/
theorem e1_regel_lokal (i : Unit) : RegelLokal E_1 i := by
  intro c s u w plan h
  cases i with
  | unit =>
    have hrule : e1Regel c s w [plan] u := h
    rcases hrule with ⟨next, _, hpeq, _⟩ | ⟨hpeq, _⟩
    · obtain rfl := (List.cons.inj hpeq).1
      exact ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => (List.not_mem_nil hl).elim⟩
    · obtain rfl := (List.cons.inj hpeq).1
      exact ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => (List.not_mem_nil hl).elim⟩

/-- The ticket unit meets the outside rule: ticket and stutter steps record nothing and
    preserve the booking, so no question and no effect needs ownership. -/
theorem e1_aussen_gueltig : AussenGueltig E_1 := by
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext normal bereit regel aus =>
    obtain ⟨i, _, hideal⟩ := regel
    cases i with
    | unit =>
      rcases hideal with ⟨next, _, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
      · obtain rfl := (List.cons.inj hpeq).1
        subst hueq
        obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
        have hakt : ticketPlan.aktion = .sperre () .ticket := rfl
        rw [hakt] at hF
        obtain ⟨_, au⟩ := spur
        cases hF
        case sperre _ _ =>
          have hwb : s'.buchung.wirkungen = s.buchung.wirkungen := by
            generalize hg : s'.graph = g at hziel
            rw [hziel]
            rfl
          refine ⟨⟨fun ev h2 => (List.not_mem_nil h2).elim,
            ⟨[], hwb.trans (List.append_nil _).symm, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
            fun hoffen q hmem hepo hant => ?_⟩
          rw [hziel] at hmem hepo hant ⊢
          exact hoffen q hmem hepo hant
      · obtain rfl := (List.cons.inj hpeq).1
        subst hueq
        obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
        have hakt : stutterPlan.aktion = .intern := rfl
        rw [hakt] at hF
        obtain ⟨_, au⟩ := spur
        cases hF
        case intern =>
          generalize hg : s'.graph = g at hziel
          have hwb : s'.buchung.wirkungen = s.buchung.wirkungen := by
            rw [hziel]
            rfl
          refine ⟨⟨fun ev h2 => (List.not_mem_nil h2).elim,
            ⟨[], hwb.trans (List.append_nil _).symm, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
            fun hoffen q hmem hepo hant => ?_⟩
          rw [hziel] at hmem hepo hant ⊢
          exact hoffen q hmem hepo hant

theorem e1Hoch_verborgen : oeffentlich e1Hoch = false := by
  apply decide_eq_false
  intro eq
  have mem : (0 : Nat) ∈ e1Hoch := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

/-- Flow over all-high labels: nothing public changes, every step preserves the public
    projection. Ticket and stutter steps touch no journal and record no public plan. -/
theorem e1_fluss : FlussLokal E_1 := by
  refine ⟨?_, fun f => ?_⟩
  · intro s₁ s₂ _
    refine ⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
      fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩
  · cases f with
    | unit =>
      refine ⟨?_, fun low => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans low)).elim⟩
      intro c v w p u step
      have hideal : e1Regel c v w [p] u := step.2
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun _ => ?_⟩
      rcases hideal with ⟨next, _, hpeq, rfl⟩ | ⟨hpeq, rfl⟩
      · obtain rfl := (List.cons.inj hpeq).1
        exact ⟨⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
          fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩, rfl, rfl⟩
      · obtain rfl := (List.cons.inj hpeq).1
        exact ⟨⟨fun c p h => (Bool.false_ne_true (e1Hoch_verborgen.symm.trans h)).elim,
          fun c => rfl, fun x => rfl, rfl, rfl, fun c => rfl⟩, rfl, rfl⟩

/-- The ticket unit meets the bound row: bounds are open except the hold bound. -/
theorem e1_schranken_lokal : SchrankenLokal E_1 :=
  schrankenLokal_leer rfl rfl rfl

/-- The ticket unit never reports a blockade. -/
theorem e1_abschnitt : AbschnittWartefrei E_1 :=
  abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb

/-- The ticket unit meets the isolation row over the single-domain table: every domain
    is `0`, so every recorded access stays inside. -/
theorem e1_isolation : RegelIsolation E_1 (tabellePlan eineTabelle) () := by
  intro t c s u s' w p spur _ _
  exact ⟨fun a l _ _ hFremd => hFremd (Or.inl rfl),
    fun ev _ d _ hFremd => hFremd (Or.inl rfl)⟩

theorem e1_domaenen : DomaenenLokal E_1 := by
  refine ⟨eineTabelle_akzeptiert, fun s c i _ => ?_⟩
  cases i with
  | unit => exact e1_isolation

/-- The clause tables are empty. -/
theorem e1_klauseln : KlauselnWahr E_1 := by
  intro ρ _
  exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
    fun _ _ _ h => (List.not_mem_nil h).elim⟩

/-- One ideal step preserves the free lock: takes are impossible, answers and interrupts
    preserve the lock state, crashes wipe it. -/
theorem e1_I_schritt_erhaelt_frei {hw : HwLauf} {t : Nat}
    {s : Zustand Unit Unit Unit Unit Bool Unit}
    {ev : SchrittWahl Unit × SchrittSpur Unit Unit} {s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hpre : (s.sperren ()).besitzer = none)
    (step : I.Schritt E_1.einrichtung E_1.system E_1.katalog hw t s ev s') :
    (s'.sperren ()).besitzer = none := by
  cases step with
  | @kontext _ u plan spur c w _ _ hreg haus =>
    obtain ⟨i, _, hreg⟩ := hreg
    cases i with
    | unit =>
      rcases hreg with ⟨next, _hss, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
      · subst hueq
        have hplan : plan = ticketPlan := (List.cons.inj hpeq).1
        subst hplan
        obtain ⟨_, _, _, v, hF, _, heq⟩ := haus
        have hakt : ticketPlan.aktion = .sperre () .ticket := rfl
        rw [hakt] at hF
        obtain ⟨_, au⟩ := spur
        cases hF
        case sperre hF' _ =>
          cases hF' with
      | ticket _ _ =>
        rw [heq]
        exact hpre
      · subst hueq
        have hplan : plan = stutterPlan := (List.cons.inj hpeq).1
        subst hplan
        obtain ⟨_, _, _, v, hF, _, heq⟩ := haus
        have hakt : stutterPlan.aktion = .intern := rfl
        rw [hakt] at hF
        obtain ⟨_, au⟩ := spur
        cases hF
        case intern =>
          rw [heq]
          exact hpre
  | antwort _ h =>
    obtain ⟨_, _, _, heq⟩ := h
    rw [heq]
    exact hpre
  | interrupt _ h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, heq⟩ := h
    rw [heq]
    exact hpre
  | absturz h =>
    exact (absturz_leert_schlange h).2

/-- No ideal run ever owns the lock. -/
theorem e1_kein_besitzer_I (ρ : I.Lauf E_1) (lauf : I.Laeufe E_1 ρ) (t : Nat)
    (s : Zustand Unit Unit Unit Unit Bool Unit) (hzs : ρ.zeit.zustand t = s) :
    (s.sperren ()).besitzer = none := by
  revert s hzs
  induction t with
  | zero =>
    intro s hzs
    have h0 := lauf.2.2.2.1
    rw [h0] at hzs
    subst hzs
    rfl
  | succ t ih =>
    intro s hzs
    have htakt := ρ.zeit.takt t
    cases htakt with
    | wartet _ heq _ =>
      rw [heq] at hzs
      exact ih _ hzs
    | schritt _ step =>
      have hpre := ih _ rfl
      have hpost := e1_I_schritt_erhaelt_frei hpre step
      rw [hzs] at hpost
      exact hpost

/-- The holder row holds vacuously: no ideal cut ever owns the lock. -/
theorem e1_halter : SperrHalterHalten E_1 := by
  intro ρ lauf t l h hown
  cases l with
  | unit =>
    have hfree := e1_kein_besitzer_I ρ lauf t.val _ rfl
    rw [hfree] at hown
    cases hown

/-- The ticket unit is accepted. -/
theorem akzeptiert_E_1 : Akzeptiert E_1 :=
  ⟨⟨Plattform.x86_64.katalog_wohlgeformt, e1_regel_lokal,
    ⟨Gabbro.Core.Aussen.zulassung_m2 _, e1_aussen_gueltig⟩, e1_fluss,
    e1_schranken_lokal, e1_abschnitt, e1_domaenen⟩, e1_klauseln,
   ⟨fun ρ _ t op args h => by
      dsimp [kanonischeVerwendung, E_1, Quelltabellen.leer] at h
      exact h.elim,
    fun ρ _ t hC => by
      obtain ⟨C, hC⟩ := hC
      obtain ⟨c, hc⟩ := hC.1
      obtain ⟨b, hblock, _, _, _⟩ := hC.2 c hc
      exact hblock,
    e1_halter⟩⟩

end Gabbro.Core.Fortschritt
