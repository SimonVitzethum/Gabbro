/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Fortschritt/Akzeptiert.lean
  Subject:   THE PROGRESS PROMISE FOR EVERY ACCEPTED ELABORATED UNIT — the legs that hold
             without any scheduler premise.

  Two legs of the pinned `FortschrittAkzeptiertAussage` are available for every accepted
  unit today: a matched ideal run with whole-run simulation (`sim_im_lauf`) and the composed
  per-cut alternatives (`fortschritt_im_lauf`). The four form-side fields of
  `FortschrittsPflichten` are theorems of the elaborated system (`einheit_fortschrittsfelder`
  in `Beweise/Fortschritt/EinheitLaeufe.lean`). With them, `fortschritt_akzeptiert_ohne_haengen`
  is the strongest scheduler-free theorem here, leaving exactly the per-context no-hang leg
  open. Scheduler fairness is derived from the implementation transitions in
  `EinheitLaeufe.lean`. The return premise still needed by `SchedulerEinheit.lean`
  fails on an admitted hardware-fair run of the accepted empty unit.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Fortschritt
public import Core.Verfeinerung.Simulation
public import Core.Ziel.Korrektheit.Beweise.Fortschritt.EinheitLaeufe
public import Core.Ziel.Korrektheit.Zugriff
import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung
import Core.Fortschritt.Verdraengung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Ideal (RegelFortschritt)

/-- TODAY'S PROGRESS LEG FOR EVERY ACCEPTED ELABORATED UNIT: a matched ideal run with whole-run simulation and
    the composed per-cut alternatives exist. This is all of the pinned statement except the per-context
    no-hang leg; the scheduler duties are what remains. Needs the liveness of the memory model for
    access heads (`ZugriffSchrittExistiertAussage`). -/
theorem fortschritt_akzeptiert_ohne_haengen (existiert : ZugriffSchrittExistiertAussage) :
    ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
      ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
        Maschine.Laeufe (einheitVon P t) H ρ →
        ∃ η : Maschine.I.Lauf (einheitVon P t),
          Maschine.I.Laeufe (einheitVon P t) η ∧
          Maschine.I.Sim (einheitVon P t) ρ η ∧
          Maschine.I.FortschrittDerKlasse
            (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl) η := by
  intro P t _ H ρ lauf
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  obtain ⟨η, valid, sim⟩ := Maschine.I.sim_im_lauf pflicht lauf
  refine ⟨η, valid, sim, ?_⟩
  obtain ⟨fertig, regeln, komponierbar, _⟩ := einheit_fortschrittsfelder existiert P t
  refine ⟨?_, trivial⟩
  intro zeit kontext live dispatch
  exact Maschine.I.fortschritt_im_lauf_koepfen valid fertig regeln komponierbar zeit kontext live dispatch

open Katalog Fortschritt

/-- The accepted empty source unit can lose its entry dispatch on a hardware-fair run.
    Hardware selects a maskable interrupt at tick zero and offers the core thereafter.
    Interrupt entry replaces the dispatch, and no later transition restores it. -/
theorem einheitVon_fair_ohne_rueckkehr :
    ∃ (t : Ast.Unit) (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon .x86_64 t)),
      Annahme.Akzeptiert (einheitVon .x86_64 t) ∧
      Maschine.Laeufe (einheitVon .x86_64 t) H ρ ∧
      Katalog.FairLaeufe (einheitVon .x86_64 t).katalog H ρ.hw ∧
      Maschine.SchedulerFair (einheitVon .x86_64 t) ρ ∧
      ¬ Maschine.VerdraengungKehrtZurueck (einheitVon .x86_64 t) ρ := by
  let E := einheitVon .x86_64 trivialUnit
  have accepted := trivialUnit_akzeptiert Plattform.x86_64
  obtain ⟨s, zul⟩ := zulStart_erfuellbar fairV.hardware
    (bildGueltig .x86_64 trivialUnit (trivialUnit_zugelassen .x86_64))
  obtain ⟨ρ, lauf, startEq, hwEq⟩ := fairer_lauf E zul fairV
  refine ⟨trivialUnit, HV, ρ, accepted, lauf, hwEq ▸ fairV,
    einheitVon_schedulerFair .x86_64 trivialUnit lauf, ?_⟩
  intro ret
  let z := (Maschine.I.start E s).2
  have loaded : ρ.zeit.zustand 0 = some z := by
    rw [lauf.2.2.2, startEq]
    exact Beobachtung.fragment_geladen (Ast.Semantik.fragment Ast.Category.unit trivialUnit)
      .x86_64 fairV.hardware zul
  obtain ⟨boot, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ 0)
  have bootZero : boot = 0 := by
    have bound := (zul.2.2.2.1 0 boot assigned).2
    rw [HV1] at bound
    omega
  subst boot
  have bootDispatch (k : Kern) :
      (z.kerne k).laeuft = if some k = some 0 then some Ast.Semantik.eintritt else none := by
    change (if some k = s.assignment 0 then some Ast.Semantik.eintritt else none) = _
    rw [assigned]
  have entryLive : z.status Ast.Semantik.eintritt = .laeuft := rfl
  have crashFree (n : Nat) : (ρ.hw.angebot n).crash = false := by
    rw [hwEq]
    cases n <;> rfl
  let event := Ereignis.interrupt 0 irqV .handler
  let label := aussenEtikett E.einrichtung event
  obtain ⟨graph, append⟩ := Speicher.Zustand.schritt_ohne_lesen
    (Z := z.graph) Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    .aussen label (fun h => nomatch h)
  have available : ∃ spur next,
      UnterbrechungsSchritt E.einrichtung ρ.hw 0 (0, 0) z spur next := by
    rw [hwEq]
    refine ⟨⟨[(.aussen, label)], [event]⟩,
      { Zustandseintritt z 0 (0, 0) Hv false with graph := graph },
      0, irqV, Hv, false, rfl, ⟨Nat.le_refl _, Nat.le_refl _, pendingV0, ?_, auswahlV0⟩,
      NimmtUnterbrechung.handler_bei ⟨rfl, rfl⟩ (Nat.le_refl _), rfl, rfl, ?_, rfl⟩
    · exact List.not_mem_nil
    · exact .cons (.ohne (Or.inl rfl)) append (.nil _)
  have first : ∃ id spur next, ρ.zeit.spur 0 = some (.interrupt id, spur) ∧
      ρ.zeit.zustand 1 = some next ∧ (next.kerne 0).laeuft ≠ some Ast.Semantik.eintritt ∧
      ∀ k, k ≠ 0 → (next.kerne k).laeuft ≠ some Ast.Semantik.eintritt := by
    obtain ⟨next, hn⟩ := Beobachtung.fragment_zustand_some
      (p := Ast.Semantik.fragment Ast.Category.unit trivialUnit) (plattform := .x86_64) lauf 1
    have tick := ρ.zeit.takt 0
    rw [loaded, hn] at tick
    cases tick with
    | wartet _ _ noStep =>
      obtain ⟨spur, next, irq⟩ := available
      exact (noStep _ (some next) (.schritt (.interrupt (crashFree 0) irq))).elim
    | schritt recorded step =>
      cases step with
      | schritt trans =>
        cases trans with
        | kontext _ ready _ _ =>
          obtain ⟨k, opportunity, _, _⟩ := ready
          rw [hwEq] at opportunity
          cases opportunity
        | antwort _ arrives =>
          obtain ⟨_, present, _⟩ := arrives.1.2.2.2.1
          exact (List.not_mem_nil present).elim
        | interrupt _ enters =>
          obtain ⟨k, irq, c, nmi, _, pending, takes, _, _, _, state⟩ := enters
          have selected := pending.2.2.2.2
          rw [hwEq] at selected
          have sel : (0, (0, 0), irqV) = (k, _, irq) :=
            Option.some.inj (auswahlV0.symm.trans selected)
          have k0 : k = 0 := (congrArg Prod.fst sel).symm
          subst k
          have changed : (next.kerne 0).laeuft = some c := by
            rw [state]
            simp only [Zustandseintritt, Function.update_self, KernZustand.unterbrechen]
          refine ⟨_, _, next, recorded, hn, ?_, ?_⟩
          · rw [changed]
            cases takes <;> intro h <;> cases h
          · intro k hk h
            have old : (next.kerne k).laeuft = (z.kerne k).laeuft := by
              rw [state]
              simp only [Zustandseintritt, Function.update_of_ne hk]
            rw [old, bootDispatch, if_neg (fun h => hk (Option.some.inj h))] at h
            cases h
        | absturz crash =>
          have impossible := (crashFree 0).symm.trans crash.1.2
          cases impossible
  obtain ⟨id, spur, next, record, hn, absentZero, absentOther⟩ := first
  have absent (m : Nat) : ∀ v, ρ.zeit.zustand (m + 1) = some v →
      ∀ k, (v.kerne k).laeuft ≠ some Ast.Semantik.eintritt := by
    induction m with
    | zero =>
      intro v cut k
      have eq := Option.some.inj (cut.symm.trans hn)
      subst v
      by_cases hk : k = 0
      · subst k
        exact absentZero
      · exact absentOther k hk
    | succ m ih =>
      intro v cut k
      obtain ⟨u, hu⟩ := Beobachtung.fragment_zustand_some
        (p := Ast.Semantik.fragment Ast.Category.unit trivialUnit) (plattform := .x86_64) lauf (m + 1)
      have ht := ρ.zeit.takt (m + 1)
      rw [hu, cut] at ht
      cases ht with
      | wartet _ eq _ =>
        rw [Option.some.inj eq]
        exact ih u hu k
      | schritt _ step =>
        cases step with
        | schritt trans =>
          cases trans with
          | kontext _ _ regel aus =>
            rw [(einheitVon_kontext_erhaelt_impl .x86_64 trivialUnit regel aus).1]
            exact ih u hu k
          | antwort _ arrives =>
            rw [(einheitVon_antwort_erhaelt arrives.2.2.2).1]
            exact ih u hu k
          | interrupt _ enters =>
            obtain ⟨_, _, _, _, _, pending, _, _, _, _, _⟩ := enters
            have selected := pending.2.2.2.2
            rw [hwEq] at selected
            cases selected
          | absturz crash =>
            have impossible := (crashFree (m + 1)).symm.trans crash.1.2
            cases impossible
  have dispatch : (z.kerne 0).laeuft = some Ast.Semantik.eintritt := by
    rw [bootDispatch, if_pos rfl]
  obtain ⟨n, later, k, v, cut, dispatched⟩ :=
    ret Ast.Semantik.eintritt 0 0 ⟨z, loaded, dispatch, entryLive⟩ ⟨id, spur, record⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt later)
  exact absent m v cut k dispatched

end Gabbro.Core.Ziel.Korrektheit
