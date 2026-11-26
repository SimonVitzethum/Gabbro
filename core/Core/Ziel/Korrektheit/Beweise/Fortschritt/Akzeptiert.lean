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

open Ast.Semantik in
/-- A delivered handler writes its result and ends on its core. The implementation
    and ideal machine take the same return, restoring the interrupted entry. -/
theorem handler_abschluss_erfuellbar :
    let handler := Kontext.handler 0 0 (Nat.pair 0 0)
    let body := (Fragment.einzel (.literal 0 7)).anhaengen (.einzel (.faden (.beende 0)))
    let p := (Fragment.einzel (.literal 0 1)).anhaengen (body.rumpf (fun c => decide (c = handler)))
    let E := p.einheit .x86_64
    ∃ H hw start entered ready returned ingress,
      let z := (Maschine.I.start E start).2
      FairLaeufe E.katalog H hw ∧
      E.ZulStart H start ∧ E.laden start (H.lade E.bild) = some z ∧
      ImplSchritt E.einrichtung E.system E.katalog hw 0 z (.interrupt (0, 0), ingress) entered ∧
      (entered.kerne 0).laeuft = some handler ∧
      ImplSchritt E.einrichtung E.system E.katalog hw 1 entered (.kontext handler (), ⟨[], []⟩) ready ∧
      ImplSchritt E.einrichtung E.system E.katalog hw 2 ready (.kontext handler (), ⟨[], []⟩) returned ∧
      Maschine.I.Schritt E.einrichtung E.system E.katalog hw 2 ready (.kontext handler (), ⟨[], []⟩) returned ∧
      (returned.kerne 0).laeuft = some eintritt ∧ (returned.kerne 0).stapel = (z.kerne 0).stapel ∧
      returned.status handler = .beendet (.wert 7) ∧ returned.lokal eintritt = z.lokal eintritt ∧
      returned.rechte = z.rechte ∧ returned.buchung = z.buchung ∧ returned.graph = ready.graph := by
  intro handler body p E
  obtain ⟨start, zul⟩ := zulStart_erfuellbar fairV.hardware
    (bildGueltig .x86_64 trivialUnit (trivialUnit_zugelassen .x86_64))
  obtain ⟨kern, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ 0)
  have kernZero : kern = 0 := by
    have bound := (zul.2.2.2.1 0 kern assigned).2
    rw [HV1] at bound
    omega
  subst kern
  let z := (Maschine.I.start E start).2
  have loaded : E.laden start (HV.lade E.bild) = some z :=
    Beobachtung.fragment_geladen p .x86_64 fairV.hardware zul
  let event := Ereignis.interrupt 0 irqV .handler
  let label := aussenEtikett E.einrichtung event
  obtain ⟨graph, append⟩ := Speicher.Zustand.schritt_ohne_lesen
    (Z := z.graph) Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    .aussen label (fun h => nomatch h)
  let entered := { Zustandseintritt z 0 (0, 0) handler false with graph := graph }
  let ingress : SchrittSpur Zelle Int := ⟨[(.aussen, label)], [event]⟩
  have deliver : UnterbrechungsSchritt E.einrichtung hwV 0 (0, 0) z ingress entered :=
    ⟨0, irqV, handler, false, rfl,
      ⟨Nat.le_refl _, Nat.le_refl _, pendingV0, List.not_mem_nil, auswahlV0⟩,
      NimmtUnterbrechung.handler_bei ⟨rfl, rfl⟩ (Nat.le_refl _), rfl, rfl,
      .cons (.ohne (Or.inl rfl)) append (.nil _), rfl⟩
  let write : Befehl := .literal 0 7
  let ready := write.nach handler entered
  have calculate : E.system.ImplSchritt handler entered () [Ast.Semantik.plan] ready :=
    ⟨write, by
      change kopf p.code (Zustandseintritt z 0 (0, 0) handler false) handler = some write
      exact (handler_beginnt_im_rumpf p .x86_64 start 0 (0, 0) handler false
        (fun h => Kontext.noConfusion h) (pos := 1) rfl).trans rfl, rfl, rfl⟩
  have writeExec : FuehrtSchrittAus E.einrichtung 1 handler entered ready Ast.Semantik.plan ⟨[], []⟩ ready := by
    exact write.vollzug E.einrichtung 1 handler entered (Or.inl rfl)
  let finish : Befehl := .faden (.beende 0)
  let plan := finish.plan (ready.lokal handler) 0
  let u := finish.form.faedenNach handler ready
  have finishHead : E.system.kopf ready handler = some finish := by
    exact kopf_laufend (code := p.code) (s := ready) (c := handler)
      (by simp only [ready, Befehl.nach, entered, Zustandseintritt, Function.update_self])
      (by simp only [ready, Befehl.nach, Function.update_self]; rfl)
      (by simp only [ready, Befehl.nach, Function.update_self]; rfl) |>.trans (by
        simp only [ready, Befehl.nach, Function.update_self]
        rfl)
  have rule : finish.ideal handler ready () [plan] u := by
    change (_ ∨ (_ = true ∧ _ ∧ _))
    exact Or.inr ⟨by simp only [ready, Befehl.nach, Function.update_self]; rfl, rfl, rfl⟩
  let returned := Abschlussrueckkehr ready u handler
  have ended : u.status handler = .beendet (.wert 7) := by
    simp only [u, Schrittform.faedenNach, finish, Befehl.form, Befehl.klasse, Fadenform.klasse,
      ready, Befehl.nach, Function.update_self]
    rfl
  have frame : Zustandsrahmen ready u :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have execute : FuehrtSchrittAus E.einrichtung 2 handler ready u plan ⟨[], []⟩ returned :=
    ⟨frame, fun _ h => (List.not_mem_nil h).elim, [], returned, FuehrtAus.beende ended, .nil _, rfl⟩
  have enteredDispatch : (entered.kerne 0).laeuft = some handler := by
    simp only [entered, Zustandseintritt, Function.update_self, KernZustand.unterbrechen]
  have enteredLive : entered.status handler = .laeuft := by
    simp only [entered, Zustandseintritt, Function.update_self]
  have readyOnCore : KannSchreiten hwV 2 handler ready := ⟨0, rfl, enteredDispatch, enteredLive⟩
  have active : KehrtZurueck ready handler 0 := .handler enteredDispatch (by
    simp only [ready, Befehl.nach, entered, Zustandseintritt, KernZustand.unterbrechen,
      Function.update_self]
    exact fun h => nomatch h)
  have restored : returned = Zustandsrueckkehr u 0 := active.abschluss frame.kerne
  have dispatch : (z.kerne 0).laeuft = some eintritt := by
    change (if some 0 = start.assignment 0 then some eintritt else none) = _
    rw [assigned, if_pos rfl]
  refine ⟨HV, hwV, start, entered, ready, returned, ingress, fairV, zul, loaded,
    .interrupt rfl deliver, enteredDispatch,
    .kontext rfl ⟨0, rfl, enteredDispatch, enteredLive⟩ calculate writeExec,
    .kontext rfl readyOnCore ⟨finish, finishHead, rule⟩ execute,
    .kontext rfl readyOnCore ⟨finish, finishHead, rule⟩ execute,
    ?_, ?_, ended, ?_, rfl, rfl, rfl⟩
  · rw [restored]
    exact (rueckkehr_setzt_fort z 0 (0, 0) handler false).1.trans dispatch
  · rw [restored]
    exact (rueckkehr_setzt_fort z 0 (0, 0) handler false).2
  · change Function.update ready.lokal handler
      (finish.form.uebertrag (ready.lokal handler) ready.regionLive 0) eintritt = z.lokal eintritt
    have different : eintritt ≠ handler := fun h => Kontext.noConfusion h
    rw [Function.update_of_ne different]
    exact write.nach_lokal_anderer different entered

/-- The accepted empty source unit can lose its entry dispatch on a hardware-fair run.
    Hardware selects a maskable interrupt at tick zero and offers the core thereafter.
    The empty unit supplies no handler body with an explicit end, so no later transition
    reaches the interrupt return. -/
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
