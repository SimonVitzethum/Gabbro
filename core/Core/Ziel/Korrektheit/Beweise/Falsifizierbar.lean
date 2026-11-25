/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Falsifizierbar.lean
  Subject:   THE THREE FALSIFIABILITY STATEMENTS of `Ziel/Korrektheit/Verfeinerung`: the per-form
             simulation duty is discriminating, the whole-run simulation separates ideal runs, and the
             refinement refuses an implementation run. Each statement is an existential over a unit, so
             the proofs construct ONE concrete one-form unit whose single form takes a private `.intern`
             step on a hardware history with a single opportunity.

             Two rule variants give the witnesses. The refusing variant has an empty ideal rule, so
             every ideal run is separated from the run (`simRefutierbar`) and the per-form duty is false
             (`regelSimDiskriminiert`). The tolerant variant keeps the ideal transition and hides the
             form-local state from the local relation, so the checked stutter bound alone decides the
             match: of two ideal runs of it one replays the transition and one spends the private tick
             (`simTrennt`). `nicht_sim_bei_stotterueberlauf` supplies the refutation in both cases.
             The pinned statements are unchanged.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Erfuellbar
public import Core.Verfeinerung.LetztesAngebot

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine Katalog
open Gabbro.Core.Maschine.I

/-! ### A concrete one-form unit with one private step -/

def falsifizierbaresBild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def falsifizierbarerEintrag : Kontext := Kontext.faden 0

def falsifizierbareDaten (kern : Nat) : Startdaten Unit Unit Unit Unit :=
  ⟨fun _ => (), fun c => if c = falsifizierbarerEintrag then .laeuft else .ruht,
    fun j => ⟨if j = kern then some falsifizierbarerEintrag else none, .nutzer, (), fun _ => false, 0, false, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩

def falsifizierbareEinrichtung : Einrichtung Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
    fun _ _ => True, ⟨0, 1⟩,
    ⟨falsifizierbarerEintrag, 0, fun _ => falsifizierbareDaten 0, fun _ _ => ()⟩,
    fun _ => 0, fun _ _ _ => none⟩

def falsifizierbarerPlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def falsifizierbareAenderung (c : Kontext) (s : Zustand Unit Unit Unit Unit Unit Unit) := s

def falsifizierbareImpl (c : Kontext) (s : Zustand Unit Unit Unit Unit Unit Unit) (_ : Unit)
    (plans : List (SchrittPlan Unit Unit Unit Unit))
    (u : Zustand Unit Unit Unit Unit Unit Unit) : Prop :=
  plans = [falsifizierbarerPlan] ∧ u = s

def falsifizierbaresSystem : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => ⟨falsifizierbareImpl, falsifizierbareImpl⟩, fun _ _ => some (),
    fun _ _ => False, fun _ _ _ => False⟩

def falsifizierbareEinheit : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, falsifizierbaresBild, falsifizierbareEinrichtung,
    falsifizierbaresSystem, fun s => falsifizierbareDaten s.bootCore, fun _ _ => 0,
    (fun s _ =>
      let d := falsifizierbareDaten s.bootCore
      some (Zustand.start d.lokal d.status d.kerne d.rechte
        falsifizierbareEinrichtung.initial (.leer (fun _ => 0)))),
    Eq, (fun _ => 1), .leer, .leer, .leer, .leer⟩

def falsifizierbareSicht (t : Nat) : AussenVerlauf → AussenSicht := fun _ =>
  ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩

def falsifizierbarerHw : HwLauf :=
  Umgebung.referenzLauf Plattform.x86_64.katalog 1 falsifizierbareSicht

def falsifizierbareUmgebung : Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 1 falsifizierbareSicht

theorem falsifizierbaresBild_gueltig :
    falsifizierbaresBild.gueltig Plattform.x86_64.katalog.plattform.ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro a mem
    have h : a = 0 := List.mem_singleton.mp mem
    subst a
    exact ⟨0, rfl⟩

theorem falsifizierbarerPlan_autorisiert
    (s : Zustand Unit Unit Unit Unit Unit Unit) (c : Kontext) :
    falsifizierbarerPlan.Autorisiert falsifizierbareEinrichtung s c :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

theorem falsifizierbares_letztesAngebot_konform {k h hw} (valid : HwLauf.konform k h hw) :
    (letztesAngebot hw).konform k h := by
  refine ⟨valid.1, fun t => ?_⟩
  cases t with
  | zero => exact valid.2 0
  | succ _ =>
      exact ⟨fun _ h => (Option.some_ne_none _ h.symm).elim,
        fun _ h => (Bool.false_ne_true h).elim,
        fun _ h => (List.not_mem_nil h).elim,
        fun _ h => (Bool.false_ne_true h).elim,
        fun h => (h.elim Bool.false_ne_true Bool.false_ne_true).elim⟩

theorem falsifizierbares_letztesAngebot_ideal {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type}
    [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    {hw : HwLauf} (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) :
    KeinSchritt (Schritt E.einrichtung E.system E.katalog (letztesAngebot hw)) (t + 1) s := by
  intro event next step
  cases step with
  | kontext _ ready _ _ =>
      obtain ⟨_, offered, _, _⟩ := ready
      exact Option.some_ne_none _ offered.symm
  | antwort _ arrives =>
      have received := arrives.1.2.1.1
      rw [arrives.1.1] at received
      exact Bool.false_ne_true received
  | interrupt _ enters =>
      obtain ⟨_, _, _, _, offered, _⟩ := enters
      exact Bool.false_ne_true offered
  | absturz crash => exact Bool.false_ne_true crash.1.2

theorem falsifizierbares_letztesAngebot_konkret {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type}
    [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    {hw : HwLauf} (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) :
    KeinSchritt (Lauffolge E (letztesAngebot hw)) (t + 1) (some s) := by
  intro event next step
  cases step with
  | schritt step =>
      cases step with
      | kontext _ ready _ _ =>
          obtain ⟨_, offered, _, _⟩ := ready
          exact Option.some_ne_none _ offered.symm
      | antwort _ arrives =>
          have received := arrives.1.2.1.1
          rw [arrives.1.1] at received
          exact Bool.false_ne_true received
      | interrupt _ enters =>
          obtain ⟨_, _, _, _, offered, _⟩ := enters
          exact Bool.false_ne_true offered
      | absturz crash => exact Bool.false_ne_true crash.1.2

/-! ### The concrete run and its one private step -/

theorem falsifizierbar_konfiguration :
    ∃ (s : AussenStart) (z z' u : Zustand Unit Unit Unit Unit Unit Unit)
      (plan : SchrittPlan Unit Unit Unit Unit) (spur : SchrittSpur Unit Unit)
      (ρ : Maschine.Lauf falsifizierbareEinheit),
      falsifizierbareEinheit.ZulStart falsifizierbareUmgebung s ∧
      (Maschine.I.start falsifizierbareEinheit s).2 = z ∧
      plan = falsifizierbarerPlan ∧ u = z' ∧
      z' = falsifizierbareAenderung falsifizierbarerEintrag z ∧
      ρ.start = s ∧ ρ.hw = falsifizierbarerHw ∧
      Maschine.Laeufe falsifizierbareEinheit falsifizierbareUmgebung ρ ∧
      ρ.zeit.spur 0 = some (.kontext falsifizierbarerEintrag (), spur) ∧ spur = ⟨[], []⟩ ∧
      ρ.zeit.zustand 0 = some z ∧ ρ.zeit.zustand 1 = some z' ∧
      (falsifizierbareEinheit.system.regel ()).impl falsifizierbarerEintrag z () [plan] u ∧
      FuehrtSchrittAus falsifizierbareEinrichtung 0 falsifizierbarerEintrag z u plan spur z' ∧
      KannSchreiten falsifizierbarerHw 0 falsifizierbarerEintrag z ∧
      (falsifizierbarerHw.angebot 0).crash = false := by
  let E₀ := falsifizierbareEinheit
  let e := falsifizierbareEinrichtung
  let plan := falsifizierbarerPlan
  let hw := falsifizierbarerHw
  let h := falsifizierbareUmgebung
  let entry := falsifizierbarerEintrag
  have fair : FairLaeufe E₀.katalog h hw := by
    change FairLaeufe Plattform.x86_64.katalog
      (Umgebung.referenz Plattform.x86_64.katalog 1 falsifizierbareSicht)
      (Umgebung.referenzLauf Plattform.x86_64.katalog 1 falsifizierbareSicht)
    exact Umgebung.referenz_fair _ 1 _ Plattform.x86_64.katalog_wohlgeformt (Nat.zero_lt_succ _)
  have bild : E₀.bild.gueltig E₀.katalog.plattform.ziel := by
    change falsifizierbaresBild.gueltig Plattform.x86_64.katalog.plattform.ziel
    exact falsifizierbaresBild_gueltig
  obtain ⟨s, admissible⟩ := zulStart_erfuellbar fair.hardware bild
  have boot : s.bootCore = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ admissible.2.1)
  let z := (Maschine.I.start E₀ s).2
  let z' := falsifizierbareAenderung entry z
  let label : SchrittWahl Unit × SchrittSpur Unit Unit := (.kontext entry (), ⟨[], []⟩)
  have execute (t : Nat) (c : Kontext) (x : Zustand Unit Unit Unit Unit Unit Unit) :
      FuehrtSchrittAus e t c x x plan label.2 x := by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun _ hn => (List.not_mem_nil hn).elim, [], x, .intern, .nil _, rfl⟩
  let zustand (t : Nat) : Zustand Unit Unit Unit Unit Unit Unit := z
  have dispatch : (z.kerne 0).laeuft = some entry := by
    change (if 0 = s.bootCore then some entry else none) = some entry
    rw [boot, ite_eq_left rfl]
  have live : z.status entry = .laeuft := by
    change (if entry = entry then Status.laeuft else Status.ruht) = (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have opportunity (t : Nat) : hw.gelegenheit t 0 := congrArg some (Nat.mod_one _)
  have step (t : Nat) : Lauffolge E₀ hw t (some z) label (some z) :=
    .schritt (.kontext rfl ⟨0, opportunity t, dispatch, live⟩ ⟨(), rfl, rfl, rfl⟩ (execute t entry z))
  let ρ : Maschine.Lauf E₀ := ⟨s, hw, {
    zustand := fun _ => some z
    spur := fun _ => some label
    takt := fun t => .schritt rfl (step t) }⟩
  have konkret : Maschine.Laeufe E₀ h ρ := ⟨fair.hardware, fair.konform, admissible, rfl⟩
  have ready : KannSchreiten hw 0 entry z := ⟨0, opportunity 0, dispatch, live⟩
  have normal : (hw.angebot 0).crash = false := rfl
  have implSchritt : (E₀.system.regel ()).impl entry z () [plan] z := by
    change falsifizierbareImpl entry z () [falsifizierbarerPlan] z
    exact ⟨rfl, rfl⟩
  have exec : FuehrtSchrittAus e 0 entry z z plan ⟨[], []⟩ z := by
    simpa only [z', label] using execute 0 entry z
  refine ⟨s, z, z', z, plan, ⟨[], []⟩, ρ, admissible, rfl, rfl, rfl, rfl, rfl, rfl,
    konkret, rfl, rfl, rfl, rfl, implSchritt, exec, ready, normal⟩

/-! ### The per-form duty distinguishes a rule whose ideal side is empty -/

theorem regelSimDiskriminiert : RegelSimDiskriminiertAussage := by
  obtain ⟨s, z, z', u, plan, spur, ρ, zul, zStart, planEq, uEq, z'Eq, ρstart, ρhw, konkret,
    ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ := falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  have z'z : z' = z := by rw [z'Eq]; rfl
  subst z'
  let syRef : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbaresSystem with regel := fun _ => ⟨falsifizierbareImpl, fun _ _ _ _ _ => False⟩ }
  let ERef : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with system := syRef, stotterLaenge := fun _ => 0 }
  refine ⟨ERef, (), ?_⟩
  intro sim
  have folgerung := sim falsifizierbarerHw 0 falsifizierbarerEintrag () z z z
    z falsifizierbarerPlan ⟨[], []⟩ ⟨ProtokollBezug.refl z, rfl⟩ normal ready rfl implSchritt exec
  cases folgerung with
  | inl idealFolge =>
      obtain ⟨i', idealSchritt, _⟩ := idealFolge
      cases idealSchritt with
      | kontext _ _ regelIdeal _ =>
          simpa only [ERef, syRef] using regelIdeal
  | inr privat =>
      have ueberlauf : 0 < 0 := by
        simpa only [ERef] using privat.2.2.2.2
      exact (Nat.lt_irrefl 0 ueberlauf)

/-! ### The same real match and a stuttering ideal run separate `Sim` -/

theorem simTrennt : SimTrenntAussage := by
  obtain ⟨s, z, z', u, plan, spur, ρ, zul, zStart, planEq, uEq, z'Eq, ρstart, ρhw, konkret,
    ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ := falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  have z'z : z' = z := by rw [z'Eq]; rfl
  subst z'
  let syTrenn : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbaresSystem with
      regel := fun _ => ⟨falsifizierbareImpl,
        fun _ x _ plans v => plans = [falsifizierbarerPlan] ∧ v = x⟩ }
  let ETrenn : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with
      system := syTrenn
      lokalerBezug := fun l i => ∀ c, c ≠ falsifizierbarerEintrag → l c = i c
      stotterLaenge := fun _ => 0 }
  have initial : Zustandsbezug ETrenn z z := ⟨ProtokollBezug.refl z, fun _ _ => rfl⟩
  have final : Zustandsbezug ETrenn z z := initial
  have konform : falsifizierbarerHw.konform ETrenn.katalog falsifizierbareUmgebung := by
    rw [← ρhw]
    exact konkret.2.1
  have loaded : ETrenn.laden s (falsifizierbareUmgebung.lade ETrenn.bild) = some z := by
    change falsifizierbareEinheit.laden s (falsifizierbareUmgebung.lade falsifizierbaresBild) = some z
    rw [← ρstart]
    exact (ρz0.symm.trans konkret.2.2.2).symm
  have lastOpportunity : (letztesAngebot falsifizierbarerHw).gelegenheit 0 0 := by
    change falsifizierbarerHw.gelegenheit 0 0
    exact congrArg some (Nat.mod_one 0)
  have boot : s.bootCore = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ zul.2.1)
  have dispatchZ : (z.kerne 0).laeuft = some falsifizierbarerEintrag := by
    rw [← zStart]
    change (if 0 = s.bootCore then some falsifizierbarerEintrag else none) = some falsifizierbarerEintrag
    rw [boot, ite_eq_left rfl]
  have liveZ : z.status falsifizierbarerEintrag = .laeuft := by
    rw [← zStart]
    change (if falsifizierbarerEintrag = falsifizierbarerEintrag then Status.laeuft else Status.ruht) =
      (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have lastReady : KannSchreiten (letztesAngebot falsifizierbarerHw) 0 falsifizierbarerEintrag z :=
    ⟨0, lastOpportunity, dispatchZ, liveZ⟩
  have privateStep : ImplSchritt falsifizierbareEinrichtung syTrenn ETrenn.katalog
      (letztesAngebot falsifizierbarerHw) 0 z
      (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) z :=
    .kontext rfl lastReady ⟨(), rfl, rfl, rfl⟩ exec
  have execKeep : FuehrtSchrittAus falsifizierbareEinrichtung 0 falsifizierbarerEintrag z z
      falsifizierbarerPlan ⟨[], []⟩ z := by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun _ h => (List.not_mem_nil h).elim, [], z, .intern, .nil _, rfl⟩
  have idealStepKeep : Schritt falsifizierbareEinrichtung syTrenn ETrenn.katalog
      (letztesAngebot falsifizierbarerHw) 0 z
      (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) z :=
    .kontext rfl lastReady ⟨(), rfl, rfl, rfl⟩ execKeep
  have konformLetztes := falsifizierbares_letztesAngebot_konform konform
  let ρT : Maschine.Lauf ETrenn := ⟨s, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => some z
    spur := fun | 0 => some (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) | _ + 1 => none
    takt := fun
      | 0 => .schritt rfl (.schritt privateStep)
      | t + 1 => .wartet rfl rfl (falsifizierbares_letztesAngebot_konkret ETrenn t z) }⟩
  have runT : Maschine.Laeufe ETrenn falsifizierbareUmgebung ρT :=
    ⟨konkret.1, konformLetztes, zul, by
      change some z = ETrenn.laden s (falsifizierbareUmgebung.lade ETrenn.bild)
      exact loaded.symm⟩
  let η₂ : I.Lauf ETrenn := ⟨s, falsifizierbareUmgebung, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => z
    spur := fun _ => none
    takt := fun
      | 0 => .wartet rfl rfl (fun h => Bool.false_ne_true (normal.symm.trans h.2))
      | t + 1 => .wartet rfl rfl (fun h => Bool.false_ne_true h.2) },
    fun | 0 => some falsifizierbarerEintrag | _ + 1 => none⟩
  have valid₂ : Laeufe ETrenn η₂ := by
    refine ⟨konkret.1, konformLetztes, zul, rfl, ?_, ?_⟩
    · constructor
      · intro t still frei
        cases t with
        | zero =>
            change none = some (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) at still
            cases still
        | succ t => exact falsifizierbares_letztesAngebot_ideal ETrenn t z
      · intro endlich
        refine ⟨1, fun i after => ?_⟩
        cases i with
        | zero => exact (Nat.not_succ_le_zero _ after).elim
        | succ _ => rfl
    · intro t d mark
      cases t with
      | zero =>
          have deq : d = falsifizierbarerEintrag := Option.some.inj mark
          subst d
          exact ⟨rfl, lastReady⟩
      | succ _ => exact (Option.some_ne_none _ mark.symm).elim
  let η₁ : I.Lauf ETrenn := ⟨s, falsifizierbareUmgebung, letztesAngebot falsifizierbarerHw, {
    zustand := fun _ => z
    spur := fun | 0 => some (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) | _ + 1 => none
    takt := fun
      | 0 => .schritt rfl idealStepKeep
      | t + 1 => .wartet rfl rfl (fun h => Bool.false_ne_true h.2) },
    fun _ => none⟩
  have valid₁ : Laeufe ETrenn η₁ := by
    refine ⟨konkret.1, konformLetztes, zul, rfl, ?_, ?_⟩
    · constructor
      · intro t still frei
        cases t with
        | zero =>
            change none = some (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) at still
            cases still
        | succ t => exact falsifizierbares_letztesAngebot_ideal ETrenn t z
      · intro endlich
        exact ⟨0, fun _ _ => rfl⟩
    · intro t d mark
      cases mark
  have matched₁ : Laufabgleich ρT η₁ := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t
      exact ⟨z, rfl, initial⟩
    · intro t
      cases t with
      | zero => exact .schritt rfl
      | succ _ => exact .pause
    · intro t
      cases t with
      | zero =>
          refine ⟨fun _ => Or.inr ?_, fun _ => rfl⟩
          change some (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) ≠ none
          exact Option.some_ne_none _
      | succ _ => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    · intro t d mark
      cases mark
  have authorityT : ∀ t, BerechtigungAmTakt ρT t := by
    intro t a b c w sp u p ha hb hspur hcrash hready himpl hex
    cases t with
    | zero =>
        change some (.kontext falsifizierbarerEintrag (), ⟨[], []⟩) = some (.kontext c w, sp) at hspur
        have eq := Option.some.inj hspur
        cases eq
        obtain ⟨hp, _⟩ := himpl
        cases (List.cons.inj hp).1
        exact falsifizierbarerPlan_autorisiert a c
    | succ t =>
        change none = some (.kontext c w, sp) at hspur
        cases hspur
  have continuationT : ∀ a i, Zustandsbezug ETrenn a i → FortsetzungsBezug ETrenn a i := by
    intro a i related c
    exact ⟨congrFun (congrArg Zustand.status related.1) c, Iff.rfl, fun _ => Iff.rfl⟩
  have simη₁ : Sim ETrenn ρT η₁ :=
    matched₁.sim valid₁ (StotterSchranke.ohne_stottern (fun _ => rfl)) authorityT continuationT
  have interval₂ : Stotterintervall η₂ falsifizierbarerEintrag () 0 1 := by
    intro t lower upper
    have ht : t = 0 := by omega
    subst t
    refine ⟨rfl, ?_, ?_⟩
    · intro w sp h
      exact (Option.some_ne_none _ h.symm).elim
    · intro h
      exact (Option.some_ne_none _ h.symm).elim
  have ueberlauf₂ : ETrenn.stotterLaenge () <
      zaehle (fun t => decide (η₂.belegt t = some falsifizierbarerEintrag)) 0 1 := by
    change 0 < zaehle (fun t => decide (η₂.belegt t = some falsifizierbarerEintrag)) 0 1
    simpa only [zaehle, Nat.zero_add] using Nat.zero_lt_one
  have notSim₂ : ¬ Sim ETrenn ρT η₂ := nicht_sim_bei_stotterueberlauf interval₂ ueberlauf₂
  exact ⟨ETrenn, ρT, η₁, η₂, valid₁, simη₁, valid₂, notSim₂⟩

/-! ### The empty ideal rule refutes every ideal run of a concrete implementation run -/

theorem simRefutierbar : SimRefutierbarAussage := by
  obtain ⟨s, z, z', u, plan, spur, ρ, zul, zStart, planEq, uEq, z'Eq, ρstart, ρhw, konkret,
    ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ := falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  have z'z : z' = z := by rw [z'Eq]; rfl
  subst z'
  let syRef : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbaresSystem with regel := fun _ => ⟨falsifizierbareImpl, fun _ _ _ _ _ => False⟩ }
  let ERef : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with system := syRef, stotterLaenge := fun _ => 0 }
  refine ⟨ERef, falsifizierbareUmgebung, ρ, ?_, ?_⟩
  · change Maschine.Laeufe falsifizierbareEinheit falsifizierbareUmgebung ρ
    exact konkret
  · intro η validη simη
    rcases simη with ⟨_, matched, bound, _⟩
    have matchSpur := matched.spur 0
    cases matchSpur with
    | privat c w =>
        have ηspur0 : η.zeit.spur 0 = none := by
          rfl
        have ηbelegt : η.belegt 0 ≠ none := by
          intro leer
          have alternatives := (matched.frei 0).mp leer
          cases alternatives with
          | inl ρleer =>
              exact (Option.some_ne_none _ (ρspur0.symm.trans ρleer)).elim
          | inr ηaktiv => exact ηaktiv ηspur0
        cases hmark : η.belegt 0 with
        | none => exact (ηbelegt hmark).elim
        | some d =>
            obtain ⟨w', f, ρspurPrivat, headF⟩ := matched.belegt 0 d hmark
            have eq := Option.some.inj (ρspurPrivat.symm.trans ρspur0)
            cases eq
            have interval : Stotterintervall η falsifizierbarerEintrag f 0 1 := by
              intro t lower upper
              have ht : t = 0 := by omega
              subst t
              refine ⟨headF, ?_, ?_⟩
              · intro w s h
                exact (Option.some_ne_none _ (h.symm.trans ηspur0)).elim
              · intro h
                exact (Option.some_ne_none _ (h.symm.trans ηspur0)).elim
            have ueberlauf : ERef.stotterLaenge f <
                zaehle (fun t => decide (η.belegt t = some falsifizierbarerEintrag)) 0 1 := by
              change 0 < zaehle (fun t => decide (η.belegt t = some falsifizierbarerEintrag)) 0 1
              simpa only [zaehle, Nat.zero_add, decide_eq_true hmark, ite_true] using Nat.zero_lt_one
            exact nicht_sim_bei_stotterueberlauf interval ueberlauf
    | schritt event =>
        have etakt := η.zeit.takt 0
        have hηevent : η.zeit.spur 0 = some event := by
          rfl
        rw [hηevent] at etakt
        cases etakt with
        | schritt labelEq idealSchritt =>
            cases idealSchritt with
            | kontext _ _ regelIdeal _ =>
                simpa only [ERef, syRef] using regelIdeal

end Gabbro.Core.Ziel.Korrektheit
