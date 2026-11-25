module

public import Core.Verfeinerung.Abnahme.StotterMass
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ziel.Korrektheit.Beweise.FalsifizierbarBasis

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog
open Gabbro.Core.Ast.Semantik (Regeleinheit)
open Gabbro.Core.Ziel.Korrektheit

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- The stutter duty is satisfiable by a declared unit: the one-form unit of a
    class has zero stutter length, so the per-form bound holds without any
    caller-supplied choice. -/
theorem RegelStotterSchranke.erfuellbar :
    ∃ (platform : Plattform) (f : _root_.Unit),
      RegelStotterSchranke (Regeleinheit platform
        ⟨fun _ _ _ _ _ => False, fun _ _ _ _ _ => False⟩) f := by
  refine ⟨.x86_64, (), ?_⟩
  exact RegelStotterSchranke.null rfl

/-- The stutter duty is not trivial: a unit with length one and a matched pair
    of runs whose ideal run pauses through two private ticks spends two units
    in one stutter interval, so the bound fails. The same overflow is what
    `nicht_sim_bei_stotterueberlauf` excludes from `Sim`. -/
theorem RegelStotterSchranke.nichtTrivial :
    ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (f : Unit),
      ¬ RegelStotterSchranke E f := by
  obtain ⟨s, z, z', u, plan, spur, ρ, admissible, zStart, planEq, uEq, z'Eq, ρstart, ρhw,
    konkret, ρspur0, spurEq, ρz0, ρz1, implSchritt, exec, ready, normal⟩ :=
    falsifizierbar_konfiguration
  subst u
  subst plan
  subst spur
  let E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { falsifizierbareEinheit with stotterLaenge := fun _ => 1 }
  let entry := falsifizierbarerEintrag
  let label : SchrittWahl Unit × SchrittSpur Unit Unit := (.kontext entry (), ⟨[], []⟩)
  have fair : FairLaeufe E.katalog falsifizierbareUmgebung falsifizierbarerHw := by
    change FairLaeufe Plattform.x86_64.katalog
      (Umgebung.referenz Plattform.x86_64.katalog 1 falsifizierbareSicht)
      (Umgebung.referenzLauf Plattform.x86_64.katalog 1 falsifizierbareSicht)
    exact Umgebung.referenz_fair _ 1 _ Plattform.x86_64.katalog_wohlgeformt (Nat.zero_lt_succ _)
  have hwValid : falsifizierbarerHw.konform E.katalog falsifizierbareUmgebung := fair.konform
  have hardware : Hardware E.katalog falsifizierbareUmgebung := by
    simpa only [E] using konkret.1
  let hw2 : HwLauf := ⟨(fun
    | 0 => falsifizierbarerHw.angebot 0
    | 1 => falsifizierbarerHw.angebot 1
    | t + 2 => (letztesAngebot falsifizierbarerHw).angebot (t + 2)), falsifizierbarerHw.politik⟩
  have hw2konform : hw2.konform E.katalog falsifizierbareUmgebung := by
    refine ⟨hwValid.1, fun i => ?_⟩
    cases i with
    | zero =>
      have g := hwValid.2 0
      unfold AngebotGueltig at g ⊢
      rcases g with ⟨g1, g2, _, g4, g5⟩
      refine ⟨g1, g2, ?_, g4, g5⟩
      intro sig mem
      have empty : False := by
        simpa only [hw2, falsifizierbarerHw, Umgebung.referenzLauf, List.not_mem_nil] using mem
      exact False.elim empty
    | succ i =>
      cases i with
      | zero =>
        have g := hwValid.2 1
        unfold AngebotGueltig at g ⊢
        rcases g with ⟨g1, g2, _, g4, g5⟩
        refine ⟨g1, g2, ?_, g4, g5⟩
        intro sig mem
        have empty : False := by
          simpa only [hw2, falsifizierbarerHw, Umgebung.referenzLauf, List.not_mem_nil] using mem
        exact False.elim empty
      | succ i =>
        exact ⟨fun _ h => (Option.some_ne_none _ h.symm).elim,
          fun _ h => (Bool.false_ne_true h).elim,
          fun _ h => (List.not_mem_nil h).elim,
          fun _ h => (Bool.false_ne_true h).elim,
          fun h => (h.elim Bool.false_ne_true Bool.false_ne_true).elim⟩
  have boot : s.bootCore = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ admissible.2.1)
  have zStartE : (start E s).2 = z := by
    change (start falsifizierbareEinheit s).2 = z
    exact zStart
  have dispatch : (z.kerne 0).laeuft = some entry := by
    rw [← zStart]
    change (if 0 = s.bootCore then some entry else none) = some entry
    rw [boot, ite_eq_left rfl]
  have live : z.status entry = .laeuft := by
    rw [← zStart]
    change (if entry = entry then Status.laeuft else Status.ruht) = (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have ready0 : KannSchreiten hw2 0 entry z := by
    rcases ready with ⟨k, opp, disp, stat⟩
    exact ⟨k, by change (falsifizierbarerHw.angebot 0).core = some k; exact opp, disp, stat⟩
  have ready1 : KannSchreiten hw2 1 entry z := by
    refine ⟨0, ?_, dispatch, live⟩
    change some (1 % 1) = some 0
    simp only [Nat.mod_one]
  have normal0 : (hw2.angebot 0).crash = false := rfl
  have normal1 : (hw2.angebot 1).crash = false := rfl
  have execAt (t : Nat) : FuehrtSchrittAus E.einrichtung t entry z z falsifizierbarerPlan
      ⟨[], []⟩ z := by
    change FuehrtSchrittAus falsifizierbareEinrichtung t falsifizierbarerEintrag z z
      falsifizierbarerPlan ⟨[], []⟩ z
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun _ h => (List.not_mem_nil h).elim, [], z, .intern, .nil _, rfl⟩
  have privateStep0 : ImplSchritt E.einrichtung E.system E.katalog hw2 0 z label z :=
    .kontext normal0 ready0 ⟨(), rfl, rfl, rfl⟩ (execAt 0)
  have privateStep1 : ImplSchritt E.einrichtung E.system E.katalog hw2 1 z label z :=
    .kontext normal1 ready1 ⟨(), rfl, rfl, rfl⟩ (execAt 1)
  let ρ' : Maschine.Lauf E := ⟨s, hw2, {
    zustand := fun _ => some z
    spur := fun
      | 0 => some label
      | 1 => some label
      | _ + 2 => none
    takt := fun
      | 0 => .schritt rfl (.schritt privateStep0)
      | 1 => .schritt rfl (.schritt privateStep1)
      | t + 2 => .wartet rfl rfl (by
        intro event next step
        cases step with
        | schritt step =>
          cases step with
          | kontext _ getreten _ _ =>
            obtain ⟨_, angeboten, _, _⟩ := getreten
            exact Option.some_ne_none _ angeboten.symm
          | antwort _ arrives =>
            have received := arrives.1.2.1.1
            rw [arrives.1.1] at received
            exact Bool.false_ne_true received
          | interrupt _ enters =>
            obtain ⟨_, _, _, _, angeboten, _⟩ := enters
            exact Bool.false_ne_true angeboten
          | absturz crash => exact Bool.false_ne_true crash.1.2) }⟩
  have run' : Maschine.Laeufe E falsifizierbareUmgebung ρ' := by
    refine ⟨hardware, hw2konform, admissible, ?_⟩
    have init := konkret.2.2.2
    rw [ρstart, ρz0] at init
    change some z = E.laden s (falsifizierbareUmgebung.lade E.bild)
    simpa only [E] using init
  let η : Lauf E := ⟨s, falsifizierbareUmgebung, hw2, {
    zustand := fun _ => z
    spur := fun _ => none
    takt := fun
      | 0 => .wartet rfl rfl (fun h => Bool.false_ne_true (normal0.symm.trans h.2))
      | 1 => .wartet rfl rfl (fun h => Bool.false_ne_true (normal1.symm.trans h.2))
      | t + 2 => .wartet rfl rfl (fun h => by
        rcases h with ⟨_, hcrash⟩
        have : (hw2.angebot (t + 2)).crash = false := rfl
        rw [this] at hcrash
        exact Bool.false_ne_true hcrash) },
    fun
      | 0 => some entry
      | 1 => some entry
      | _ + 2 => none⟩
  have validη : Laeufe E η := by
    refine ⟨hardware, hw2konform, admissible, ?_, ?_, ?_⟩
    · change z = (start E s).2
      exact zStartE.symm
    · refine ⟨?_, ?_⟩
      · intro t still frei
        cases t with
        | zero => change some entry = none at frei; cases frei
        | succ t =>
          cases t with
          | zero => change some entry = none at frei; cases frei
          | succ t =>
            intro event next step
            cases step with
            | kontext _ getreten _ _ =>
              obtain ⟨_, angeboten, _, _⟩ := getreten
              exact Option.some_ne_none _ angeboten.symm
            | antwort _ arrives =>
              have received := arrives.1.2.1.1
              rw [arrives.1.1] at received
              exact Bool.false_ne_true received
            | interrupt _ enters =>
              obtain ⟨_, _, _, _, angeboten, _⟩ := enters
              exact Bool.false_ne_true angeboten
            | absturz crash => exact Bool.false_ne_true crash.1.2
      · intro endlich
        refine ⟨2, fun i after => ?_⟩
        cases i with
        | zero => omega
        | succ i => cases i with | zero => omega | succ i => rfl
    · intro t c mark
      cases t with
      | zero =>
        change some entry = some c at mark
        have hc : c = entry := Option.some.inj mark.symm
        subst c
        exact ⟨rfl, ready0⟩
      | succ t =>
        cases t with
        | zero =>
          change some entry = some c at mark
          have hc : c = entry := Option.some.inj mark.symm
          subst c
          exact ⟨rfl, ready1⟩
        | succ t => exact (Option.some_ne_none _ mark.symm).elim
  have ref : Zustandsbezug E z z := by
    refine ⟨ProtokollBezug.refl z, ?_⟩
    change Eq z.lokal z.lokal
    rfl
  have matched : Laufabgleich ρ' η := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t
      exact ⟨z, rfl, ref⟩
    · intro t
      cases t with
      | zero => exact .privat entry ()
      | succ t => cases t with | zero => exact .privat entry () | succ _ => exact .pause
    · intro t
      cases t with
      | zero =>
        constructor
        · intro h; change some entry = none at h; cases h
        · intro h
          rcases h with empty | visible
          · change some label = none at empty; cases empty
          · exact (visible rfl).elim
      | succ t =>
        cases t with
        | zero =>
          constructor
          · intro h; change some entry = none at h; cases h
          · intro h
            rcases h with empty | visible
            · change some label = none at empty; cases empty
            · exact (visible rfl).elim
        | succ _ =>
          constructor
          · intro _; exact Or.inl rfl
          · intro _; rfl
    · intro t d mark
      cases t with
      | zero =>
        change some entry = some d at mark
        have hd : d = entry := Option.some.inj mark.symm
        subst d
        exact ⟨(), (), rfl, rfl⟩
      | succ t =>
        cases t with
        | zero =>
          change some entry = some d at mark
          have hd : d = entry := Option.some.inj mark.symm
          subst d
          exact ⟨(), (), rfl, rfl⟩
        | succ t => exact (Option.some_ne_none _ mark.symm).elim
  have checked : BelegungGeprueft η := by
    intro t c g mark head
    cases t with
    | zero =>
      change some entry = some c at mark
      have hc : c = entry := Option.some.inj mark.symm
      subst c
      have hg : g = () := Option.some.inj (by simpa only [E] using head)
      subst g
      change 0 < (1 : Nat)
      omega
    | succ t =>
      cases t with
      | zero =>
        change some entry = some c at mark
        have hc : c = entry := Option.some.inj mark.symm
        subst c
        have hg : g = () := Option.some.inj (by simpa only [E] using head)
        subst g
        change 0 < (1 : Nat)
        omega
      | succ t => exact (Option.some_ne_none _ mark.symm).elim
  have interval : Stotterintervall η entry () 0 2 := by
    intro t lo hi
    have ht : t = 0 ∨ t = 1 := by omega
    rcases ht with rfl | rfl
    · refine ⟨rfl, ?_, ?_⟩
      · intro w sp h
        change none = some (SchrittWahl.kontext entry w, sp) at h
        cases h
      · intro h
        change none = some (SchrittWahl.absturz, absturzSpur) at h
        cases h
    · refine ⟨rfl, ?_, ?_⟩
      · intro w sp h
        change none = some (SchrittWahl.kontext entry w, sp) at h
        cases h
      · intro h
        change none = some (SchrittWahl.absturz, absturzSpur) at h
        cases h
  have m0 : η.belegt 0 = some entry := rfl
  have m1 : η.belegt 1 = some entry := rfl
  have ueberlauf : E.stotterLaenge () <
      zaehle (fun t => decide (η.belegt t = some entry)) 0 2 := by
    change 1 < zaehle (fun t => decide (η.belegt t = some entry)) 0 2
    simp only [zaehle, Nat.zero_add, decide_eq_true m0, decide_eq_true m1, ite_true]
    omega
  refine ⟨E, (), ?_⟩
  intro duty
  have bound := duty falsifizierbareUmgebung ρ' η run' matched checked entry 0 2 interval
  exact (Nat.not_lt_of_ge bound) ueberlauf

end Gabbro.Core.Maschine.I
