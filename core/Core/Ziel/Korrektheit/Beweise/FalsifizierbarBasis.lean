/-
  File:      core/Core/Ziel/Korrektheit/Beweise/FalsifizierbarBasis.lean
  Subject:   THE CONCRETE WITNESS for the three refinement falsifiability statements: a one-form unit
             whose single form takes a private `.intern` step on a hardware history with one
             opportunity, together with a maximal implementation run of it. The unit and the run are
             shared by `Falsifizierbar.lean`; the rule variants that falsify the statements are built
             there from this one construction.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Erfuellbar
public import Core.Verfeinerung.LetztesAngebot

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine Katalog
open Gabbro.Core.Maschine.I



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
    Eq, (fun _ => 1), .leer, eineTabelle, .leer, .leer, .leer⟩

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
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
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

end Gabbro.Core.Ziel.Korrektheit
