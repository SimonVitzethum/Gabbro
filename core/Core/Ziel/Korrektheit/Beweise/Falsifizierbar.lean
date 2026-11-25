/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Falsifizierbar.lean
  Subject:   THE THREE FALSIFIABILITY STATEMENTS of `Ziel/Korrektheit/Verfeinerung`: the per-form
             simulation duty is discriminating, the whole-run simulation separates ideal runs, and the
             refinement refuses an implementation run. Each statement is an existential over a unit, so
             the proofs construct ONE concrete one-form unit whose single form toggles a private local
             value at the last hardware opportunity.

             The unit is the same as in `Verfeinerung/Erfuellbar`: a private `.intern` step changes one
             boolean local state. Two rule variants give the two witnesses: the refusing variant makes
             the ideal rule empty, so no ideal run matches (the refinement is refuted and the duty
             discriminated); the tolerant variant keeps the ideal transition and hides the changed
             local value from the local relation, so the stutter bound alone decides the match. On a
             history whose only opportunity is tick zero, the tolerant variant with bound zero has one
             ideal run that replays the transition and one that spends the private tick, separating
             `Sim`. All three statements are proved; none of the pinned statements is changed.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Erfuellbar
public import Core.Verfeinerung.LetztesAngebot

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine Katalog
open Gabbro.Core.Maschine.I

/-! ### A concrete one-form unit with a single private toggle -/

def falsifizierbaresBild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def falsifizierbarerEintrag : Kontext := Kontext.faden 0

def falsifizierbareDaten (kern : Nat) : Startdaten Unit Unit Bool Unit :=
  ⟨fun _ => false, fun c => if c = falsifizierbarerEintrag then .laeuft else .ruht,
    fun j => ⟨if j = kern then some falsifizierbarerEintrag else none, .nutzer, (), fun _ => false, 0, false, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩

def falsifizierbareEinrichtung : Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
    fun _ _ => True, ⟨0, 1⟩,
    ⟨falsifizierbarerEintrag, 0, fun _ => falsifizierbareDaten 0, fun _ _ => ()⟩,
    fun _ => 0, fun _ _ _ => none⟩

def falsifizierbarerPlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def falsifizierbareAenderung (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) :=
  { s with lokal := Function.update s.lokal c (!s.lokal c) }

def falsifizierbareImpl (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (_ : Unit)
    (plans : List (SchrittPlan Unit Unit Unit Unit))
    (u : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  plans = [falsifizierbarerPlan] ∧ u = falsifizierbareAenderung c s

def falsifizierbaresSystem : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨falsifizierbareImpl, falsifizierbareImpl⟩, fun _ _ => some (),
    fun _ _ => False, fun _ _ _ => False⟩

def falsifizierbareEinheit : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
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
    (s : Zustand Unit Unit Unit Unit Bool Unit) (c : Kontext) :
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

theorem falsifizierbares_letztesAngebot_ideal {L Ort Wert Raum Lok Grund Bedingung Wahl F ι : Type}
    [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F ι)
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

/-! ### The concrete run and its one private step -/

theorem falsifizierbar_konfiguration :
    ∃ (s : AussenStart) (z z' u : Zustand Unit Unit Unit Unit Bool Unit)
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
      (falsifizierbarerHw.angebot 0).crash = false ∧
      z.lokal falsifizierbarerEintrag = false ∧ z'.lokal falsifizierbarerEintrag = true := by
  let E₀ := falsifizierbareEinheit
  let e := falsifizierbareEinrichtung
  let sy := falsifizierbaresSystem
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
  have execute (t : Nat) (c : Kontext) (x : Zustand Unit Unit Unit Unit Bool Unit) :
      FuehrtSchrittAus e t c x (falsifizierbareAenderung c x) plan label.2
        (falsifizierbareAenderung c x) := by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun _ hn => (List.not_mem_nil hn).elim, [], falsifizierbareAenderung c x, .intern, .nil _, rfl⟩
  let zustand (t : Nat) : Zustand Unit Unit Unit Unit Bool Unit :=
    Nat.rec z (fun _ => falsifizierbareAenderung entry) t
  have protocol (t : Nat) : (zustand t).kerne = z.kerne ∧ (zustand t).status = z.status := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih => exact ih
  have dispatch : (z.kerne 0).laeuft = some entry := by
    change (if 0 = s.bootCore then some entry else none) = some entry
    rw [boot, ite_eq_left rfl]
  have live : z.status entry = .laeuft := by
    change (if entry = entry then Status.laeuft else Status.ruht) = (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have opportunity (t : Nat) : hw.gelegenheit t 0 := congrArg some (Nat.mod_one _)
  have step (t : Nat) : Lauffolge E₀ hw t (some (zustand t)) label (some (zustand (t + 1))) :=
    .schritt (.kontext rfl
      ⟨0, opportunity t,
        (congrArg (fun cores => (cores 0).laeuft) (protocol t).1).trans dispatch,
        (congrFun (protocol t).2 entry).trans live⟩
      ⟨(), rfl, rfl, rfl⟩ (execute t entry (zustand t)))
  let ρ : Maschine.Lauf E₀ := ⟨s, hw, {
    zustand := fun t => some (zustand t)
    spur := fun _ => some label
    takt := fun t => .schritt rfl (step t) }⟩
  have konkret : Maschine.Laeufe E₀ h ρ := ⟨fair.hardware, fair.konform, admissible, rfl⟩
  have takt := ρ.zeit.takt 0
  change Takt (Lauffolge E₀ hw) 0 (some z) (some label) (some z') at takt
  cases takt with
  | schritt eq lauf =>
      cases lauf with
      | schritt impl =>
          cases impl with
          | kontext normal ready rule exec =>
              have eq' : label = (.kontext falsifizierbarerEintrag (), ⟨[], []⟩ : SchrittSpur Unit Unit) := rfl
              rw [eq'] at eq
              cases Option.some.inj eq
              obtain ⟨hp, hu⟩ := rule
              cases (List.cons.inj hp).1
              subst u
              refine ⟨s, z, z', z', plan, ⟨[], []⟩, ρ, admissible, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, konkret, rfl, rfl, rfl, rfl, ?_, ?_, ready, normal, rfl, rfl⟩
              · change falsifizierbareImpl falsifizierbarerEintrag z () [falsifizierbarerPlan] z'
                exact ⟨rfl, rfl⟩
              · simpa only [z'] using exec

end Gabbro.Core.Ziel.Korrektheit
