/-
  File:      core/Core/Ast/Semantik/Runtime/ZugriffSicher/Induktion.lean
  Subject:   THE SAFETY INDUCTION WITHOUT THE PER-STEP RACE LEG. `sicherheit_aus_regeln`
              (`Sicherheit/Lauf`) derives the four run-level safety legs from a per-form duty
              `RegelPflichten`, whose `RegelSicher.rennen` leg quantifies over EVERY pre-state. A
              plain store has no such leg: a pre-state with an unordered conflicting write is a
              model state the machine can reach, so no per-form theorem can close it. For the
              fragments of a source unit the race is instead a RUN invariant, carried by the
              induction (`RennenImGraph` at every cut). This module splits `SchrittSicherheit`
              into the five legs that remain per-form and the race leg, and reruns the induction
              with the race supplied from outside. The class-determined legs of an access command
              then close the five; the one-context argument of `RennenBein` closes the sixth.
              Nothing here changes a pinned statement or weakens a guarantee: the original
              induction keeps its theorem, and this one asks for strictly more information at
              the run level in exchange for strictly less at the step level.
-/
module

public import Core.Sicherheit.Lauf

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
variable {H : Umgebung} {ρ : Lauf E}

/-- The five legs of `SchrittSicherheit` that a form must discharge on its own. The race leg
    (`RennenImGraph vor.graph → RennenImGraph nach.graph`) is NOT among them: it is carried along
    the run instead. -/
structure SchrittSicherheitOhneRennen (H : Umgebung) (ρ : Lauf E) (t : Nat)
    (vor nach : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert) : Prop where
  speicher : ZugriffGebucht vor nach spur ∧
    ∃ neu, NeueWirkungen vor nach spur neu ∧ FreigabenGueltig vor nach ρ.hw t spur neu
  invarianten : InvariantenAmSchnitt E vor → InvariantenAmSchnitt E nach
  sperrwechsel : ¬ Absturz spur → InvariantenBeimWechsel E vor nach
  register : RegisterImSchritt ρ.hw t vor spur nach
  toctou : CommitImSchritt E H ρ t vor spur nach

/-- Forget the race leg of a full step certificate. -/
theorem SchrittSicherheit.ohneRennen (voll : SchrittSicherheit E H ρ t vor nach spur) :
    SchrittSicherheitOhneRennen H ρ t vor nach spur :=
  ⟨voll.speicher, voll.invarianten, voll.sperrwechsel, voll.register, voll.toctou⟩

/-- Restore the race leg from a run-level fact about the successor state. -/
theorem SchrittSicherheitOhneRennen.mitRennen
    (fünf : SchrittSicherheitOhneRennen H ρ t vor nach spur)
    (rennen : RennenImGraph nach.graph) : SchrittSicherheit E H ρ t vor nach spur :=
  ⟨fünf.speicher, fünf.invarianten, fünf.sperrwechsel, fun _ => rennen, fünf.register, fünf.toctou⟩

/-- The per-form duty without the race leg. -/
def RegelSicherOhneRennen (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (f : Form) : Prop :=
  ∀ (H : Umgebung) (ρ : Lauf E) (t : Nat) (c : Kontext) (w : Wahl) (vor zwischen nach : Zustand L Ort Wert Raum Lok Grund)
    (plan : SchrittPlan L Ort Wert Bedingung) (spur : SchrittSpur Ort Wert),
    E.maschine.system.kopf vor c = some f →
    (E.maschine.system.regel f).impl c vor w [plan] zwischen →
    FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach →
    SchrittSicherheitOhneRennen H ρ t vor nach spur

/-- The pending-authority duty and the five legs together. -/
def RegelPflichtenOhneRennen (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (f : Form) : Prop :=
  RegelSicherOhneRennen E f ∧ RegelAntwortSicher E f

/-- The induction cut without the race component. -/
private def SchnittOhneRennen (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  InvariantenAmSchnitt E s ∧ FragenVor t s ∧ OffeneFragenBefugt s

private theorem impl_sicher_ohne_rennen (grenzen : GrenzenSicher E)
    (regeln : ∀ f, RegelPflichtenOhneRennen E f)
    (lauf : Maschine.Laeufe E.maschine H ρ)
    {t wspur vor nach}
    (h : ImplSchritt E.maschine.einrichtung E.maschine.system E.maschine.katalog ρ.hw t vor wspur nach)
    (vorher : SchnittOhneRennen E t vor) :
    SchrittSicherheitOhneRennen H ρ t vor nach wspur.2 ∧ SchnittOhneRennen E (t + 1) nach := by
  have sicher : SchrittSicherheitOhneRennen H ρ t vor nach wspur.2 ∧
      FragenVor (t + 1) nach ∧ OffeneFragenBefugt nach := by
    cases h with
    | kontext _ _ regel aus =>
      obtain ⟨f, kopf, impl⟩ := regel
      obtain ⟨schritt, antwort⟩ := (regeln f)
      exact ⟨schritt H ρ _ _ _ _ _ _ _ _ kopf impl aus, kontext_fragen_vor aus vorher.2.1,
        antwort _ _ _ _ _ _ _ _ kopf impl aus vorher.2.2⟩
    | antwort _ schritt =>
      have voll := antwort_sicher grenzen lauf.1 lauf.2.1.1 schritt vorher.2.1 vorher.2.2
      exact ⟨voll.1.ohneRennen, voll.2.1, voll.2.2⟩
    | interrupt _ schritt =>
      have voll := interrupt_sicher (H := H) grenzen schritt vorher.2.1 vorher.2.2
      exact ⟨voll.1.ohneRennen, voll.2.1, voll.2.2⟩
    | absturz schritt =>
      have voll := absturz_sicher (H := H) grenzen schritt vorher.2.1
      exact ⟨voll.1.ohneRennen, voll.2.1, voll.2.2⟩
  exact ⟨sicher.1, sicher.1.invarianten vorher.1, sicher.2.1, sicher.2.2⟩

/-- The four safety legs from per-form duties without the race leg and a run-level race
    invariant. The loader, answer, interrupt and restart boundaries keep their original
    certificates; only the per-form `rennen` obligation is replaced. -/
theorem sicherheit_aus_regeln_ohne_rennen (grenzen : GrenzenSicher E)
    (regeln : ∀ f, RegelPflichtenOhneRennen E f) :
    ∀ (H : Umgebung) (ρ : Lauf E),
      (∀ (t : Nat) s, ρ.zeit.zustand t = some s → RennenImGraph s.graph) →
      Maschine.Laeufe E.maschine H ρ →
      Speichersicher E H ρ ∧ InvariantenErhalten E H ρ ∧ Rennfrei E H ρ ∧ ToctouFrei E H ρ := by
  intro H ρ rennen lauf
  have geladen {s} (anfang : ρ.zeit.zustand 0 = some s) :=
    grenzen.laden H ρ.start s lauf.1 lauf.2.2.1 (lauf.2.2.2.symm.trans anfang)
  have schnitte (t : Nat) : ∀ s, ρ.zeit.zustand t = some s → SchnittOhneRennen E t s := by
    induction t with
    | zero =>
      intro s anfang
      obtain ⟨ereignisse, _, fragen, invariant⟩ := geladen anfang
      exact ⟨invariant, fragen_leer fragen⟩
    | succ t ih =>
      intro s nachher
      cases ρ.zeit.takt t with
      | wartet _label gleich _pause =>
        have vorher := ih s (gleich.symm.trans nachher)
        exact ⟨vorher.1, fun q mem => Nat.lt_succ_of_lt (vorher.2.1 q mem), vorher.2.2⟩
      | schritt _label step =>
        rw [nachher] at step
        cases vorher : ρ.zeit.zustand t with
        | none =>
          rw [vorher] at step
          cases step
        | some vor =>
          rw [vorher] at step
          cases step with
          | schritt h => exact (impl_sicher_ohne_rennen grenzen regeln lauf h (ih vor vorher)).2
  have uebergaenge (t vor spur nach) (h : Uebergang E ρ t vor spur nach) :
      SchrittSicherheit E H ρ t vor nach spur := by
    obtain ⟨vorher, ⟨w, label⟩, nachher⟩ := h
    have takt := ρ.zeit.takt t
    rw [vorher, label, nachher] at takt
    cases takt with
    | wartet impossible _ _ => cases impossible
    | schritt gleich step =>
      cases Option.some.inj gleich
      cases step with
      | schritt h =>
        exact (impl_sicher_ohne_rennen grenzen regeln lauf h (schnitte t vor vorher)).1.mitRennen
          (rennen (t + 1) nach nachher)
  exact ⟨⟨fun _ h => ⟨(geladen h).1, (geladen h).2.1⟩, fun t vor spur nach h => (uebergaenge t vor spur nach h).speicher⟩,
    ⟨fun t s h => (schnitte t.val s h).1, fun t vor spur nach h => (uebergaenge t vor spur nach h).sperrwechsel⟩,
    ⟨fun t s h => rennen t.val s h, fun t vor spur nach h => (uebergaenge t vor spur nach h).register⟩,
    ⟨fun _ h => (geladen h).2.1, fun t vor spur nach h => (uebergaenge t vor spur nach h).toctou⟩⟩

end Gabbro.Core.Sicherheit
