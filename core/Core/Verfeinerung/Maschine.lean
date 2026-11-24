module

public import Core.Verfeinerung.Lauf
public import Core.Verfeinerung.Protokoll

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]

abbrev LokalerBezug (Lok : Type) := (Kontext → Lok) → (Kontext → Lok) → Prop

/-- The machine protocol and the forms account for their respective parts of the state. -/
abbrev Zustandsbezug (lokal : LokalerBezug Lok) (s i : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ProtokollBezug s i ∧ lokal s.lokal i.lokal

/-- A private concrete step preserves the entire M4 trace and spends part of a
    finite private suffix. A matched step preserves the concrete trace verbatim. -/
inductive SpurAbgleich (vorher nachher : Nat) :
    Option (SchrittSpur Ort Wert) → Option (SchrittWahl Wahl × SchrittSpur Ort Wert) → Prop where
  | pause : SpurAbgleich vorher nachher none none
  | privat (sinkt : nachher < vorher) : SpurAbgleich vorher nachher (some ⟨[], []⟩) none
  | schritt (wahl : SchrittWahl Wahl) (spur : SchrittSpur Ort Wert) :
      SpurAbgleich vorher nachher (some spur) (some (wahl, spur))

variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

abbrev PrivatMass (L Ort Wert Raum Lok Grund : Type) :=
  Zustand L Ort Wert Raum Lok Grund → Zustand L Ort Wert Raum Lok Grund → Nat

/-- M4 obligations at the head of one context. A form either supplies its ideal
    step on the same tick or proves that this transition only advances private work.
    The private case requires that the ideal machine has no transition at this tick,
    which also ensures maximality when private work forms part of a finite tail. -/
def RegelAbgleich (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (lokal : LokalerBezug Lok) (mass : PrivatMass L Ort Wert Raum Lok Grund) (f : F) : Prop :=
  ∀ hw t c s u s' i plan spur, Zustandsbezug lokal s i →
    (hw.angebot t).crash = false → KannSchreiten hw t c s →
    E.system.kopf s c = some f → (E.system.regel f).impl c s [plan] u →
    FuehrtSchrittAus E.einrichtung t c s u plan spur s' →
    (∃ w i', Schritt E.einrichtung E.system E.katalog hw t i (.kontext c w, spur) i' ∧
      Zustandsbezug lokal s' i') ∨
    (spur = ⟨[], []⟩ ∧ Zustandsbezug lokal s' i ∧ mass s' i < mass s i ∧
      KeinSchritt (Schritt E.einrichtung E.system E.katalog hw) t i)

/-- Obligations for the M4 clock and trace match. If the concrete machine takes
    no step at an opportunity, the matched ideal state has no transition there. -/
structure AbgleichPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (lokal : LokalerBezug Lok) (mass : PrivatMass L Ort Wert Raum Lok Grund) : Prop where
  lokal_refl : ∀ l, lokal l l
  laden : ∀ h s, Hardware E.katalog h → E.ZulStart h s →
    ∃ z, E.laden s (h.lade E.bild) = some z ∧ Zustandsbezug lokal z (start E s).2
  regel : ∀ f, RegelAbgleich E lokal mass f
  pause : ∀ hw t s i, Zustandsbezug lokal s i → KeinSchritt (Lauffolge E hw) t (some s) →
    KeinSchritt (Schritt E.einrichtung E.system E.katalog hw) t i

variable {lokal : LokalerBezug Lok} {mass : PrivatMass L Ort Wert Raum Lok Grund}

theorem AbgleichPflichten.schritt (pflicht : AbgleichPflichten E lokal mass)
    {hw t s s' i spur} (bezug : Zustandsbezug lokal s i)
    (konkret : ImplSchritt E.einrichtung E.system E.katalog hw t s spur s') :
    ∃ r : Zustand L Ort Wert Raum Lok Grund × Option (SchrittWahl Wahl × SchrittSpur Ort Wert),
      Zustandsbezug lokal s' r.1 ∧
      Takt (Schritt E.einrichtung E.system E.katalog hw) (fun n _ => ¬ AbsturzAngeboten E.katalog hw n)
        t i r.2 r.1 ∧ SpurAbgleich (mass s i) (mass s' r.1) (some spur) r.2 ∧
      (r.2 = none → KeinSchritt (Schritt E.einrichtung E.system E.katalog hw) t i) := by
  cases konkret with
  | kontext normal ready rule execute =>
    obtain ⟨f, kopf, impl⟩ := rule
    rcases pflicht.regel f _ _ _ _ _ _ _ _ _ bezug normal ready kopf impl execute with step | privateStep
    · obtain ⟨w, i', step, related⟩ := step
      exact ⟨(i', some (.kontext _ w, _)), related, .schritt rfl step, .schritt _ _, fun h => nomatch h⟩
    · obtain ⟨rfl, related, decreases, stuck⟩ := privateStep
      exact ⟨(i, none), related, .wartet rfl rfl (fun offer => Bool.noConfusion (normal.symm.trans offer.2)),
        .privat decreases, fun _ => stuck⟩
  | antwort normal arrives =>
    obtain ⟨i', step, publicEq, sameLocal⟩ := bezug.1.antwort arrives
    refine ⟨(i', some (.antwort _, _)), ⟨publicEq, ?_⟩, .schritt rfl (.antwort normal step), .schritt _ _,
      fun h => nomatch h⟩
    rw [arrives.2.2.2, sameLocal]
    exact bezug.2
  | interrupt normal enters =>
    obtain ⟨i', step, publicEq, sameLocal⟩ := bezug.1.interrupt enters
    obtain ⟨_, _, _, _, _, _, _, _, _, _, state⟩ := enters
    refine ⟨(i', some (.interrupt _, _)), ⟨publicEq, ?_⟩, .schritt rfl (.interrupt normal step), .schritt _ _,
      fun h => nomatch h⟩
    rw [state, sameLocal]
    exact bezug.2
  | absturz crash =>
    exact ⟨(s', some (.absturz, _)), ⟨ProtokollBezug.refl s', pflicht.lokal_refl _⟩,
      .schritt rfl (.absturz (bezug.1.absturz crash)), .schritt _ _, fun h => nomatch h⟩

/-- A single ideal run has the same hardware and start, the related states at each
    tick, and exactly the recorded concrete events after private ticks are erased. -/
structure Laufabgleich (ρ : Maschine.Lauf E) (η : Lauf E) (lokal : LokalerBezug Lok)
    (mass : PrivatMass L Ort Wert Raum Lok Grund) : Prop where
  hardware : η.hw = ρ.hw
  start : η.start = ρ.start
  zustand : ∀ t, ∃ s, ρ.zeit.zustand t = some s ∧ Zustandsbezug lokal s (η.zeit.zustand t)
  spur : ∀ t, SpurAbgleich ((ρ.zeit.zustand t).elim 0 fun s => mass s (η.zeit.zustand t))
    ((ρ.zeit.zustand (t + 1)).elim 0 fun s => mass s (η.zeit.zustand (t + 1))) (ρ.zeit.spur t) (η.zeit.spur t)
  endlich : ρ.zeit.Endlich ↔ η.zeit.Endlich

theorem SpurAbgleich.gedeckt {prior later : Nat} {konkret : Option (SchrittSpur Ort Wert)}
    {ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (h : SpurAbgleich prior later konkret ideal) (pause : konkret = none) : ideal = none := by
  cases h with
  | pause => rfl
  | privat _ => cases pause
  | schritt _ _ => cases pause

theorem SpurAbgleich.sinkt {prior later : Nat} {konkret : Option (SchrittSpur Ort Wert)}
    {ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)} {event : SchrittSpur Ort Wert}
    (h : SpurAbgleich prior later konkret ideal) (privateTick : ideal = none) (step : konkret = some event) :
    later < prior := by
  cases h with
  | pause => cases step
  | privat decreases => exact decreases
  | schritt _ _ => cases privateTick

/-- Lift the local M4 obligations to one maximal ideal run over the given
    concrete run, with the canonical start and matching finite/infinite status. -/
theorem laufabgleich (pflicht : AbgleichPflichten E lokal mass)
    {h : Umgebung} {ρ : Maschine.Lauf E} (run : Maschine.Laeufe E h ρ) :
    ∃ η : Lauf E, Laeufe E η ∧ Laufabgleich ρ η lokal mass := by
  let bezug := fun (z : Option (Zustand L Ort Wert Raum Lok Grund)) i =>
    ∃ s, z = some s ∧ Zustandsbezug lokal s i
  let budget := fun (t : Nat) i => (ρ.zeit.zustand t).elim 0 fun s => mass s i
  let lokalTakt := fun t i (label : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)) i' =>
    SpurAbgleich (budget t i) (budget (t + 1) i') (ρ.zeit.spur t) label ∧
      (label = none → KeinSchritt (Schritt E.einrichtung E.system E.katalog ρ.hw) t i)
  obtain ⟨z, loaded, init⟩ := pflicht.laden h ρ.start run.1 run.2.2.1
  have folgt : Zeitlauf.Fortsetzung ρ.zeit bezug lokalTakt
      (Schritt E.einrichtung E.system E.katalog ρ.hw) (fun n _ => ¬ AbsturzAngeboten E.katalog ρ.hw n) := by
    rintro t i ⟨s, atCut, related⟩
    have tick := ρ.zeit.takt t
    rw [atCut] at tick
    cases tick with
    | schritt mark transition =>
      cases after : ρ.zeit.zustand (t + 1) with
      | none =>
        rw [after] at transition
        cases transition
      | some next =>
        rw [after] at transition
        cases transition with
        | schritt step =>
          obtain ⟨r, rel, idealTick, aligned, maximal⟩ := pflicht.schritt related step
          refine ⟨r, ⟨next, rfl, rel⟩, ⟨idealTick, fun empty => ?_⟩, ?_⟩
          · cases empty.symm.trans mark
          · refine ⟨?_, maximal⟩
            simpa only [budget, atCut, after, mark, Option.elim] using aligned
    | wartet mark after stuck =>
      have idealStuck := pflicht.pause _ _ _ _ related stuck
      have noCrash : ¬ AbsturzAngeboten E.katalog ρ.hw t :=
        fun offer => idealStuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer i))
      refine ⟨(i, none), ⟨s, after, related⟩,
        ⟨.wartet rfl rfl noCrash, fun _ => ⟨rfl, idealStuck⟩⟩, ?_, fun _ => idealStuck⟩
      rw [mark]
      exact .pause
  obtain ⟨ideal, idealStart, related, ticks⟩ := Zeitlauf.laufbild ρ.zeit bezug lokalTakt _
    ⟨z, run.2.2.2.trans loaded, init⟩ folgt
  have finite := Zeitlauf.endlich_iff (ρ := ρ.zeit) (η := ideal) (fun t no => (ticks t).2.1.gedeckt no)
    (fun t => budget t (ideal.zustand t))
    (fun t no => by
      have implSame := (ρ.zeit.wartet no).1
      have idealSame := (ideal.wartet ((ticks t).2.1.gedeckt no)).1
      simp only [budget, implSame, idealSame])
    (fun t _ no event => (ticks t).2.1.sinkt no event)
  have maximal : ideal.Maximal :=
    fun _ tail t after => (ticks t).2.2 (tail t after)
  exact ⟨⟨ρ.start, h, ρ.hw, ideal⟩, ⟨run.1, run.2.1, run.2.2.1, idealStart, maximal⟩,
    rfl, rfl, related, fun t => (ticks t).2.1, finite⟩

end Gabbro.Core.Maschine.I
