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
    Option (SchrittWahl Wahl × SchrittSpur Ort Wert) → Option (SchrittWahl Wahl × SchrittSpur Ort Wert) → Prop where
  | pause : SpurAbgleich vorher nachher none none
  | privat (c : Kontext) (w : Wahl) (sinkt : nachher < vorher) :
      SpurAbgleich vorher nachher (some (.kontext c w, ⟨[], []⟩)) none
  | schritt (event : SchrittWahl Wahl × SchrittSpur Ort Wert) :
      SpurAbgleich vorher nachher (some event) (some event)

variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

abbrev PrivatMass (L Ort Wert Raum Lok Grund : Type) :=
  Zustand L Ort Wert Raum Lok Grund → Zustand L Ort Wert Raum Lok Grund → Nat

/-- M4 obligations at the head of one context. A form either supplies its ideal
    step on the same tick or proves that this transition only advances private work. -/
def RegelAbgleich (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (lokal : LokalerBezug Lok) (mass : PrivatMass L Ort Wert Raum Lok Grund) (f : F) : Prop :=
  ∀ hw t c w s u s' i plan spur, Zustandsbezug lokal s i →
    (hw.angebot t).crash = false → KannSchreiten hw t c s →
    E.system.kopf s c = some f → (E.system.regel f).impl c s w [plan] u →
    FuehrtSchrittAus E.einrichtung t c s u plan spur s' →
    (∃ i', Schritt E.einrichtung E.system E.katalog hw t i (.kontext c w, spur) i' ∧
      Zustandsbezug lokal s' i') ∨
    (spur = ⟨[], []⟩ ∧ Zustandsbezug lokal s' i ∧ mass s' i < mass s i)

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
      (r.2 = none → ∃ c w, spur = (.kontext c w, ⟨[], []⟩) ∧ KannSchreiten hw t c i) := by
  cases konkret with
  | kontext normal ready rule execute =>
    obtain ⟨f, kopf, impl⟩ := rule
    rcases pflicht.regel f _ _ _ _ _ _ _ _ _ _ bezug normal ready kopf impl execute with step | privateStep
    · obtain ⟨i', step, related⟩ := step
      exact ⟨(i', some _), related, .schritt rfl step, .schritt _, fun h => nomatch h⟩
    · obtain ⟨rfl, related, decreases⟩ := privateStep
      have shared := bezug.1
      change { s with lokal := i.lokal } = i at shared
      have idealReady {c} (h : KannSchreiten hw t c s) : KannSchreiten hw t c i := by
        rw [← shared]
        exact h
      exact ⟨(i, none), related, .wartet rfl rfl (fun offer => Bool.noConfusion (normal.symm.trans offer.2)),
        .privat _ _ decreases, fun _ => ⟨_, _, rfl, idealReady ready⟩⟩
  | antwort normal arrives =>
    obtain ⟨i', step, publicEq, sameLocal⟩ := bezug.1.antwort arrives
    refine ⟨(i', some (.antwort _, _)), ⟨publicEq, ?_⟩, .schritt rfl (.antwort normal step), .schritt _,
      fun h => nomatch h⟩
    rw [arrives.2.2.2, sameLocal]
    exact bezug.2
  | interrupt normal enters =>
    obtain ⟨i', step, publicEq, sameLocal⟩ := bezug.1.interrupt enters
    obtain ⟨_, _, _, _, _, _, _, _, _, _, state⟩ := enters
    refine ⟨(i', some (.interrupt _, _)), ⟨publicEq, ?_⟩, .schritt rfl (.interrupt normal step), .schritt _,
      fun h => nomatch h⟩
    rw [state, sameLocal]
    exact bezug.2
  | absturz crash =>
    exact ⟨(s', some (.absturz, _)), ⟨ProtokollBezug.refl s', pflicht.lokal_refl _⟩,
      .schritt rfl (.absturz (bezug.1.absturz crash)), .schritt _, fun h => nomatch h⟩

/-- A single ideal run has the same hardware and start, the related states at each
    tick, and exactly the recorded concrete events after private ticks are erased. -/
structure Laufabgleich (ρ : Maschine.Lauf E) (η : Lauf E) (lokal : LokalerBezug Lok)
    (mass : PrivatMass L Ort Wert Raum Lok Grund) : Prop where
  hardware : η.hw = ρ.hw
  start : η.start = ρ.start
  zustand : ∀ t, ∃ s, ρ.zeit.zustand t = some s ∧ Zustandsbezug lokal s (η.zeit.zustand t)
  spur : ∀ t, SpurAbgleich ((ρ.zeit.zustand t).elim 0 fun s => mass s (η.zeit.zustand t))
    ((ρ.zeit.zustand (t + 1)).elim 0 fun s => mass s (η.zeit.zustand (t + 1))) (ρ.zeit.spur t) (η.zeit.spur t)
  frei : ∀ t, η.belegt t = none ↔ ρ.zeit.spur t = none ∨ η.zeit.spur t ≠ none
  belegt : ∀ t c, η.belegt t = some c → ∃ w, ρ.zeit.spur t = some (.kontext c w, ⟨[], []⟩)
  endlich : ρ.zeit.Endlich ↔ η.zeit.Endlich

theorem SpurAbgleich.gedeckt {prior later : Nat} {konkret : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    {ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (h : SpurAbgleich prior later konkret ideal) (pause : konkret = none) : ideal = none := by
  cases h with
  | pause => rfl
  | privat _ _ _ => cases pause
  | schritt _ => cases pause

theorem SpurAbgleich.sinkt {prior later : Nat} {konkret ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    {event : SchrittWahl Wahl × SchrittSpur Ort Wert}
    (h : SpurAbgleich prior later konkret ideal) (privateTick : ideal = none) (step : konkret = some event) :
    later < prior := by
  cases h with
  | pause => cases step
  | privat _ _ decreases => exact decreases
  | schritt _ => cases privateTick

/-- Lift the local M4 obligations to one maximal ideal run over the given
    concrete run, with the canonical start and matching finite/infinite status. -/
theorem laufabgleich (pflicht : AbgleichPflichten E lokal mass)
    {h : Umgebung} {ρ : Maschine.Lauf E} (run : Maschine.Laeufe E h ρ) :
    ∃ η : Lauf E, Laeufe E η ∧ Laufabgleich ρ η lokal mass := by
  classical
  let bezug := fun (z : Option (Zustand L Ort Wert Raum Lok Grund)) i =>
    ∃ s, z = some s ∧ Zustandsbezug lokal s i
  let budget := fun (t : Nat) i => (ρ.zeit.zustand t).elim 0 fun s => mass s i
  let lokalTakt := fun t i (label : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)) i' =>
    SpurAbgleich (budget t i) (budget (t + 1) i') (ρ.zeit.spur t) label ∧
      (ρ.zeit.spur t ≠ none → label = none →
        ∃ c w, ρ.zeit.spur t = some (.kontext c w, ⟨[], []⟩) ∧ KannSchreiten ρ.hw t c i)
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
          obtain ⟨r, rel, idealTick, aligned, privateTick⟩ := pflicht.schritt related step
          refine ⟨r, ⟨next, rfl, rel⟩, ⟨idealTick, fun empty => ?_⟩, ?_⟩
          · cases empty.symm.trans mark
          · constructor
            · simpa only [budget, atCut, after, mark, Option.elim] using aligned
            · intro _ idle
              obtain ⟨c, w, named, ready⟩ := privateTick idle
              exact ⟨c, w, mark.trans (congrArg some named), ready⟩
    | wartet mark after stuck =>
      have idealStuck := pflicht.pause _ _ _ _ related stuck
      have noCrash : ¬ AbsturzAngeboten E.katalog ρ.hw t :=
        fun offer => idealStuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer i))
      refine ⟨(i, none), ⟨s, after, related⟩,
        ⟨.wartet rfl rfl noCrash, fun _ => ⟨rfl, idealStuck⟩⟩, ?_, fun step _ => (step mark).elim⟩
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
  let belegt (t : Nat) : Option Kontext :=
    if priv : ρ.zeit.spur t ≠ none ∧ ideal.spur t = none then
      some (Classical.choose ((ticks t).2.2 priv.1 priv.2))
    else none
  have frei (t : Nat) : belegt t = none ↔ ρ.zeit.spur t = none ∨ ideal.spur t ≠ none := by
    by_cases priv : ρ.zeit.spur t ≠ none ∧ ideal.spur t = none
    · rw [show belegt t = some (Classical.choose ((ticks t).2.2 priv.1 priv.2)) from dif_pos priv]
      constructor
      · intro h
        cases h
      · rintro (pause | step)
        · exact (priv.1 pause).elim
        · exact (step priv.2).elim
    · refine ⟨fun _ => ?_, fun _ => dif_neg priv⟩
      by_cases pause : ρ.zeit.spur t = none
      · exact Or.inl pause
      · exact Or.inr (fun idle => priv ⟨pause, idle⟩)
  have maximal : ideal.Maximal (fun t => belegt t = none) := by
    refine ⟨fun t idle vacant => ?_, fun ends => ?_⟩
    · rcases (frei t).mp vacant with pause | step
      · exact ((ticks t).1.pause pause).2
      · exact (step idle).elim
    · obtain ⟨k, tail⟩ := finite.mpr ends
      exact ⟨k.val, fun t after => (frei t).mpr (Or.inl (tail t after))⟩
  have occupied (t c) (marked : belegt t = some c) :
      (ideal.spur t = none ∧ KannSchreiten ρ.hw t c (ideal.zustand t)) ∧
      ∃ w, ρ.zeit.spur t = some (.kontext c w, ⟨[], []⟩) := by
    by_cases priv : ρ.zeit.spur t ≠ none ∧ ideal.spur t = none
    · rw [show belegt t = some (Classical.choose ((ticks t).2.2 priv.1 priv.2)) from dif_pos priv] at marked
      obtain ⟨w, named, ready⟩ := Option.some.inj marked ▸ Classical.choose_spec ((ticks t).2.2 priv.1 priv.2)
      exact ⟨⟨priv.2, ready⟩, w, named⟩
    · rw [show belegt t = none from dif_neg priv] at marked
      cases marked
  exact ⟨⟨ρ.start, h, ρ.hw, ideal, belegt⟩,
    ⟨run.1, run.2.1, run.2.2.1, idealStart, maximal, fun t c h => (occupied t c h).1⟩,
    rfl, rfl, related, fun t => (ticks t).2.1, frei, fun t c h => (occupied t c h).2, finite⟩

end Gabbro.Core.Maschine.I
