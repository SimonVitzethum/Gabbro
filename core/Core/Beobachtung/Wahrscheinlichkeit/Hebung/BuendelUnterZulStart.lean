/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/BuendelUnterZulStart.lean
  Subject:   The sharpened lift statement, proved from an admissible start.

  With `∃ s, E.ZulStart h s` as a premise, a full `Hebebuendel` is constructed:
  the product measure gives `massErhalt`, and a replay on a completely idle
  hardware history takes no step at any cut. An idle replay is causal, vacuously
  follows any scheduler, and consumes no draw answer. `hebe` closes the pinned
  statement; image validity is the premise the former unsharpened form lacked.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.ZiehungsMass
public import Core.Beobachtung.Wahrscheinlichkeit.Aussagen
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Maschine
open Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- A hardware history without core opportunities, arrivals, interrupts or crashes. -/
def idlerHwlauf (h : Umgebung) : HwLauf :=
  ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩, h.politik⟩

theorem idlerHwlauf_konform (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (hardware : Hardware E.katalog h) : (idlerHwlauf h).konform E.katalog h := by
  refine ⟨rfl, fun i => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun _ hc => nomatch hc
  · exact fun _ hi => nomatch hi
  · exact fun signal mem => (List.not_mem_nil mem).elim
  · exact fun _ he => nomatch he
  · intro offer
    cases offer with
    | inl medium => cases medium
    | inr crash => cases crash

/-- No implementation step is possible on an idle history. -/
theorem idlerHwlauf_keinSchritt
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittWahl Wahl × SchrittSpur Ort Wert)
    (s' : Zustand L Ort Wert Raum Lok Grund) :
    ¬ ImplSchritt E.einrichtung E.system E.katalog (idlerHwlauf h) t s spur s' := by
  intro step
  cases step with
  | kontext _ bereit _ _ =>
      obtain ⟨core, opportunity, _, _⟩ := bereit
      change (none : Option Nat) = some core at opportunity
      cases opportunity
  | antwort _ arrival =>
      have offered := arrival.1
      have erlaubt := offered.2.1
      have delivery := erlaubt.1
      change false = true at delivery
      cases delivery
  | interrupt _ delivery =>
      obtain ⟨core, _, _, _, offer, _, _, _⟩ := delivery
      change false = true at offer
      cases offer
  | absturz crash =>
      have offer := crash.1
      have katalogZeile := offer.1
      have angebot := offer.2
      change false = true at angebot
      cases angebot

/-- A takt without a possible step is the pause takt. -/
theorem takt_ist_wartet
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (t : Nat) (s s' : Option (Zustand L Ort Wert Raum Lok Grund))
    (spur : Option (SchrittWahl Wahl × SchrittSpur Ort Wert))
    (kein : ∀ (vorher : Option (Zustand L Ort Wert Raum Lok Grund))
      (markierung : SchrittWahl Wahl × SchrittSpur Ort Wert)
      (nachher : Option (Zustand L Ort Wert Raum Lok Grund)),
      ¬ Lauffolge E (idlerHwlauf h) t vorher markierung nachher)
    (takt : Takt (Lauffolge E (idlerHwlauf h))
      (KeinSchritt (Lauffolge E (idlerHwlauf h))) t s spur s') :
    spur = none := by
  cases takt with
  | schritt label step => exact (kein _ _ _ step).elim
  | wartet label _ _ => exact label

/-- Every cut of the idle replay pauses. -/
theorem idlerHwlauf_zeitPause
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (s : AussenStart) (hardware : Hardware E.katalog h)
    (zul : E.ZulStart h s) (zeit : Zeitlauf (Lauffolge E (idlerHwlauf h)))
    (init : zeit.zustand 0 = E.laden s (h.lade E.bild)) (t : Nat) :
    zeit.spur t = none := by
  refine takt_ist_wartet E h t (zeit.zustand t) (zeit.zustand (t + 1)) (zeit.spur t) ?_ (zeit.takt t)
  intro vorher markierung nachher step
  cases vorher with
  | none => cases step
  | some s =>
      cases nachher with
      | none => cases step
      | some s' =>
          cases step with
          | schritt impl =>
              exact idlerHwlauf_keinSchritt E h t s markierung s' impl

/-- The full bundle under the missing admissible-start premise. -/
noncomputable def buendelUnterZulStart (B : Zufallsbindung) (S : Scheduler)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (hardware : Hardware E.katalog h)
    (start : ∃ s : AussenStart, E.ZulStart h s) : Hebebuendel B S E h := by
  let s := Classical.choose start
  have zul := Classical.choose_spec start
  let hw := idlerHwlauf h
  have konform := idlerHwlauf_konform E h hardware
  let rest := Zeitlauf.existiert (Lauffolge E hw) (E.laden s (h.lade E.bild))
  let zeit := Classical.choose rest
  have init := Classical.choose_spec rest
  let ρ : Maschine.Lauf E := ⟨s, hw, zeit⟩
  have zulaessig : Maschine.Laeufe E h ρ := ⟨hardware, konform, zul, init⟩
  have spurKein (t : Nat) : ρ.zeit.spur t = none := by
    change zeit.spur t = none
    exact idlerHwlauf_zeitPause E h s hardware zul zeit init t
  have praefixLeer (t : Nat) : praefixAntworten B ρ t = [] := by
    unfold praefixAntworten
    simp only [spurKein]
    induction (List.finRange t) with
    | nil => rfl
    | cons i is ih => simpa only [List.flatMap_cons, ih]
  let mass := massBuendel_erfuellbar B
  exact
    { mu := mass.mu
      replay := fun _ => ρ
      istWMass := mass.istWMass
      massErhalt := mass.massErhalt
      replayZulaessig := fun _ => zulaessig
      replayKausal := fun _ _ _ _ _ _ => ⟨rfl, rfl⟩
      replayFolgtScheduler := by
        intro band t c w spur folge
        rw [spurKein t] at folge
        cases folge
      replayZiehungen := by
        intro band t a antwort
        rw [praefixLeer t] at antwort
        cases antwort }

/-- The sharpened pinned lift statement is proved: hardware conformity, a
    selected random row and an admissible start deliver the bundle. -/
theorem hebe : hebeAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form _ E B S h hw selected start
  exact ⟨buendelUnterZulStart B S E h hw start, trivial⟩

end Gabbro.Core.Beobachtung
