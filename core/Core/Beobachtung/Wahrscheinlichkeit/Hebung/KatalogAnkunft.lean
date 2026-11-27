/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/KatalogAnkunft.lean
  Subject:   Random answers at the atomic catalogue and machine arrival boundary.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung

public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Katalog Gabbro.Core.Maschine

private theorem zufallsfrage_exchange {B : Zufallsbindung} {q : Frage} (frage : Zufallsfrage B q) :
    ∃ tag, q.operation = .exchange tag := by
  cases operation : q.operation
  all_goals first
    | exact ⟨_, rfl⟩
    | exact ⟨_, operation⟩
    | simp only [Zufallsfrage, istZufallsfrage, operation, Bool.false_eq_true] at frage

/-- A marked exchange cannot commit the register result used by the original replay encoding. -/
theorem ziehungsAntwort_nichtZulaessig {B : Zufallsbindung} {k : Katalog} {s : AussenSicht}
    {q : Frage} (frage : Zufallsfrage B q) (origin : Herkunft) (wert : Nat) :
    ¬ k.zulaessig s q (ZiehungsAntwort origin wert) := by
  obtain ⟨tag, operation⟩ := zufallsfrage_exchange frage
  intro erlaubt
  have atom := erlaubt.2
  unfold atomar at atom
  split at atom
  · cases congrArg Antwort.result (Entscheidung.antwort.inj atom)
  split at atom
  · cases congrArg Antwort.result (Entscheidung.antwort.inj atom)
  split at atom
  · cases atom
  have result := congrArg Antwort.result (Entscheidung.antwort.inj atom)
  change (if (s.objects q.handle.origin.object).ready then s.erfolg k.plattform q
    else .error .unavailable) = .ok (.register wert) at result
  split at result
  · simp only [AussenSicht.erfolg, operation] at result
    cases result
  · cases result

variable {L Ort Wert Raum Lok Grund Bedingung : Type}
variable {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
variable {k : Katalog} {h : Umgebung} {run : HwLauf} {t : Nat} {a : AntwortEreignis}
variable {s s' : Zustand L Ort Wert Raum Lok Grund} {spur : SchrittSpur Ort Wert}

/-- A conforming arrival cannot carry the original replay encoding, even when the question is pending. -/
theorem antwortSchritt_keineZiehungsAntwort (hardware : Hardware k h) (konform : run.konform k h)
    (schritt : AntwortSchritt e k run t a s spur s') (frage : Zufallsfrage B a.question)
    (wert : Nat) : a.reply ≠ ZiehungsAntwort a.reply.origin wert := by
  intro gleich
  have erlaubt := schritt.1.zulaessig hardware konform
  rw [gleich] at erlaubt
  exact ziehungsAntwort_nichtZulaessig frage _ wert erlaubt

/-- Even across different schedules, one fixed environment fixes the entire answer at equal
    cut, history and question. The equality covers data, origin and revalidation footprint. -/
theorem antwortSchritt_gleichePolitik {run₂ : HwLauf} {a₂ : AntwortEreignis}
    {s₂ s₂' : Zustand L Ort Wert Raum Lok Grund} {spur₂ : SchrittSpur Ort Wert}
    (konform : run.konform k h) (konform₂ : run₂.konform k h)
    (schritt : AntwortSchritt e k run t a s spur s')
    (schritt₂ : AntwortSchritt e k run₂ t a₂ s₂ spur₂ s₂')
    (geschichte : s.verlauf = s₂.verlauf) (frage : a.question = a₂.question) : a.reply = a₂.reply := by
  have erste := schritt.1.2.1.2
  have zweite := schritt₂.1.2.1.2
  rw [schritt.1.1, konform.1, geschichte, frage] at erste
  rw [schritt₂.1.1, konform₂.1] at zweite
  exact Entscheidung.antwort.inj (erste.symm.trans zweite)

end Gabbro.Core.Beobachtung
