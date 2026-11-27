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

variable {Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

private theorem fuehrtAus_keineAntwort {c u aktion sperren aussen v}
    (protokoll : FuehrtAus e t c s u aktion sperren aussen v) : Ereignis.antwort a ∉ aussen := by
  intro mem
  cases protokoll <;> simp only [List.not_mem_nil, List.mem_singleton, reduceCtorEq] at mem

private theorem takt_antwortAnkunft
    {vorher nachher : Option (Zustand L Ort Wert Raum Lok Grund)}
    {label : SchrittWahl Wahl × SchrittSpur Ort Wert}
    (takt : Takt (Lauffolge E run) (KeinSchritt (Lauffolge E run)) t vorher (some label) nachher)
    (mem : Ereignis.antwort a ∈ label.2.aussen) :
    ∃ s s', AntwortSchritt E.einrichtung E.katalog run t a s label.2 s' := by
  cases takt with
  | wartet eq _ _ => cases eq
  | schritt eq schritt =>
    cases Option.some.inj eq
    cases schritt with
    | schritt impl =>
      cases impl with
      | kontext _ _ _ aus =>
        obtain ⟨_, _, _, _, protokoll, _, _⟩ := aus
        exact (fuehrtAus_keineAntwort protokoll mem).elim
      | antwort _ ankunft =>
        rw [ankunft.2.1, List.mem_singleton] at mem
        cases Ereignis.antwort.inj mem
        exact ⟨_, _, ankunft⟩
      | interrupt _ ankunft =>
        obtain ⟨_, _, _, _, _, _, _, _, trace, _, _⟩ := ankunft
        rw [trace, List.mem_singleton] at mem
        cases mem
      | absturz crash =>
        rw [crash.2.1] at mem
        simp only [absturzSpur, List.mem_singleton, reduceCtorEq] at mem

/-- Every replay satisfying the current bundle omits all marked replies. This applies to
    arbitrary admitted replays, not just the particular idle construction. -/
theorem Hebebuendel.praefixAntworten_leer {B : Zufallsbindung} {S : Scheduler}
    (hb : Hebebuendel B S E h) (band : Band) (t : Nat) :
    praefixAntworten B (hb.replay band) t = [] := by
  suffices kein : ∀ a, a ∉ praefixAntworten B (hb.replay band) t by
    cases eq : praefixAntworten B (hb.replay band) t with
    | nil => rfl
    | cons a as =>
      exfalso
      apply kein a
      rw [eq]
      exact List.mem_cons_self
  intro a mem
  obtain ⟨index, draw⟩ := hb.replayZiehungen band t a mem
  rw [praefixAntworten, List.mem_flatMap] at mem
  obtain ⟨i, _, hit⟩ := mem
  cases mark : (hb.replay band).zeit.spur i with
  | none =>
    rw [mark] at hit
    exact List.not_mem_nil hit
  | some label =>
    rw [mark, List.mem_filterMap] at hit
    obtain ⟨event, enthalten, test⟩ := hit
    cases event <;> try cases test
    rename_i antwort
    by_cases zufall : Zufallsfrage B antwort.question
    · change istZufallsfrage B antwort.question = true at zufall
      simp only [zufall, ↓reduceIte] at test
      cases Option.some.inj test
      have takt := (hb.replay band).zeit.takt i
      rw [mark] at takt
      obtain ⟨_, _, ankunft⟩ := takt_antwortAnkunft takt enthalten
      have zul := hb.replayZulaessig band
      exact antwortSchritt_keineZiehungsAntwort zul.1 zul.2.1 ankunft zufall _ draw
    · change ¬ istZufallsfrage B antwort.question = true at zufall
      simp only [if_neg zufall, reduceCtorEq] at test

end Gabbro.Core.Beobachtung
