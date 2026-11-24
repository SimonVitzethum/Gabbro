module

public import Core.Maschine.Zustand

@[expose] public section

namespace Gabbro.Core.Maschine.Zustand

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund : Type}

/-- Issuing a question allocates a fresh instance. The history includes unanswered questions. -/
def stelleFrage (z : Zustand L Ort Wert Raum Lok Grund) (t : Nat) (c : Kontext) (q : Frage) :
    FrageEreignis :=
  ⟨t, c.nummer, z.fragen.length, q⟩

def frage (z : Zustand L Ort Wert Raum Lok Grund) (e : FrageEreignis) :
    Zustand L Ort Wert Raum Lok Grund :=
  { z with fragen := z.fragen ++ [e], verlauf := z.verlauf ++ [(e.cut, .frage e.question)] }

/-- The asynchronous boundary uses the offered opportunity and the policy at this cut. An answer
    arrives only once, for the same question instance, context and outside object. -/
def AntwortAngeboten (z : Zustand L Ort Wert Raum Lok Grund) (k : Katalog.Katalog)
    (run : HwLauf) (t : Nat) (a : AntwortEreignis) : Prop :=
  a.cut = t ∧ a.erlaubt run z.verlauf ∧
    k.enthaelt (.endpoint a.question.endpoint) ∧
    (∃ q ∈ z.fragen, a.zu q) ∧ ∀ e ∈ z.antworten, e.questionInstance ≠ a.questionInstance

/-- The conformant outside policy revalidates the answer at arrival. -/
theorem AntwortAngeboten.zulaessig {z : Zustand L Ort Wert Raum Lok Grund} {k h run t a}
    (offered : z.AntwortAngeboten k run t a) (hardware : Hardware k h) (konform : run.konform k h) :
    k.zulaessig (run.politik.sicht t z.verlauf) a.question a.reply := by
  rw [konform.1]
  apply (hardware.antwort_zulaessig offered.2.2.1 t z.verlauf a.reply).mp
  have answer := offered.2.1.2
  rw [offered.1, konform.1] at answer
  exact answer

def antwort (z : Zustand L Ort Wert Raum Lok Grund) (a : AntwortEreignis) :
    Zustand L Ort Wert Raum Lok Grund :=
  { z with antworten := z.antworten ++ [a], verlauf := z.verlauf ++ [(a.cut, .antwort a.question a.reply)] }

/-- The context can take its first unconsumed reply, across all outside objects it has contacted. -/
def naechsteAntwort (z : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) : Option AntwortEreignis :=
  (z.angekommen c)[z.verbraucht c]?

def verbrauche (z : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) :
    Zustand L Ort Wert Raum Lok Grund :=
  { z with verbraucht := Function.update z.verbraucht c (z.verbraucht c + 1) }

theorem antwort_global (z : Zustand L Ort Wert Raum Lok Grund) (a : AntwortEreignis) :
    (z.antwort a).antworten = z.antworten ++ [a] ∧
      (z.antwort a).verbraucht = z.verbraucht :=
  ⟨rfl, rfl⟩

theorem verbrauch_lokal (z : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) :
    (z.verbrauche c).antworten = z.antworten ∧
      (z.verbrauche c).verbraucht c = z.verbraucht c + 1 ∧
      ∀ d, d ≠ c → (z.verbrauche c).verbraucht d = z.verbraucht d :=
  ⟨rfl, Function.update_self c _ _, fun d other => Function.update_of_ne other _ _⟩

theorem antwort_verbrauch {z : Zustand L Ort Wert Raum Lok Grund} (h : z.Verbrauch)
    (a : AntwortEreignis) : (z.antwort a).Verbrauch := by
  intro c
  simpa only [antwort, angekommen, List.filter_append, List.length_append] using
    Nat.le_trans (h c) (Nat.le_add_right _ (List.filter (fun e : AntwortEreignis => e.context == c.nummer) [a]).length)

theorem verbrauche_verbrauch {z : Zustand L Ort Wert Raum Lok Grund} (h : z.Verbrauch)
    {c : Kontext} {a : AntwortEreignis} (ready : z.naechsteAntwort c = some a) :
    (z.verbrauche c).Verbrauch := by
  intro d
  by_cases same : d = c
  · subst d
    exact (verbrauch_lokal z c).2.1 ▸ Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp ready).1
  · exact (verbrauch_lokal z c).2.2 d same ▸ h d

end Gabbro.Core.Maschine.Zustand
