/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Erhalt.lean
  Subject:   WHAT THE THREAD-LIFECYCLE ACTIONS OF THE PROTOCOL DO AND DO NOT TOUCH (MK-07). The four lifecycle actions
             (`starte`, `verbinde`, `beende`, `wechsle`) record no lock event and no outside event. They leave the
             questions, the answers, the locks, the graph, the authority state and the ledger of the state the form
             produced alone; they move only three things, each in its own action:
             * `starte` makes the resting thread with the next number run and moves the counter on
               (`FuehrtAus.starte_genau`);
             * `wechsle` makes a core run another context (`FuehrtAus.wechsle_genau`);
             * `verbinde` and `beende` move nothing (the form sets the status of the ending thread).
             A start picks the next number, so no number is used twice (`starte_zaehler_waechst`); a switch to a
             context that already runs on a core is not an action (`wechsle_genau`), so no context runs on two
             cores (`wechsle_erhaelt_einkern`).
-/
module

public import Core.Maschine.Schritte

@[expose] public section

namespace Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung : Type}

/-- **A still action**: the internal action or a lifecycle action. It records no lock event and no outside event. -/
def Aktion.Still : Aktion L Bedingung → Prop
  | .starte => True
  | .verbinde _ => True
  | .beende => True
  | .wechsle _ _ => True
  | .intern => True
  | .warte _ => False
  | .sperre _ _ => False
  | .frage _ => False
  | .verbrauche _ => False
  | .rueckkehr => False

/-- **What the machine needs for a still action to run**, in the state `s` before the step and the state `u` the form
    produced: a start needs the thread with the next number to rest, a join needs the joined context to have ended,
    an end needs the form to have set the outcome of the acting thread, a switch needs a core the acting context holds
    or that is idle and a running context that runs on no core and is not the acting one. The internal action always
    runs; the other actions of the protocol are not lifecycle actions. -/
def Aktion.Ausfuehrbar (s u : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) :
    Aktion L Bedingung → Prop
  | .intern => True
  | .starte => s.status (.faden s.naechsterFaden) = .ruht
  | .verbinde kind => ∃ ausgang, s.status kind = .beendet ausgang
  | .beende => ∃ ausgang, u.status c = .beendet ausgang
  | .wechsle kern kind =>
    ((s.kerne kern).laeuft = some c ∨ (s.kerne kern).laeuft = none) ∧ s.status kind = .laeuft ∧
      (∀ k, (s.kerne k).laeuft ≠ some kind) ∧ kind ≠ c
  | .warte _ => False
  | .sperre _ _ => False
  | .frage _ => False
  | .verbrauche _ => False
  | .rueckkehr => False

variable {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung} [DecidableEq L]
  {t : Nat} {c : Kontext} {s u v : Zustand L Ort Wert Raum Lok Grund}

/-- **A lifecycle action changes only status, counter and cores of the state the form produced.** It records no
    lock event and no outside event. -/
theorem FuehrtAus.still_erhaelt {a : Aktion L Bedingung} {sperren : List (Speicher.Etikett Ort Wert)}
    {ereignisse : List Gabbro.Core.Katalog.Ereignis}
    (h : FuehrtAus e t c s u a sperren ereignisse v) (ha : a.Still) :
    sperren = [] ∧ ereignisse = [] ∧ v.lokal = u.lokal ∧ v.sperren = u.sperren ∧ v.rechte = u.rechte ∧
      v.graph = u.graph ∧ v.fragen = u.fragen ∧ v.antworten = u.antworten ∧ v.verlauf = u.verlauf ∧
      v.verbraucht = u.verbraucht ∧ v.geliefert = u.geliefert ∧ v.leihen = u.leihen ∧
      v.initial = u.initial ∧ v.persistenz = u.persistenz ∧ v.epoche = u.epoche ∧ v.verworfen = u.verworfen ∧
      v.buchung = u.buchung := by
  cases h with
  | intern => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | warte _ => exact False.elim ha
  | sperre _ _ => exact False.elim ha
  | frage _ => exact False.elim ha
  | verbrauche _ => exact False.elim ha
  | rueckkehr _ _ => exact False.elim ha
  | starte _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | verbinde _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | beende _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | wechsle _ _ _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A start, exactly**: the thread with the next number runs, the counter is one higher, no other status changes. -/
theorem FuehrtAus.starte_genau {sperren ereignisse}
    (h : FuehrtAus e t c s u .starte sperren ereignisse v) :
    s.status (.faden s.naechsterFaden) = .ruht ∧ v.status (.faden s.naechsterFaden) = .laeuft ∧
      v.naechsterFaden = s.naechsterFaden + 1 ∧
      ∀ d, d ≠ .faden s.naechsterFaden → v.status d = u.status d := by
  cases h with
  | starte ruht =>
    refine ⟨ruht, Function.update_self _ _ _, rfl, fun d hd => Function.update_of_ne hd _ _⟩

/-- **A start moves the counter on**: the number of a later start is higher, so no number is used twice. -/
theorem FuehrtAus.starte_zaehler_waechst {sperren ereignisse}
    (h : FuehrtAus e t c s u .starte sperren ereignisse v) : s.naechsterFaden < v.naechsterFaden := by
  obtain ⟨_, _, hz, _⟩ := h.starte_genau
  omega

/-- **A switch, exactly**: the core runs the context switched to; the acting context held the core or the core
    was idle; the context switched to ran on no core and is not the acting one; no other core changes. -/
theorem FuehrtAus.wechsle_genau {kern kind sperren ereignisse}
    (h : FuehrtAus e t c s u (.wechsle kern kind) sperren ereignisse v) :
    ((s.kerne kern).laeuft = some c ∨ (s.kerne kern).laeuft = none) ∧ s.status kind = .laeuft ∧
      (∀ k, (s.kerne k).laeuft ≠ some kind) ∧ kind ≠ c ∧ (v.kerne kern).laeuft = some kind ∧
      ∀ k, k ≠ kern → v.kerne k = u.kerne k := by
  cases h with
  | wechsle frei laeuft nirgends anders =>
    exact ⟨frei, laeuft, nirgends, anders, by simp only [Function.update_self], fun k hk =>
      Function.update_of_ne hk _ _⟩

/-- **A join runs only for a context that has ended.** -/
theorem FuehrtAus.verbinde_nur_beendet {kind sperren ereignisse}
    (h : FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v) : ∃ ausgang, s.status kind = .beendet ausgang := by
  cases h with
  | verbinde fertig => exact ⟨_, fertig⟩

/-- **An end sets the outcome of the acting thread.** -/
theorem FuehrtAus.beende_status {sperren ereignisse}
    (h : FuehrtAus e t c s u .beende sperren ereignisse v) : ∃ ausgang, u.status c = .beendet ausgang := by
  cases h with
  | beende ende => exact ⟨_, ende⟩

/-- **No context runs on two cores**: a core runs a context only if no other core runs it. -/
def Zustand.EinKern (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ k k' d, (s.kerne k).laeuft = some d → (s.kerne k').laeuft = some d → k = k'

/-- **A switch keeps the one-core invariant**, for the state the form produced: the context switched to ran on no
    core, so after the switch it runs on exactly the core `kern`. The context that gave up the core runs on none. -/
theorem FuehrtAus.wechsle_erhaelt_einkern {kern kind sperren ereignisse}
    (h : FuehrtAus e t c s u (.wechsle kern kind) sperren ereignisse v)
    (rahmen : u.kerne = s.kerne) (eins : s.EinKern) : v.EinKern := by
  obtain ⟨_, _, nirgends, _, hkern, andere⟩ := h.wechsle_genau
  intro k k' d hk hk'
  by_cases h1 : k = kern <;> by_cases h2 : k' = kern
  · rw [h1, h2]
  · rw [h1] at hk
    have hd : d = kind := Option.some.inj (hk.symm.trans hkern)
    have hk'' : (s.kerne k').laeuft = some kind := by
      rw [← rahmen, ← andere k' h2, hk', hd]
    exact (nirgends k' hk'').elim
  · rw [h2] at hk'
    have hd : d = kind := Option.some.inj (hk'.symm.trans hkern)
    have hk'' : (s.kerne k).laeuft = some kind := by
      rw [← rahmen, ← andere k h1, hk, hd]
    exact (nirgends k hk'').elim
  · exact eins k k' d (by rw [← rahmen, ← andere k h1]; exact hk)
      (by rw [← rahmen, ← andere k' h2]; exact hk')

end Gabbro.Core.Maschine
