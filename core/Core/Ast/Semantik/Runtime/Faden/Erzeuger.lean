/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Erzeuger.lean
  Subject:   THE CREATOR OF A THREAD AND THE SINGLE JOIN (MK-07), pinned under `FadenAussagen`:
             * `VerbindeNurErzeugerAussage`: every machine join of a context runs through its creator: the
               joiner is the context the start recorded in `erzeuger`. A join by any other context has no
               machine step. PROVED (`verbindeNurErzeuger`) from `FuehrtAus.verbinde_genau`.
             * `VerbindeEinmalAussage`: a join clears the creator entry of the joined thread, so no second
               join of the same thread has a machine step, by any joiner. PROVED (`verbindeEinmal`) from
               `FuehrtAus.verbinde_genau`.
             Each has a satisfiability lemma (`…_erfuellbar`: the premises hold jointly) and a non-triviality
             lemma (`…_nichtTrivial`): the model REPRESENTS the foreign join — the form step of the lifecycle
             class fires for it (the checker line names only the operand), but the machine has no step for a
             joiner that did not start the thread — and the statement excludes it; and the model represents a
             first join whose successor admits no second join.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Gesamt
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Faden
public import Core.Ast.Semantik.Runtime.Faden.Erhalt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-! ### A join runs only through the creator -/

/-- **A join runs only through the creator.** Every machine join of a context `kind` is executed by the
    context the start recorded as its creator: `s.erzeuger kind = some c`. The thread counter alone cannot
    express this: thread numbers are integers with no creator relation, so without the entry any context
    could join a foreign ended thread and take over its authority. -/
def VerbindeNurErzeugerAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung : Type) [DecidableEq L]
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung) (t : Nat) (c : Kontext)
    (s u v : Maschine.Zustand L Ort Wert Raum Lok Grund) (kind : Kontext)
    (sperren : List (Speicher.Etikett Ort Wert)) (ereignisse : List Ereignis),
    FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v → s.erzeuger kind = some c

/-- **A join runs only through the creator** (the proof of `VerbindeNurErzeugerAussage`). -/
theorem verbindeNurErzeuger : VerbindeNurErzeugerAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung _ e t c s u v kind sperren ereignisse h
  exact (h.verbinde_genau).1

/-- **The premises of the creator statement hold jointly**: a state in which the thread `1` has ended and
    the entry thread is recorded as its creator, joined by the entry thread. -/
theorem verbindeNurErzeuger_erfuellbar :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s u v : Zustand)
      (kind : Kontext) (sperren : List (Speicher.Etikett Zelle Int)) (ereignisse : List Ereignis),
      FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v := by
  let s : Zustand := { Leerzustand with
    status := fun d => if d = Kontext.faden 1 then .beendet (.wert 7) else .ruht,
    erzeuger := fun d => if d = Kontext.faden 1 then some eintritt else none }
  have fertig : s.status (Kontext.faden 1) = .beendet (.wert 7) := by
    change (if Kontext.faden 1 = Kontext.faden 1 then Status.beendet (.wert 7) else .ruht) = _
    rw [if_pos rfl]
  have erz : s.erzeuger (Kontext.faden 1) = some eintritt := by
    change (if Kontext.faden 1 = Kontext.faden 1 then some eintritt else none) = some eintritt
    rw [if_pos rfl]
  exact ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt,
    s, s, _, Kontext.faden 1, [], [], .verbinde fertig erz⟩

/-- **The creator statement is not trivial**: the model represents the foreign join — the thread `1` has
    ended with an outcome, its recorded creator is another thread, and the form step of the class
    `verbinde` fires for the entry thread (its guard names only the operand) — but the machine has no
    step for the foreign joiner, so a join never takes over foreign authority. -/
theorem verbindeNurErzeuger_nichtTrivial :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s u : Zustand)
      (kind : Kontext) (F : Schrittform) (p : Plan),
      s.status kind = .beendet (.wert 7) ∧ s.erzeuger kind ≠ some c ∧
        F.klasse = .verbinde ∧ F.ideal c s () [p] (F.faedenNach c s) ∧
        ∀ (v : Zustand) sperren ereignisse, ¬ FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v := by
  let F : Schrittform := ⟨.verbinde, fun _ => { Operand.keiner with faden := { Fadenoperand.keiner with kind := 1 } },
    fun r _ _ => r⟩
  let s : Zustand := { Leerzustand with
    status := fun d => if d = Kontext.faden 1 then .beendet (.wert 7) else .ruht,
    erzeuger := fun d => if d = Kontext.faden 1 then some (Kontext.faden 2) else none }
  have hif : s.erzeuger (Kontext.faden 1) = some (Kontext.faden 2) := by
    change (if Kontext.faden 1 = Kontext.faden 1 then some (Kontext.faden 2) else none) = _
    rw [if_pos rfl]
  have hne : s.erzeuger (Kontext.faden 1) ≠ some eintritt := by
    intro h
    rw [hif] at h
    exact (by decide : (2 : Nat) ≠ 0) (Kontext.faden.inj (Option.some.inj h))
  refine ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt,
    s, s, Kontext.faden 1, F, F.plan (s.lokal eintritt) 0, ?_, hne, rfl, Or.inr ⟨rfl, rfl, rfl⟩, ?_⟩
  · change (if Kontext.faden 1 = Kontext.faden 1 then Status.beendet (.wert 7) else .ruht) = _
    rw [if_pos rfl]
  · intro v sperren ereignisse h
    cases h with
    | verbinde _ erz =>
      rw [hif] at erz
      exact (by decide : (2 : Nat) ≠ 0) (Kontext.faden.inj (Option.some.inj erz))

/-! ### A join runs only once -/

/-- **A join runs only once.** After a machine join of a context `kind` its creator entry is cleared, so no
    second join of the same context has a machine step, by any joiner. Without the clearing the ended
    status alone would admit the same join again, and the take-back of authority could run twice. -/
def VerbindeEinmalAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung : Type) [DecidableEq L]
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung) (t : Nat) (c : Kontext)
    (s u v : Maschine.Zustand L Ort Wert Raum Lok Grund) (kind : Kontext)
    (sperren : List (Speicher.Etikett Ort Wert)) (ereignisse : List Ereignis),
    FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v → v.erzeuger kind = none ∧
      ∀ (t' : Nat) (c' : Kontext) (u' v' : Maschine.Zustand L Ort Wert Raum Lok Grund)
        (sperren' : List (Speicher.Etikett Ort Wert)) (ereignisse' : List Ereignis),
        ¬ FuehrtAus e t' c' v u' (.verbinde kind) sperren' ereignisse' v'

/-- **A join runs only once** (the proof of `VerbindeEinmalAussage`). -/
theorem verbindeEinmal : VerbindeEinmalAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung _ e t c s u v kind sperren ereignisse h
  obtain ⟨_, geloeschts, _⟩ := h.verbinde_genau
  refine ⟨geloeschts, ?_⟩
  intro t' c' u' v' sperren' ereignisse' h2
  obtain ⟨erz', _, _⟩ := h2.verbinde_genau
  rw [geloeschts] at erz'
  cases erz'

/-- **The premises of the single-join statement hold jointly**: a join of the thread `1` by its recorded
    creator. -/
theorem verbindeEinmal_erfuellbar :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s u v : Zustand)
      (kind : Kontext) (sperren : List (Speicher.Etikett Zelle Int)) (ereignisse : List Ereignis),
      FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v := by
  let s : Zustand := { Leerzustand with
    status := fun d => if d = Kontext.faden 1 then .beendet (.wert 7) else .ruht,
    erzeuger := fun d => if d = Kontext.faden 1 then some eintritt else none }
  have fertig : s.status (Kontext.faden 1) = .beendet (.wert 7) := by
    change (if Kontext.faden 1 = Kontext.faden 1 then Status.beendet (.wert 7) else .ruht) = _
    rw [if_pos rfl]
  have erz : s.erzeuger (Kontext.faden 1) = some eintritt := by
    change (if Kontext.faden 1 = Kontext.faden 1 then some eintritt else none) = some eintritt
    rw [if_pos rfl]
  exact ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt,
    s, s, _, Kontext.faden 1, [], [], .verbinde fertig erz⟩

/-- **The single-join statement is not trivial**: the model represents a first join of the thread `1` by
    its recorded creator, and its successor admits no second join of the same thread, by any joiner: the
    creator entry is cleared. -/
theorem verbindeEinmal_nichtTrivial :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s u v : Zustand)
      (kind : Kontext) (sperren : List (Speicher.Etikett Zelle Int)) (ereignisse : List Ereignis),
      FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v ∧
        ∀ (t' : Nat) (c' : Kontext) (u' v' : Zustand) (sperren' : List (Speicher.Etikett Zelle Int))
          (ereignisse' : List Ereignis),
          ¬ FuehrtAus e t' c' v u' (.verbinde kind) sperren' ereignisse' v' := by
  let s : Zustand := { Leerzustand with
    status := fun d => if d = Kontext.faden 1 then .beendet (.wert 7) else .ruht,
    erzeuger := fun d => if d = Kontext.faden 1 then some eintritt else none }
  let v : Zustand := { s with erzeuger := Function.update s.erzeuger (Kontext.faden 1) none }
  have fertig : s.status (Kontext.faden 1) = .beendet (.wert 7) := by
    change (if Kontext.faden 1 = Kontext.faden 1 then Status.beendet (.wert 7) else .ruht) = _
    rw [if_pos rfl]
  have erz : s.erzeuger (Kontext.faden 1) = some eintritt := by
    change (if Kontext.faden 1 = Kontext.faden 1 then some eintritt else none) = some eintritt
    rw [if_pos rfl]
  have hstep : FuehrtAus (einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher)
      0 eintritt s s (.verbinde (Kontext.faden 1)) [] [] v := .verbinde fertig erz
  have hclear : v.erzeuger (Kontext.faden 1) = none := by
    show Function.update s.erzeuger (Kontext.faden 1) none (Kontext.faden 1) = none
    exact Function.update_self _ _ _
  refine ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt,
    s, s, v, Kontext.faden 1, [], [], hstep, ?_⟩
  · intro t' c' u' v' sperren' ereignisse' h2
    obtain ⟨erz', _, _⟩ := h2.verbinde_genau
    rw [hclear] at erz'
    cases erz'

end Gabbro.Core.Ast.Semantik
