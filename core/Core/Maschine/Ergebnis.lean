/-
  File:      core/Core/Maschine/Ergebnis.lean
  Subject:   THE PINNED OUTCOME TYPE, THE BLOCKING REASONS, THE CATALOGUE EVENTS AND THE TYPESTATES OF THE
             OUTSIDE (PERFECT-MODEL §3.4, §4, step M4).
             * `Ergebnis`: exactly two kinds -- an end (a written value or a reason exit) and a catalogue
               event; no logic, budget or visibility stop exists.
             * `Blockade`: a context is blocked only at a lock, an `await` (naming its false condition), a
               join, an outstanding catalogue question, or a hardware delay.
             * `Ereignis`: the events of the concrete catalogue rows.
             * `Leihe`: the typestate of a region lent to a device, a DMA engine or a guest.
-/
module

public import Core.Maschine.Kontext
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Katalog

/-- The primary object of the question, as named by its handle. -/
def Frage.objekt (q : Frage) : Objekt := q.handle.origin.object

/-- At the commit snapshot the selected row permits precisely its atomic answer. -/
def Katalog.zulaessig (k : Katalog) (s : AussenSicht) (q : Frage) (a : Antwort) : Prop :=
  k.enthaelt (.endpoint q.endpoint) ∧ atomar k.plattform s q = .antwort a

/-- A selected question is ready when the row returns an answer at this snapshot. -/
def Katalog.bereit (k : Katalog) (s : AussenSicht) (q : Frage) : Prop :=
  ∃ a, k.zulaessig s q a

theorem Hardware.antwort_zulaessig (hw : Hardware k h) (selected : k.enthaelt (.endpoint q.endpoint))
    (time : Nat) (history : AussenVerlauf) (a : Antwort) :
    h.politik.antwort time history q = .antwort a ↔ k.zulaessig (h.politik.sicht time history) q a := by
  rw [hw.antwort time history q selected]
  exact ⟨fun answer => ⟨selected, answer⟩, And.right⟩

/-- The hosted row of each platform can answer a read. -/
theorem katalog_antwort_erfuellbar (p : Plattform) (bytes : List UInt8) :
    ∃ s q a, p.katalog.zulaessig s q a ∧ p.katalog.bereit s q ∧ a.result = .ok (.data bytes) := by
  obtain ⟨s, q, a, endpoint, _, reply, result⟩ := hosted_lesen_erfuellbar p bytes
  have selected : p.katalog.enthaelt (.endpoint q.endpoint) := by
    rw [endpoint]
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_map_of_mem
    cases p <;> exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  exact ⟨s, q, a, ⟨selected, reply⟩, ⟨a, selected, reply⟩, result⟩

/-- A physical core opportunity in the exogenous hardware schedule. -/
def HwLauf.gelegenheit (run : HwLauf) (t core : Nat) : Prop :=
  (run.angebot t).core = some core

/-- Events at the boundary, carrying the observations of the selected rows. -/
inductive Ereignis where
  | frage (e : FrageEreignis)
  | antwort (e : AntwortEreignis)
  | interrupt (core : Nat) (irq : Unterbrechung) (entry : Eintritt)
  | geraet (endpoint : Endpunkt) (action : GeraeteAktion)
  | dma (endpoint : Endpunkt) (access : DmaZugriff)
  | seite (e : SeitenEreignis)
  | persistenz (e : PersistEreignis)

end Gabbro.Core.Katalog

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

/-- **The end of a context**: a written value or a reason exit. -/
inductive Ende (Wert Grund : Type) where
  | wert (v : Wert)
  | grund (r : Grund)

/-- **THE OUTCOME TYPE, pinned to two kinds**: an end, or a catalogue event. -/
inductive Ergebnis (Wert Grund : Type) where
  | ende (e : Ende Wert Grund)
  | katalog (e : Ereignis)

/-- **Why a context is blocked**: a lock, an `await` with its false condition, a join of a context,
    an outstanding catalogue question, or a hardware delay (its core gets no opportunity). -/
inductive Blockade (Sperre Bedingung : Type) where
  | sperre (l : Sperre)
  | warten (b : Bedingung)
  | join (k : Kontext)
  | frage (q : Frage)
  | verzoegert (k : Kern)

/-- **The typestate of a region**: owned by the program, or lent to an outside object. -/
inductive Leihe (Objekt : Type) where
  | eigen
  | verliehen (an : Objekt)

namespace Leihe

variable {Objekt : Type}

/-- The program may access the region itself: only when it owns it. -/
def Zugriff : Leihe Objekt → Prop
  | eigen => True
  | verliehen _ => False

/-- Lending: only an owned region is lent. -/
inductive Verleihen : Leihe Objekt → Objekt → Leihe Objekt → Prop
  | eigen (o : Objekt) : Verleihen eigen o (verliehen o)

/-- Taking back: only from the object it was lent to. -/
inductive Zuruecknehmen : Leihe Objekt → Objekt → Leihe Objekt → Prop
  | verliehen (o : Objekt) : Zuruecknehmen (verliehen o) o eigen

/-- A lent region is not accessible to the program. -/
theorem verliehen_kein_zugriff {l l' : Leihe Objekt} {o : Objekt} (h : Verleihen l o l') :
    ¬ Zugriff l' := by
  cases h
  exact id

/-- Satisfiability: a region is lent and taken back. -/
theorem leihe_erfuellbar (o : Objekt) :
    Verleihen (eigen : Leihe Objekt) o (verliehen o) ∧ Zuruecknehmen (verliehen o) o eigen :=
  ⟨.eigen o, .verliehen o⟩

end Leihe

end Gabbro.Core.Maschine
