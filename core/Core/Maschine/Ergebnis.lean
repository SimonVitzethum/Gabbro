/-
  File:      core/Core/Maschine/Ergebnis.lean
  Subject:   THE PINNED OUTCOME TYPE, THE BLOCKING REASONS, THE CATALOGUE INTERFACE AND THE TYPESTATES OF THE
             OUTSIDE (PERFECT-MODEL §3.4, §4, step M4).
             * `Ergebnis`: exactly two kinds -- an end (a written value or a reason exit) and a catalogue
               event; no logic, budget or visibility stop exists.
             * `Blockade`: a context is blocked only at a lock, an `await` (naming its false condition), a
               join, an outstanding catalogue question, or a hardware delay.
             * `Katalog`: what the machines need from the catalogue (M2, `Core/Katalog/`): outside objects,
               questions about an object, the answers a row allows, the enabling condition of an answer
               (false: the specified non-answer), the opportunity schedule of the cores, and catalogue events.
             * `Leihe`: the typestate of a region lent to a device, a DMA engine or a guest.
-/
module

public import Core.Maschine.Kontext

@[expose] public section

namespace Gabbro.Core.Maschine

/-- **The end of a context**: a written value or a reason exit. -/
inductive Ende (Wert Grund : Type) where
  | wert (v : Wert)
  | grund (r : Grund)

/-- **THE OUTCOME TYPE, pinned to two kinds**: an end, or a catalogue event. -/
inductive Ergebnis (Wert Grund KEreignis : Type) where
  | ende (e : Ende Wert Grund)
  | katalog (e : KEreignis)

/-- **Why a context is blocked**: a lock, an `await` with its false condition, a join of a context,
    an outstanding catalogue question, or a hardware delay (its core gets no opportunity). -/
inductive Blockade (Sperre Bedingung Frage : Type) where
  | sperre (l : Sperre)
  | warten (b : Bedingung)
  | join (k : Kontext)
  | frage (q : Frage)
  | verzoegert (k : Kern)

/-- **The catalogue interface** both machines are written against (M2 connects its rows here). -/
structure Katalog where
  /-- Outside objects: devices, DMA engines, firmware, operating-system interfaces, guests. -/
  Objekt : Type
  Frage : Type
  Antwort : Type
  /-- The outside object a question is about (§4: every answer carries its object). -/
  objekt : Frage → Objekt
  /-- The answers a row allows to a question. -/
  zulaessig : Frage → Antwort → Prop
  /-- The enabling condition of the answer; false is the specified non-answer. -/
  bereit : Frage → Prop
  /-- The exogenous opportunity schedule: core `k` may advance at time `t`. -/
  gelegenheit : Nat → Kern → Prop
  /-- Catalogue events: interrupt deliveries, device writes into lent regions, guest exits. -/
  Ereignis : Type

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
