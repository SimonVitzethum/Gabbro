/-
  File:      core/Core/Maschine/Zustand.lean
  Subject:   THE STATE OF BOTH MACHINES (PERFECT-MODEL §3.4, §3.5, step M4). The implementation machine and
             `I` share one state shape; they differ in their steps. A state holds, from the start, every
             concept the low-level forms need:
             * the local state of every context (what the forms of M6 keep: positions, environments);
             * the per-core state (running context, privilege, active address space, mask, NMI, preemption
               stack) and the run status of every context;
             * the locks with owner, ticket queue and hand-off; the authority state;
             * ONE execution graph of M3 (the memory and the execution witness of the run);
             * the outstanding catalogue questions, the ARRIVED answers in global order and per context the
               number it CONSUMED (§3.6: arrival and consumption are tracked separately);
             * the typestate of every lendable region.
-/
module

public import Core.Maschine.Sperre
public import Core.Maschine.Griff
public import Core.Maschine.Ergebnis
public import Core.Maschine.Speicherfolge
public import Core.Maschine.Buchung

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

/-- **The run status of a context**: not started, running, ended with an outcome. -/
inductive Status (Wert Grund : Type) where
  | ruht
  | laeuft
  | beendet (e : Ende Wert Grund)

/-- **A state of the machines.** `L` the locks, `Ort`/`Wert` the
    locations and values of memory events, `Raum` the address spaces, `Lok` the local state of a
    context, `Grund` the reason exits. -/
structure Zustand (L Ort Wert Raum Lok Grund : Type) where
  lokal : Kontext → Lok
  status : Kontext → Status Wert Grund
  kerne : Kern → KernZustand Raum
  sperren : L → SperrZustand
  rechte : Rechte
  graph : SpeicherGraph Ort Wert
  fragen : List FrageEreignis
  antworten : List AntwortEreignis
  verlauf : AussenVerlauf
  verbraucht : Kontext → Nat
  geliefert : List (Nat × Nat)
  leihen : Nat → Leihe Objekt
  initial : Ort → Wert
  persistenz : PersistZustand
  epoche : Nat
  verworfen : Kontext → Nat
  buchung : Sicherheit.Buchung Ort := .leer
  /-- **The number of the next thread to start** (MK-07): a start gives the new thread the context
      `faden naechsterFaden` and advances the counter, so no number is ever used twice. A start state has
      only the entry thread `faden 0`, hence `1`. -/
  naechsterFaden : Nat := 1
  /-- **The creator of every context** (MK-07): a start records the acting context as the creator of the
      new thread. A join requires the creator and clears the entry, so only the creator joins and only
      once; a second join has no step. The entry thread and never-started threads have no creator. -/
  erzeuger : Kontext → Option Kontext := fun _ => none

namespace Zustand

variable {L Ort Wert Raum Lok Grund : Type}

/-- The answers that arrived for a context, in arrival order. -/
def angekommen (z : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) :
    List AntwortEreignis :=
  z.antworten.filter (fun e => e.context == c.nummer)

/-- **Arrival and consumption**: a context consumes only answers that arrived. -/
def Verbrauch (z : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ c, z.verworfen c + z.verbraucht c ≤ (z.angekommen c).length

/-- Every arrived answer is one the catalogue allows at its commit snapshot. -/
def Zulaessig (z : Zustand L Ort Wert Raum Lok Grund) (k : Katalog.Katalog)
    (sicht : Nat → AussenSicht) : Prop :=
  ∀ e ∈ z.antworten, k.zulaessig (sicht e.cut) e.question e.reply

/-- **The graph part is a consistent, complete prefix** (M3). -/
def SpeicherGut (z : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  z.graph.graph.Konsistent ∧ z.graph.graph.Vollstaendig

/-- **A start state**: the given local states and cores, every lock free, the given authority, no
    memory event, no question, no answer, every region owned. -/
def start (lok : Kontext → Lok) (st : Kontext → Status Wert Grund) (kerne : Kern → KernZustand Raum)
    (r : Rechte) (initial : Ort → Wert) (medium : PersistZustand) : Zustand L Ort Wert Raum Lok Grund where
  lokal := lok
  status := st
  kerne := kerne
  sperren := fun _lock => SperrZustand.frei
  rechte := r
  graph := Speicher.Zustand.leer
  fragen := []
  antworten := []
  verlauf := []
  verbraucht := fun _context => 0
  geliefert := []
  leihen := fun _region => .eigen
  initial := initial
  persistenz := medium
  epoche := 0
  verworfen := fun _context => 0

/-- **Satisfiability of the start's invariants**: a start state has a consistent complete memory,
    consumes nothing that did not arrive and holds only allowed answers. -/
theorem start_gut (lok : Kontext → Lok) (st : Kontext → Status Wert Grund)
    (kerne : Kern → KernZustand Raum) (r : Rechte) (initial : Ort → Wert) (medium : PersistZustand)
    (k : Katalog.Katalog) (sicht : Nat → AussenSicht) :
    (start (L := L) (Ort := Ort) lok st kerne r initial medium).SpeicherGut ∧
      (start (L := L) (Ort := Ort) lok st kerne r initial medium).Verbrauch ∧
      (start (L := L) (Ort := Ort) lok st kerne r initial medium).Zulaessig k sicht :=
  ⟨⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩,
    fun _ => Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩

end Zustand

end Gabbro.Core.Maschine
