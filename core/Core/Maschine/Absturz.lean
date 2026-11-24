module

public import Core.Maschine.Aussen

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

/-- Boot data computed from the entry declaration and granted inputs. -/
structure Startdaten (Wert Raum Lok Grund : Type) where
  lokal : Kontext → Lok
  status : Kontext → Status Wert Grund
  kerne : Kern → KernZustand Raum
  rechte : Rechte

/-- The declared restart entry, its core, and its initial data. The declaration sees the
    durable bytes only. Recovery code itself steps through the ordinary form rules. -/
structure Wiederanlauf (Ort Wert Raum Lok Grund : Type) where
  eintritt : Kontext
  kern : Kern
  daten : (Nat → UInt8) → Startdaten Wert Raum Lok Grund
  initial : (Nat → UInt8) → Ort → Wert

abbrev SpeicherSpur (Ort Wert : Type) := List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)

structure SchrittSpur (Ort Wert : Type) where
  speicher : SpeicherSpur Ort Wert
  aussen : List Ereignis

def AbsturzAngeboten (k : Katalog.Katalog) (run : HwLauf) (t : Nat) : Prop :=
  k.enthaelt .persistence ∧ (run.angebot t).crash = true

variable {L Ort Wert Raum Lok Grund : Type}

/-- The persistence row retains its durable bytes and ordering metadata. -/
def nachAbsturz (s : PersistZustand) : PersistZustand :=
  { s with fluechtig := [], eingereiht := [] }

theorem persistenz_absturz_iff {r : Strecke} {s p : PersistZustand} :
    persistenz r s .crash p ↔ p = nachAbsturz s :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .crash s⟩

/-- Reset the volatile machine and dispatch the recovery entry. The outside ledgers record
    past events, while the epoch and cancellation counters exclude all pre-crash pending work. -/
def Zustand.wiederanlauf (s : Zustand L Ort Wert Raum Lok Grund)
    (w : Wiederanlauf Ort Wert Raum Lok Grund) (t : Nat) (p : PersistZustand) :
    Zustand L Ort Wert Raum Lok Grund :=
  let d := w.daten p.dauerhaft
  let status := fun c => if c = w.eintritt then .laeuft else .ruht
  let kerne := fun k => { d.kerne k with
    laeuft := if k = w.kern then some w.eintritt else none
    nmiAktiv := false
    stapel := [] }
  { Zustand.start d.lokal status kerne d.rechte (w.initial p.dauerhaft) p with
    fragen := s.fragen
    antworten := s.antworten
    verlauf := s.verlauf
    verbraucht := s.verbraucht
    verworfen := fun c => (s.angekommen c).length - s.verbraucht c
    epoche := t + 1 }

def absturzSpur : SchrittSpur Ort Wert := ⟨[], [.persistenz .crash]⟩

/-- The crash boundary both loses volatile state and prepares the declared entry. Subsequent
    hardware opportunities drive that entry's ordinary continuation. -/
def AbsturzSchritt (region : Strecke) (w : Wiederanlauf Ort Wert Raum Lok Grund)
    (k : Katalog.Katalog) (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  AbsturzAngeboten k run t ∧ spur = absturzSpur ∧
    ∃ p, persistenz region s.persistenz .crash p ∧ s' = s.wiederanlauf w t p

theorem absturz_schritt_erfuellbar (region : Strecke) (w : Wiederanlauf Ort Wert Raum Lok Grund)
    {k run t} (offer : AbsturzAngeboten k run t) (s : Zustand L Ort Wert Raum Lok Grund) :
    AbsturzSchritt region w k run t s absturzSpur (s.wiederanlauf w t (nachAbsturz s.persistenz)) :=
  ⟨offer, rfl, _, .crash _, rfl⟩

theorem AbsturzSchritt.genau {region w k run t} {s s' : Zustand L Ort Wert Raum Lok Grund} {spur}
    (h : AbsturzSchritt region w k run t s spur s') :
    spur = absturzSpur ∧ s' = s.wiederanlauf w t (nachAbsturz s.persistenz) := by
  obtain ⟨_, label, p, crash, rfl⟩ := h
  exact ⟨label, congrArg (s.wiederanlauf w t) (persistenz_absturz_iff.mp crash)⟩

theorem AbsturzSchritt.medienzeile {region w k run t} {s s' : Zustand L Ort Wert Raum Lok Grund} {spur}
    {h : Umgebung} (step : AbsturzSchritt region w k run t s spur s') (hardware : Hardware k h) :
    h.medium region s.persistenz .crash s'.persistenz := by
  obtain ⟨offer, _, p, crash, rfl⟩ := step
  exact (hardware.persistence _ _ _ _).mpr ⟨offer.1, crash⟩

theorem AbsturzSchritt.neustart {region w k run t} {s s' : Zustand L Ort Wert Raum Lok Grund} {spur}
    (step : AbsturzSchritt region w k run t s spur s') :
    s'.persistenz.dauerhaft = s.persistenz.dauerhaft ∧
      s'.persistenz.fluechtig = [] ∧ s'.persistenz.eingereiht = [] ∧
      s'.initial = w.initial s.persistenz.dauerhaft ∧
      s'.status w.eintritt = .laeuft ∧ (s'.kerne w.kern).laeuft = some w.eintritt ∧
      s'.epoche = t + 1 ∧ s'.SpeicherGut := by
  rw [step.genau.2]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl, Speicher.Zustand.leer_konsistent,
    Speicher.Zustand.leer_vollstaendig⟩
  · simp only [Zustand.wiederanlauf, Zustand.start, ↓reduceIte]
  · simp only [Zustand.wiederanlauf, Zustand.start, ↓reduceIte]

theorem AbsturzSchritt.verbrauch {region w k run t} {s s' : Zustand L Ort Wert Raum Lok Grund} {spur}
    (step : AbsturzSchritt region w k run t s spur s') (vorher : s.Verbrauch) :
    s'.Verbrauch ∧ ∀ c, s'.naechsteAntwort c = none := by
  have used (c : Kontext) : s.verbraucht c ≤ (s.angekommen c).length :=
    Nat.le_trans (Nat.le_add_left _ _) (vorher c)
  have index (c : Kontext) :
      (s.angekommen c).length - s.verbraucht c + s.verbraucht c = (s.angekommen c).length :=
    Nat.sub_add_cancel (used c)
  rw [step.genau.2]
  constructor
  · intro c
    change (s.angekommen c).length - s.verbraucht c + s.verbraucht c ≤ (s.angekommen c).length
    exact (index c).le
  · intro c
    change (s.angekommen c)[(s.angekommen c).length - s.verbraucht c + s.verbraucht c]? = none
    exact List.getElem?_eq_none (index c).symm.le

end Gabbro.Core.Maschine
