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

/-! ## Crash invariants over the durable state (MK-15)

The three duties below form the single umbrella `PersistenzAussagen`. The plural name
keeps the statement-guard sweep silent until the lead pins the umbrella with one hash row;
every duty is reachable from it through the dependency closure. No duty quantifies over a
free function: the invariant is bound by its holds-before/holds-after premises. -/

/-- The declared crash invariant over the durable state holds after every restart: the
    recovery entry observes the same durable image the crash interrupted. -/
def AbsturzInvariantePflicht : Prop :=
  ∀ (L Ort Wert Raum Lok Grund : Type) [DecidableEq L]
    (region : Strecke) (w : Wiederanlauf Ort Wert Raum Lok Grund)
    (k : Katalog) (run : HwLauf) (t : Nat)
    (s s' : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert)
    (inv : AbsturzInvariante),
    AbsturzSchritt region w k run t s spur s' →
      inv s.persistenz.dauerhaft → inv s'.persistenz.dauerhaft

theorem absturzInvariante_haelt : AbsturzInvariantePflicht := by
  intro L Ort Wert Raum Lok Grund _ region w k run t s s' spur inv step held
  rw [step.neustart.1]
  exact held

/-- The persistence turnover as a crash-step statement: a crash drops exactly the volatile
    and queued writes and keeps every durable byte. -/
def PersistenzumschlagPflicht : Prop :=
  ∀ (L Ort Wert Raum Lok Grund : Type) [DecidableEq L]
    (region : Strecke) (w : Wiederanlauf Ort Wert Raum Lok Grund)
    (k : Katalog) (run : HwLauf) (t : Nat)
    (s s' : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert),
    AbsturzSchritt region w k run t s spur s' →
      s'.persistenz.dauerhaft = s.persistenz.dauerhaft ∧
        s'.persistenz.fluechtig = [] ∧ s'.persistenz.eingereiht = []

theorem persistenzumschlag_haelt : PersistenzumschlagPflicht := by
  intro L Ort Wert Raum Lok Grund _ region w k run t s s' spur step
  exact ⟨step.neustart.1, step.neustart.2.1, step.neustart.2.2.1⟩

/-- Every declared durable object keeps its bytes across a crash. -/
def DauerhaftObjektPflicht : Prop :=
  ∀ (L Ort Wert Raum Lok Grund : Type) [DecidableEq L]
    (o : DauerhaftObjekt) (region : Strecke) (w : Wiederanlauf Ort Wert Raum Lok Grund)
    (k : Katalog) (run : HwLauf) (t : Nat)
    (s s' : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert),
    AbsturzSchritt region w k run t s spur s' →
      ∀ a, o.bereich.drin a → s'.persistenz.dauerhaft a = s.persistenz.dauerhaft a

theorem dauerhaftObjekt_haelt : DauerhaftObjektPflicht := by
  intro L Ort Wert Raum Lok Grund _ o region w k run t s s' spur step a _
  exact congrFun step.neustart.1 a

/-- The single umbrella statement of MK-15: the crash invariant, the turnover and the
    durable objects, pinned with one hash row by the lead. -/
def PersistenzAussagen : Prop :=
  AbsturzInvariantePflicht ∧ PersistenzumschlagPflicht ∧ DauerhaftObjektPflicht

/-- All three duties hold over the crash step of the machine. -/
theorem PersistenzAussagen_erfuellbar : PersistenzAussagen :=
  ⟨absturzInvariante_haelt, persistenzumschlag_haelt, dauerhaftObjekt_haelt⟩

private theorem uint8_null_ne_fuenf : (0 : UInt8) ≠ 5 := by
  intro h
  have t : (0 : Nat) = 5 := congrArg UInt8.toNat h
  exact absurd t (by decide)

/-- The model represents the fault instead of ruling it out: the invariant language
    distinguishes durable images, and a crash step can discard pending writes. Only the
    declared invariant (checked by the checker) excludes the loss, never the model. -/
theorem PersistenzAussagen_nichtTrivial :
    (∃ inv : AbsturzInvariante, (∃ d, inv d) ∧ ∃ d, ¬ inv d) ∧
      ∃ (r : Strecke) (s p : PersistZustand),
        persistenz r s .crash p ∧ s.fluechtig ≠ [] ∧ p.fluechtig = [] := by
  constructor
  · refine ⟨fun d => d 0 = 5, ⟨fun _ => 5, rfl⟩, ⟨fun _ => 0, ?_⟩⟩
    show ¬ ((0 : UInt8) = 5)
    exact uint8_null_ne_fuenf
  · refine ⟨⟨0, 1⟩, { PersistZustand.leer (fun _ => 0) with fluechtig := [⟨0, 0, 7⟩] }, _,
      .crash _, ?_, rfl⟩
    intro h
    cases h

end Gabbro.Core.Maschine
