module

public import Core.Maschine.Zeitlauf

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- Initial machine data computed from the declared entries and granted boot input. -/
structure Startdaten (Wert Raum Lok Grund : Type) where
  lokal : Kontext → Lok
  status : Kontext → Status Wert Grund
  kerne : Kern → KernZustand Raum
  rechte : Rechte

/-- The unit supplies its rules, image declaration, canonical source initialisation and the
    implementation loader. Loader failure is represented by an empty implementation state. -/
structure Einheit (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type) where
  katalog : Katalog.Katalog
  bild : Bild
  einrichtung : Einrichtung L Ort Wert Raum Lok Grund Bedingung
  system : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι
  startdaten : AussenStart → Startdaten Wert Raum Lok Grund
  laden : AussenStart → Ladung → Option (Zustand L Ort Wert Raum Lok Grund)

variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)

/-- The catalogue judges starts before either machine initialises, independently of loader success. -/
def Einheit.ZulStart (h : Umgebung) (s : AussenStart) : Prop :=
  Katalog.ZulStart E.katalog h E.bild s

namespace I

/-- Canonical ideal initialisation keeps the entire catalogue start at the initial cut. -/
def start (s : AussenStart) : AussenStart × Zustand L Ort Wert Raum Lok Grund :=
  let d := E.startdaten s
  (s, Zustand.start d.lokal d.status d.kerne d.rechte)

theorem start_grenze (s : AussenStart) :
    (start E s).1.inputBytes = s.inputBytes ∧ (start E s).1.assignment = s.assignment ∧
      (start E s).1.outside = s.outside :=
  ⟨rfl, rfl, rfl⟩

end I

variable [DecidableEq L]

/-- Implementation failure is terminal. A working state follows the concrete step relation. -/
inductive Lauffolge (hw : HwLauf) (t : Nat) :
    Option (Zustand L Ort Wert Raum Lok Grund) → SchrittSpur Ort Wert →
      Option (Zustand L Ort Wert Raum Lok Grund) → Prop where
  | schritt {s s' spur} (h : ImplSchritt E.einrichtung E.system E.katalog hw t s spur s') :
      Lauffolge hw t (some s) spur (some s')

structure Lauf where
  start : AussenStart
  hw : HwLauf
  zeit : Zeitlauf (Lauffolge E hw)

def Schnitt (ρ : Lauf E) : Type := ρ.zeit.Schnitt

/-- Maximal implementation runs, with the recorded hardware schedule and its total policy. -/
def Laeufe (h : Umgebung) (ρ : Lauf E) : Prop :=
  Hardware E.katalog h ∧ ρ.hw.konform E.katalog h ∧ E.ZulStart h ρ.start ∧
    ρ.zeit.zustand 0 = E.laden ρ.start (h.lade E.bild)

theorem lauf_mit_hw {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) (konform : hw.konform E.katalog h) :
    ∃ ρ, Laeufe E h ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert (Lauffolge E hw) (E.laden s (h.lade E.bild))
  exact ⟨⟨s, hw, zeit⟩, ⟨hardware, konform, start, init⟩, rfl, rfl⟩

/-- The fair-history lift with the exact start and hardware projection of the seventh conjunct. -/
theorem fairer_lauf {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (start : E.ZulStart h s) (fair : FairLaeufe E.katalog h hw) :
    ∃ ρ, Laeufe E h ρ ∧ ρ.start = s ∧ ρ.hw = hw :=
  lauf_mit_hw E fair.hardware start fair.konform

theorem lauf_ab_start {h : Umgebung} {s : AussenStart}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) :
    ∃ ρ, Laeufe E h ρ ∧ ρ.start = s := by
  let hw : HwLauf := ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩, h.politik⟩
  have konform : hw.konform E.katalog h := by
    refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact fun _ h => nomatch h
    · exact fun _ h => nomatch h
    · exact fun _ h => (List.not_mem_nil h).elim
    · exact fun _ h => nomatch h
    · exact fun h => h.elim (fun h => nomatch h) (fun h => nomatch h)
  obtain ⟨ρ, run, sameStart, _⟩ := lauf_mit_hw E hardware start konform
  exact ⟨ρ, run, sameStart⟩

theorem lauf_erfuellbar (katalog : KatalogWohlgeformt E.katalog) (bild : E.bild.gueltig E.katalog.plattform.ziel) :
    ∃ h s hw ρ, E.ZulStart h s ∧ FairLaeufe E.katalog h hw ∧
      Laeufe E h ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  obtain ⟨h, hw, hardware, fair⟩ := katalog_nichtLeer E.katalog katalog
  obtain ⟨s, start⟩ := zulStart_erfuellbar hardware bild
  obtain ⟨ρ, run, sameStart, sameHw⟩ := fairer_lauf E start fair
  exact ⟨h, s, hw, ρ, start, fair, run, sameStart, sameHw⟩

theorem ladefehler_endlich (ρ : Lauf E) (failure : ρ.zeit.zustand 0 = none) :
    ρ.zeit.Endlich := by
  have idle (t : Nat) (absent : ρ.zeit.zustand t = none) :
      ρ.zeit.spur t = none ∧ ρ.zeit.zustand (t + 1) = none := by
    cases ρ.zeit.takt t with
    | schritt _label step =>
      rw [absent] at step
      cases step
    | wartet label eq _pause => exact ⟨label, eq.trans absent⟩
  have absent (t : Nat) : ρ.zeit.zustand t = none := by
    induction t with
    | zero => exact failure
    | succ t ih => exact (idle t ih).2
  exact ⟨⟨0, Or.inl rfl⟩, fun t _ => (idle t (absent t)).1⟩

namespace I

structure Lauf where
  start : AussenStart
  umgebung : Umgebung
  hw : HwLauf
  zeit : Zeitlauf (Schritt E.einrichtung E.system E.katalog hw) (fun _ _ => True)

abbrev Schnitt (ρ : Lauf E) : Type := ρ.zeit.Schnitt

def ZustandAm (ρ : Lauf E) (t : Schnitt E ρ) : AussenStart × Zustand L Ort Wert Raum Lok Grund :=
  (ρ.start, ρ.zeit.zustand t.val)

def Laeufe (ρ : Lauf E) : Prop :=
  Hardware E.katalog ρ.umgebung ∧ ρ.hw.konform E.katalog ρ.umgebung ∧
    E.ZulStart ρ.umgebung ρ.start ∧ ρ.zeit.zustand 0 = (start E ρ.start).2 ∧ ρ.zeit.Maximal

theorem anfang (ρ : Lauf E) (h : Laeufe E ρ) :
    ZustandAm E ρ ⟨0, Or.inl rfl⟩ = start E ρ.start :=
  Prod.ext rfl h.2.2.2.1

theorem lauf_mit_hw {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) (konform : hw.konform E.katalog h) :
    ∃ ρ, Laeufe E ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert (Schritt E.einrichtung E.system E.katalog hw) (I.start E s).2
  exact ⟨⟨s, h, hw, zeit.erlaubePausen⟩, ⟨hardware, konform, start, init, zeit.erlaubePausen_maximal⟩, rfl, rfl⟩

end I

end Gabbro.Core.Maschine
