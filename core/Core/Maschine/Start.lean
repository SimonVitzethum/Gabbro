module

public import Core.Maschine.Zeitlauf

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- The unit supplies its rules, image declaration, canonical source initialisation and the
    implementation loader. Loader failure is represented by an empty implementation state. -/
structure Einheit (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type) where
  katalog : Katalog.Katalog
  bild : Bild
  einrichtung : Einrichtung L Ort Wert Raum Lok Grund Bedingung
  system : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι
  startdaten : AussenStart → Startdaten Wert Raum Lok Grund
  startmedium : AussenStart → Nat → UInt8
  laden : AussenStart → Ladung → Option (Zustand L Ort Wert Raum Lok Grund)

variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)

/-- The catalogue judges starts before either machine initialises, independently of loader success. -/
def Einheit.ZulStart (h : Umgebung) (s : AussenStart) : Prop :=
  Katalog.ZulStart E.katalog h E.bild s

namespace I

/-- Canonical ideal initialisation keeps the entire catalogue start at the initial cut. -/
def start (s : AussenStart) : AussenStart × Zustand L Ort Wert Raum Lok Grund :=
  let d := E.startdaten s
  (s, Zustand.start d.lokal d.status d.kerne d.rechte E.einrichtung.initial
    (.leer (E.startmedium s)))

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

/-- Every offered crash is taken at a cut with a loaded implementation state. -/
theorem absturz_am_schnitt {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}
    {ρ : Lauf E} {t : Nat} {s : Zustand L Ort Wert Raum Lok Grund}
    (atCut : ρ.zeit.zustand t = some s) (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ∃ spur next, ρ.zeit.spur t = some spur ∧ ρ.zeit.zustand (t + 1) = some next ∧
      AbsturzSchritt E.einrichtung.persistenzRegion E.einrichtung.wiederanlauf E.katalog ρ.hw t s spur next := by
  have tick := ρ.zeit.takt t
  rw [atCut] at tick
  cases tick with
  | schritt label step =>
    cases transition : ρ.zeit.zustand (t + 1) with
    | none =>
      rw [transition] at step
      cases step
    | some next =>
      rw [transition] at step
      cases step with
      | schritt h => exact ⟨_, next, label, rfl, h.absturzfall _ _ offer⟩
  | wartet _ _ pause =>
    exact (pause _ _ (.schritt (.absturz (absturz_schritt_erfuellbar _ _ offer s)))).elim

/-- A crash can be placed at any chosen cut of a fair hardware history selecting the row. -/
theorem fairer_absturz_erfuellbar {k h hw} (fair : FairLaeufe k h hw)
    (selected : k.enthaelt .persistence) (crashCut : Nat) :
    ∃ next, FairLaeufe k h next ∧ AbsturzAngeboten k next crashCut := by
  let next : HwLauf := { hw with
    angebot := fun t => { hw.angebot t with crash := if t = crashCut then true else (hw.angebot t).crash } }
  refine ⟨next, ⟨fair.hardware, fair.politik, ?_, fair.kerne, fair.interrupts,
    fair.auslieferung, fair.medium, fair.cycles, fair.zeit⟩, selected, ?_⟩
  · intro t
    have valid := fair.gueltig t
    exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, fun _ => selected⟩
  · simp only [next, ↓reduceIte]

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
  zeit : Zeitlauf (Schritt E.einrichtung E.system E.katalog hw) (fun t _ => ¬ AbsturzAngeboten E.katalog hw t)

abbrev Schnitt (ρ : Lauf E) : Type := ρ.zeit.Schnitt

def ZustandAm (ρ : Lauf E) (t : Schnitt E ρ) : AussenStart × Zustand L Ort Wert Raum Lok Grund :=
  (ρ.start, ρ.zeit.zustand t.val)

def Laeufe (ρ : Lauf E) : Prop :=
  Hardware E.katalog ρ.umgebung ∧ ρ.hw.konform E.katalog ρ.umgebung ∧
    E.ZulStart ρ.umgebung ρ.start ∧ ρ.zeit.zustand 0 = (start E ρ.start).2 ∧ ρ.zeit.Maximal

/-- A crash offer is mandatory even at an ideal cut where a private step could normally pause. -/
theorem absturz_am_schnitt (ρ : Lauf E) {t : Nat} (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ρ.zeit.spur t = some (.absturz, absturzSpur) ∧
      AbsturzSchritt E.einrichtung.persistenzRegion E.einrichtung.wiederanlauf E.katalog ρ.hw t
        (ρ.zeit.zustand t) absturzSpur (ρ.zeit.zustand (t + 1)) := by
  cases ρ.zeit.takt t with
  | schritt label step =>
    obtain ⟨wahl, crash⟩ := step.absturzfall _ _ offer
    exact ⟨label.trans (congrArg some (Prod.ext wahl crash.genau.1)), crash.genau.1 ▸ crash⟩
  | wartet _ _ pause => exact (pause offer).elim

theorem anfang (ρ : Lauf E) (h : Laeufe E ρ) :
    ZustandAm E ρ ⟨0, Or.inl rfl⟩ = start E ρ.start :=
  Prod.ext rfl h.2.2.2.1

theorem lauf_mit_hw {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) (konform : hw.konform E.katalog h) :
    ∃ ρ, Laeufe E ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert (Schritt E.einrichtung E.system E.katalog hw) (I.start E s).2
  have pause t z (stuck : KeinSchritt (Schritt E.einrichtung E.system E.katalog hw) t z) :
      ¬ AbsturzAngeboten E.katalog hw t :=
    fun offer => stuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer z))
  exact ⟨⟨s, h, hw, zeit.erlaubePausen pause⟩,
    ⟨hardware, konform, start, init, zeit.erlaubePausen_maximal pause⟩, rfl, rfl⟩

end I

/-- An admissible fair history can exercise the crash boundary in both machines. The
    implementation premise records an actual successful load, as for the generic cut lemma. -/
theorem absturz_laeufe_erfuellbar {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    {z : Zustand L Ort Wert Raum Lok Grund}
    (start : E.ZulStart h s) (fair : FairLaeufe E.katalog h hw)
    (selected : E.katalog.enthaelt .persistence) (loaded : E.laden s (h.lade E.bild) = some z) :
    ∃ ρ : Lauf E, ∃ η : I.Lauf E, Laeufe E h ρ ∧ I.Laeufe E η ∧
      ρ.start = s ∧ η.start = s ∧ ρ.hw = η.hw ∧ FairLaeufe E.katalog h ρ.hw ∧
      ρ.zeit.spur 0 = some absturzSpur ∧ η.zeit.spur 0 = some (.absturz, absturzSpur) := by
  obtain ⟨crashHw, fairCrash, offer⟩ := fairer_absturz_erfuellbar fair selected 0
  obtain ⟨ρ, run, startEq, hwEq⟩ := fairer_lauf E start fairCrash
  obtain ⟨η, ideal, startEq', hwEq'⟩ := I.lauf_mit_hw E fairCrash.hardware start fairCrash.konform
  have load : ρ.zeit.zustand 0 = some z := by
    rw [run.2.2.2, startEq, loaded]
  obtain ⟨_, _, label, _, crash⟩ := absturz_am_schnitt load (hwEq.symm ▸ offer)
  obtain ⟨label', _⟩ := I.absturz_am_schnitt E η (hwEq'.symm ▸ offer)
  exact ⟨ρ, η, run, ideal, startEq, startEq', hwEq.trans hwEq'.symm, hwEq.symm ▸ fairCrash,
    label.trans (congrArg some crash.genau.1), label'⟩

end Gabbro.Core.Maschine
