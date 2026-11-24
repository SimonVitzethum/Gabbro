/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Gegenbeispiel.lean
  Subject:   Counterexample to the three unpinned-by-a-footprint family duties.

  `aggregatSchrankenAussage`, `textSchrankenAussage` and `regionSchrankenAussage`
  quantify over an arbitrary unit `E` and only pin the depth interpretation
  `tiefe`. `RegelSchranken E b` however quantifies over the unit's own rule: with
  a finite stack ceiling and a rule that pushes one continuation, the pre-state
  meets the bound and the post-state does not. The unit below is admitted in the
  sense of `I.Laeufe` (its hardware, start and maximality are the standard ones),
  so the three assertions are false as pinned; each needs the per-form step
  footprint premise that `kontrollflussSkalarSchrankenAussage` already carries
  (or `E.system.regel b = b.regel`).
-/
module

public import Core.Beobachtung.SchrankenB9B21Pflichten
public import Core.Annahme.HostedLauf
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast
open Annahme.Hosted

private def gegenFortsetzung : Semantik.Fortsetzung :=
  ⟨0, fun _ => none, [], fun _ => none, fun _ => none, none, none, none⟩

private def gegenRahmen (r : Semantik.Rahmen) : Semantik.Rahmen :=
  { r with fortsetzungen := gegenFortsetzung :: r.fortsetzungen }

private def gegenZustand (s : Semantik.Zustand) (c : Kontext) : Semantik.Zustand :=
  { s with lokal := Function.update s.lokal c (gegenRahmen (s.lokal c)) }

private def gegenRegel (b : Semantik.Befehl) : Regel Semantik.Zustand Semantik.Plan PUnit :=
  ⟨fun _ _ _ _ _ => False,
    fun c s _ plans u => plans = [Semantik.plan] ∧ u = gegenZustand s c⟩

private theorem gegen_aus (t : Nat) (s : Semantik.Zustand) (c : Kontext) :
    FuehrtSchrittAus (Semantik.einrichtung []) t c s (gegenZustand s c) Semantik.plan
      ⟨[], []⟩ (gegenZustand s c) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro l mem
    exact (List.not_mem_nil mem).elim
  · refine ⟨[], gegenZustand s c, .intern, ?_, rfl⟩
    exact .nil _

private def gegenSystem (b : Semantik.Befehl) : Semantik.LokalSystem :=
  ⟨fun _ => gegenRegel b,
    fun s c => if c = Semantik.eintritt then some b else none,
    fun _ _ => False, fun _ _ _ => False⟩

private def gegenEinheit (b : Semantik.Befehl) : Semantik.Einheit :=
  { katalog := Plattform.x86_64.katalog
    bild := Semantik.bild
    einrichtung := Semantik.einrichtung []
    system := gegenSystem b
    startdaten := fun s => Semantik.startdaten [] (s.assignment 0) Plattform.x86_64 s.regions
    startmedium := Semantik.startmedium
    laden := Semantik.laden [] Plattform.x86_64
    lokalerBezug := Eq
    stotterLaenge := fun _ => 0
    quelltabellen := .leer
    schranken := { Schrankendaten.leer with
      stapel := some 0, stapelTiefe := fun r => r.fortsetzungen.length } }

private theorem gegen_tiefe (b : Semantik.Befehl) :
    ∀ r : Semantik.Rahmen, (gegenEinheit b).schranken.stapelTiefe r = r.fortsetzungen.length :=
  fun _ => rfl

private def gegenFolge (b : Semantik.Befehl) (start : AussenStart) : Nat → Semantik.Zustand
  | 0 => (I.start (gegenEinheit b) start).2
  | t + 1 => gegenZustand (gegenFolge b start t) Semantik.eintritt

private theorem gegen_bereit (b : Semantik.Befehl) (start : AussenStart) (t : Nat)
    (zu : start.assignment 0 = some 0) :
    KannSchreiten (Hosted.hardware []) t Semantik.eintritt (gegenFolge b start t) := by
  have felder : (gegenFolge b start t).kerne = (gegenFolge b start 0).kerne ∧
      (gegenFolge b start t).status = (gegenFolge b start 0).status := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih =>
      simp only [gegenFolge, gegenZustand, ih.1, ih.2, and_self]
  refine ⟨0, ?_, ?_, ?_⟩
  · simp only [HwLauf.gelegenheit, Umgebung.referenzLauf]
    exact congrArg some (Nat.mod_one t)
  · rw [felder.1]
    change ((Semantik.startdaten [] (start.assignment 0) Plattform.x86_64 start.regions).kerne 0).laeuft =
      some Semantik.eintritt
    rw [zu]
    simp only [Semantik.startdaten, ↓reduceIte]
  · rw [felder.2]
    change (Semantik.startdaten [] (start.assignment 0) Plattform.x86_64 start.regions).status
      Semantik.eintritt = .laeuft
    rw [zu]
    simp only [Semantik.startdaten, ↓reduceIte]

private theorem gegen_schritt (b : Semantik.Befehl) (start : AussenStart) (t : Nat)
    (zu : start.assignment 0 = some 0) :
    I.Schritt (gegenEinheit b).einrichtung (gegenEinheit b).system (gegenEinheit b).katalog
      (Hosted.hardware []) t (gegenFolge b start t)
      (.kontext Semantik.eintritt (), ⟨[], []⟩) (gegenFolge b start (t + 1)) := by
  refine .kontext ?_ (gegen_bereit b start t zu) ?_ (gegen_aus t _ _)
  · rfl
  · refine ⟨b, ?_, ⟨by rfl, by rfl⟩⟩
    simp only [gegenEinheit, gegenSystem, ↓reduceIte]

private theorem regelSchranken_wachsend_falsch (b : Semantik.Befehl) :
    ¬ RegelSchranken (gegenEinheit b) b := by
  intro rs
  obtain ⟨start, zul⟩ := zulStart_erfuellbar (Hosted.erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  have zu : start.assignment 0 = some 0 := by
    obtain ⟨c, hc⟩ := zul.2.2.1 0 (by decide : 0 < Sicherheit.Laufkonstruktion.bild.entries.length)
    have hc0 : c = 0 := Nat.lt_one_iff.mp (zul.2.2.2.1 0 c hc).2
    simpa [hc0] using hc
  let E := gegenEinheit b
  let η : I.Lauf E :=
    ⟨start, Hosted.umgebung [], Hosted.hardware [],
      ⟨fun t => gegenFolge b start t,
        fun _ => some (.kontext Semantik.eintritt (), ⟨[], []⟩),
        fun t => .schritt rfl (gegen_schritt b start t zu)⟩, fun _ => none⟩
  have lauf : I.Laeufe E η := by
    refine ⟨Hosted.erlaubt [], Hosted.konform [], ?_, ?_, ?_, ?_⟩
    · exact zul
    · rfl
    · constructor
      · intro t spurNone frei step event next
        cases spurNone
      · intro endlich
        obtain ⟨cut, quiet⟩ := endlich
        cases quiet cut.val (Nat.le_refl _)
    · intro t c belegt
      cases belegt
  have kopf0 : (gegenEinheit b).system.kopf (gegenFolge b start 0) Semantik.eintritt = some b := by
    simp only [gegenEinheit, gegenSystem, ↓reduceIte]
  have grenzen := rs lauf 0 Semantik.eintritt () ⟨[], []⟩ (gegenFolge b start 0)
    (gegenFolge b start 1) rfl kopf0 rfl rfl
    (gegen_schritt b start 0 zu) ?_ ?_
  · have bound : ((gegenZustand (gegenFolge b start 0) Semantik.eintritt).lokal
        Semantik.eintritt).fortsetzungen.length ≤ 0 := grenzen.1 Semantik.eintritt 0 rfl
    simp only [gegenZustand, Function.update_self, gegenRahmen, List.length_cons] at bound
    exact (Nat.not_succ_le_zero _) bound
  · intro c n eq
    cases Option.some.inj eq
    change ((Semantik.startdaten [] (start.assignment 0) Plattform.x86_64 start.regions).lokal c).fortsetzungen.length ≤ 0
    simp only [Semantik.startdaten, Semantik.Rahmen.start, List.map_nil, List.length_nil]
    exact Nat.zero_le _
  · intro n eq
    cases eq

theorem aggregatSchrankenAussage_falsch : ¬ aggregatSchrankenAussage := by
  intro h
  let b := Semantik.Befehl.baueArray 0 (.int 0 0) 0
  exact regelSchranken_wachsend_falsch b ((h (gegenEinheit b) (gegen_tiefe b)).1 0 (.int 0 0) 0)

theorem textSchrankenAussage_falsch : ¬ textSchrankenAussage := by
  intro h
  let b := Semantik.Befehl.textLiteral 0 []
  exact regelSchranken_wachsend_falsch b ((h (gegenEinheit b) (gegen_tiefe b)).1 0 [])

theorem regionSchrankenAussage_falsch : ¬ regionSchrankenAussage := by
  intro h
  let b := Semantik.Befehl.bindeRegion 0 .address
  exact regelSchranken_wachsend_falsch b (h (gegenEinheit b) (gegen_tiefe b) 0 .address)

end Gabbro.Core.Beobachtung
