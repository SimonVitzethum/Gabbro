module

public import Core.Beobachtung.SchrankenB9B21Pflichten
public import Core.Annahme.HostedLauf
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast
open Annahme.Hosted

private def probeFortsetzung : Semantik.Fortsetzung :=
  ⟨0, fun _ => none, [], fun _ => none, fun _ => none, none, none, none⟩

private def probeRahmen (r : Semantik.Rahmen) : Semantik.Rahmen :=
  { r with fortsetzungen := probeFortsetzung :: r.fortsetzungen }

private def probeZustand (s : Semantik.Zustand) (c : Kontext) : Semantik.Zustand :=
  { s with lokal := Function.update s.lokal c (probeRahmen (s.lokal c)) }

private def probeRegel (b : Semantik.Befehl) : Regel Semantik.Zustand Semantik.Plan PUnit :=
  ⟨fun _ _ _ _ _ => False,
    fun c s _ plans u => plans = [Semantik.plan] ∧ u = probeZustand s c⟩

private theorem probe_aus (t : Nat) (s : Semantik.Zustand) (c : Kontext) :
    FuehrtSchrittAus (Semantik.einrichtung []) t c s (probeZustand s c) Semantik.plan
      ⟨[], []⟩ (probeZustand s c) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro l mem
    exact (List.not_mem_nil mem).elim
  · refine ⟨[], probeZustand s c, .intern, ?_, rfl⟩
    exact .nil _

private def probeSystem (b : Semantik.Befehl) : Semantik.LokalSystem :=
  ⟨fun _ => probeRegel b,
    fun s c => if c = Semantik.eintritt then some b else none,
    fun _ _ => False, fun _ _ _ => False⟩

private def probeEinheit (b : Semantik.Befehl) : Semantik.Einheit :=
  { katalog := Plattform.x86_64.katalog
    bild := Semantik.bild
    einrichtung := Semantik.einrichtung []
    system := probeSystem b
    startdaten := fun s => Semantik.startdaten [] (s.assignment 0) Plattform.x86_64 s.regions
    startmedium := Semantik.startmedium
    laden := Semantik.laden [] Plattform.x86_64
    lokalerBezug := Eq
    stotterLaenge := fun _ => 0
    quelltabellen := .leer
    schranken := { Schrankendaten.leer with
      stapel := some 0, stapelTiefe := fun r => r.fortsetzungen.length } }

private theorem probe_tiefe (b : Semantik.Befehl) :
    ∀ r : Semantik.Rahmen, (probeEinheit b).schranken.stapelTiefe r = r.fortsetzungen.length :=
  fun _ => rfl

private def probeFolge (b : Semantik.Befehl) (start : AussenStart) : Nat → Semantik.Zustand
  | 0 => (I.start (probeEinheit b) start).2
  | t + 1 => probeZustand (probeFolge b start t) Semantik.eintritt

private theorem probe_bereit (b : Semantik.Befehl) (start : AussenStart) (t : Nat)
    (zu : start.assignment 0 = some 0) :
    KannSchreiten (Hosted.hardware []) t Semantik.eintritt (probeFolge b start t) := by
  have felder : (probeFolge b start t).kerne = (probeFolge b start 0).kerne ∧
      (probeFolge b start t).status = (probeFolge b start 0).status := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih =>
      simp only [probeFolge, probeZustand, ih.1, ih.2, and_self]
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

private theorem probe_schritt (b : Semantik.Befehl) (start : AussenStart) (t : Nat)
    (zu : start.assignment 0 = some 0) :
    I.Schritt (probeEinheit b).einrichtung (probeEinheit b).system (probeEinheit b).katalog
      (Hosted.hardware []) t (probeFolge b start t)
      (.kontext Semantik.eintritt (), ⟨[], []⟩) (probeFolge b start (t + 1)) := by
  refine .kontext ?_ (probe_bereit b start t zu) ?_ (probe_aus t _ _)
  · rfl
  · refine ⟨b, ?_, ⟨by rfl, by rfl⟩⟩
    simp only [probeEinheit, probeSystem, ↓reduceIte]

private theorem probe_nicht_regel (b : Semantik.Befehl) :
    ¬ RegelSchranken (probeEinheit b) b := by
  intro rs
  obtain ⟨start, zul⟩ := zulStart_erfuellbar (Hosted.erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  have zu : start.assignment 0 = some 0 := by
    obtain ⟨c, hc⟩ := zul.2.2.1 0 (by decide : 0 < Sicherheit.Laufkonstruktion.bild.entries.length)
    have hc0 : c = 0 := Nat.lt_one_iff.mp (zul.2.2.2.1 0 c hc).2
    simpa [hc0] using hc
  let E := probeEinheit b
  let η : I.Lauf E :=
    ⟨start, Hosted.umgebung [], Hosted.hardware [],
      ⟨fun t => probeFolge b start t,
        fun _ => some (.kontext Semantik.eintritt (), ⟨[], []⟩),
        fun t => .schritt rfl (probe_schritt b start t zu)⟩, fun _ => none⟩
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
  have kopf0 : (probeEinheit b).system.kopf (probeFolge b start 0) Semantik.eintritt = some b := by
    simp only [probeEinheit, probeSystem, ↓reduceIte]
  have grenzen := rs lauf 0 Semantik.eintritt () ⟨[], []⟩ (probeFolge b start 0)
    (probeFolge b start 1) rfl kopf0 rfl rfl
    (probe_schritt b start 0 zu) ?_ ?_
  · have bound : ((probeZustand (probeFolge b start 0) Semantik.eintritt).lokal
        Semantik.eintritt).fortsetzungen.length ≤ 0 := grenzen.1 Semantik.eintritt 0 rfl
    simp only [probeZustand, Function.update_self, probeRahmen, List.length_cons] at bound
    exact (Nat.not_succ_le_zero _) bound
  · intro c n eq
    cases Option.some.inj eq
    change ((Semantik.startdaten [] (start.assignment 0) Plattform.x86_64 start.regions).lokal c).fortsetzungen.length ≤ 0
    simp only [Semantik.startdaten, Semantik.Rahmen.start, List.map_nil, List.length_nil]
    exact Nat.zero_le _
  · intro n eq
    cases eq

private theorem probe_nicht_aggregat : ¬ aggregatSchrankenAussage := by
  intro h
  let b := Semantik.Befehl.baueArray 0 (.int 0 0) 0
  exact probe_nicht_regel b ((h (probeEinheit b) (probe_tiefe b)).1 0 (.int 0 0) 0)

private theorem probe_nicht_text : ¬ textSchrankenAussage := by
  intro h
  let b := Semantik.Befehl.textLiteral 0 []
  exact probe_nicht_regel b ((h (probeEinheit b) (probe_tiefe b)).1 0 [])

private theorem probe_nicht_region : ¬ regionSchrankenAussage := by
  intro h
  let b := Semantik.Befehl.bindeRegion 0 .address
  exact probe_nicht_regel b (h (probeEinheit b) (probe_tiefe b) 0 .address)

end Gabbro.Core.Beobachtung
