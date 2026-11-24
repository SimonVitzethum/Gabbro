/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/Gegenbeispiel.lean
  Subject:   The pinned lift statement needs image validity; without it the statement is false.

  `Hebebuendel.replayZulaessig` demands an admitted run for every band. Admission
  (`Laeufe`) contains `Einheit.ZulStart`, whose first conjunct is the validity of
  the declared image. The pinned `hebeAussage` only assumes hardware conformity
  and the selected random row, so an otherwise admissible unit with an invalid
  image has no bundle. This module proves that obstruction and the resulting
  negation of the pinned statement, without changing statement, structure or pins.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Aussagen
public import Core.Annahme.Annahme
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Maschine
open Gabbro.Core.Annahme
open Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- Every bundle forces image validity: the replay is admitted for every band,
    admission contains `ZulStart`, and `ZulStart` starts with image validity. -/
theorem buendel_braucht_bild (B : Zufallsbindung) (S : Scheduler)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (hb : Hebebuendel B S E h) :
    E.bild.gueltig E.katalog.plattform.ziel := by
  exact (hb.replayZulaessig (fun _ _ => 0)).2.2.1.1

/-- The pinned statement `hebeAussage` is false: the trivial unit with an image
    that declares an entry without a backing byte has no admissible start, hence
    no bundle, while its catalogue and environment satisfy both premises. -/
theorem hebeAussage_falsch : ¬ hebeAussage := by
  intro H
  let k : Katalog := Plattform.x86_64.katalog
  let h : Umgebung := Umgebung.referenz k 2 (fun _ _ => AussenSicht.leer)
  have hw : Hardware k h :=
    Umgebung.referenz_hardware k 2 (fun _ _ => AussenSicht.leer)
      (Plattform.katalog_wohlgeformt .x86_64) (by decide)
  let Q : Zufallsquelle := muenzQuelle
  let B : Zufallsbindung := ⟨Q, .hosted, []⟩
  let S : Scheduler := ⟨fun _ _ => 0⟩
  let E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
    { trivialeEinheit with katalog := k, bild := ⟨Bildformat.elf, fun _ => none, [0]⟩ }
  have selected : E.katalog.enthaelt (Zeile.zufall B.quelle.id) := by
    simpa only [E, B, Q, muenzQuelle, k, Plattform.katalog, Katalog.enthaelt] using
      (show Zeile.zufall 0 ∈ Plattform.x86_64.katalog.zeilen by decide)
  obtain ⟨hb, _⟩ := H Unit Unit Unit Unit Unit Unit Unit Unit Unit E B S h hw selected
  have gueltig := buendel_braucht_bild B S E h hb
  have ungueltig : ¬ E.bild.gueltig E.katalog.plattform.ziel := by
    intro valid
    have backed := valid.2.2 0 (by simp only [E, List.mem_singleton])
    simp only [E] at backed
    obtain ⟨byte, eintrag⟩ := backed
    cases eintrag
  exact ungueltig gueltig

end Gabbro.Core.Beobachtung
