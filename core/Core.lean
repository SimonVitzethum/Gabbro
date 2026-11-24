/-
  File:      Core.lean
  Subject:   The package root of the new Gabbro model (`dokumente/PERFECT-MODEL.md`). Every module of `core/` is
             reached from here; `core/` never imports `grammatik/`.
-/
module
public import Core.Ziel.Form
public import Core.Ziel.Sicherheit
public import Core.Text.Model
public import Core.Ast
public import Core.Speicher
public import Core.Maschine
public import Core.Maschine.Schritte
public import Core.Maschine.Start
public import Core.Ideal
public import Core.Ideal.Linearisierung
public import Core.Ideal.Replay
public import Core.Ideal.Absturz
public import Core.Fortschritt.Klasse
public import Core.Fortschritt.Saetze
public import Core.Fortschritt.Verzoegerung
public import Core.Fortschritt.SperrHilfen
public import Core.Fortschritt.SperrSchranke
public import Core.Fortschritt.Beispiele
public import Core.Fortschritt.Verhungern
public import Core.Fortschritt.Sackgasse
public import Core.Fortschritt.WarteBeispiel
public import Core.Fortschritt.WarteBundle
public import Core.Fortschritt.SperrErhalt
public import Core.Fortschritt.SperrGegenbeispiel
public import Core.Fortschritt.SperrFair
public import Core.Katalog.Erfuellbar
public import Core.Aussen
public import Core.Annahme
public import Core.Sicherheit.Erfuellbar
public import Core.Sicherheit.RegelnErfuellbar
public import Core.Verfeinerung.Erfuellbar
public import Core.Verfeinerung.Formen.Erfuellbar
public import Core.Verfeinerung.Abnahme.StotterMass
public import Core.Verfeinerung.Abnahme.Flush
public import Core.Verfeinerung.Abnahme.LockFree
public import Core.Beobachtung.SchrankenErfuellbar
public import Core.Beobachtung.Projektion
public import Core.Beobachtung.Nichtinterferenz
public import Core.Beobachtung.NichtinterferenzErfuellbar
public import Core.Beobachtung.Fluss.Abschluss
public import Core.Beobachtung.Fluss.Beschriftung.Sicht
public import Core.Beobachtung.Fluss.Beschriftung.Einheit
public import Core.Beobachtung.Fluss.Beschriftung.Regel
public import Core.Beobachtung.Fluss.Beschriftung.Schreiben
public import Core.Beobachtung.Fluss.Beschriftung.Skalar
public import Core.Beobachtung.Fluss.Beschriftung.Sprung
public import Core.Beobachtung.Fluss.Beschriftung.Flussregel
public import Core.Beobachtung.Fluss.Beschriftung.Leck
public import Core.Beobachtung.Fluss.Beschriftung.Erfuellbar
public import Core.Beobachtung.Fluss.Beschriftung.Aufgaben
public import Core.Beobachtung.Fluss.Erfuellbar
public import Core.Beobachtung.Fluss.Region
public import Core.Beobachtung.Fluss.Speicherverwaltung
public import Core.Beobachtung.Fluss.Geraet
public import Core.Beobachtung.SchrankenB8
public import Core.Beobachtung.SchrankenB8Aussagen
public import Core.Beobachtung.SchrankenB8Beweise
public import Core.Beobachtung.SchrankenB8Zeit
public import Core.Beobachtung.SchrankenB8Erfuellbar
public import Core.Beobachtung.SchrankenB9B21
public import Core.Beobachtung.SchrankenB9B21Erfuellbar
meta import Core.Waechter.Check

#check_core
