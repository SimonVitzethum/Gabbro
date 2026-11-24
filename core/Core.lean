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
public import Core.Katalog.Erfuellbar
public import Core.Aussen
public import Core.Annahme
public import Core.Sicherheit.Erfuellbar
public import Core.Sicherheit.RegelnErfuellbar
public import Core.Verfeinerung.Erfuellbar
public import Core.Beobachtung.SchrankenErfuellbar
public import Core.Beobachtung.Projektion
public import Core.Beobachtung.Nichtinterferenz
public import Core.Beobachtung.NichtinterferenzErfuellbar
public import Core.Beobachtung.SchrankenB8
public import Core.Beobachtung.SchrankenB8Aussagen
public import Core.Beobachtung.SchrankenB8Erfuellbar
meta import Core.Waechter.Check

#check_core
