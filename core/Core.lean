/-
  File:      Core.lean
  Subject:   The package root of the new Gabbro model (`dokumente/PERFECT-MODEL.md`). Every module of `core/` is
             reached from here; `core/` never imports `grammatik/`.
-/
module
public import Core.Ziel.Form
public import Core.Text.Model
public import Core.Speicher
public import Core.Maschine
public import Core.Ideal
