module

public import Core.Ast.Semantik.Runtime.ExpressionCode
public import Core.Katalog.Ziel

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog

/-- A linked module: its name, its source fragment, the names it exports and the names it imports.
    The full source of every module is present; nothing is hidden. -/
structure Modul where
  name : String
  fragment : Fragment
  exporte : List String
  importe : List String

/-- A declarative build file: the modules, the dependency edges, the target platform and the entry. -/
structure Bauplan where
  module : List Modul
  abhaengigkeiten : List (String × String)
  plattform : Plattform
  einstieg : String

/-- The module names of the plan. -/
def modulNamen (plan : Bauplan) : List String :=
  plan.module.map Modul.name

/-- All exported names of the plan. -/
def alleExporte (plan : Bauplan) : List String :=
  plan.module.flatMap Modul.exporte

/-- Module names are unique. -/
def modulNamenEindeutig (plan : Bauplan) : Bool :=
  (modulNamen plan).eraseDups.length == (modulNamen plan).length

/-- Exported names are unique across the whole plan. -/
def exporteEindeutig (plan : Bauplan) : Bool :=
  (alleExporte plan).eraseDups.length == (alleExporte plan).length

/-- The entry names a module of the plan. -/
def einstiegVorhanden (plan : Bauplan) : Bool :=
  (modulNamen plan).contains plan.einstieg

/-- Every import is exported by some module of the plan. -/
def importeGedeckt (plan : Bauplan) : Bool :=
  plan.module.all fun mod => mod.importe.all fun imp => (alleExporte plan).contains imp

/-- Every dependency edge names two modules of the plan. -/
def abhaengigkeitenOk (plan : Bauplan) : Bool :=
  plan.abhaengigkeiten.all fun p => (modulNamen plan).contains p.1 && (modulNamen plan).contains p.2

/-- The declarative link check: names unique, imports resolved, entry and edges valid. -/
def bauplanOk (plan : Bauplan) : Bool :=
  modulNamenEindeutig plan && exporteEindeutig plan && einstiegVorhanden plan &&
    importeGedeckt plan && abhaengigkeitenOk plan

/-- Concatenation of all fragments in plan order. -/
def verknuepfteFragmente (plan : Bauplan) : Fragment :=
  plan.module.foldl (fun acc m => acc.anhaengen m.fragment) Fragment.leer

/-- Linking: resolve imports, append fragments, keep names unique. Returns `none` when the
    declarative check fails; the linked whole program is then checked as one unit. -/
def linke (plan : Bauplan) : Option Fragment :=
  if bauplanOk plan then some (verknuepfteFragmente plan) else none

end Gabbro.Core.Linken
