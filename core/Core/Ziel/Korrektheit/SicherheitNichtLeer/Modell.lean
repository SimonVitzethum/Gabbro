/-
  File:      core/Core/Ziel/Korrektheit/SicherheitNichtLeer/Modell.lean
  Subject:   THE CONCRETE WITNESS FRAMEWORK for `SicherheitNichtLeerInstanzAussage`: a loader whose
             implementation steps are supplied by a `Formular`, assembled at the exact type of
             `Ast.Semantik.Einheit`. This is the concrete-type counterpart of
             `Core.Sicherheit.Laufkonstruktion`; the four refutations built from it are theorems in
             the sibling modules, and every witness is an `Ast.Semantik.Einheit`, not a generic model.
 -/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Sicherheit.Praefix

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.SicherheitNichtLeer

open Gabbro.Core
open Maschine Katalog
open Gabbro.Core.Sicherheit
open Gabbro.Core.Speicher (Etikett)

/-- The exact unit type of the frame `R₀`. -/
abbrev Modell := Gabbro.Core.Ast.Semantik.Einheit
abbrev Zustand := Maschine.Zustand Nat Gabbro.Core.Ast.Semantik.Zelle Int Nat
  Gabbro.Core.Ast.Semantik.Rahmen PUnit
abbrev Plan := SchrittPlan Nat Gabbro.Core.Ast.Semantik.Zelle Int PUnit
abbrev Spur := SchrittSpur Gabbro.Core.Ast.Semantik.Zelle Int
abbrev Formular := Kontext → Zustand → List Plan → Zustand → Prop
abbrev Sicht := Nat → AussenVerlauf → AussenSicht

def katalog := Plattform.x86_64.katalog

def bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def daten : Startdaten Int Nat Gabbro.Core.Ast.Semantik.Rahmen PUnit :=
  ⟨fun _ => Gabbro.Core.Ast.Semantik.Rahmen.start [], fun _ => .laeuft,
    fun k => ⟨some (.faden k), .nutzer, 0, fun _ => false, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 1⟩⟩

def einrichtung : Einrichtung Nat Gabbro.Core.Ast.Semantik.Zelle Int Nat
    Gabbro.Core.Ast.Semantik.Rahmen PUnit PUnit :=
  ⟨fun _ => 0, fun _ => .sperre 0, fun _ => .aussen, fun _ => 0,
    fun _ _ _ => False, fun _ _ => True, ⟨0, 1⟩,
    ⟨.faden 0, 0, fun _ => daten, fun _ _ => 0⟩,
    fun z => z.objekt, fun _ _ _ => none⟩

def start : Zustand :=
  Maschine.Zustand.start daten.lokal daten.status daten.kerne daten.rechte
    einrichtung.initial (.leer (fun _ => 0))

/-- A unit whose only contribution is the supplied form rule; the catalogue, the image and the loader
    are the fixed concrete ones. The `kopf` selects `Befehl.ende`, whose rule ignores the command. -/
def einheit (z : Zustand) (form : Formular) (quelltabellen : Quelltabellen Zustand) : Modell :=
  ⟨katalog, bild, einrichtung,
    ⟨fun _ => ⟨fun c s _ plans u => form c s plans u, fun _ _ _ _ _ => False⟩,
      fun _ _ => some Gabbro.Core.Ast.Semantik.Befehl.ende, fun _ _ => False, fun _ _ _ => False⟩,
    fun _ => daten, fun _ => 0, fun _ _ => some z, Eq, (fun _ => 0), quelltabellen, eineTabelle, .leer, .leer, .leer⟩

def umgebung (sicht : Sicht) := Umgebung.referenz katalog 2 sicht
def hardware (sicht : Sicht) := Umgebung.referenzLauf katalog 2 sicht
def leer : Sicht := fun _ _ => .leer

theorem erlaubt (sicht : Sicht) : Hardware katalog (umgebung sicht) :=
  Umgebung.referenz_hardware katalog 2 sicht Plattform.x86_64.katalog_wohlgeformt (by decide)

theorem konform (sicht : Sicht) : (hardware sicht).konform katalog (umgebung sicht) :=
  (Umgebung.referenz_fair katalog 2 sicht Plattform.x86_64.katalog_wohlgeformt (by decide)).konform

theorem bild_gueltig : bild.gueltig katalog.plattform.ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro a mem
    have aZero : a = 0 := List.mem_singleton.mp mem
    subst a
    exact ⟨0, rfl⟩

theorem laeuft {z : Zustand} {form : Formular} {qt : Quelltabellen Zustand} {sicht : Sicht}
    (zeit : Zeitlauf (Lauffolge (einheit z form qt) (hardware sicht)))
    (boot : zeit.zustand 0 = some z) :
    ∃ a, Maschine.Laeufe (einheit z form qt) (umgebung sicht) ⟨a, hardware sicht, zeit⟩ := by
  obtain ⟨a, zul⟩ := zulStart_erfuellbar (erlaubt sicht) bild_gueltig
  exact ⟨a, erlaubt sicht, konform sicht, zul, boot⟩

def ruhigerPlan : Plan := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => 0⟩

/-- The location written by `schreibPlan` and `schreibLabel`. -/
def schreibOrt : Gabbro.Core.Ast.Semantik.Zelle := .region 0 0

def schreibPlan : Plan := { ruhigerPlan with fuss := [schreibOrt], schreibt := fun _ => true }

def schreibLabel : Etikett Gabbro.Core.Ast.Semantik.Zelle Int := ⟨.schreiben, schreibOrt, .na, 0, 0⟩

theorem rahmen (z : Zustand) (b : Buchung Gabbro.Core.Ast.Semantik.Zelle) :
    Zustandsrahmen z { z with buchung := b } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ausfuehren {z : Zustand} {form : Formular} {qt : Quelltabellen Zustand}
    {sicht t c vor u spur plan nach}
    (bereit : KannSchreiten (hardware sicht) t c vor)
    (regel : form c vor [plan] u) (aus : FuehrtSchrittAus einrichtung t c vor u plan spur nach) :
    Lauffolge (einheit z form qt) (hardware sicht) t (some vor) (.kontext c PUnit.unit, spur) (some nach) :=
  .schritt (.kontext rfl bereit ⟨Gabbro.Core.Ast.Semantik.Befehl.ende, rfl, regel⟩ aus)

theorem schreiben {t c} (vor : Zustand) (b : Buchung Gabbro.Core.Ast.Semantik.Zelle) {es g}
    (folge : Speicherfolge vor.initial (.kontext c) vor.graph [schreibLabel] es g) :
    FuehrtSchrittAus einrichtung t c vor { vor with buchung := b } schreibPlan
      ⟨es, []⟩ { vor with buchung := b, graph := g } :=
  ⟨rahmen vor b, fun _ absent => (List.not_mem_nil absent).elim, [], _, .intern, folge, rfl⟩

end Gabbro.Core.Ziel.Korrektheit.SicherheitNichtLeer
