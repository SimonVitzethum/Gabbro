module

public import Core.Sicherheit.Praefix

@[expose] public section

namespace Gabbro.Core.Sicherheit.Laufkonstruktion

open Maschine Katalog
open Speicher (Etikett)

abbrev Modell := Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit
abbrev Zustand := Maschine.Zustand Unit Unit Unit Unit Unit Unit
abbrev Plan := SchrittPlan Unit Unit Unit Unit
abbrev Spur := SchrittSpur Unit Unit
abbrev Formular := Kontext → Zustand → List Plan → Zustand → Prop
abbrev Sicht := Nat → AussenVerlauf → AussenSicht

def katalog := Plattform.x86_64.katalog
def bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩
def daten : Startdaten Unit Unit Unit Unit :=
  ⟨fun _ => (), fun _ => .laeuft,
    fun k => ⟨some (.faden k), .nutzer, (), fun _ => false, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 1⟩⟩

def einrichtung : Einrichtung Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
    fun _ _ => True, ⟨0, 1⟩, ⟨.faden 0, 0, fun _ => daten, fun _ _ => ()⟩,
    fun _ => 0, fun _ _ _ => none⟩

def start : Zustand :=
  Maschine.Zustand.start daten.lokal daten.status daten.kerne daten.rechte
    einrichtung.initial (.leer (fun _ => 0))

def einheit (z : Zustand) (form : Formular) (invarianten : List (Invariante Unit Zustand)) : Modell :=
  ⟨⟨katalog, bild, einrichtung,
      ⟨fun _ => ⟨fun c s _ plans u => form c s plans u, fun _ _ _ _ _ => False⟩, fun _ _ => some (),
        fun _ _ => False, fun _ _ _ => False⟩,
      fun _ => daten, fun _ _ => 0, fun _ _ => some z, Eq, (fun _ => 0), .leer, .leer, .leer, .leer⟩, invarianten⟩

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

theorem laeuft {z : Zustand} {form : Formular} {inv} {sicht : Sicht}
    (zeit : Zeitlauf (Lauffolge (einheit z form inv).maschine (hardware sicht)))
    (boot : zeit.zustand 0 = some z)
    (fair : ∀ a, Maschine.SchedulerFair (einheit z form inv).maschine ⟨a, hardware sicht, zeit⟩) :
    ∃ a, Maschine.Laeufe (einheit z form inv).maschine (umgebung sicht)
      ⟨a, hardware sicht, zeit⟩ := by
  obtain ⟨a, zul⟩ := zulStart_erfuellbar (erlaubt sicht) bild_gueltig
  exact ⟨a, erlaubt sicht, konform sicht, zul, boot, fair a⟩

def ruhigerPlan : Plan := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def schreibPlan : Plan := { ruhigerPlan with fuss := [()], schreibt := fun _ => true }

def schreibLabel : Etikett Unit Unit := ⟨.schreiben, (), .na, (), ()⟩

theorem rahmen (z : Zustand) (b : Buchung Unit) : Zustandsrahmen z { z with buchung := b } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ausfuehren {z : Zustand} {form : Formular} {inv sicht t c vor u spur plan nach}
    (bereit : KannSchreiten (hardware sicht) t c vor)
    (regel : form c vor [plan] u) (aus : FuehrtSchrittAus einrichtung t c vor u plan spur nach) :
    Lauffolge (einheit z form inv).maschine (hardware sicht) t (some vor) (.kontext c (), spur) (some nach) :=
  .schritt (.kontext rfl bereit ⟨(), rfl, regel⟩ aus)

theorem schreiben {t c} (vor : Zustand) (b : Buchung Unit) {es g}
    (folge : Speicherfolge vor.initial (.kontext c) vor.graph [schreibLabel] es g) :
    FuehrtSchrittAus einrichtung t c vor { vor with buchung := b } schreibPlan
      ⟨es, []⟩ { vor with buchung := b, graph := g } :=
  ⟨rahmen vor b, fun _ absent => (List.not_mem_nil absent).elim, [], _, .intern, folge, rfl⟩

end Gabbro.Core.Sicherheit.Laufkonstruktion
