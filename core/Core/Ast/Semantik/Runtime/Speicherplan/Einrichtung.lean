/-
  File:      core/Core/Ast/Semantik/Runtime/Speicherplan/Einrichtung.lean
  Subject:   THE UNIT'S MEMORY IS REAL (MK-02). The unit's interpretation of memory comes from its memory plan:
             the declared initial cells, the lock words, the one event location, the region slot as the object of a
             cell. A context accesses exactly the cells of the regions its frame was granted
             (`zugriff_region`, `kein_zugriff_*`); at the start only the entry context holds regions
             (`start_zugriff_eintritt`, with MK-01's `startdaten_regionen_eindeutig`). Satisfiability
             (`speicherplan_erfuellbar`): a fragment that declares a lock and initial content, a start state in
             which the entry context may access a cell and a second context, the lock word and the event location
             may not, and the initial content of the cell is the declared one.
-/
module

public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Mehrkontext.Start

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

section Einrichtung

variable (scope : Scope) (eintritte : Kontext → Option Nat) (speicher : Speicherplan)

theorem einrichtung_initial : (einrichtung scope eintritte speicher).initial = speicher.initial := rfl

theorem einrichtung_sperrOrt (l : Nat) : (einrichtung scope eintritte speicher).sperrOrt l = .sperre l := rfl

theorem einrichtung_ereignisOrt (e : Ereignis) :
    (einrichtung scope eintritte speicher).ereignisOrt e = .aussen := rfl

theorem einrichtung_speicherObjekt (z : Zelle) :
    (einrichtung scope eintritte speicher).speicherObjekt z = z.objekt := rfl

/-- **A context accesses the cells of the regions it was granted.** It lists the slot among its arrival
    regions, the slot's object lives in its arrival generation and is not lent out. -/
theorem zugriff_region {s : Zustand} {c : Kontext} {slot : Nat} (offset : Nat)
    (gehalten : slot < (s.lokal c).arrivalRegions.length) (lebt : s.rechte.lebt slot = true)
    (gen : s.rechte.gen slot = 0) (eigen : s.leihen slot = .eigen) :
    (einrichtung scope eintritte speicher).Zugriff s c (.region slot offset) := by
  refine ⟨⟨slot, 0⟩, by simp only [einrichtung, Zustand.griff, if_pos gehalten], rfl, ⟨lebt, gen⟩, ?_⟩
  change (s.leihen slot).Zugriff
  rw [eigen]
  exact trivial

/-- A context that was not granted the region has no handle for its cells. -/
theorem griff_ohne_region {s : Zustand} {c : Kontext} {slot : Nat} (offset : Nat)
    (fehlt : (s.lokal c).arrivalRegions.length ≤ slot) :
    s.griff c (.region slot offset) = none :=
  by simp only [Zustand.griff, if_neg (Nat.not_lt.mpr fehlt)]

theorem kein_zugriff_ohne_region {s : Zustand} {c : Kontext} {slot : Nat} (offset : Nat)
    (fehlt : (s.lokal c).arrivalRegions.length ≤ slot) :
    ¬ (einrichtung scope eintritte speicher).Zugriff s c (.region slot offset) := by
  rintro ⟨g, hg, _⟩
  have none : s.griff c (.region slot offset) = none := griff_ohne_region offset fehlt
  change s.griff c (.region slot offset) = some g at hg
  rw [none] at hg
  cases hg

/-- **A lock word is no region**: no handle reaches it, so no form can read or write it as a cell. -/
theorem kein_zugriff_sperre (s : Zustand) (c : Kontext) (l : Nat) :
    ¬ (einrichtung scope eintritte speicher).Zugriff s c (.sperre l) := by
  rintro ⟨g, hg, _⟩
  change none = some g at hg
  cases hg

/-- The location of the outside events is no region either. -/
theorem kein_zugriff_aussen (s : Zustand) (c : Kontext) :
    ¬ (einrichtung scope eintritte speicher).Zugriff s c .aussen := by
  rintro ⟨g, hg, _⟩
  change none = some g at hg
  cases hg

end Einrichtung

/-- **At the start the entry context may access every cell of every region it is granted.** -/
theorem start_zugriff_eintritt (p : Fragment) (platform : Plattform) (start : AussenStart)
    {slot : Nat} (offset : Nat) (h : slot < start.regions.length) :
    (p.einheit platform).einrichtung.Zugriff (I.start (p.einheit platform) start).2 eintritt
      (.region slot offset) := by
  have arrival : ((I.start (p.einheit platform) start).2.lokal eintritt).arrivalRegions =
      start.regions := rfl
  exact zugriff_region p.eingang p.eintritte p.speicher offset (by rw [arrival]; exact h)
    (by change decide (slot < start.regions.length) = true; exact decide_eq_true h) rfl rfl

/-- **At the start no other context may access any region cell**: the arrival regions belong to the
    entry context alone. -/
theorem start_kein_zugriff_anderer (p : Fragment) (platform : Plattform) (start : AussenStart)
    {c : Kontext} (hc : c ≠ eintritt) (slot offset : Nat) :
    ¬ (p.einheit platform).einrichtung.Zugriff (I.start (p.einheit platform) start).2 c
      (.region slot offset) := by
  have arrival : ((I.start (p.einheit platform) start).2.lokal c).arrivalRegions = [] :=
    startdaten_regionen_eindeutig p.eingang p.eintritte (start.assignment 0) platform start.regions hc
  exact kein_zugriff_ohne_region p.eingang p.eintritte p.speicher offset
    (by rw [arrival]; exact Nat.zero_le _)

/-- A fragment that declares one lock and the initial content `7` of cell `3` of region `0`. -/
def mitSpeicher : Fragment :=
  { Fragment.leer with speicher := ⟨1, 0, fun slot offset => if slot = 0 ∧ offset = 3 then 7 else 0⟩ }

/-- **Satisfiability of the unit's memory.** In the loaded state of a fragment that declares a lock and
    initial content, with one region granted: the declared cell holds its declared content, every other cell
    and the lock word start at `0`; the entry context may access the cell, a handler may not; neither the
    lock word nor the event location may be accessed; and the lock word is the location the unit names for
    its lock. -/
theorem speicherplan_erfuellbar (platform : Plattform) :
    let E := mitSpeicher.einheit platform
    let d := startdaten mitSpeicher.eingang mitSpeicher.eintritte (some 0) platform [⟨0, 4096⟩]
    let s : Zustand := Maschine.Zustand.start d.lokal d.status d.kerne d.rechte
      E.einrichtung.initial (.leer (fun _ => (0 : UInt8)))
    s.initial (.region 0 3) = 7 ∧ s.initial (.region 0 4) = 0 ∧ s.initial (.sperre 0) = 0 ∧
      E.einrichtung.sperrOrt 0 = .sperre 0 ∧
      E.einrichtung.Zugriff s eintritt (.region 0 3) ∧
      ¬ E.einrichtung.Zugriff s (.handler 0 0 0) (.region 0 3) ∧
      (∀ l, ¬ E.einrichtung.Zugriff s eintritt (.sperre l)) ∧
      ¬ E.einrichtung.Zugriff s eintritt .aussen := by
  intro E d s
  have handler : Kontext.handler 0 0 0 ≠ eintritt := fun same => Kontext.noConfusion same
  have arrival : (s.lokal (.handler 0 0 0)).arrivalRegions = [] :=
    startdaten_regionen_eindeutig mitSpeicher.eingang mitSpeicher.eintritte (some 0) platform
      [⟨0, 4096⟩] handler
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, fun l => kein_zugriff_sperre _ _ _ _ _ l,
    kein_zugriff_aussen _ _ _ _ _⟩
  · exact zugriff_region mitSpeicher.eingang mitSpeicher.eintritte mitSpeicher.speicher 3
      (by change 0 < ([⟨0, 4096⟩] : List Strecke).length; exact Nat.zero_lt_one) rfl rfl rfl
  · exact kein_zugriff_ohne_region mitSpeicher.eingang mitSpeicher.eintritte mitSpeicher.speicher 3
      (by rw [arrival]; exact Nat.zero_le _)

end Gabbro.Core.Ast.Semantik
