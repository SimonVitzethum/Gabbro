module

public import Core.Linken.Relativ

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- Relocation keeps the continuation temporaries. -/
theorem fortsetzungZurueck_temp (off : Nat) (k : Fortsetzung) :
    (fortsetzungZurueck off k).temp = k.temp :=
  rfl

/-- Relocation keeps the continuation locals. -/
theorem fortsetzungZurueck_lokale (off : Nat) (k : Fortsetzung) :
    (fortsetzungZurueck off k).lokale = k.lokale :=
  rfl

/-- Relocation keeps the continuation entry. -/
theorem fortsetzungZurueck_eingang (off : Nat) (k : Fortsetzung) :
    (fortsetzungZurueck off k).eingang = k.eingang :=
  rfl

/-- Relocation keeps the continuation measure. -/
theorem fortsetzungZurueck_mass (off : Nat) (k : Fortsetzung) :
    (fortsetzungZurueck off k).mass = k.mass :=
  rfl

/-- Relocation keeps the function address, shifted. -/
theorem funktionZurueck_adresse (off : Nat) (f : Funktion) :
    (funktionZurueck off f).adresse = f.adresse - off :=
  rfl

/-- Relocation keeps the constant count. -/
theorem funktionZurueck_konstanten (off : Nat) (f : Funktion) :
    (funktionZurueck off f).konstanten = f.konstanten :=
  rfl

/-- Only the position moves. -/
theorem frameZurueck_mitPc (off : Nat) (r : Rahmen) (e : Nat) :
    frameZurueck off { r with pc := e } = { frameZurueck off r with pc := e - off } := by
  simp only [frameZurueck]

/-- A step with locals and globals commutes with relocation. -/
theorem schrittLokal_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (l : List (Option Dynamisch)) (g : List (Option Dynamisch)) :
    frameZurueck off { r with pc := r.pc + 1, lokale := l, globale := g } = { frameZurueck off r with pc := (frameZurueck off r).pc + 1, lokale := l, globale := g } := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- A step with locals commutes with relocation. -/
theorem schrittLokal2_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (l : List (Option Dynamisch)) :
    frameZurueck off { r with pc := r.pc + 1, lokale := l } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + 1, lokale := l } := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- Stopping with a return value commutes with relocation. -/
theorem ende_proj (off : Nat) (r : Rahmen)
    (v : Option Dynamisch) (s : Option Abschluss) :
    frameZurueck off { r with stopp := s, rueckgabe := v } =
      { frameZurueck off r with stopp := s, rueckgabe := v } := by
  simp only [frameZurueck]

/-- Ending the thread commutes with relocation. -/
theorem beende_proj (off : Nat) (r : Rahmen) :
    frameZurueck off { r with stopp := some Abschluss.fertig } =
      { frameZurueck off r with stopp := some Abschluss.fertig } := by
  simp only [frameZurueck]

/-- Returning through an empty stack commutes with relocation. -/
theorem rueckNil_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (v : Option Dynamisch) (s : Option Abschluss) :
    frameZurueck off { r with pc := r.pc + 1, rueckgabe := v, stopp := s } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + 1, rueckgabe := v, stopp := s } := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- Choosing the environment commutes with relocation. -/
theorem umgebung_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (e : List (Identifier × DienstAbi × FirmwareZeile)) :
    frameZurueck off { r with pc := r.pc + 1, environment := e } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + 1, environment := e } := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- Setting the descent measure commutes with relocation. -/
theorem massSetzen_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (m : Option Nat) :
    frameZurueck off { r with pc := r.pc + 1, mass := m } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + 1, mass := m } := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- Defining a function commutes with relocation: the skip moves, the entry shifts. -/
theorem definiereRecord_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (f : Funktion) (skip : Nat) :
    frameZurueck off { r with pc := r.pc + skip, funktionen := f :: r.funktionen } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + skip, funktionen := (funktionZurueck off f) :: (frameZurueck off r).funktionen } := by
  have h : (r.pc + skip) - off = (r.pc - off) + skip := by omega
  simp only [frameZurueck, frameZurueck_pc, funktionen_proj, List.map_cons, h]

/-- Binding a read value commutes with relocation. -/
theorem bindeGelesen_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc)
    (ziel : Nat) (typ : Ty .value) (gelesen : Int) :
    frameZurueck off (Rahmen.bindeGelesen r ziel typ gelesen) =
      Rahmen.bindeGelesen (frameZurueck off r) ziel typ gelesen := by
  simp only [Rahmen.bindeGelesen]
  split
  all_goals simp only [schreibe_proj, halt_proj, hpc]

/-- An access transfer commutes with relocation. -/
theorem zugriff_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc)
    (z : Zugriffsform) (g : Int) :
    z.uebertrag (frameZurueck off r) g = frameZurueck off (z.uebertrag r g) := by
  cases z with
  | erwarte ziel region index erwartet typ modus =>
    simp only [Zugriffsform.uebertrag]
    split
    all_goals simp only [bindeGelesen_proj, hpc]
  | speichere _ _ _ _ =>
    simp only [Zugriffsform.uebertrag, Rahmen.weiter, weiter_proj, hpc]
  | veroeffentliche _ _ _ _ =>
    simp only [Zugriffsform.uebertrag, Rahmen.weiter, weiter_proj, hpc]
  | zaun _ =>
    simp only [Zugriffsform.uebertrag, Rahmen.weiter, weiter_proj, hpc]
  | lade _ _ _ _ _ =>
    simp only [Zugriffsform.uebertrag, bindeGelesen_proj, hpc]
  | tausche _ _ _ _ _ _ =>
    simp only [Zugriffsform.uebertrag, bindeGelesen_proj, hpc]
  | vergleicheTausche _ _ _ _ _ _ _ =>
    simp only [Zugriffsform.uebertrag, bindeGelesen_proj, hpc]
  | holeUndAddiere _ _ _ _ _ _ =>
    simp only [Zugriffsform.uebertrag, bindeGelesen_proj, hpc]

/-- A lifecycle transfer commutes with relocation. -/
theorem faden_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc)
    (z : Fadenform) (v : Int) :
    z.uebertrag (frameZurueck off r) v = frameZurueck off (z.uebertrag r v) := by
  cases z with
  | starte ziel eintritt typ uebergabe =>
    simp only [Fadenform.uebertrag, bindeGelesen_proj, hpc]
  | beende quelle =>
    simp only [Fadenform.uebertrag, beende_proj]
  | verbinde ziel kind typ =>
    simp only [Fadenform.uebertrag, bindeGelesen_proj, hpc]
  | wechsle kern kind =>
    simp only [Fadenform.uebertrag, Rahmen.weiter, weiter_proj, hpc]
  | kernStart kern kind =>
    simp only [Fadenform.uebertrag, Rahmen.weiter, weiter_proj, hpc]

/-- The stack guard reads only continuation functions, so it survives relocation. -/
theorem stackFind_map (off : Nat) (fs : List Fortsetzung) (name : Identifier) :
    (fs.map (fortsetzungZurueck off)).find?
        (fun k => (k.funktion.map Subtype.val) == some name.val) =
      ((fs.find? (fun k => (k.funktion.map Subtype.val) == some name.val)).map
        (fortsetzungZurueck off)) := by
  have h : (fun k => (k.funktion.map Subtype.val) == some name.val) ∘ fortsetzungZurueck off =
      (fun k => (k.funktion.map Subtype.val) == some name.val) := by
    funext k
    simp only [Function.comp_apply, fortsetzungZurueck_funktion]
  rw [List.find?_map, h]

/-- A frame borrows a region through its locals and continuations, so it survives relocation. -/
theorem borrowsRegion_proj (off : Nat) (r : Rahmen) (slot : Nat) :
    (frameZurueck off r).borrowsRegion slot = r.borrowsRegion slot := by
  unfold Rahmen.borrowsRegion
  simp only [frameZurueck_lokale, fortsetzungen_proj]
  have key : ∀ ks : List Fortsetzung,
      (ks.map (fortsetzungZurueck off)).any
          (fun k => (k.lokale.any fun v => v.any (Dynamisch.borrowsRegion slot))) =
        ks.any
          (fun k => (k.lokale.any fun v => v.any (Dynamisch.borrowsRegion slot))) := by
    intro ks
    induction ks with
    | nil => rfl
    | cons k ks ih =>
      simp only [List.map_cons, List.any_cons, fortsetzungZurueck_lokale, ih]
  rw [key]

/-- Continuing a passed loop commutes with relocation. -/
theorem passWeiter_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (v : Option Nat) :
    frameZurueck off { r with pc := r.pc + 1, zaehler := Function.update r.zaehler r.pc v } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + 1, zaehler := Function.update (frameZurueck off r).zaehler (frameZurueck off r).pc v } := by
  simp only [frameZurueck]
  congr 1
  · omega
  · funext j
    by_cases hj : j = r.pc - off
    · subst hj
      have h1 : (r.pc - off) + off = r.pc := by omega
      simp only [karteZurueck, Function.update_self, h1, Function.update_self]
    · have h2 : j + off ≠ r.pc := by omega
      simp only [karteZurueck, Function.update_of_ne hj, Function.update_of_ne h2]

/-- Leaving a passed loop commutes with relocation. -/
theorem passEnde_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (exit : Nat) :
    frameZurueck off { r with pc := r.pc + exit, zaehler := Function.update r.zaehler r.pc none } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + exit, zaehler := Function.update (frameZurueck off r).zaehler (frameZurueck off r).pc none } := by
  simp only [frameZurueck]
  congr 1
  · omega
  · funext j
    by_cases hj : j = r.pc - off
    · subst hj
      have h1 : (r.pc - off) + off = r.pc := by omega
      simp only [karteZurueck, Function.update_self, h1, Function.update_self]
    · have h2 : j + off ≠ r.pc := by omega
      simp only [karteZurueck, Function.update_of_ne hj, Function.update_of_ne h2]

/-- Reading the acting counter survives relocation. -/
theorem zaehlerAmPc_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) :
    (frameZurueck off r).zaehler (frameZurueck off r).pc = r.zaehler r.pc := by
  have hpc0 : (r.pc - off) + off = r.pc := by omega
  simp only [frameZurueck_zaehler, frameZurueck_pc, hpc0]

/-- Reading the acting bound survives relocation. -/
theorem obergrenzenAmPc_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) :
    (frameZurueck off r).obergrenzen (frameZurueck off r).pc = r.obergrenzen r.pc := by
  have hpc0 : (r.pc - off) + off = r.pc := by omega
  simp only [frameZurueck_obergrenzen, frameZurueck_pc, hpc0]

/-- The loop guard transfer commutes with relocation. -/
theorem pass_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc)
    (takePass : Bool) (exit : Nat) (handler : Option Identifier) :
    (frameZurueck off r).pass takePass exit handler =
      frameZurueck off (r.pass takePass exit handler) := by
  simp only [Rahmen.pass, zaehlerAmPc_proj, hpc]
  by_cases hT : (!takePass) = true
  · simp only [if_pos hT, passEnde_proj, hpc]
  · simp only [if_neg hT]
    split
    all_goals first
      | simp only [passWeiter_proj, hpc]
      | simp only [halt_proj]

/-- Entering a loop commutes with relocation. -/
theorem forAnfangMain_proj (off : Nat) (r : Rahmen)
    (hpc : off ≤ r.pc) (initial : Option Dynamisch) (b : Ganzzahl) (n : Nat) :
    frameZurueck off { r with pc := r.pc + 1, lokale := initial :: r.lokale, obergrenzen := Function.update r.obergrenzen (r.pc + 1) (some b), zaehler := Function.update r.zaehler (r.pc + 1) (some n) } =
      { frameZurueck off r with pc := (frameZurueck off r).pc + 1, lokale := initial :: (frameZurueck off r).lokale, obergrenzen := Function.update (frameZurueck off r).obergrenzen ((frameZurueck off r).pc + 1) (some b),         zaehler := Function.update (frameZurueck off r).zaehler ((frameZurueck off r).pc + 1) (some n) } := by
  simp only [frameZurueck]
  congr 1
  · omega
  · funext j
    have hkey : (r.pc - off) + 1 = (r.pc + 1) - off := by omega
    by_cases hj : j = r.pc + 1 - off
    · subst hj
      have h1 : (r.pc + 1 - off) + off = r.pc + 1 := by omega
      simp only [karteZurueck, hkey, Function.update_self, h1, Function.update_self]
    · have h2 : j + off ≠ r.pc + 1 := by omega
      simp only [karteZurueck, hkey, Function.update_of_ne hj, Function.update_of_ne h2]
  · funext j
    have hkey : (r.pc - off) + 1 = (r.pc + 1) - off := by omega
    by_cases hj : j = r.pc + 1 - off
    · subst hj
      have h1 : (r.pc + 1 - off) + off = r.pc + 1 := by omega
      simp only [karteZurueck, hkey, Function.update_self, h1, Function.update_self]
    · have h2 : j + off ≠ r.pc + 1 := by omega
      simp only [karteZurueck, hkey, Function.update_of_ne hj, Function.update_of_ne h2]

/-- Advancing a loop commutes with relocation. -/
theorem forNaechsterRec_proj (off : Nat) (r : Rahmen)
    (back : Nat) (l : List (Option Dynamisch)) :
    frameZurueck off { r with pc := r.pc - back, lokale := l } =
      { frameZurueck off r with pc := (frameZurueck off r).pc - back, lokale := l } := by
  have h : (r.pc - back) - off = (r.pc - off) - back := by omega
  simp only [frameZurueck, frameZurueck_pc, frameZurueck_lokale, h]

/-- Returning through a stored continuation commutes with relocation. -/
theorem rueckkehr_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (result : Option Dynamisch) :
    (frameZurueck off r).rueckkehr result = frameZurueck off (r.rueckkehr result) := by
  cases hstack : r.fortsetzungen with
  | nil =>
    have hnil : (frameZurueck off r).fortsetzungen = [] := by
      rw [fortsetzungen_proj, hstack]
      rfl
    simp only [Rahmen.rueckkehr, hnil, hstack]
    congr 1
    show (frameZurueck off r).pc + 1 = (r.pc + 1) - off
    rw [frameZurueck_pc]
    omega
  | cons k ks =>
    have hcons : (frameZurueck off r).fortsetzungen =
        fortsetzungZurueck off k :: (ks.map (fortsetzungZurueck off)) := by
      rw [fortsetzungen_proj, hstack, List.map_cons]
    simp only [Rahmen.rueckkehr, hcons, hstack, List.map_cons, fortsetzungZurueck, fortsetzungZurueck_funktion, fortsetzungZurueck_temp, fortsetzungZurueck_lokale, fortsetzungZurueck_eingang, fortsetzungZurueck_mass, frameZurueck]

end Gabbro.Core.Linken
