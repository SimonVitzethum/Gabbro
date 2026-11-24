/-
  File:      core/Core/Ziel/Korrektheit/Instanz.lean
  Subject:   THE CONCRETE FRAME `R₀` AND ITS SAFETY RECORD `S₀` (PERFECT-MODEL §2, §6.4), assembled from the
             definitions that exist in `core/`.

  `GabbroZielForm R` is trivially satisfiable for a free `Rahmen` (`GabbroZielForm.vakuos`,
  `Verfeinerung/Review/Befunde.lean`): the force of the goal theorem lies in the fields of the one frame it is
  stated over. `R₀ P B` binds every field of `Rahmen` to the concrete constants of `core/`:

  * the units are the elaborated units (`Ast.Semantik.Einheit`), acceptance is `Annahme.Akzeptiert`, the
    denotation of text is `Ast.Semantik.Bezeichnet P .unit` on the selected platform `P`, the catalogue is the
    unit's own `katalog`, hardware, fair histories and starts are those of `Katalog`;
  * the runs are the maximal implementation runs `Maschine.Laeufe`, the ideal runs `Maschine.I.Laeufe`, the
    refinement `Maschine.I.Sim`, today's guarantee `Maschine.ZielFX`, hanging `Maschine.I.Haengt`, bounds
    `Beobachtung.ImSchranken`, noninterference the projections of `Beobachtung/Projektion` and the low trace
    `Beobachtung.NiedrigeBeob`.

  PLUMBING. `Rahmen.Lauf`, `Rahmen.IdealLauf` and `Rahmen.Schnitt` do not depend on the unit, while `Maschine.Lauf E`
  does. The frame therefore uses runs tagged with their unit (`Σ E, Maschine.Lauf E`); every field mentions the
  tag of its run and ties it to the unit it is asked about, so no cast is needed except where two runs meet, and
  there a tag equality is part of the field. (Report, diff D-K1: indexing `Lauf`, `IdealLauf`, `Schnitt` by the unit
  in `Rahmen` would remove the tags; that changes a hash-pinned shape and is the owner's decision.)

  WHAT IS NOT YET BOUND. (a) The registry evidence of forms (`Form`, `enthaelt`, `realisiert`) is supplied by
  `FormBeleg`: the inventory exists as data but the map from a source tree to the constructors it contains does not
  (M6 registry). (b) `klasse` is bound to `deadlockFree` for every unit: the class a unit declares is not part of the
  elaborated unit yet; `deadlockFree` follows from `WaechterHalten` (`deadlockfrei_aus_waechter`) and
  `starvationFree` is already inside `Verfeinert` (`∀ c, ¬ Haengt`). (c) The platform `P` is an argument: the
  denotation of a text depends on the platform whose rows it selects; §6.4 of PERFECT-MODEL asks for an
  argument-free `R₀` (report, diff D-K2: state the goal as `∀ P, GabbroZielForm (R₀ P B₀)` for the three platforms,
  or let the text select the platform by name).

  `S₀` is the safety record over `R₀`: the four predicates of `Core/Sicherheit` applied to the safety unit
  `sicherheitVon E`, which carries the declared invariants read from the unit's clause table.
-/
module

public import Core.Ziel.Sicherheit
public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Verfeinerung.Fortschritt
public import Core.Fortschritt.Klasse
public import Core.Beobachtung.Satz
public import Core.Beobachtung.Schranken

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The registry evidence of the language's forms: the form list, the occurrence of a form in a text, and the
realisation of one occurrence in the denoted unit. The inventory is data (`Core.Inventory.forms`); the functions
that read constructors out of source trees are M6 registry work, so this is a parameter of the frame until then. -/
structure FormBeleg where
  Form : Type
  enthaelt : Text.RawText → Form → Prop
  realisiert : Form → Text.RawText → Ast.Semantik.Einheit → Prop

/-- The safety unit of an elaborated unit: the unit itself with the declared invariants read from its clause
table (`Quelltabellen.klauseln.invariant`), each with no lock scope. -/
def sicherheitVon (E : Ast.Semantik.Einheit) :
    Gabbro.Core.Sicherheit.Einheit Nat Ast.Semantik.Zelle Int Nat Ast.Semantik.Rahmen PUnit PUnit PUnit
      Ast.Semantik.Befehl :=
  ⟨E, E.quelltabellen.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩)⟩

/-- The concrete frame of the goal theorem for platform `P`: every field is a constant of `core/`. -/
@[reducible] noncomputable def R₀ (P : Katalog.Plattform) (B : FormBeleg) : Ziel.Rahmen where
  Text := Text.RawText
  WohlgeformterText := Text.WohlgeformterText (Text.tokenGrammar (Ast.Category.reads Ast.Category.unit))
    (fun t => Ast.Semantik.zugelassen P Ast.Category.unit t)
  Form := B.Form
  Einheit := Ast.Semantik.Einheit
  enthaelt := B.enthaelt
  realisiert := B.realisiert
  Bezeichnet := Ast.Semantik.Bezeichnet P Ast.Category.unit
  Akzeptiert := fun E => Annahme.Akzeptiert E
  Katalog := Katalog.Katalog
  katalog := fun E => E.katalog
  KatalogWohlgeformt := fun K => Katalog.KatalogWohlgeformt K
  Umgebung := Katalog.Umgebung
  Hardware := fun K H => Katalog.Hardware K H
  HwLauf := Katalog.HwLauf
  FairLaeufe := fun K H h => Katalog.FairLaeufe K H h
  Lauf := Σ E : Ast.Semantik.Einheit, Maschine.Lauf E
  Laeufe := fun E H ρ => ρ.1 = E ∧ Maschine.Laeufe ρ.1 H ρ.2
  Schnitt := fun ρ => Maschine.Schnitt ρ.1 ρ.2
  hw := fun ρ => ρ.2.hw
  Start := Katalog.AussenStart
  start := fun ρ => ρ.2.start
  ZulStart := fun E H s => E.ZulStart H s
  IdealLauf := Σ E : Ast.Semantik.Einheit, Maschine.I.Lauf E
  IdealLaeufe := fun E ι => ι.1 = E ∧ Maschine.I.Laeufe ι.1 ι.2
  Bestimmt := fun E => Maschine.I.Bestimmt E.einrichtung E.system
  IdealFortschritt := fun E => Maschine.I.Fortschritt E.einrichtung E.system
  Sim := fun E ρ ι => ρ.1 = E ∧ ∃ h : ι.1 = ρ.1, Maschine.I.Sim ρ.1 ρ.2 (h ▸ ι.2)
  ZielFX := fun E H ρ t => ρ.1 = E ∧ Maschine.ZielFX ρ.1 H ρ.2 t
  Kontext := Maschine.Kontext
  Haengt := fun E ρ ι c => ρ.1 = E ∧ ∃ h : ι.1 = ρ.1, Maschine.I.Haengt ρ.1 ρ.2 (h ▸ ι.2) c
  Klasse := Gabbro.Core.Fortschritt.Klasse Ast.Semantik.Befehl
  klasse := fun _ => Gabbro.Core.Fortschritt.Klasse.deadlockFree
  Fortschritt := fun k ρ ι =>
    ∃ h : ι.1 = ρ.1, Gabbro.Core.Fortschritt.KlassenFortschritt k ρ.2 (h ▸ ι.2)
  ImSchranken := fun E ρ => ρ.1 = E ∧ Beobachtung.ImSchranken ρ.1 ρ.2
  NiedrigGleich := fun E s₁ s₂ => Beobachtung.NiedrigGleich E s₁ s₂
  GleicheNiedrigeUmgebung := fun E h₁ h₂ => Beobachtung.GleicheNiedrigeUmgebung E h₁ h₂
  GleichePolitik := fun E ρ₁ ρ₂ =>
    ρ₁.1 = E ∧ ∃ h : ρ₂.1 = ρ₁.1, Beobachtung.GleichePolitik ρ₁.1 ρ₁.2 (h ▸ ρ₂.2)
  Beob := Beobachtung.Beob Ast.Semantik.Zelle Int PUnit Ast.Semantik.Befehl
  NiedrigeBeob := fun _ ρ => Beobachtung.NiedrigeBeob ρ.1 ρ.2
  NiedrigAequiv := fun E a b => Beobachtung.NiedrigAequiv E a b

/-- The safety record over `R₀`: the four properties of `Core/Sicherheit` at the unit's safety unit. -/
@[reducible] noncomputable def S₀ (P : Katalog.Plattform) (B : FormBeleg) : Ziel.Sicherheit (R₀ P B) where
  Speichersicher := fun _ H ρ => Gabbro.Core.Sicherheit.Speichersicher (sicherheitVon ρ.1) H ρ.2
  InvariantenErhalten := fun _ H ρ => Gabbro.Core.Sicherheit.InvariantenErhalten (sicherheitVon ρ.1) H ρ.2
  Rennfrei := fun _ H ρ => Gabbro.Core.Sicherheit.Rennfrei (sicherheitVon ρ.1) H ρ.2
  ToctouFrei := fun _ H ρ => Gabbro.Core.Sicherheit.ToctouFrei (sicherheitVon ρ.1) H ρ.2

end Gabbro.Core.Ziel.Korrektheit
