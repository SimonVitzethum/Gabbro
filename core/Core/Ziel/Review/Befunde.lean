/-
  File:      Core/Ziel/Review/Befunde.lean
  Subject:   Review findings on the collection statements and the goal/safety shapes of Core/Ziel.
             This module contains ONLY counterexamples and vacuity witnesses; no existing statement is changed.

  Findings proved below:

  * `KorrektheitAussagen` is FALSE as written. Its docstring says that every pinned statement is a conjunct
    "with its parameters universally quantified", and the definition does quantify `C : Pruefer` and
    `π : Parser` universally. It therefore claims that EVERY checker is correct and non-trivial and that
    EVERY parser agrees with the reference relation. A checker whose three verdict functions are constantly
    `false` fails `PrueferNichtTrivialAussage` (and `PrueferKorrektAussage` on any accepted unit); the
    universal closure is refuted below. The statement is hash-pinned (PinTable), so it is not changed here.
    The intended collection is an existential choice of checker/parser, or a structure with those fields.

  * `GabbroSicherheitForm` is VACUOUS over a free frame, exactly as `GabbroZielForm` is (the latter is
    recorded in `Verfeinerung/Review/Befunde.lean`). With `Laeufe` nonempty, all four safety predicates
    constant false and `Bezeichnet` constant false, `SicherheitNichtLeer` is discharged by one triple and
    the universal clause has no instance: the shape holds without any accepted program or run. The force
    of the safety theorem lies in the concrete frame `S₀ P B`, which `SicherheitAusTeilenAussage` supplies.
    `Sicherheit.lean` states that shape-only reading in its header but does not record this vacuity; the
    witness below records it. No claim is made that the statement over `S₀ P B` is vacuous.
-/
module

public import Core.Ziel.Korrektheit.Alle

@[expose] public section

namespace Gabbro.Core.Ziel.Review

open Gabbro.Core
open Gabbro.Core.Ziel
open Gabbro.Core.Ziel.Korrektheit
open Gabbro.Core.Katalog

/-- The pinned collection statement is false: quantifying the checker universally makes it assert that a
    refuse-everything checker is non-trivial. -/
theorem KorrektheitAussagen.falsch : ¬ KorrektheitAussagen := by
  intro h
  let C : Pruefer :=
    { pruefeLokal := fun _ _ => false
      pruefeKlauseln := fun _ _ => false
      pruefeWaechter := fun _ _ => false
      fragmentLokal := fun _ _ => false
      fragmentKlauseln := fun _ _ => false
      fragmentWaechter := fun _ _ => false }
  let B : FormBeleg := ⟨PEmpty, fun _ _ => False, fun _ _ _ => False⟩
  let π : Parser := { parse := fun _ => none }
  have hk := h Plattform.x86_64 B C π
  have hnt : PrueferNichtTrivialAussage C := hk.2.2.2.2.2.2.2.2.1
  rcases hnt with ⟨_, _, ht⟩
  dsimp only [Pruefer.pruefe, C] at ht
  cases ht

/-- The safety SHAPE is satisfiable without any accepted program: a free frame whose denotation and
    acceptance are empty, whose run relation is nonempty and whose four safety predicates are constant
    false makes `SicherheitNichtLeer` true by one triple and leaves the universal clause vacuous. -/
theorem GabbroSicherheitForm.vakuos : ∃ (R : Rahmen) (S : Sicherheit R), GabbroSicherheitForm R S := by
  let R : Rahmen :=
    { Text := PUnit
      WohlgeformterText := fun _ => False
      Form := PEmpty
      Einheit := PUnit
      enthaelt := fun _ _ => False
      realisiert := fun _ _ _ => False
      Bezeichnet := fun _ _ => False
      Akzeptiert := fun _ => False
      Katalog := PUnit
      katalog := fun _ => ()
      KatalogWohlgeformt := fun _ => False
      Umgebung := PUnit
      Hardware := fun _ _ => False
      HwLauf := PUnit
      FairLaeufe := fun _ _ _ => False
      Lauf := PUnit
      Laeufe := fun _ _ _ => True
      Schnitt := fun _ => PUnit
      hw := fun _ => ()
      Start := PUnit
      start := fun _ => ()
      ZulStart := fun _ _ _ => False
      IdealLauf := PUnit
      IdealLaeufe := fun _ _ => False
      Bestimmt := fun _ => False
      IdealFortschritt := fun _ => False
      Sim := fun _ _ _ => False
      ZielFX := fun _ _ _ _ => False
      Kontext := PUnit
      Haengt := fun _ _ _ _ => False
      Klasse := PUnit
      klasse := fun _ => ()
      Fortschritt := fun _ _ _ => False
      ImSchranken := fun _ _ => False
      NiedrigGleich := fun _ _ _ => False
      GleicheNiedrigeUmgebung := fun _ _ _ => False
      GleichePolitik := fun _ _ _ => False
      Beob := PUnit
      NiedrigeBeob := fun _ _ => ()
      NiedrigAequiv := fun _ _ _ => False }
  let S : Sicherheit R :=
    { Speichersicher := fun _ _ _ => False
      InvariantenErhalten := fun _ _ _ => False
      Rennfrei := fun _ _ _ => False
      ToctouFrei := fun _ _ _ => False }
  refine ⟨R, S, ?_⟩
  dsimp only [GabbroSicherheitForm, SicherheitNichtLeer, R, S]
  constructor
  · exact ⟨⟨(), (), (), trivial, id⟩, ⟨(), (), (), trivial, id⟩,
      ⟨(), (), (), trivial, id⟩, ⟨(), (), (), trivial, id⟩⟩
  · intro a E h
    cases h

end Gabbro.Core.Ziel.Review
