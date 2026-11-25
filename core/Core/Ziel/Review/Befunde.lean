/-
  File:      Core/Ziel/Review/Befunde.lean
  Subject:   Review findings on the collection statements and the goal/safety shapes of Core/Ziel.
             This module contains ONLY counterexamples and vacuity witnesses; no existing statement is changed.

  Findings proved below:

  * The checker package inside `KorrektheitAussagen` is existential, and it is not fulfilled by an
    arbitrary checker: a checker whose three verdict functions are constantly `false` fails
    `PrueferNichtTrivialAussage` (and hence the package `PrueferKorrektAussage ∧ PrueferVollstaendigAussage ∧
    PrueferNichtTrivialAussage ∧ PrueferDecktFormenAussage`, for every registry evidence). The witness
    below records this. The earlier universal reading of `KorrektheitAussagen` ("every checker is correct
    and non-trivial") was false and has been replaced by the existential one.

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

/-- The existential checker package is not fulfilled by an arbitrary checker: the refuse-everything
    checker fails non-triviality, hence fails the package for every registry evidence. -/
theorem KorrektheitAussagen.nichtTrivial :
    ∃ C : Pruefer, ∀ B : FormBeleg, ¬ (PrueferKorrektAussage C ∧ PrueferVollstaendigAussage C ∧
      PrueferNichtTrivialAussage C ∧ PrueferDecktFormenAussage C B) := by
  let C : Pruefer :=
    { pruefeLokal := fun _ _ => false
      pruefeKlauseln := fun _ _ => false
      pruefeWaechter := fun _ _ => false
      fragmentLokal := fun _ _ => false
      fragmentKlauseln := fun _ _ => false
      fragmentWaechter := fun _ _ => false }
  refine ⟨C, fun _ h => ?_⟩
  obtain ⟨_, _, hnt, _⟩ := h
  obtain ⟨_, _, ht⟩ := hnt.1
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
