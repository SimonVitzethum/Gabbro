/-
  File:      Core/Verfeinerung/Review/Befunde.lean
  Subject:   Review findings for the Aussagen, Pflichtstrukturen and main theorems of
             Core/Annahme, Core/Sicherheit, Core/Verfeinerung, Core/Fortschritt and Core/Ziel.

  A review of statements, not of proofs. Two statements are vacuous as written:

  * `LockFreeSimAussage` takes its operation decoder `sicht`, its abstract start state and its
    specification as free parameters. The definition never ties them to the unit's rules, so a
    degenerate decoder that emits no operation and a trivial specification prove the Aussage for
    every unit. This is the same defect already known for `FlushSimAussage` and
    `StotterMassAussage`; unlike those two it had not been reported.
  * `GabbroZielForm R` quantifies over a freely supplied `Rahmen` whose fields are free Prop
    fields. With all predicates false and an empty form type it is satisfiable without a single
    run. This is documented in `Core/Ziel/Form.lean` and the statement is hash-pinned as the
    mere shape of the goal; the proof below records the documented vacuity, it does not change
    the pinned statement.

  No statement was found to be false: every other Aussage either names what its comment claims
  and has a jointly satisfiable premise bundle, or is an intentionally pinned open target.
-/
module

public import Core.Verfeinerung.Abnahme.LockFree
public import Core.Ziel.Form

@[expose] public section

namespace Gabbro.Core.Verfeinerung.Review

open Gabbro.Core.Maschine
open Gabbro.Core.Maschine.I
open Gabbro.Core.Ziel

/-- Vacuity of `LockFreeSimAussage`: the operation decoder, abstract start and specification are
    free parameters. A decoder that never emits an event, together with an empty operation set
    and a trivial specification, satisfies the Aussage for an arbitrary unit. -/
theorem LockFreeSimAussage.vakuos
    {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) :
    ∃ (operation : F → Prop)
      (sicht : EffektSicht Ort Wert Wahl (LockFreeTakt PUnit PUnit PUnit))
      (start : PUnit) (spezifikation : PUnit → PUnit → PUnit → PUnit → Prop),
      LockFreeSimAussage E operation sicht start spezifikation := by
  refine ⟨fun _ => False, ⟨fun _ => none, rfl, fun _ _ => rfl⟩, PUnit.unit,
    fun _ _ _ _ => True, ?_⟩
  constructor
  · intro f nichtLeer
    cases nichtLeer
  · intro η lauf
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro id x y t u ht hu
        change none = some (id, x) at ht
        cases ht
      · intro id x y r s t u ht hu
        change none = some (id, x, r) at ht
        cases ht
      · intro id r s t u ht hu
        change none = some (id, r) at ht
        cases ht
      · intro id x r t ht
        change none = some (id, x, r) at ht
        cases ht
      · intro id r t ht
        change none = some (id, r) at ht
        cases ht
    · refine ⟨fun _ => PUnit.unit, rfl, ?_⟩
      intro t
      rfl

/-- Documented vacuity of the pinned goal SHAPE: over a freely supplied `Rahmen` with false
    predicates, an empty form type and an empty `Laeufe`, `GabbroZielForm` holds without any run. -/
theorem GabbroZielForm.vakuos : ∃ R : Rahmen, GabbroZielForm R := by
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
      Laeufe := fun _ _ _ => False
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
  refine ⟨R, ?_⟩
  unfold GabbroZielForm
  unfold NichtLeer
  unfold NI
  dsimp only [R]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      constructor
      · intro h
        cases h
      · rintro ⟨E, h⟩
        cases h
    · intro a E E' h
      cases h
    · intro f
      cases f
    · intro E h
      cases h
    · intro K h
      cases h
    · intro a E h
      cases h
    · intro a E h
      cases h
    · intro E h
      cases h
  · intro a E h
    cases h
  · intro E H1 H2 ρ1 s2 h
    cases h

end Gabbro.Core.Verfeinerung.Review
