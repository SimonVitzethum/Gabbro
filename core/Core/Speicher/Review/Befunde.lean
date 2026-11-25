/-
  File:      core/Core/Speicher/Review/Befunde.lean
  Subject:   Review findings on the statements of `Core.Maschine`, `Core.Ideal`, `Core.Speicher` and
             `Core.Aussen`. This module contains ONLY proofs of the negation or the vacuity of
             statements that failed the review; no existing statement is changed here.

  Findings proved below:
  * `revalidiert_gueltig` is logically equivalent to `atomar_gueltig`: the five premises about the
    earlier answer (`a₀`, `v₀`, `kam`, `wahl`, `entschieden`) are inert. `wahl` is a freely chosen
    function that can always be set to `fun _ => q`, so no dependence on an earlier answer is
    formalized. The equivalence below proves the vacuity of that decoration.
  * `Zustand.Zulaessig` takes a free snapshot function `sicht` with no constraining premise; on the
    only state where the predicate is currently discharged (`antworten = []`) it holds for every
    such function, so the parameter is inert there.

  (The `ReihenStabil`/`stabil`-branch findings are fixed: stability is now bound to the
  catalogue row, see `Core.Aussen.Bindung`.)
-/
module

public import Core.Aussen.Bindung
public import Core.Ideal.Eigenschaften
public import Core.Katalog.Erfuellbar
public import Core.Maschine.Zustand

@[expose] public section

namespace Gabbro.Core.Speicher.Review

open Gabbro.Core.Aussen
open Gabbro.Core.Katalog
open Gabbro.Core.Maschine
open Gabbro.Core.Ideal

/-- Vacuity of the decoration of `revalidiert_gueltig`: the theorem is logically equivalent to
    `atomar_gueltig`. The earlier-answer premises can always be supplied (choose any successful
    answer and `wahl := fun _ => q`) and are ignored by the conclusion. -/
theorem revalidiert_gueltig_vakuum :
    (∀ (p : Plattform) (s : AussenSicht) (q : Frage) (a : Antwort)
       (a₀ : Antwort) (v₀ : AussenWert) (kam : a₀.result = .ok v₀)
       (wahl : AussenWert → Frage) (entschieden : q = wahl v₀)
       (antwort : atomar p s q = .antwort a) (erfolg : a.result.isOk = true),
       GueltigBeiCommit p s q) ↔
    (∀ {p : Plattform} {s : AussenSicht} {q : Frage} {a : Antwort},
       atomar p s q = .antwort a → a.result.isOk = true → GueltigBeiCommit p s q) := by
  constructor
  · intro h p s q a antwort erfolg
    let a₀ : Antwort := ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.data [])⟩
    exact h p s q a a₀ (.data []) rfl (fun _ => q) rfl antwort erfolg
  · intro h p s q a _ _ _ _ _ antwort erfolg
    exact h antwort erfolg

/-- Vacuity of `Zustand.Zulaessig` at its only discharge site: when the state carries no answers,
    the predicate holds for every freely chosen snapshot function and every catalogue. -/
theorem zulaessig_ohne_antworten_vakuös {L Ort Wert Raum Lok Grund : Type}
    (z : Gabbro.Core.Maschine.Zustand L Ort Wert Raum Lok Grund) (hz : z.antworten = [])
    (k : Katalog.Katalog) : ∀ sicht : Nat → AussenSicht, z.Zulaessig k sicht := by
  intro sicht e he
  rw [hz] at he
  exact False.elim (List.not_mem_nil he)

end Gabbro.Core.Speicher.Review
