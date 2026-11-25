/-
  File:      core/Core/Ziel/Korrektheit/NichtAkzeptierteEinheit.lean
  Subject:   a concrete SOURCE unit whose elaboration is not accepted, and the two
             non-triviality witnesses that were waiting for exactly this object.

  The witness unit's only declaration is a constant that indexes an empty text at
  offset `0`. The guarded instruction `.textIndex` writes the demand `.index (0, 0)`,
  which the pinned guard row refuses (`0 < 0`). A conforming hardware history that
  offers only the entry core forces an ideal run through the two setup instructions;
  at the third cut the demand is canonical, so `WaechterHalten` fails.

  Nothing here changes a pinned statement. The unit is a source `Ast.Unit`, so its
  elaboration is `einheitVon P t`, the object the checker statements quantify over.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Beweise.BegleitPruefer
public import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung
public import Core.Linken.GegenbeispielVerknuepft
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog
open Gabbro.Core.Maschine

/-- The name of the witness constant. -/
def indexName : Identifier :=
  keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

theorem indexName_ordinary : ordinaryLocal indexName :=
  (directName_of_singleton (name := indexName) rfl).1

/-- A source unit whose only declaration indexes an empty text at offset `0`. -/
def textIndexUnit : Ast.Unit :=
  let written : WrittenType := .integer false 8 none
  let value : Expr [] (.int 0 255) := Expr.textIndex (Expr.textLiteral []) (Expr.lit 0)
  ⟨[⟨indexName, .int 0 255, false, true⟩],
    .step (.constant indexName indexName_ordinary written
      (by norm_num [WrittenType.valid, WrittenType.storage]) value
      (by dsimp [value]; decide) (by dsimp [value, written]; decide)) .done⟩

/-- The elaborated code: two setup instructions, the guarded index, the binding, the entry and the end. -/
theorem textIndexUnit_code :
    (fragment Ast.Category.unit textIndexUnit).code =
      [.textLiteral 0 [], .literal 1 0, .textIndex 0 (sourceUtf8 []).size,
        .bindeWert 0 (.int 0 255) true, .starte mainName, .ende] := by
  rfl

end Gabbro.Core.Ziel.Korrektheit
