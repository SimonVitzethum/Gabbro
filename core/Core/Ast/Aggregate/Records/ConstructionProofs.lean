module

public import Core.Ast.Aggregate.Records.Construction
public import Core.Ast.Semantik.Formbeweise

/-!
# RecordValue

- `Surface.RecordValueInversionAussage`
- `Surface.RecordValueSuffixAussage`
- `Surface.RecordValueDerivationAussage`
- `RecordValueParseAussage`
- `RecordValueElaboriertAussage`
- `RecordValueRealisiertAussage`
- `RecordValueAnnahmeAussage`
- `RecordValueIdealAussage`
- `RecordValueEinheitAussage`
- `RecordValueImplAussage`
- `RecordValueErhaltungAussage`
- `RecordValueRegelSicherAussage`
- `RecordValueErfuellbarAmAussage`
- `RecordValueSlotsAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

private theorem recordValue_reads (scope : Scope) (args : RecordValueArgs scope) {tokens : List Token}
    (prod : (recordValue scope).production args tokens) :
    (Category.expression scope).reads tokens ((recordValue scope).tree args) := by
  rcases prod with ⟨input, rfl, labelRead⟩
  change ExprReads scope 0 (.word args.ref.name.val :: openParen :: input)
    ((Surface.recordValue scope).tree args).2 []
  exact .atom (AtomReads.recordValue args.ref args.fields args.fits labelRead)
    (.stop noOperatorAtEnd)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem recordValue_parse : RecordValueParseAussage := by
  intro scope args text pieces lexed prod
  exact (Category.syntax (category := .expression scope)).parse_iff.mpr
    ⟨pieces, lexed, Surface.recordValue_reads scope args prod⟩

theorem recordValue_elaboriert : RecordValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem recordValue_annahme : RecordValueAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (recordValueForm scope)

theorem recordValue_einheit : RecordValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((recordValueForm scope).befehl args).kommutation⟩

theorem recordValue_impl : RecordValueImplAussage := by
  intro scope args c s w plans u
  rfl

theorem recordValue_erhaltung : RecordValueErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (recordValueForm scope) (fun args =>
    expr_keine_invarianten 0 ((Surface.recordValue scope).tree args).2)

theorem recordValue_regelSicher : RecordValueRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (recordValueForm scope) (fun a =>
    expr_keine_invarianten 0 ((Surface.recordValue scope).tree a).2) platform args).2.2.2

end Gabbro.Core.Ast.Semantik
