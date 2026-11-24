module

public import Core.Ast.Aggregate.Records.Fields

/-!
# RecordField

- `Surface.RecordFieldInversionAussage`
- `Surface.RecordFieldSuffixAussage`
- `Surface.RecordFieldDerivationAussage`
- `RecordFieldParseAussage`
- `RecordFieldElaboriertAussage`
- `RecordFieldRealisiertAussage`
- `RecordFieldAnnahmeAussage`
- `RecordFieldIdealAussage`
- `RecordFieldEinheitAussage`
- `RecordFieldImplAussage`
- `RecordFieldErhaltungAussage`
- `RecordFieldRegelSicherAussage`
- `RecordFieldErfuellbarAmAussage`
- `RecordFieldValueAussage`
-/

namespace Gabbro.Core.Ast.Surface

theorem RecordFieldSuffix : RecordFieldSuffixAussage := by
  intro scope name labels types minimum input type field allowed read
  exact (ExprTail.consumes read).trans (List.suffix_cons.trans List.suffix_cons)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem RecordFieldElaboriert : RecordFieldElaboriertAussage := by
  intro scope platform args
  rfl

theorem RecordFieldRealisiert : RecordFieldRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (recordFieldForm scope).realisiert (fun args => by
    change (((expr 0 args.base).code ++ [Befehl.liesRecordFeld 0 args.name args.labels args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesRecordFeld 0 args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  ) platform args s running active live atPc

theorem RecordFieldAnnahme : RecordFieldAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (recordFieldForm scope)

theorem RecordFieldIdeal : RecordFieldIdealAussage := by
  intro scope
  refine ⟨?_, ?_⟩
  · intro args
    change (((expr 0 args.base).code ++ [Befehl.liesRecordFeld 0 args.name args.labels args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesRecordFeld 0 args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    exact ⟨((recordFieldForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem RecordFieldEinheit : RecordFieldEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((recordFieldForm scope).befehl args).kommutation⟩

theorem RecordFieldImpl : RecordFieldImplAussage := by
  intro scope args c s w plans u
  rfl

theorem RecordFieldErhaltung : RecordFieldErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (recordFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.recordField scope).tree args).2)

theorem RecordFieldRegelSicher : RecordFieldRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (recordFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.recordField scope).tree args).2)
    platform args).2.2.2

theorem RecordFieldValue : RecordFieldValueAussage := by
  intro scope args frame record h
  change ((Befehl.liesRecordFeld 0 args.name args.labels args.types args.index).auswerten frame).temp 0 =
    some ⟨args.types.get args.index, tupleGet args.types args.index record⟩
  simp [Befehl.auswerten, Rahmen.schreibe, h, wertAls]

end Gabbro.Core.Ast.Semantik
