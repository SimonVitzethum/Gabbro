module

public import Core.Ast.Aggregate.Tuples

/-!
# TupleValue

Prove the pinned statements in this file.

- `Surface.TupleValueInversionAussage`
- `Surface.TupleValueSuffixAussage`
- `Surface.TupleValueDerivationAussage`
- `TupleValueParseAussage`
- `TupleValueElaboriertAussage`
- `TupleValueRealisiertAussage`
- `TupleValueAnnahmeAussage`
- `TupleValueIdealAussage`
- `TupleValueEinheitAussage`
- `TupleValueImplAussage`
- `TupleValueErhaltungAussage`
- `TupleValueRegelSicherAussage`
- `TupleValueErfuellbarAmAussage`
-/

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

theorem tupleValue_am_ort (scope : Scope) : (tupleValueForm scope).RegelAmOrt := by
  intro args
  change ((((expr 0 args.first).anhaengen (expr 1 args.second)).anhaengen
    (itemCode 2 args.tail)).anhaengen (.einzel (.baueTupel 0 args.types))).code[
      (((expr 0 args.first).anhaengen (expr 1 args.second)).anhaengen (itemCode 2 args.tail)).code.length]?
    = some (.baueTupel 0 args.types)
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem tupleValue_elaboriert : TupleValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem tupleValue_realisiert : TupleValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (tupleValueForm scope).realisiert (tupleValue_am_ort scope) platform args s
    running active live atPc

theorem tupleValue_annahme : TupleValueAnnahmeAussage := by
  intro scope
  exact (tupleValueForm scope).annahme

theorem tupleValue_ideal : TupleValueIdealAussage := by
  intro scope
  refine ⟨tupleValue_am_ort scope, ?_⟩
  intro args
  exact ⟨((tupleValueForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem tupleValue_einheit : TupleValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((tupleValueForm scope).befehl args).kommutation⟩

theorem tupleValue_impl : TupleValueImplAussage := by
  intro scope args c s w plans u
  rfl

theorem tupleValue_erhaltung : TupleValueErhaltungAussage := by
  intro scope
  exact (tupleValueForm scope).erhaltung (fun _ _ => rfl)

theorem tupleValue_regelSicher : TupleValueRegelSicherAussage := by
  intro scope platform args
  exact ((tupleValueForm scope).befehl args).sicher ((tupleValueForm scope).fragment args)
    platform (by rfl)

end Gabbro.Core.Ast.Semantik
