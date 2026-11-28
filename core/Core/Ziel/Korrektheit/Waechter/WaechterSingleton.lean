module
public import Core.Ziel.Korrektheit.Beweise.BegleitPruefer
public import Core.Ast.Semantik.Runtime.ValueCoercion

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast Gabbro.Core.Ast.Semantik Gabbro.Core.Katalog

/-- The only partial operation indexes the one-byte literal at offset zero. -/
private def singletonIndexUnit : Ast.Unit :=
  let written : WrittenType := .integer false 8 none
  let value : Expr [] (.int 0 255) := Expr.textIndex (Expr.textLiteral ['x']) (Expr.lit 0)
  ⟨[⟨indexName, .int 0 255, false, true⟩],
    .step (.constant indexName indexName_ordinary written
      (by
        change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
        omega) value
      (by dsimp only [value, Expr.static]; exact ⟨trivial, trivial⟩)
      (by change (0 : Int) ≤ 0 ∧ (255 : Int) ≤ 255; omega)) .done⟩

private abbrev singletonFragment : Fragment := fragment .unit singletonIndexUnit
private abbrev singletonCapacity : Nat := (sourceUtf8 ['x']).size
private abbrev singletonIndex : Befehl := .textIndex 0 singletonCapacity

private theorem singletonCode :
    singletonFragment.code =
      [.textLiteral 0 ['x'], .literal 1 0, singletonIndex,
        .bindeWert 0 (.int 0 255) true, .starte mainName, .ende] := rfl

private theorem singletonLokal : lokalPruefeCode singletonFragment.code = true := by
  rw [singletonCode]
  rfl

private theorem singletonImFragment : waechterFragmentCode singletonFragment.code = true := by
  rw [singletonCode]
  rfl

/-- Indexing the first byte of a one-byte literal satisfies the deployed guard check. -/
private theorem singletonWaechter : waechterPruefeCode singletonFragment.code = true := by
  rw [singletonCode]
  rfl

/-- The combined checker decides and accepts a unit with an in-place text index. -/
theorem prueferKombiniert_akzeptiertIndex :
    ∃ t, prueferKombiniert.fragment .x86_64 t = true ∧
      prueferKombiniert.pruefe .x86_64 t = true := by
  have clauseFragment : prueferKombiniert.fragmentKlauseln .x86_64 ⟨singletonIndexUnit, []⟩ = true := by
    show (programmMitInvarianten ⟨singletonIndexUnit, []⟩).code.all (pruefeBefehlErhalt []) = true
    exact List.all_eq_true.mpr (fun _ _ => rfl)
  refine ⟨singletonIndexUnit, ?_, ?_⟩
  · simp only [Pruefer.fragment, Bool.and_eq_true]
    exact ⟨⟨singletonLokal, clauseFragment⟩, singletonImFragment⟩
  · simp only [Pruefer.pruefe, Bool.and_eq_true]
    exact ⟨⟨singletonLokal, pruefeEinheit_leer _⟩, singletonWaechter⟩

private abbrev teilfolgeCode : List Befehl :=
  [.textLiteral 0 ['x'], .literal 1 1, .literal 2 1, .substring 0 (sourceUtf8 ['x']).size]

/-- A slice can overwrite the text it just read in forward-only code. -/
private theorem waechterPruefe_akzeptiertTeilfolge : waechterPruefeCode teilfolgeCode = true := rfl

/-- Reentering the same slice would use the now empty result as input. -/
private theorem waechterPruefe_verweigertTeilfolgeRuecksprung :
    waechterPruefeCode (teilfolgeCode ++ [.zurueckSprung 1]) = false := rfl

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
