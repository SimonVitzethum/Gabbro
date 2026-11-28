module

public import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.BegleitZusammensetzung
public import Core.Ziel.Korrektheit.PrueferLokal
public import Core.Ziel.Korrektheit.Beweise2.FormBelegDatensatz

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Ast.Semantik Katalog WaechterAnalyse

private theorem prueferKombiniert_aus_code (t : Ast.Unit)
    (code : List Befehl) (elaboriert : (fragment Ast.Category.unit t).code = code)
    (checks : lokalPruefeCode code = true ∧ waechterFragmentCode code = true ∧ waechterPruefeCode code = true) :
    prueferKombiniert.fragment Plattform.x86_64 t = true ∧
      prueferKombiniert.pruefe Plattform.x86_64 t = true := by
  have klauseln : (fragment Ast.Category.unit t).code.all (pruefeBefehlErhalt []) = true :=
    List.all_eq_true.mpr (fun _ _ => rfl)
  constructor
  · change (lokalPruefeCode (fragment Ast.Category.unit t).code &&
      ((fragment Ast.Category.unit t).code.all (pruefeBefehlErhalt [])) &&
      waechterFragmentCode (fragment Ast.Category.unit t).code) = true
    rw [klauseln, elaboriert, checks.1, checks.2.1] <;> rfl
  · have klauseln := pruefeEinheit_leer (fragment Ast.Category.unit t)
    change (lokalPruefeCode (fragment Ast.Category.unit t).code &&
      pruefeEinheit (fragment Ast.Category.unit t) [] &&
      waechterPruefeCode (fragment Ast.Category.unit t).code) = true
    rw [klauseln, elaboriert, checks.1, checks.2.2] <;> rfl

private theorem prueferKombiniert_druckform (B : FormBeleg) (f : B.Form) (t : Ast.Unit)
    (enthaelt : B.enthaelt (Ast.print (category := Ast.Category.unit) t) f)
    (checks : prueferKombiniert.fragment Plattform.x86_64 t = true ∧
      prueferKombiniert.pruefe Plattform.x86_64 t = true) :
    ∃ (P : Plattform) (u : Ast.Unit) (a : Text.RawText),
      prueferKombiniert.fragment P u = true ∧ prueferKombiniert.pruefe P u = true ∧
        Ast.Parse (category := Ast.Category.unit) a u ∧ B.enthaelt a f :=
  ⟨Plattform.x86_64, t, Ast.print (category := Ast.Category.unit) t,
    checks.1, checks.2, Ast.parse_print (category := Ast.Category.unit) t, enthaelt⟩

/-- The combined checker covers the single-form certificate at the empty source unit. -/
theorem prueferKombiniert_beleg_gedeckt : PrueferDecktFormenAussage prueferKombiniert beleg := by
  intro f
  refine prueferKombiniert_druckform beleg f trivialUnit
    (Ast.parse_print (category := Ast.Category.unit) trivialUnit) ?_
  exact prueferKombiniert_aus_code _ [.starte mainName, .ende] rfl ⟨rfl, rfl, rfl⟩

/-- The combined checker covers each of the eleven registered scalar forms. -/
theorem prueferKombiniert_basisBeleg_gedeckt : PrueferDecktFormenAussage prueferKombiniert basisBeleg := by
  intro f
  refine prueferKombiniert_druckform basisBeleg f (basisUnit f) rfl ?_
  cases f <;> refine prueferKombiniert_aus_code _ _ ?_ ?_
  all_goals
    first
    | exact basisUnit_code_lit
    | exact basisUnit_code_binary
    | exact basisUnit_code_trueLit
    | exact basisUnit_code_falseLit
    | exact basisUnit_code_variable
    | exact basisUnit_code_negativeLit
    | exact basisUnit_code_neg
    | exact basisUnit_code_not
    | exact basisUnit_code_div
    | exact basisUnit_code_compare
    | exact basisUnit_code_logic
    | exact ⟨rfl, rfl, rfl⟩

/-- The combined checker covers the four aggregate forms in the current certificate. -/
theorem prueferKombiniert_aggregatBeleg_gedeckt :
    PrueferDecktFormenAussage prueferKombiniert aggregatBeleg := by
  intro f
  refine prueferKombiniert_druckform aggregatBeleg f (aggregatUnit f) rfl ?_
  cases f <;> refine prueferKombiniert_aus_code _ _ ?_ ?_
  all_goals
    first
    | exact aggregatUnit_code_arrayValue
    | exact aggregatUnit_code_arrayIndex
    | exact aggregatUnit_code_tupleValue
    | exact aggregatUnit_code_tupleField
    | exact ⟨rfl, rfl, rfl⟩

/-- The combined checker covers the three record and variant forms in the current certificate. -/
theorem prueferKombiniert_datensatzBeleg_gedeckt :
    PrueferDecktFormenAussage prueferKombiniert datensatzBeleg := by
  intro f
  refine prueferKombiniert_druckform datensatzBeleg f (datensatzUnit f) rfl ?_
  cases f <;> refine prueferKombiniert_aus_code _ _ ?_ ?_
  all_goals
    first
    | exact recordZeugnisEinheit_code
    | exact variantZeugnisEinheit_code
    | exact ⟨rfl, rfl, rfl⟩

/-- The combined checker covers the union of the current typed form certificates. -/
theorem prueferKombiniert_formen_gedeckt :
    PrueferDecktFormenAussage prueferKombiniert
      (FormBeleg.summe (FormBeleg.summe basisBeleg aggregatBeleg) datensatzBeleg) := by
  intro f
  rcases f with (f | f) | f
  · exact prueferKombiniert_basisBeleg_gedeckt f
  · exact prueferKombiniert_aggregatBeleg_gedeckt f
  · exact prueferKombiniert_datensatzBeleg_gedeckt f

end Gabbro.Core.Ziel.Korrektheit
