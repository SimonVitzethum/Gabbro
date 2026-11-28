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
  cases f with
  | lit => exact prueferKombiniert_aus_code _ _ basisUnit_code_lit ⟨rfl, rfl, rfl⟩
  | binary => exact prueferKombiniert_aus_code _ _ basisUnit_code_binary ⟨rfl, rfl, rfl⟩
  | trueLit => exact prueferKombiniert_aus_code _ _ basisUnit_code_trueLit ⟨rfl, rfl, rfl⟩
  | falseLit => exact prueferKombiniert_aus_code _ _ basisUnit_code_falseLit ⟨rfl, rfl, rfl⟩
  | «variable» => exact prueferKombiniert_aus_code _ _ basisUnit_code_variable ⟨rfl, rfl, rfl⟩
  | negativeLit => exact prueferKombiniert_aus_code _ _ basisUnit_code_negativeLit ⟨rfl, rfl, rfl⟩
  | neg => exact prueferKombiniert_aus_code _ _ basisUnit_code_neg ⟨rfl, rfl, rfl⟩
  | not => exact prueferKombiniert_aus_code _ _ basisUnit_code_not ⟨rfl, rfl, rfl⟩
  | div => exact prueferKombiniert_aus_code _ _ basisUnit_code_div ⟨rfl, rfl, rfl⟩
  | compare => exact prueferKombiniert_aus_code _ _ basisUnit_code_compare ⟨rfl, rfl, rfl⟩
  | logic => exact prueferKombiniert_aus_code _ _ basisUnit_code_logic ⟨rfl, rfl, rfl⟩

/-- The combined checker covers the four aggregate forms in the current certificate. -/
theorem prueferKombiniert_aggregatBeleg_gedeckt :
    PrueferDecktFormenAussage prueferKombiniert aggregatBeleg := by
  intro f
  refine prueferKombiniert_druckform aggregatBeleg f (aggregatUnit f) rfl ?_
  cases f with
  | arrayValue => exact prueferKombiniert_aus_code _ _ aggregatUnit_code_arrayValue ⟨rfl, rfl, rfl⟩
  | arrayIndex => exact prueferKombiniert_aus_code _ _ aggregatUnit_code_arrayIndex ⟨rfl, rfl, rfl⟩
  | tupleValue => exact prueferKombiniert_aus_code _ _ aggregatUnit_code_tupleValue ⟨rfl, rfl, rfl⟩
  | tupleField => exact prueferKombiniert_aus_code _ _ aggregatUnit_code_tupleField ⟨rfl, rfl, rfl⟩

/-- The combined checker covers the three record and variant forms in the current certificate. -/
theorem prueferKombiniert_datensatzBeleg_gedeckt :
    PrueferDecktFormenAussage prueferKombiniert datensatzBeleg := by
  intro f
  refine prueferKombiniert_druckform datensatzBeleg f (datensatzUnit f) rfl ?_
  cases f with
  | recordValue => exact prueferKombiniert_aus_code _ _ recordZeugnisEinheit_code ⟨rfl, rfl, rfl⟩
  | recordField => exact prueferKombiniert_aus_code _ _ recordZeugnisEinheit_code ⟨rfl, rfl, rfl⟩
  | variantValue => exact prueferKombiniert_aus_code _ _ variantZeugnisEinheit_code ⟨rfl, rfl, rfl⟩

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
