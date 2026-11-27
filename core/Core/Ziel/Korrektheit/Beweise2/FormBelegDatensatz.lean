/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/FormBelegDatensatz.lean
  Subject:   A TYPED, COMPOSABLE form certificate for the three record/variant `Expr` constructors
             (`Expr.recordValue`, `Expr.recordField`, `Expr.variantValue`). This is the next isolated M12
             form-register part after the eleven scalar base forms (`FormBelegBasis.lean`) and the four
             aggregate forms (`FormBelegAggregate.lean`). Each form gets a source witness, admission and
             acceptance proof, a real occurrence at the registry's linearisation position and the registry's
             stronger joint-satisfiability evidence (`ErfuellbarAm`). Acceptance is transported to the
             concrete `Annahme.Quelle.Akzeptiert` the frame `R₀` binds. Coverage is composed with the
             existing certificates through `FormBeleg.summe`: no registry row is duplicated and no syntax
             is added.

  This module does NOT replace the Unit placeholder `beleg` of `BegleitZusammensetzung.lean`, and it does
  not touch `R₀`, any Zielsatz, a pin or the root (registered by the lead). It adds a separate composable
  certificate and proves that the union with the base and aggregate certificates stays covered.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ziel.Korrektheit.Beweise2.FormBelegAggregate
public import Core.Ast.Inventory.Entries.Records
public import Core.Ast.Inventory.Entries.Variants

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Katalog
open Gabbro.Core.Waechter
open Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

/-- The three record/variant expression forms, one per registered inventory row. -/
inductive DatensatzForm where
  | recordValue
  | recordField
  | variantValue

/-- The shared record witness: a record schema declaration and a constant that computes a field of the
    built record. The constant's written type is `bool`, so the record construction is a frame-only
    top-level code prefix. The `recordValue` form is the base of this expression, the `recordField` form
    the projection; both instructions occur at fixed positions. -/
def recordFeldArgumente : RecordFieldArgs RecordExample.scope := by
  let index : Fin RecordExample.value.types.length := ⟨0, Nat.zero_lt_succ _⟩
  let checked : RecordFieldAt RecordExample.value.labels RecordExample.field index.val :=
    ⟨List.nodup_singleton _, rfl⟩
  exact ⟨RecordExample.value.ref.name.val, RecordExample.value.labels,
    RecordExample.value.types, RecordExample.value.expression, RecordExample.field, index, checked⟩

def recordZeugnisEinheit : Ast.Unit :=
  let schema : Decl [] RecordExample.scope :=
    .record false RecordExample.name [⟨RecordExample.field, .bool⟩]
      (by intro m belongs; cases List.mem_singleton.mp belongs; trivial) (List.nodup_singleton _)
  let wert := recordFeldArgumente.expression
  ⟨⟨basisName, .bool, false, true⟩ :: RecordExample.scope,
    .step schema (.step (.constant basisName basisName_ordinary .bool (by trivial) wert
      (by trivial) (by trivial)) .done)⟩

/-- The elaborated code of the shared record witness. -/
theorem recordZeugnisEinheit_code :
    (fragment Ast.Category.unit recordZeugnisEinheit).code =
      [.definiereRecord RecordExample.name.val [RecordExample.field] [.bool],
       .wahrheitswert 0 true,
       .baueRecord 0 RecordExample.name.val [RecordExample.field] [.bool] [0],
       .liesRecordFeld 0 RecordExample.name.val [RecordExample.field] [.bool] 0,
       .bindeWert 0 .bool true, .starte Ast.Semantik.mainName, .ende] := rfl

/-- The variant witness scope: one ordinary tag with no payload. -/
def variantZeugnisName : Identifier :=
  keywordName 'v' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

def variantZeugnisLabel : Identifier :=
  keywordName 'a' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

def variantZeugnisMember : VariantMember := ⟨variantZeugnisLabel, none⟩

def variantZeugnisLabels : List Identifier := variantLabels [variantZeugnisMember]

def variantZeugnisPayloads : List (Option (Ty .value)) := variantPayloads [variantZeugnisMember]

def variantZeugnisTyp : Ty .value :=
  variantSchemaType variantZeugnisName.val variantZeugnisLabels variantZeugnisPayloads

def variantZeugnisBinding : Binding := ⟨variantZeugnisName, variantZeugnisTyp, false, true⟩

def variantZeugnisScope : Scope := [variantZeugnisBinding]

def variantZeugnisArgumente : VariantValueArgs variantZeugnisScope := by
  let refSchema : Local variantZeugnisScope variantZeugnisTyp := .here
  let ref : VariantRef variantZeugnisScope variantZeugnisLabels variantZeugnisPayloads :=
    ⟨variantZeugnisName, refSchema, trivial, rfl, rfl,
      by change [variantZeugnisLabel.val].Nodup; exact List.nodup_singleton _⟩
  let index : Fin variantZeugnisPayloads.length := ⟨0, Nat.zero_lt_succ _⟩
  have written : variantZeugnisLabels[index.val]? = some variantZeugnisLabel := rfl
  have ordinary : ordinaryLocal variantZeugnisLabel :=
    (directName_of_singleton (name := variantZeugnisLabel) rfl).1
  have available : availableCase variantZeugnisScope variantZeugnisLabel := by
    constructor
    · exact List.count_singleton_self
    · intro b hb
      have same : b = variantZeugnisBinding := List.mem_singleton.mp hb
      subst b
      intro same
      cases same
  exact ⟨variantZeugnisLabels, variantZeugnisPayloads, ref, variantZeugnisLabel, index,
    written, ordinary, available, .nullary false⟩

/-- The variant witness: a tagged declaration and a `main` function whose body binds the variant value.
    Function bodies are appended to the unit's top-level code, so `baueVariante` occurs there directly. -/
def variantZeugnisEinheit : Ast.Unit :=
  let schema : Decl [] variantZeugnisScope :=
    .tagged false variantZeugnisName variantZeugnisMember []
      (by
        intro m belongs
        rcases List.mem_cons.mp belongs with rfl | empty
        · exact ⟨(directName_of_singleton (name := variantZeugnisLabel) rfl).1,
            by decide, by trivial⟩
        · exact (List.not_mem_nil empty).elim)
      (by change [variantZeugnisLabel.val].Nodup; exact List.nodup_singleton _)
  let body : BracedBlock none variantZeugnisScope :=
    .braces (.step (.letValue basisName (by decide) variantZeugnisArgumente.expression) .done)
  let main : Decl variantZeugnisScope variantZeugnisScope :=
    .function Ast.Semantik.mainName Ast.Semantik.mainName_direct [] none
      (fun _ h => (List.not_mem_nil h).elim) none body List.nodup_nil (fun h => by cases h) none
  ⟨⟨basisName,
      variantValueType variantZeugnisName.val variantZeugnisLabels variantZeugnisPayloads,
      false, false⟩ :: variantZeugnisScope,
    .step schema (.step main .done)⟩

theorem variantZeugnisEinheit_code :
    (fragment Ast.Category.unit variantZeugnisEinheit).code =
      [.definiereVariante variantZeugnisName.val variantZeugnisLabels variantZeugnisPayloads,
       .definiere Ast.Semantik.mainName [] none 1 5 false [] none,
       .baueVariante 0 variantZeugnisName.val variantZeugnisLabels variantZeugnisPayloads 0,
       .binden basisName 0, .blockEnde 1, .rueckVoid,
       .starte Ast.Semantik.mainName, .ende] := by
  rfl

/-- The witness unit of each form. -/
def datensatzUnit : DatensatzForm → Ast.Unit
  | .recordValue => recordZeugnisEinheit
  | .recordField => recordZeugnisEinheit
  | .variantValue => variantZeugnisEinheit

/-- Environment admission: the witnesses declare no environment interface. -/
private theorem zeugnisEnvironmentAllowed (code : List Befehl) (P : Plattform)
    (hcode : (fragment Ast.Category.unit recordZeugnisEinheit).code = code ∨
      (fragment Ast.Category.unit variantZeugnisEinheit).code = code) :
    (match hcode with
    | Or.inl _ => (fragment Ast.Category.unit recordZeugnisEinheit).environmentAllowed P.katalog
    | Or.inr _ => (fragment Ast.Category.unit variantZeugnisEinheit).environmentAllowed P.katalog) := by
  cases hcode with
  | inl h =>
      rw [h, recordZeugnisEinheit_code]
      simp only [Fragment.environmentAllowed, Fragment.environment, List.filterMap_cons,
        List.filterMap_nil]
      exact ⟨List.nodup_nil, fun e present => (List.not_mem_nil present).elim⟩
  | inr h =>
      rw [h, variantZeugnisEinheit_code]
      simp only [Fragment.environmentAllowed, Fragment.environment, List.filterMap_cons,
        List.filterMap_nil]
      exact ⟨List.nodup_nil, fun e present => (List.not_mem_nil present).elim⟩

theorem datensatzUnit_zugelassen (f : DatensatzForm) (P : Plattform) :
    Ast.Semantik.zugelassen P Ast.Category.unit (datensatzUnit f) := by
  cases f <;>
    change (fragment Ast.Category.unit (datensatzUnit f)).environmentAllowed P.katalog ∧
      (fragment Ast.Category.unit (datensatzUnit f)).code.all (Befehl.platformAllowed P) = true
  all_goals
    constructor
    · exact zeugnisEnvironmentAllowed _ P (Or.inl rfl)
    · simp only [datensatzUnit, recordZeugnisEinheit_code, Befehl.platformAllowed, platformType,
        tupleType, List.all_cons, List.all_nil, Bool.true_and]

/-- Every instruction of a witness code is frame-only. -/
private theorem recordZeugnisEinheit_rein :
    ∀ b ∈ (fragment Ast.Category.unit recordZeugnisEinheit).code, b.Privat := by
  rw [recordZeugnisEinheit_code]
  intro b present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

private theorem variantZeugnisEinheit_rein :
    ∀ b ∈ (fragment Ast.Category.unit variantZeugnisEinheit).code, b.Privat := by
  rw [variantZeugnisEinheit_code]
  intro b present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

theorem datensatzUnit_rein (f : DatensatzForm) :
    ∀ b ∈ (fragment Ast.Category.unit (datensatzUnit f)).code, b.Privat := by
  cases f
  · exact recordZeugnisEinheit_rein
  · exact recordZeugnisEinheit_rein
  · exact variantZeugnisEinheit_rein

/-- The static guard verdict accepts both codes: record and variant instructions carry no guard. -/
private theorem recordZeugnisEinheit_guarded :
    waechterPruefeCode (fragment Ast.Category.unit recordZeugnisEinheit).code = true := by
  rw [recordZeugnisEinheit_code]
  rfl

private theorem variantZeugnisEinheit_guarded :
    waechterPruefeCode (fragment Ast.Category.unit variantZeugnisEinheit).code = true := by
  rw [variantZeugnisEinheit_code]
  rfl

theorem datensatzUnit_guarded (f : DatensatzForm) :
    waechterPruefeCode (fragment Ast.Category.unit (datensatzUnit f)).code = true := by
  cases f
  · exact recordZeugnisEinheit_guarded
  · exact recordZeugnisEinheit_guarded
  · exact variantZeugnisEinheit_guarded

/-- A fragment with empty clauses, frame-only code and a passing guard analysis yields an accepted unit. -/
private theorem datensatzAkzeptiert (p : Fragment) (P : Plattform)
    (clauses : p.klauseln = .leer) (rein : ∀ b ∈ p.code, b.Privat)
    (guarded : waechterPruefeCode p.code = true) :
    Annahme.Akzeptiert (p.einheit P) := by
  refine ⟨p.lokal_rahmen P rein, ?_, waechterAbstrakt p P guarded⟩
  intro run conforms
  change (∀ pred ∈ p.klauseln.voraus, _) ∧
    (∀ _ : Maschine.I.Schnitt (p.einheit P) run, ∀ pred ∈ p.klauseln.invariant, _) ∧
    ∀ _ : Maschine.I.Schnitt (p.einheit P) run, _ → ∀ pred ∈ p.klauseln.sicher, _
  rw [clauses]
  exact ⟨fun _ h => (List.not_mem_nil h).elim,
    fun _ _ h => (List.not_mem_nil h).elim,
    fun _ _ _ h => (List.not_mem_nil h).elim⟩

theorem datensatzUnit_akzeptiert (f : DatensatzForm) (P : Plattform) :
    Annahme.Akzeptiert (einheitVon P (datensatzUnit f)) := by
  let p := fragment Ast.Category.unit (datensatzUnit f)
  change Annahme.Akzeptiert (p.einheit P)
  exact datensatzAkzeptiert p P rfl (datensatzUnit_rein f) (datensatzUnit_guarded f)

/-- The concrete source acceptance `R₀` binds agrees with the elaborated acceptance on every witness. -/
theorem datensatzUnit_quellAkzeptiert (f : DatensatzForm) (P : Plattform) :
    Annahme.Quelle.Akzeptiert (einheitVon P (datensatzUnit f)) := by
  exact (Annahme.Quelle.akzeptiert_elaboriert_iff P (datensatzUnit f)).2
    (datensatzUnit_akzeptiert f P)

/-- The instruction realising each form and the exact linearisation position of its witness. -/
def datensatzBefehl : DatensatzForm → Befehl
  | .recordValue => .baueRecord 0 RecordExample.name.val [RecordExample.field] [.bool] [0]
  | .recordField => .liesRecordFeld 0 RecordExample.name.val [RecordExample.field] [.bool] 0
  | .variantValue =>
      .baueVariante 0 variantZeugnisName.val variantZeugnisLabels variantZeugnisPayloads 0

def datensatzPosition : DatensatzForm → Nat
  | .recordValue => 2
  | .recordField => 3
  | .variantValue => 2

theorem datensatzUnit_occurrence (f : DatensatzForm) :
    (fragment Ast.Category.unit (datensatzUnit f)).code[datensatzPosition f]? =
      some (datensatzBefehl f) := by
  cases f
  · rw [datensatzUnit, recordZeugnisEinheit_code]
    rfl
  · rw [datensatzUnit, recordZeugnisEinheit_code]
    rfl
  · rw [datensatzUnit, variantZeugnisEinheit_code]
    rfl

/-- The typed, composable certificate. The registry occurrence is carried by the exact code position
    above; the registry's stronger joint satisfiability is carried by the existing `ErfuellbarAm` proofs. -/
def datensatzBeleg : FormBeleg where
  Form := DatensatzForm
  enthaelt a f := a = Ast.print (category := Ast.Category.unit) (datensatzUnit f)
  realisiert f a E :=
    a = Ast.print (category := Ast.Category.unit) (datensatzUnit f) ∧
    E = einheitVon Plattform.x86_64 (datensatzUnit f) ∧
    (fragment Ast.Category.unit (datensatzUnit f)).code[datensatzPosition f]? =
      some (datensatzBefehl f) ∧
    ∀ start : AussenStart,
      match f with
      | .recordValue => ∃ scope args, (recordValueForm scope).ErfuellbarAm
          Plattform.x86_64 start args
      | .recordField => ∃ scope args, (recordFieldForm scope).ErfuellbarAm
          Plattform.x86_64 start args
      | .variantValue => ∃ scope args, (variantValueForm scope).ErfuellbarAm
          Plattform.x86_64 start args

/-- The registry's joint-satisfiability statements are inhabited by the existing form proofs. -/
private theorem datensatzForm_erfuellbar (f : DatensatzForm) (start : AussenStart) :
    match f with
    | .recordValue => ∃ scope args, (recordValueForm scope).ErfuellbarAm
        Plattform.x86_64 start args
    | .recordField => ∃ scope args, (recordFieldForm scope).ErfuellbarAm
        Plattform.x86_64 start args
    | .variantValue => ∃ scope args, (variantValueForm scope).ErfuellbarAm
        Plattform.x86_64 start args := by
  cases f
  · exact recordValue_erfuellbarAm Plattform.x86_64 start
  · exact RecordFieldErfuellbarAm Plattform.x86_64 start
  · exact variantValue_erfuellbarAm Plattform.x86_64 start

/-- Every form occurs in an accepted source unit, is denoted there, is realised at its registry position
    and is backed by the registry's reachable-and-guarded evidence. -/
theorem datensatzBeleg_gedeckt : FormenGedecktAussage Plattform.x86_64 datensatzBeleg := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (datensatzUnit f),
    einheitVon Plattform.x86_64 (datensatzUnit f), ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨datensatzUnit f, Ast.parse_print (category := Ast.Category.unit) (datensatzUnit f),
      ⟨rfl, datensatzUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact datensatzUnit_akzeptiert f Plattform.x86_64
  · exact ⟨rfl, rfl, datensatzUnit_occurrence f, datensatzForm_erfuellbar f⟩

/-- The same coverage under the concrete source acceptance `R₀` binds as its `Akzeptiert` field. -/
theorem datensatzBeleg_gedeckt_quell :
    ∀ f : DatensatzForm, ∃ (a : Text.RawText) (E : Ast.Semantik.Einheit),
      datensatzBeleg.enthaelt a f ∧
      Ast.Semantik.Bezeichnet Plattform.x86_64 Ast.Category.unit a E ∧
      Annahme.Quelle.Akzeptiert E ∧ datensatzBeleg.realisiert f a E := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (datensatzUnit f),
    einheitVon Plattform.x86_64 (datensatzUnit f), ?_, ?_, ?_, ?_⟩
  · rfl
  · exact ⟨datensatzUnit f, Ast.parse_print (category := Ast.Category.unit) (datensatzUnit f),
      ⟨rfl, datensatzUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact datensatzUnit_quellAkzeptiert f Plattform.x86_64
  · exact ⟨rfl, rfl, datensatzUnit_occurrence f, datensatzForm_erfuellbar f⟩

/-- The family is genuinely backed by the existing registry: each form maps to a constructor whose
    complete typed `RegistryEntry` is already registered. -/
def datensatzFormConstructor : DatensatzForm → Lean.Name
  | .recordValue => ``Expr.recordValue
  | .recordField => ``Expr.recordField
  | .variantValue => ``Expr.variantValue

theorem datensatzForm_registry_covered (f : DatensatzForm) :
    Nonempty (RegistryEntry (datensatzFormConstructor f) (exprSchema (datensatzFormConstructor f))) := by
  cases f
  · exact ⟨recordValueEntry.entry⟩
  · exact ⟨recordFieldEntry.entry⟩
  · exact ⟨variantValueEntry.entry⟩

/-- The three forms lie outside both the base and the aggregate families. -/
theorem aggregatForm_nicht_datensatz (f : AggregatForm) :
    aggregatFormConstructor f ≠ ``Expr.recordValue ∧
    aggregatFormConstructor f ≠ ``Expr.recordField ∧
    aggregatFormConstructor f ≠ ``Expr.variantValue := by
  cases f <;> simp only [aggregatFormConstructor, ne_eq, Lean.Name.str.injEq, String.reduceEq,
    and_false, not_false_eq_true, and_self]

theorem datensatzForm_nicht_basis_oder_aggregat (f : DatensatzForm) :
    datensatzFormConstructor f ≠ ``Expr.lit ∧
    datensatzFormConstructor f ≠ ``Expr.arrayValue ∧
    datensatzFormConstructor f ≠ ``Expr.arrayIndex ∧
    datensatzFormConstructor f ≠ ``Expr.tupleValue ∧
    datensatzFormConstructor f ≠ ``Expr.tupleField := by
  cases f <;> simp only [datensatzFormConstructor, ne_eq, Lean.Name.str.injEq, String.reduceEq,
    and_false, not_false_eq_true, and_self]

/-- Combined coverage: the union with the already-covered base and aggregate certificates is covered.
    This reuses `FormBeleg.summe` and `FormenGedecktAussage.summe`; no registry row or syntax is added. -/
theorem basisAggregatUndDatensatzBeleg_gedeckt :
    FormenGedecktAussage Plattform.x86_64
      (FormBeleg.summe (FormBeleg.summe basisBeleg aggregatBeleg) datensatzBeleg) :=
  FormenGedecktAussage.summe Plattform.x86_64 (FormBeleg.summe basisBeleg aggregatBeleg)
    datensatzBeleg (basisUndAggregatBeleg_gedeckt) datensatzBeleg_gedeckt

end Gabbro.Core.Ziel.Korrektheit
