module

public import Core.Ast.Semantik.Quellform
public import Core.Ast.Semantik.ProgramForms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

def tableForm (scope : Scope) : Quellform (.declaration scope) (TableDeclaration scope) where
  produktion :=
    { tree := fun item => ⟨_, .table item⟩
      production := fun item tokens =>
        ∃ input, tokens = item.header.map PrintedToken.value ++ input ∧
          TableFieldsRead (carrierFieldScope scope item.name item.count) input item.fields [closeBrace] }
  befehl := tableInstruction
  position := fun _ => 0

def TableInversionAussage : Prop :=
  ∀ {scope input tree rest} (head : TableDeclaration scope),
    DeclReads scope (head.header.map PrintedToken.value ++ input) tree rest →
    ∃ item : TableDeclaration scope,
      item.name = head.name ∧ item.count = head.count ∧ item.exported = head.exported ∧
      TableFieldsRead (carrierFieldScope scope item.name item.count) input item.fields (closeBrace :: rest) ∧
      tree = (tableForm scope).produktion.tree item

def TableDerivationAussage : Prop :=
  ∀ scope, (tableForm scope).produktion.Entry

def TableScopeAussage : Prop :=
  ∀ (scope : Scope) (item : TableDeclaration scope),
    let after := ((tableForm scope).produktion.tree item).1
    after.carrierCount item.name = some item.count ∧
    (∀ other : Identifier, other.val ≠ item.name.val →
      after.carrierCount other = scope.carrierCount other) ∧
    ¬ item.binding.type.valueBinding

def TableBindingAussage : Prop :=
  ∀ (scope : Scope) (item : TableDeclaration scope) (frame : Rahmen),
    let next := (tableInstruction item).auswerten frame
    let marker : Dynamisch := ⟨.carrierSchema item.count ((recordLabels item.fields).map Subtype.val)
      (tupleType (recordTypes item.fields)), PUnit.unit⟩
    marker.1 = item.binding.type ∧ next.lokale = some marker :: frame.lokale ∧
      next.globale = some marker :: frame.globale ∧ next.pc = frame.pc + 1 ∧ next.temp = frame.temp

def TableParseAussage : Prop :=
  ∀ scope, (tableForm scope).ParseAussage

def TableElaboriertAussage : Prop :=
  ∀ scope, (tableForm scope).ElaboriertAussage

def TableRealisiertAussage : Prop :=
  ∀ scope, (tableForm scope).RealisiertAussage

def TableAnnahmeAussage : Prop :=
  ∀ scope, (tableForm scope).AnnahmeAussage

def TableIdealAussage : Prop :=
  ∀ scope, (tableForm scope).IdealAussage

def TableEinheitAussage : Prop :=
  ∀ scope, (tableForm scope).EinheitAussage

def TableImplAussage : Prop :=
  ∀ scope, (tableForm scope).ImplAussage

def TableErhaltungAussage : Prop :=
  ∀ scope, (tableForm scope).ErhaltungsAussage

def TableRegelSicherAussage : Prop :=
  ∀ scope platform item,
    let form := tableForm scope
    Sicherheit.RegelSicher ((form.fragment item).sicherheitsEinheit platform) (form.befehl item)

/-- Both carrier-derived types occur after the declaration in the same parsed unit. -/
def TableErfuellbarAmAussage : Prop :=
  ∀ platform start,
    ∃ (item : TableDeclaration []) after (rest : UnitBody [item.binding] after)
      (text : RawText) (s : Zustand),
      let tree : Ast.Unit := ⟨after, .step (.table item) rest⟩
      let E := elaborieren platform tree
      item.count > 0 ∧
      (∃ (args : Surface.FunctionArgs [item.binding]) (tail : UnitBody [item.binding] after),
        rest = .step (.function args.name args.ordinary args.parameters args.result args.valid
          args.measure args.body args.distinct args.returns) tail ∧
        (∃ p ∈ args.parameters, p.written = .index item.name item.count) ∧
        (∃ p ∈ args.parameters, p.written = .indexOption item.name item.count)) ∧
      Ast.Parse text tree ∧ Elaboriert platform tree E ∧
      E.system.IErreichbar (I.start E start).2 s ∧
      E.system.kopf s eintritt = some (tableInstruction item) ∧
      E.system.ISchritt eintritt s () [plan] ((tableInstruction item).nach eintritt s) ∧
      E.system.ImplSchritt eintritt s () [plan] ((tableInstruction item).nach eintritt s)

def TableProofPacket : Prop :=
  TableInversionAussage ∧
  TableDerivationAussage ∧
  TableScopeAussage ∧
  TableBindingAussage ∧
  TableParseAussage ∧
  TableElaboriertAussage ∧
  TableRealisiertAussage ∧
  TableAnnahmeAussage ∧
  TableIdealAussage ∧
  TableEinheitAussage ∧
  TableImplAussage ∧
  TableErhaltungAussage ∧
  TableRegelSicherAussage ∧
  TableErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
