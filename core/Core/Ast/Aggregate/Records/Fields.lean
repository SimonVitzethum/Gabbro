module

public import Core.Ast.Aggregate.Records.RecordForms
public import Core.Ast.Aggregate.Records.Syntax

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def RecordFieldParseAussage : Prop :=
  ∀ scope, (recordFieldForm scope).ParseAussage

def RecordFieldElaboriertAussage : Prop :=
  ∀ scope, (recordFieldForm scope).ElaboriertAussage

def RecordFieldRealisiertAussage : Prop :=
  ∀ scope, (recordFieldForm scope).RealisiertAussage

def RecordFieldAnnahmeAussage : Prop :=
  ∀ scope, (recordFieldForm scope).AnnahmeAussage

def RecordFieldIdealAussage : Prop :=
  ∀ scope, (recordFieldForm scope).IdealAussage

def RecordFieldEinheitAussage : Prop :=
  ∀ scope, (recordFieldForm scope).EinheitAussage

def RecordFieldImplAussage : Prop :=
  ∀ scope, (recordFieldForm scope).ImplAussage

def RecordFieldErhaltungAussage : Prop :=
  ∀ scope, (recordFieldForm scope).ErhaltungsAussage

def RecordFieldRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := recordFieldForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def RecordFieldErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ scope, ∃ args, (recordFieldForm scope).ErfuellbarAm platform start args

def RecordFieldProofPacket : Prop :=
  Surface.RecordFieldInversionAussage ∧
  Surface.RecordFieldSuffixAussage ∧
  Surface.RecordFieldDerivationAussage ∧
  RecordFieldParseAussage ∧
  RecordFieldElaboriertAussage ∧
  RecordFieldRealisiertAussage ∧
  RecordFieldAnnahmeAussage ∧
  RecordFieldIdealAussage ∧
  RecordFieldEinheitAussage ∧
  RecordFieldImplAussage ∧
  RecordFieldErhaltungAussage ∧
  RecordFieldRegelSicherAussage ∧
  RecordFieldErfuellbarAmAussage ∧
  RecordFieldValueAussage

def AssignFieldParseAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).ParseAussage

def AssignFieldElaboriertAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).ElaboriertAussage

def AssignFieldRealisiertAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).RealisiertAussage

def AssignFieldAnnahmeAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).AnnahmeAussage

def AssignFieldIdealAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).IdealAussage

def AssignFieldEinheitAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).EinheitAussage

def AssignFieldImplAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).ImplAussage

def AssignFieldErhaltungAussage : Prop :=
  ∀ ctx, (assignFieldForm ctx).ErhaltungsAussage

def AssignFieldRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := assignFieldForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def AssignFieldErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ ctx, ∃ args, (assignFieldForm ctx).ErfuellbarAm platform start args

/-- An assignment in a closed source unit reaches a live record local and changes its field. -/
def AssignFieldProgramAussage : Prop :=
  ∀ platform start, ∃ (tree : Ast.Unit) (text : Gabbro.Core.Text.RawText) (s : Zustand)
    (src indexLocal : Nat) (name : List Char) (labels : List Identifier)
    (types : List (Ty .value)) (i : Fin types.length),
    Ast.Parse (category := .unit) text tree ∧
    let E := elaborieren platform (category := .unit) tree
    let b := Befehl.setzeRecordFeld src indexLocal name labels types i
    E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s eintritt = some b ∧
    ∃ (before after : Wert (recordValueType name labels types)),
      (s.lokal eintritt).lokale[indexLocal]? = some (some ⟨recordValueType name labels types, before⟩) ∧
      ((b.nach eintritt s).lokal eintritt).lokale[indexLocal]? =
        some (some ⟨recordValueType name labels types, after⟩) ∧
      tupleGet types i before ≠ tupleGet types i after

def AssignFieldProofPacket : Prop :=
  Surface.AssignFieldInversionAussage ∧
  Surface.AssignFieldSuffixAussage ∧
  Surface.AssignFieldDerivationAussage ∧
  AssignFieldParseAussage ∧
  AssignFieldElaboriertAussage ∧
  AssignFieldRealisiertAussage ∧
  AssignFieldAnnahmeAussage ∧
  AssignFieldIdealAussage ∧
  AssignFieldEinheitAussage ∧
  AssignFieldImplAussage ∧
  AssignFieldErhaltungAussage ∧
  AssignFieldRegelSicherAussage ∧
  AssignFieldErfuellbarAmAussage ∧
  AssignFieldFrameAussage ∧
  AssignFieldProgramAussage

end Gabbro.Core.Ast.Semantik
