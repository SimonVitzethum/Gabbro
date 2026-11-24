module

public import Core.Ast.Aggregate.RecordForms
public import Core.Ast.Aggregate.Records.Syntax

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def TupleBindParseAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).ParseAussage

def TupleBindElaboriertAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).ElaboriertAussage

def TupleBindRealisiertAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).RealisiertAussage

def TupleBindAnnahmeAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).AnnahmeAussage

def TupleBindIdealAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).IdealAussage

def TupleBindEinheitAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).EinheitAussage

def TupleBindImplAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).ImplAussage

def TupleBindErhaltungAussage : Prop :=
  ∀ ctx, (tupleBindForm ctx).ErhaltungsAussage

def TupleBindRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := tupleBindForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TupleBindErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (tupleBindForm ([], none)).ErfuellbarAm platform start args

def TupleBindProofPacket : Prop :=
  Surface.TupleBindInversionAussage ∧
  Surface.TupleBindSuffixAussage ∧
  Surface.TupleBindDerivationAussage ∧
  TupleBindParseAussage ∧
  TupleBindElaboriertAussage ∧
  TupleBindRealisiertAussage ∧
  TupleBindAnnahmeAussage ∧
  TupleBindIdealAussage ∧
  TupleBindEinheitAussage ∧
  TupleBindImplAussage ∧
  TupleBindErhaltungAussage ∧
  TupleBindRegelSicherAussage ∧
  TupleBindErfuellbarAmAussage ∧
  TupleBindLocalsAussage

end Gabbro.Core.Ast.Semantik
