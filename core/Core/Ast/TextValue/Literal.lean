module

public import Core.Ast.TextValue.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

open Gabbro.Core.Text

def TextLiteralInversionAussage : Prop :=
  ∀ {scope decoded input type} {tree : Expr scope type} {rest},
    AtomReads scope (.string decoded :: input) tree rest →
    tree.typed = (Expr.textLiteral (scope := scope) decoded).typed ∧ rest = input

def TextLiteralDerivationAussage : Prop :=
  ∀ scope, (Surface.textLiteral scope).Entry

def TextLiteralBytesAussage : Prop :=
  ∀ decoded (frame : Rahmen),
    let next := (Befehl.textLiteral 0 decoded).auswerten frame
    next.temp 0 = some ⟨.text (sourceUtf8 decoded).size, TextValue.literal decoded⟩ ∧
      (TextValue.literal decoded).bytes = decoded.utf8Encode ∧
      next.pc = frame.pc + 1

def TextLiteralParseAussage : Prop :=
  ∀ scope, (textLiteralForm scope).ParseAussage

def TextLiteralElaboriertAussage : Prop :=
  ∀ scope, (textLiteralForm scope).ElaboriertAussage

def TextLiteralRealisiertAussage : Prop :=
  ∀ scope, (textLiteralForm scope).RealisiertAussage

def TextLiteralAnnahmeAussage : Prop :=
  ∀ scope, (textLiteralForm scope).AnnahmeAussage

def TextLiteralIdealAussage : Prop :=
  ∀ scope, (textLiteralForm scope).IdealAussage

def TextLiteralEinheitAussage : Prop :=
  ∀ scope, (textLiteralForm scope).EinheitAussage

def TextLiteralImplAussage : Prop :=
  ∀ scope, (textLiteralForm scope).ImplAussage

def TextLiteralErhaltungAussage : Prop :=
  ∀ scope, (textLiteralForm scope).ErhaltungsAussage

def TextLiteralKernOrtAussage : Prop :=
  ∀ scope, (textLiteralForm scope).RegelAmOrt

def TextLiteralRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textLiteralForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TextLiteralRegelAntwortSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textLiteralForm scope
    RegelAntwortSicher (form.fragment args) platform (form.befehl args)

def TextLiteralKostenUndSpurAussage : Prop :=
  ∀ scope platform args,
    let form := textLiteralForm scope
    TextInstructionCost (form.fragment args) platform (form.befehl args)

def TextLiteralErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (textLiteralForm []).TextErfuellbar platform start args

def TextLiteralProofPacket : Prop :=
  TextLiteralParseAussage ∧
  TextLiteralElaboriertAussage ∧
  TextLiteralRealisiertAussage ∧
  TextLiteralAnnahmeAussage ∧
  TextLiteralIdealAussage ∧
  TextLiteralEinheitAussage ∧
  TextLiteralImplAussage ∧
  TextLiteralErhaltungAussage ∧
  TextLiteralKernOrtAussage ∧
  TextLiteralRegelSicherAussage ∧
  TextLiteralRegelAntwortSicherAussage ∧
  TextLiteralKostenUndSpurAussage ∧
  TextLiteralErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
