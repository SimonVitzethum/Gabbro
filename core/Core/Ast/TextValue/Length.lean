module

public import Core.Ast.TextValue.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

open Gabbro.Core.Text

def TextLengthInversionAussage : Prop :=
  ∀ {scope type input rest} {tree : Expr scope type},
    AtomReads scope (lenofKeyword :: openParen :: input) tree rest →
    ∃ (capacity : Nat) (base : Expr scope (.text capacity)),
      ExprReads scope 0 input base (closeParen :: rest) ∧
        tree.typed = (Expr.textLength base).typed

def TextLengthDerivationAussage : Prop :=
  ∀ scope, (Surface.textLength scope).Entry

def TextLengthBytesAussage : Prop :=
  ∀ capacity (text : TextValue capacity) (frame : Rahmen),
    frame.temp 0 = some ⟨.text capacity, text⟩ →
    let next := (Befehl.textLength 0 capacity).auswerten frame
    next.temp 0 = some ⟨.int 0 capacity, text.lengthValue⟩ ∧
      text.lengthValue.wert = (text.bytes.size : Int) ∧ next.pc = frame.pc + 1

def TextLengthParseAussage : Prop :=
  ∀ scope, (textLengthForm scope).ParseAussage

def TextLengthElaboriertAussage : Prop :=
  ∀ scope, (textLengthForm scope).ElaboriertAussage

def TextLengthRealisiertAussage : Prop :=
  ∀ scope, (textLengthForm scope).RealisiertAussage

def TextLengthAnnahmeAussage : Prop :=
  ∀ scope, (textLengthForm scope).AnnahmeAussage

def TextLengthIdealAussage : Prop :=
  ∀ scope, (textLengthForm scope).IdealAussage

def TextLengthEinheitAussage : Prop :=
  ∀ scope, (textLengthForm scope).EinheitAussage

def TextLengthImplAussage : Prop :=
  ∀ scope, (textLengthForm scope).ImplAussage

def TextLengthErhaltungAussage : Prop :=
  ∀ scope, (textLengthForm scope).ErhaltungsAussage

def TextLengthKernOrtAussage : Prop :=
  ∀ scope, (textLengthForm scope).RegelAmOrt

def TextLengthRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textLengthForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TextLengthRegelAntwortSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textLengthForm scope
    RegelAntwortSicher (form.fragment args) platform (form.befehl args)

def TextLengthKostenUndSpurAussage : Prop :=
  ∀ scope platform args,
    let form := textLengthForm scope
    TextInstructionCost (form.fragment args) platform (form.befehl args)

def TextLengthErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (textLengthForm []).TextErfuellbar platform start args

def TextLengthProofPacket : Prop :=
  TextLengthInversionAussage ∧
  TextLengthDerivationAussage ∧
  TextLengthBytesAussage ∧
  TextLengthParseAussage ∧
  TextLengthElaboriertAussage ∧
  TextLengthRealisiertAussage ∧
  TextLengthAnnahmeAussage ∧
  TextLengthIdealAussage ∧
  TextLengthEinheitAussage ∧
  TextLengthImplAussage ∧
  TextLengthErhaltungAussage ∧
  TextLengthKernOrtAussage ∧
  TextLengthRegelSicherAussage ∧
  TextLengthRegelAntwortSicherAussage ∧
  TextLengthKostenUndSpurAussage ∧
  TextLengthErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
