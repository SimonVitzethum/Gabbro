module

public import Core.Ast.TextValue.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

open Gabbro.Core.Text

def TextConcatInversionAussage : Prop :=
  ∀ {scope a minimum input type} {left : Expr scope (.text a)} {tree : Expr scope type} {rest},
    minimum ≤ Arith.add.precedence →
    ExprTail scope minimum left (Arith.add.token :: input) tree rest →
    ∃ (b : Nat) (right : Expr scope (.text b)) (suffix : List Token),
      ExprReads scope (Arith.add.precedence + 1) input right suffix ∧
      ExprTail scope minimum (.textConcat left right) suffix tree rest

def TextConcatDerivationAussage : Prop :=
  ∀ scope, (Surface.textConcat scope).Entry

def TextConcatBytesAussage : Prop :=
  ∀ a b (left : TextValue a) (right : TextValue b) (frame : Rahmen),
    frame.temp 0 = some ⟨.text a, left⟩ → frame.temp 1 = some ⟨.text b, right⟩ →
    let out := left.concat right
    let next := (Befehl.textConcat 0 a b).auswerten frame
    next.temp 0 = some ⟨.text (a + b), out⟩ ∧
      out.bytes = left.bytes ++ right.bytes ∧ out.bytes.size ≤ a + b ∧ next.pc = frame.pc + 1

def TextConcatParseAussage : Prop :=
  ∀ scope, (textConcatForm scope).ParseAussage

def TextConcatElaboriertAussage : Prop :=
  ∀ scope, (textConcatForm scope).ElaboriertAussage

def TextConcatRealisiertAussage : Prop :=
  ∀ scope, (textConcatForm scope).RealisiertAussage

def TextConcatAnnahmeAussage : Prop :=
  ∀ scope, (textConcatForm scope).AnnahmeAussage

def TextConcatIdealAussage : Prop :=
  ∀ scope, (textConcatForm scope).IdealAussage

def TextConcatEinheitAussage : Prop :=
  ∀ scope, (textConcatForm scope).EinheitAussage

def TextConcatImplAussage : Prop :=
  ∀ scope, (textConcatForm scope).ImplAussage

def TextConcatErhaltungAussage : Prop :=
  ∀ scope, (textConcatForm scope).ErhaltungsAussage

def TextConcatKernOrtAussage : Prop :=
  ∀ scope, (textConcatForm scope).RegelAmOrt

def TextConcatRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textConcatForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TextConcatRegelAntwortSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textConcatForm scope
    RegelAntwortSicher (form.fragment args) platform (form.befehl args)

def TextConcatKostenUndSpurAussage : Prop :=
  ∀ scope platform args,
    let form := textConcatForm scope
    TextInstructionCost (form.fragment args) platform (form.befehl args)

def TextConcatErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (textConcatForm []).TextErfuellbar platform start args

def TextConcatProofPacket : Prop :=
  TextConcatParseAussage ∧
  TextConcatElaboriertAussage ∧
  TextConcatRealisiertAussage ∧
  TextConcatAnnahmeAussage ∧
  TextConcatIdealAussage ∧
  TextConcatEinheitAussage ∧
  TextConcatImplAussage ∧
  TextConcatErhaltungAussage ∧
  TextConcatKernOrtAussage ∧
  TextConcatRegelSicherAussage ∧
  TextConcatRegelAntwortSicherAussage ∧
  TextConcatKostenUndSpurAussage ∧
  TextConcatErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
