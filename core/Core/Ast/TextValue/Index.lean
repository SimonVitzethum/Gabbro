module

public import Core.Ast.TextValue.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

open Gabbro.Core.Text

def TextIndexDerivationAussage : Prop :=
  ∀ scope, (Surface.textIndex scope).Entry

def TextIndexSuffixAussage : Prop :=
  ∀ {scope capacity type minimum first rest} {base : Expr scope (.text capacity)} {tree : Expr scope type},
    minimum ≤ Infix.index.precedence →
    ExprTail scope minimum base (openBracket :: first) tree rest → rest <:+ first

def TextIndexBytesAussage : Prop :=
  ∀ capacity (text : TextValue capacity) (index : Ganzzahl) (frame : Rahmen),
    frame.temp 0 = some ⟨.text capacity, text⟩ → frame.zahl 1 = some index →
    let b := Befehl.textIndex 0 capacity
    let offset := index.zahl.wert
    let next := b.auswerten frame
    b.guard frame = some ⟨.index, (if offset < 0 then text.bytes.size else offset.toNat, text.bytes.size)⟩ ∧
      (∀ byte, 0 ≤ offset → text.bytes[offset.toNat]? = some byte →
        next.temp 0 = some ⟨.int 0 255, byteValue byte⟩ ∧ next.pc = frame.pc + 1) ∧
      (offset < 0 ∨ (text.bytes.size : Int) ≤ offset → next.stopp = some .ungueltigerWert)

def TextIndexParseAussage : Prop :=
  ∀ scope, (textIndexForm scope).ParseAussage

def TextIndexElaboriertAussage : Prop :=
  ∀ scope, (textIndexForm scope).ElaboriertAussage

def TextIndexRealisiertAussage : Prop :=
  ∀ scope, (textIndexForm scope).RealisiertAussage

def TextIndexAnnahmeAussage : Prop :=
  ∀ scope, (textIndexForm scope).AnnahmeAussage

def TextIndexIdealAussage : Prop :=
  ∀ scope, (textIndexForm scope).IdealAussage

def TextIndexEinheitAussage : Prop :=
  ∀ scope, (textIndexForm scope).EinheitAussage

def TextIndexImplAussage : Prop :=
  ∀ scope, (textIndexForm scope).ImplAussage

def TextIndexErhaltungAussage : Prop :=
  ∀ scope, (textIndexForm scope).ErhaltungsAussage

def TextIndexKernOrtAussage : Prop :=
  ∀ scope, (textIndexForm scope).RegelAmOrt

def TextIndexRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textIndexForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TextIndexRegelAntwortSicherAussage : Prop :=
  ∀ scope platform args,
    let form := textIndexForm scope
    RegelAntwortSicher (form.fragment args) platform (form.befehl args)

def TextIndexKostenUndSpurAussage : Prop :=
  ∀ scope platform args,
    let form := textIndexForm scope
    TextInstructionCost (form.fragment args) platform (form.befehl args)

def TextIndexErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (textIndexForm []).TextErfuellbar platform start args

def TextIndexProofPacket : Prop :=
  TextIndexDerivationAussage ∧
  TextIndexSuffixAussage ∧
  TextIndexBytesAussage ∧
  TextIndexParseAussage ∧
  TextIndexElaboriertAussage ∧
  TextIndexRealisiertAussage ∧
  TextIndexAnnahmeAussage ∧
  TextIndexIdealAussage ∧
  TextIndexEinheitAussage ∧
  TextIndexImplAussage ∧
  TextIndexErhaltungAussage ∧
  TextIndexKernOrtAussage ∧
  TextIndexRegelSicherAussage ∧
  TextIndexRegelAntwortSicherAussage ∧
  TextIndexKostenUndSpurAussage ∧
  TextIndexErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
