module

public import Core.Ast.TextValue.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

open Gabbro.Core.Text

def SubstringDerivationAussage : Prop :=
  ∀ scope, (Surface.substring scope).Entry

def SubstringSuffixAussage : Prop :=
  ∀ {scope capacity type minimum first rest} {base : Expr scope (.text capacity)} {tree : Expr scope type},
    minimum ≤ Infix.index.precedence →
    ExprTail scope minimum base (openBracket :: first) tree rest → rest <:+ first

def SubstringBytesAussage : Prop :=
  ∀ capacity (text : TextValue capacity) (first last : Ganzzahl) (frame : Rahmen),
    frame.temp 0 = some ⟨.text capacity, text⟩ → frame.zahl 1 = some first → frame.zahl 2 = some last →
    let b := Befehl.substring 0 capacity
    let i := first.zahl.wert
    let j := last.zahl.wert
    let next := b.auswerten frame
    b.guard frame = some ⟨.teilfolge, (i, j, text.bytes.size)⟩ ∧
      (Annahme.waechterBedarf .teilfolge (i, j, text.bytes.size) →
        let out := text.slice i.toNat j.toNat
        next.temp 0 = some ⟨.text capacity, out⟩ ∧ next.pc = frame.pc + 1 ∧
          out.bytes.size = j.toNat - i.toNat ∧
          ∀ k < out.bytes.size, out.bytes[k]? = text.bytes[i.toNat + k]?) ∧
      (¬ Annahme.waechterBedarf .teilfolge (i, j, text.bytes.size) → next.stopp = some .ungueltigerWert)

def SubstringParseAussage : Prop :=
  ∀ scope, (substringForm scope).ParseAussage

def SubstringElaboriertAussage : Prop :=
  ∀ scope, (substringForm scope).ElaboriertAussage

def SubstringRealisiertAussage : Prop :=
  ∀ scope, (substringForm scope).RealisiertAussage

def SubstringAnnahmeAussage : Prop :=
  ∀ scope, (substringForm scope).AnnahmeAussage

def SubstringIdealAussage : Prop :=
  ∀ scope, (substringForm scope).IdealAussage

def SubstringEinheitAussage : Prop :=
  ∀ scope, (substringForm scope).EinheitAussage

def SubstringImplAussage : Prop :=
  ∀ scope, (substringForm scope).ImplAussage

def SubstringErhaltungAussage : Prop :=
  ∀ scope, (substringForm scope).ErhaltungsAussage

def SubstringKernOrtAussage : Prop :=
  ∀ scope, (substringForm scope).RegelAmOrt

def SubstringRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := substringForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def SubstringRegelAntwortSicherAussage : Prop :=
  ∀ scope platform args,
    let form := substringForm scope
    RegelAntwortSicher (form.fragment args) platform (form.befehl args)

def SubstringKostenUndSpurAussage : Prop :=
  ∀ scope platform args,
    let form := substringForm scope
    TextInstructionCost (form.fragment args) platform (form.befehl args)

def SubstringErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (substringForm []).TextErfuellbar platform start args

def SubstringProofPacket : Prop :=
  SubstringDerivationAussage ∧
  SubstringSuffixAussage ∧
  SubstringBytesAussage ∧
  SubstringParseAussage ∧
  SubstringElaboriertAussage ∧
  SubstringRealisiertAussage ∧
  SubstringAnnahmeAussage ∧
  SubstringIdealAussage ∧
  SubstringEinheitAussage ∧
  SubstringImplAussage ∧
  SubstringErhaltungAussage ∧
  SubstringKernOrtAussage ∧
  SubstringRegelSicherAussage ∧
  SubstringRegelAntwortSicherAussage ∧
  SubstringKostenUndSpurAussage ∧
  SubstringErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
