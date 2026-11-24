module

public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

abbrev OptionContext := Scope × Option (Ty .value)

structure OptionLetArgs (ctx : OptionContext) where
  mutable : Bool
  name : Identifier
  ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name
  carrier : Identifier
  count : Nat
  resolved : ctx.1.carrierCount carrier = some count
  value : OptionInitializer ctx.1 count

structure OptionReturnArgs (ctx : OptionContext) where
  count : Nat
  declared : ctx.2 = some (indexOptionType count)
  value : OptionInitializer ctx.1 count

def optionLetForm (ctx : OptionContext) : Quellform (.statement ctx.1 ctx.2) (OptionLetArgs ctx) where
  produktion :=
    { tree := fun a => ⟨_, .letOption a.mutable a.name a.ordinary a.carrier a.resolved a.value⟩
      production := fun a tokens => ∃ input rhs, tokens = optionLetHead a.mutable a.name ++ input ∧
        TypeReads ctx.1 input (.indexOption a.carrier a.count) (assignment :: rhs) ∧
        OptionInitializerReads ctx.1 a.count rhs a.value [semicolon] }
  befehl := fun a => optionInstruction 0 a.value
  position := fun a => (optionOperand 0 a.value).code.length

def optionReturnForm (ctx : OptionContext) :
    Quellform (.statement ctx.1 ctx.2) (OptionReturnArgs ctx) where
  produktion :=
    { tree := fun a => ⟨_, .retOption a.declared a.value⟩
      production := fun a tokens => ∃ input, tokens = returnKeyword :: input ∧
        OptionInitializerReads ctx.1 a.count input a.value [semicolon] }
  befehl := fun a => optionInstruction 0 a.value
  position := fun a => (optionOperand 0 a.value).code.length

def OptionInitializerInversionAussage : Prop :=
  (∀ {scope count input value rest},
    OptionInitializerReads scope count (.word indexSomeName.val :: input) value rest →
    ∃ lo hi (operand : Expr scope (.int lo hi)) fits rhs,
      input = openParen :: rhs ∧ ExprReads scope 0 rhs operand (closeParen :: rest) ∧
      value = .present operand fits) ∧
  (∀ {scope count input value rest},
    OptionInitializerReads scope count (.word indexNoneName.val :: input) value rest →
    input = rest ∧ value = .absent)

def OptionInitializerPrintAussage : Prop :=
  ∀ scope count (value : OptionInitializer scope count) rest,
    OptionInitializerReads scope count (value.printPieces.map PrintedToken.value ++ rest) value rest

def OptionAbsentAussage : Prop :=
  ∀ (scope : Scope) count slot frame,
    let command := optionInstruction slot (OptionInitializer.absent (scope := scope) (count := count))
    let expected : Wert (indexOptionType count) := .inr (.inl PUnit.unit)
    (command.auswerten frame).temp slot = some ⟨indexOptionType count, expected⟩

def OptionPresentAussage : Prop :=
  ∀ scope count lo hi slot (operand : Expr scope (.int lo hi)) fits frame (value : Wert (.int lo hi)),
    frame.temp slot = some ⟨.int lo hi, value⟩ →
    let command := optionInstruction slot (OptionInitializer.present (count := count) operand fits)
    let payload := Wert.widen (.int lo hi) (indexType count) fits value
    let expected : Wert (indexOptionType count) := .inl payload
    (command.auswerten frame).temp slot = some ⟨indexOptionType count, expected⟩

def OptionLetDerivationAussage : Prop :=
  ∀ ctx, (optionLetForm ctx).produktion.Entry

def OptionReturnDerivationAussage : Prop :=
  ∀ ctx, (optionReturnForm ctx).produktion.Entry

def OptionConstructorParseAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).ParseAussage) ∧
  (∀ ctx, (optionReturnForm ctx).ParseAussage)

def OptionConstructorElaboriertAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).ElaboriertAussage) ∧
  (∀ ctx, (optionReturnForm ctx).ElaboriertAussage)

def OptionConstructorRealisiertAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).RealisiertAussage) ∧
  (∀ ctx, (optionReturnForm ctx).RealisiertAussage)

def OptionConstructorAnnahmeAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).AnnahmeAussage) ∧
  (∀ ctx, (optionReturnForm ctx).AnnahmeAussage)

def OptionConstructorIdealAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).IdealAussage) ∧
  (∀ ctx, (optionReturnForm ctx).IdealAussage)

def OptionConstructorEinheitAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).EinheitAussage) ∧
  (∀ ctx, (optionReturnForm ctx).EinheitAussage)

def OptionConstructorImplAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).ImplAussage) ∧
  (∀ ctx, (optionReturnForm ctx).ImplAussage)

def OptionConstructorErhaltungAussage : Prop :=
  (∀ ctx, (optionLetForm ctx).ErhaltungsAussage) ∧
  (∀ ctx, (optionReturnForm ctx).ErhaltungsAussage)

def OptionConstructorRegelSicherAussage : Prop :=
  (∀ ctx platform args,
    let form := optionLetForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)) ∧
  (∀ ctx platform args,
    let form := optionReturnForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args))

def OptionLetErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ ctx (a : OptionLetArgs ctx),
    a.count = 0 ∧ a.value = .absent ∧ (optionLetForm ctx).ErfuellbarAm platform start a

def OptionReturnErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ ctx (a : OptionReturnArgs ctx),
    (∃ lo hi (operand : Expr ctx.1 (.int lo hi)) fits, a.value = .present operand fits) ∧
    (optionReturnForm ctx).ErfuellbarAm platform start a

def OptionConstructorProofPacket : Prop :=
  OptionInitializerInversionAussage ∧
  OptionInitializerPrintAussage ∧
  OptionAbsentAussage ∧
  OptionPresentAussage ∧
  OptionLetDerivationAussage ∧
  OptionReturnDerivationAussage ∧
  OptionConstructorParseAussage ∧
  OptionConstructorElaboriertAussage ∧
  OptionConstructorRealisiertAussage ∧
  OptionConstructorAnnahmeAussage ∧
  OptionConstructorIdealAussage ∧
  OptionConstructorEinheitAussage ∧
  OptionConstructorImplAussage ∧
  OptionConstructorErhaltungAussage ∧
  OptionConstructorRegelSicherAussage ∧
  OptionLetErfuellbarAmAussage ∧
  OptionReturnErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
