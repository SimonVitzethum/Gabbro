module

public import Core.Ast.Aggregate.Carrier.Option.Construct

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

structure OptionTestArgs (scope : Scope) where
  count : Nat
  ref : Local scope (indexOptionType count)
  visible : ref.visible
  ordinary : ordinaryLocal ref.binding.name

def optionTestForm (scope : Scope) : Quellform (.expression scope) (OptionTestArgs scope) where
  produktion :=
    { tree := fun a => (Expr.optionIsSome a.ref a.visible a.ordinary).typed
      production := fun a tokens =>
        let bare := [.word a.ref.binding.name.val, dot, .word indexIsSomeName.val, openParen, closeParen]
        tokens = bare ∨ tokens = openParen :: bare ++ [closeParen] }
  befehl := fun a => .optionIstBesetzt 0 a.count
  position := fun _ => 1

def OptionTestInversionAussage : Prop :=
  ∀ {scope count minimum input type} {ref : Local scope (indexOptionType count)}
    {visible : ref.visible} {ordinary : ordinaryLocal ref.binding.name}
    {tree : Expr scope type} {rest},
    minimum ≤ Infix.projection.precedence →
    ExprTail scope minimum (.variable ref visible ordinary)
      (dot :: .word indexIsSomeName.val :: openParen :: closeParen :: input) tree rest →
    ExprTail scope minimum (.optionIsSome ref visible ordinary) input tree rest

def OptionTestCasesAussage : Prop :=
  ∀ count slot (value : Wert (indexOptionType count)) frame,
    frame.temp slot = some ⟨indexOptionType count, value⟩ →
    let result := ((Befehl.optionIstBesetzt slot count).auswerten frame).temp slot
    (result = some ⟨.bool, true⟩ ↔ ∃ (index : Wert (indexType count)), value = .inl index) ∧
    (result = some ⟨.bool, false⟩ ↔ value = .inr (.inl PUnit.unit))

def OptionTestDerivationAussage : Prop :=
  ∀ scope, (optionTestForm scope).produktion.Entry

def OptionTestParseAussage : Prop :=
  ∀ scope, (optionTestForm scope).ParseAussage

def OptionTestElaboriertAussage : Prop :=
  ∀ scope, (optionTestForm scope).ElaboriertAussage

def OptionTestRealisiertAussage : Prop :=
  ∀ scope, (optionTestForm scope).RealisiertAussage

def OptionTestAnnahmeAussage : Prop :=
  ∀ scope, (optionTestForm scope).AnnahmeAussage

def OptionTestIdealAussage : Prop :=
  ∀ scope, (optionTestForm scope).IdealAussage

def OptionTestEinheitAussage : Prop :=
  ∀ scope, (optionTestForm scope).EinheitAussage

def OptionTestImplAussage : Prop :=
  ∀ scope, (optionTestForm scope).ImplAussage

def OptionTestErhaltungAussage : Prop :=
  ∀ scope, (optionTestForm scope).ErhaltungsAussage

def OptionTestRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := optionTestForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def OptionTestErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ scope (a : OptionTestArgs scope),
    (optionTestForm scope).ErfuellbarAm platform start a

/-- An enclosing block can initialize a live option before testing it. -/
def OptionTestInitializedAussage : Prop :=
  ∀ platform start, ∃ scope (tree : BracedBlock none scope) (text : RawText) (s : Zustand),
    let E := elaborieren (category := .block scope none) platform tree
    let b := Befehl.optionIstBesetzt 0 0
    let absent : Wert (indexOptionType 0) := .inr (.inl PUnit.unit)
    Ast.Parse (category := .block scope none) text tree ∧
    E.system.IErreichbar (I.start E start).2 s ∧
    E.system.kopf s eintritt = some b ∧ (s.lokal eintritt).temp 0 = some ⟨indexOptionType 0, absent⟩ ∧
    E.system.ISchritt eintritt s () [plan] (b.nach eintritt s) ∧
    E.system.ImplSchritt eintritt s () [plan] (b.nach eintritt s)

def OptionTestProofPacket : Prop :=
  OptionTestInversionAussage ∧
  OptionTestCasesAussage ∧
  OptionTestDerivationAussage ∧
  OptionTestParseAussage ∧
  OptionTestElaboriertAussage ∧
  OptionTestRealisiertAussage ∧
  OptionTestAnnahmeAussage ∧
  OptionTestIdealAussage ∧
  OptionTestEinheitAussage ∧
  OptionTestImplAussage ∧
  OptionTestErhaltungAussage ∧
  OptionTestRegelSicherAussage ∧
  OptionTestErfuellbarAmAussage ∧
  OptionTestInitializedAussage

end Gabbro.Core.Ast.Semantik
