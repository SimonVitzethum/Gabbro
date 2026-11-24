module

public import Core.Ast.Variant.Obligations
public import Core.Ast.Aggregate.Carrier.Option.Test

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

def OptionMatchArgs (ctx : OptionContext) :=
  {a : Surface.VariantMatchArgs ctx // ∃ count,
    a.name = [] ∧ a.labels = indexOptionLabels ∧ a.payloads = indexOptionPayloads count}

def optionMatchForm (ctx : OptionContext) : Quellform (.statement ctx.1 ctx.2) (OptionMatchArgs ctx) :=
  let matched := variantMatchForm ctx
  { produktion := ⟨fun a => matched.produktion.tree a.val,
                  fun a => matched.produktion.production a.val⟩
    befehl := fun a => matched.befehl a.val
    position := fun a => matched.position a.val }

def OptionMatchPayloadAussage : Prop :=
  ∀ count, ∀ value : Wert (indexOptionType count),
    let actual := variantCase (indexOptionPayloads count) value
    (∀ index : Wert (indexType count), value = .inl index → actual = (0, some ⟨indexType count, index⟩)) ∧
    (value = .inr (.inl PUnit.unit) → actual = (1, none))

def OptionMatchDerivationAussage : Prop :=
  ∀ ctx, Nonempty (OptionMatchArgs ctx) → (optionMatchForm ctx).produktion.Entry

def OptionMatchParseAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).ParseAussage

def OptionMatchElaboriertAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).ElaboriertAussage

def OptionMatchRealisiertAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).RealisiertAussage

def OptionMatchAnnahmeAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).AnnahmeAussage

def OptionMatchIdealAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).IdealAussage

def OptionMatchEinheitAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).EinheitAussage

def OptionMatchImplAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).ImplAussage

def OptionMatchErhaltungAussage : Prop :=
  ∀ ctx, (optionMatchForm ctx).ErhaltungsAussage

def OptionMatchRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := optionMatchForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def OptionMatchErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ ctx a, (optionMatchForm ctx).ErfuellbarAm platform start a

def OptionMatchProofPacket : Prop :=
  OptionMatchPayloadAussage ∧
  OptionMatchDerivationAussage ∧
  OptionMatchParseAussage ∧
  OptionMatchElaboriertAussage ∧
  OptionMatchRealisiertAussage ∧
  OptionMatchAnnahmeAussage ∧
  OptionMatchIdealAussage ∧
  OptionMatchEinheitAussage ∧
  OptionMatchImplAussage ∧
  OptionMatchErhaltungAussage ∧
  OptionMatchRegelSicherAussage ∧
  OptionMatchErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
