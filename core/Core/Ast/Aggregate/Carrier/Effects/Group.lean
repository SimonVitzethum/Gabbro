module

public import Core.Ast.Semantik.ProgramForms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

def effectGroupForm (scope : Scope) : Quellform (.declaration scope) (EffectGroupDeclaration scope) where
  produktion :=
    { tree := fun item => ⟨_, .effectGroup item⟩
      production := fun item tokens =>
        ∃ input, tokens = item.header.map PrintedToken.value ++ input ∧
          EffectListReads CarrierEffectReads input item.written [semicolon] }
  befehl := fun item => .definiereEffektgruppe item.resolved
  position := fun _ => 0

def EffectGroupInversionAussage : Prop :=
  ∀ {scope input tree rest} (head : EffectGroupDeclaration scope),
    DeclReads scope (head.header.map PrintedToken.value ++ input) tree rest →
    ∃ (item : EffectGroupDeclaration scope), item.name = head.name ∧ item.exported = head.exported ∧
      EffectListReads CarrierEffectReads input item.written (semicolon :: rest) ∧
      tree = (effectGroupForm scope).produktion.tree item

def EffectGroupDerivationAussage : Prop :=
  ∀ scope, (effectGroupForm scope).produktion.Entry

def EffectGroupScopeAussage : Prop :=
  ∀ (scope : Scope) (item : EffectGroupDeclaration scope),
    (item.binding :: scope).effectGroup item.name = some item.resolved ∧
      ¬ item.binding.type.valueBinding ∧
    ∀ name : Identifier, name.val ≠ item.name.val →
      (item.binding :: scope).effectGroup name = scope.effectGroup name

def EffectGroupExpansionAussage : Prop :=
  ∀ scope bound terms expanded,
    expandEffects scope bound terms = some expanded →
    ∃ parts : List (List CarrierEffect), parts.length = terms.length ∧
      (∀ i (term : EffectTerm) (part : List CarrierEffect),
        terms[i]? = some term → parts[i]? = some part → term.resolve scope bound = some part) ∧
      expanded = parts.flatten

def EffectGroupVisibilityAussage : Prop :=
  ∀ scope (item : EffectGroupDeclaration scope), item.exported = true →
    ∀ effect ∈ item.written, ∃ position, scope.effectCarrier effect.carrier = some (position, true)

def EffectGroupCaptureAussage : Prop :=
  ∀ scope bound (name : Identifier) effects,
    scope.effectGroup name = some effects →
    (bound.contains name.val = true ∨ ∃ effect ∈ effects, bound.contains effect.carrier = true) →
    (EffectTerm.group name).resolve scope bound = none

def EffectGroupSignatureAussage : Prop :=
  ∀ scope (a : Surface.FunctionArgs scope) frame,
    let out := ((functionForm scope).befehl a).auswerten frame
    ∃ registered, out.funktionen = registered :: frame.funktionen ∧
      registered.effects = declaredEffects a.effects ∧
      ∀ site ∈ registered.ruft, site.effects = registered.effects

def EffectGroupCallAussage : Prop :=
  ∀ (site : Rufstelle) functions target,
    Funktion.finde functions site.name = some target →
    site.passt functions = true → ∀ effect ∈ target.effects, effect ∈ site.effects

def EffectGroupBindingAussage : Prop :=
  ∀ scope (item : EffectGroupDeclaration scope) frame,
    let next := ((effectGroupForm scope).befehl item).auswerten frame
    let schema : Dynamisch := ⟨.effectGroupSchema item.resolved, PUnit.unit⟩
    schema.1 = item.binding.type ∧ next.lokale = some schema :: frame.lokale ∧
      next.globale = some schema :: frame.globale ∧ next.pc = frame.pc + 1 ∧ next.temp = frame.temp

def EffectGroupParseAussage : Prop :=
  ∀ scope, (effectGroupForm scope).ParseAussage

def EffectGroupElaboriertAussage : Prop :=
  ∀ scope, (effectGroupForm scope).ElaboriertAussage

def EffectGroupRealisiertAussage : Prop :=
  ∀ scope, (effectGroupForm scope).RealisiertAussage

def EffectGroupAnnahmeAussage : Prop :=
  ∀ scope, (effectGroupForm scope).AnnahmeAussage

def EffectGroupIdealAussage : Prop :=
  ∀ scope, (effectGroupForm scope).IdealAussage

def EffectGroupEinheitAussage : Prop :=
  ∀ scope, (effectGroupForm scope).EinheitAussage

def EffectGroupImplAussage : Prop :=
  ∀ scope, (effectGroupForm scope).ImplAussage

def EffectGroupErhaltungAussage : Prop :=
  ∀ scope, (effectGroupForm scope).ErhaltungsAussage

def EffectGroupRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := effectGroupForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def EffectGroupErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ (scope : Scope) (item : EffectGroupDeclaration scope),
    item.resolved ≠ [] ∧ (effectGroupForm scope).ErfuellbarAm platform start item

/-- A group term is present in a parsed signature and expands at its reachable registration. -/
def EffectGroupUseErfuellbarAussage : Prop :=
  ∀ platform start,
    ∃ (carrier : TableDeclaration []) (group : EffectGroupDeclaration [carrier.binding])
      (a : Surface.FunctionArgs [group.binding, carrier.binding]) (text : RawText) (s : Zustand),
      let tree : Ast.Unit := ⟨_, .step (.table carrier) (.step (.effectGroup group) (.step a.declaration .done))⟩
      let E := elaborieren platform tree
      let b := (functionForm [group.binding, carrier.binding]).befehl a
      let after := b.auswerten (s.lokal eintritt)
      group.resolved ≠ [] ∧
      (∃ clause, a.effects = some clause ∧ clause.written = [.group group.name]) ∧
      Ast.Parse text tree ∧ Elaboriert platform tree E ∧
      E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s eintritt = some b ∧
      E.system.ISchritt eintritt s () [plan] (b.nach eintritt s) ∧
      E.system.ImplSchritt eintritt s () [plan] (b.nach eintritt s) ∧
      (∃ signature, after.funktionen.head? = some signature ∧ signature.effects = group.resolved)

def EffectGroupProofPacket : Prop :=
  EffectGroupInversionAussage ∧
  EffectGroupDerivationAussage ∧
  EffectGroupScopeAussage ∧
  EffectGroupExpansionAussage ∧
  EffectGroupVisibilityAussage ∧
  EffectGroupCaptureAussage ∧
  EffectGroupSignatureAussage ∧
  EffectGroupCallAussage ∧
  EffectGroupBindingAussage ∧
  EffectGroupParseAussage ∧
  EffectGroupElaboriertAussage ∧
  EffectGroupRealisiertAussage ∧
  EffectGroupAnnahmeAussage ∧
  EffectGroupIdealAussage ∧
  EffectGroupEinheitAussage ∧
  EffectGroupImplAussage ∧
  EffectGroupErhaltungAussage ∧
  EffectGroupRegelSicherAussage ∧
  EffectGroupErfuellbarAmAussage ∧
  EffectGroupUseErfuellbarAussage

end Gabbro.Core.Ast.Semantik
