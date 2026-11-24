module

public import Core.Ast.Tree

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

structure WrittenCarrierEffect where
  access : CarrierAccess
  carrier : Identifier
  slots : Bool

def Scope.effectCarrier (scope : Scope) (name : Identifier) : Option (Nat × Bool) :=
  match scope with
  | [] => none
  | binding :: outer =>
    if binding.name.val = name.val then
      match binding.type with
      | .carrierSchema _ _ _ exported => some (outer.length, exported)
      | _ => none
    else Scope.effectCarrier outer name

def WrittenCarrierEffect.resolve (scope : Scope) (publicUse : Bool) (written : WrittenCarrierEffect) :
    Option CarrierEffect := do
  let (position, exported) ← scope.effectCarrier written.carrier
  if publicUse && !exported then none else
    some ⟨position, written.carrier.val, written.access⟩

def effectGroupBinding (name : Identifier) (effects : List CarrierEffect) : Binding :=
  ⟨name, .effectGroupSchema effects, false, true⟩

def Scope.effectGroup (scope : Scope) (name : Identifier) : Option (List CarrierEffect) :=
  match scope.find? (fun binding => binding.name.val == name.val) with
  | some ⟨_, .effectGroupSchema effects, _, _⟩ => some effects
  | _ => none

structure EffectGroupDeclaration (before : Scope) where
  exported : Bool
  name : Identifier
  written : List WrittenCarrierEffect
  resolved : List CarrierEffect
  checked : written.mapM (WrittenCarrierEffect.resolve before exported) = some resolved

def EffectGroupDeclaration.binding (item : EffectGroupDeclaration before) : Binding :=
  effectGroupBinding item.name item.resolved

inductive EffectTerm where
  | carrier (effect : WrittenCarrierEffect)
  | group (name : Identifier)
  | pure

def EffectTerm.resolve (scope : Scope) (bound : List RawText) : EffectTerm → Option (List CarrierEffect)
  | .carrier effect =>
    if bound.contains effect.carrier.val then none else (effect.resolve scope false).map List.singleton
  | .group name => do
    if name.val = "pure".toList ∨ bound.contains name.val = true then none else
      let effects ← scope.effectGroup name
      if effects.any (fun effect => bound.contains effect.carrier) then none else some effects
  | .pure => some []

/-- Expansion happens in source order. A group member retains the declaration position
    resolved where the group was declared. The names of the parameters cannot capture it. -/
def expandEffects (scope : Scope) (bound : List RawText) (terms : List EffectTerm) :
    Option (List CarrierEffect) :=
  (terms.mapM (EffectTerm.resolve scope bound)).map List.flatten

structure EffectClause (scope : Scope) (parameters : List (Parameter scope)) where
  written : List EffectTerm
  expanded : List CarrierEffect
  checked : expandEffects scope (parameters.map (fun p => p.name.val)) written = some expanded

def declaredEffects : Option (EffectClause scope ps) → List CarrierEffect
  | none => []
  | some clause => clause.expanded

end Gabbro.Core.Ast
