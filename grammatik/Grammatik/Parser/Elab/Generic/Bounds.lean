module
public import Grammatik.Parser.Spec.Items
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- A bound names a unary spec; tuples remain explicit spec applications, not partial bounds. -/
def checkBounds (source : List SItemTief) (bounds : List String) : Except String Unit := do
  for name in bounds do
    let some group := (Spec.groups source).find? (fun group => strEq group.name name)
      | throw ("generic.bound.unknown: " ++ name)
    if group.types.length != 1 then throw ("generic.bound.arity: " ++ name)

/-- All bounds are required, including those unused by the body. Alias normalization and
    instance identity are exactly the unified spec resolver's, with no second registry. -/
def checkTypeBounds (source : List SItemTief) (ty : STyp) (bounds : List String) :
    Except String Unit := do
  checkBounds source bounds
  for name in bounds do
    let implementations := (Spec.instances source).filter fun implementation =>
      strEq implementation.group name && beqSTypList
        (implementation.types.map (Spec.canonicalType source 128)) [Spec.canonicalType source 128 ty]
    match implementations with
    | [_] => pure ()
    | [] => throw ("generic.bound.implementation.missing: " ++ name)
    | _ => throw ("generic.bound.implementation.ambiguous: " ++ name)

/-- Type parameters remain abstract throughout the pre-instantiation body check. -/
def typeParameters (sig : FnSig) : List (String × List String) := sig.generics.filterMap fun
  | .type name bounds => some (name, bounds)
  | _ => none

mutual
def mentionsParameter (parameters : List (String × List String)) : STyp → Bool
  | .atom name => parameters.any (fun p => strEq p.1 name)
  | .path [name] => parameters.any (fun p => strEq p.1 name)
  | .tuple types => mentionsParameterList parameters types
  | .ptr _ _ ty | .range ty _ _ _ | .array ty _ | .wrap ty | .embed ty _ _ =>
    mentionsParameter parameters ty
  | .entry _ none => false
  | .entry _ (some result) => mentionsParameter parameters result
  | _ => false

/-- The parameter check over the components of a tuple. -/
def mentionsParameterList (parameters : List (String × List String)) : List STyp → Bool
  | [] => false
  | ty :: rest => mentionsParameter parameters ty || mentionsParameterList parameters rest
end

/-- An abstract type may use only a written bound. Concrete types are checked at instantiation. -/
def checkAbstractBound (parameters : List (String × List String)) (ty : STyp)
    (bound : String) : Except String Unit := do
  if mentionsParameter parameters ty then
    let name ← match ty with
      | .atom name | .path [name] => pure name
      | _ => throw ("generic.parametricity.bound: " ++ bound)
    let some (_, bounds) := parameters.find? (fun p => strEq p.1 name)
      | throw ("generic.parametricity.bound: " ++ bound)
    if !bounds.any (strEq bound) then throw ("generic.parametricity.bound: " ++ bound)

end Gabbro.Grammatik.Parser.Generic
