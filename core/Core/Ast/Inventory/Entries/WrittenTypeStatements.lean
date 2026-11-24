module

public import Core.Ast.Aggregate.Types
public import Core.Ast.LowLevel.Proofs.RegionUnit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text (PrintedToken)

def boolTypeUse : WrittenType → Prop
  | .bool => True
  | _ => False

def integerTypeUse : WrittenType → Prop
  | .integer .. => True
  | _ => False

/-- A written scalar type takes effect at the binding instruction of a typed local. -/
def LocalTypeUseAussage (select : WrittenType → Prop) : Prop :=
  (∀ ctx, (typeUseForm ctx select).ParseAussage) ∧
  (∀ ctx, (typeUseForm ctx select).ElaboriertAussage) ∧
  (∀ ctx, (typeUseForm ctx select).RealisiertAussage) ∧
  (∀ ctx, (typeUseForm ctx select).AnnahmeAussage) ∧
  (∀ ctx, (typeUseForm ctx select).IdealAussage) ∧
  (∀ ctx, (typeUseForm ctx select).EinheitAussage) ∧
  (∀ ctx, (typeUseForm ctx select).ImplAussage) ∧
  (∀ ctx, (typeUseForm ctx select).ErhaltungsAussage)

def BoolTypeErfuellbarAussage : Prop :=
  ∀ platform start, ∃ args, (typeUseForm ([], none) boolTypeUse).ErfuellbarAm platform start args

/-- Each signedness and interval spelling has an actual reachable typed binding. -/
def IntegerTypeErfuellbarAussage : Prop :=
  ∀ platform start (signed bounded : Bool),
    ∃ (width : Nat) (interval : Option (Int × Int))
      (args : {a : Surface.MutableLocalArgs [] none // integerTypeUse a.written}),
      interval.isSome = bounded ∧ args.val.written = .integer signed width interval ∧
      (typeUseForm ([], none) integerTypeUse).ErfuellbarAm platform start args

def BoolTypeRegistryAussage : Prop :=
  (∀ scope rest, TypeReads scope (WrittenType.bool.printPieces.map PrintedToken.value ++ rest) .bool rest) ∧
  LocalTypeUseAussage boolTypeUse ∧ BoolTypeErfuellbarAussage

def IntegerTypeRegistryAussage : Prop :=
  (∀ scope signed width interval rest, (WrittenType.integer signed width interval).valid scope →
    (∀ more, rest ≠ keyword "in" :: more) →
    TypeReads scope ((WrittenType.integer signed width interval).printPieces.map PrintedToken.value ++ rest)
      (.integer signed width interval) rest) ∧
  LocalTypeUseAussage integerTypeUse ∧ IntegerTypeErfuellbarAussage

/-- The written region type is realized in the owned parameter of the checked region unit. -/
def OwnedRegionTypeRegistryAussage : Prop :=
  (∀ scope rest, TypeReads scope
    (WrittenType.ownedRegion.printPieces.map PrintedToken.value ++ rest) .ownedRegion rest) ∧
  RegionBindUnitAussage

end Gabbro.Core.Ast.Semantik
