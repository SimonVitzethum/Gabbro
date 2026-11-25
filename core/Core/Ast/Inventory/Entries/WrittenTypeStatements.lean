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

/-- The universal type-use selector: every written type takes effect at the
    binding instruction of a typed local. -/
def anyTypeUse : WrittenType → Prop := fun _ => True

/-- Every written type takes effect at the binding instruction of a typed local.
    The selector is the model definition `anyTypeUse`, so the obligations below
    quantify over real uses and never over an empty subtype. -/
def LocalTypeUseAussage : Prop :=
  (∃ w, anyTypeUse w) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).ParseAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).ElaboriertAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).RealisiertAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).AnnahmeAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).IdealAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).EinheitAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).ImplAussage) ∧
  (∀ ctx, (typeUseForm ctx anyTypeUse).ErhaltungsAussage)

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
  LocalTypeUseAussage ∧ BoolTypeErfuellbarAussage

def IntegerTypeRegistryAussage : Prop :=
  (∀ scope signed width interval rest, (WrittenType.integer signed width interval).valid scope →
    (∀ more, rest ≠ keyword "in" :: more) →
    TypeReads scope ((WrittenType.integer signed width interval).printPieces.map PrintedToken.value ++ rest)
      (.integer signed width interval) rest) ∧
  LocalTypeUseAussage ∧ IntegerTypeErfuellbarAussage

/-- The written region type is realized in the owned parameter of the checked region unit. -/
def OwnedRegionTypeRegistryAussage : Prop :=
  (∀ scope rest, TypeReads scope
    (WrittenType.ownedRegion.printPieces.map PrintedToken.value ++ rest) .ownedRegion rest) ∧
  RegionBindUnitAussage

end Gabbro.Core.Ast.Semantik
