module

public import Core.Ast.Semantik.Runtime.Regeln
public import Core.Ast.Semantik.Runtime.Atom.Form

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Katalog

/-- A compound type requires every address space named by its components. -/
def platformType (platform : Plattform) : Ty .value → Bool
  | .address space => (space.width platform).isSome
  | .ptr space _ referent => (space.width platform).isSome && platformType platform referent
  | .array element _ | .regionView element => platformType platform element
  | .product head tail | .sum head tail => platformType platform head && platformType platform tail
  | .record _ _ shape | .recordSchema _ _ shape | .variant _ _ _ shape
  | .variantSchema _ _ _ shape | .carrierSchema _ _ shape _ => platformType platform shape
  | _ => true

def Befehl.platformAllowed (platform : Plattform) : Befehl → Bool
  | .definiere _ params result .. => (params ++ result.toList).all (platformType platform)
  | .bindeWert _ type _ | .zurueck _ type => platformType platform type
  | .definiereRecord _ _ fields => fields.all (platformType platform)
  | .definiereTraeger _ _ layout _ => platformType platform layout
  | .definiereVariante _ _ cases => (cases.flatMap Option.toList).all (platformType platform)
  | .rufe _ args result => (args ++ result.toList).all (platformType platform)
  | .bindeRegion _ (.view written _) => (LowLevel.layout platform.ziel written).isSome
  | .zugriff z => pruefeZugriffsform z
  | _ => true

end Gabbro.Core.Ast.Semantik
