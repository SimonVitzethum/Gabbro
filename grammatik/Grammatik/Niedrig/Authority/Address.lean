module

public import Grammatik.Niedrig.Authority.AddressData
public import Grammatik.Speichermodell.Adressen.Layout

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-- An address expression's evaluation is independent of the world; failure
    also retains it. This is a layer judgment, not a new constructor of G.Expr. -/
def evalAddress {D : Deklaration} {space : Space D} (e : AddressExpr space) (world : World D) :
    Except AddressFailure (Address space) × World D := (e.eval, world)

theorem address_world_unchanged {D : Deklaration} {space : Space D}
    (e : AddressExpr space) (world : World D) : (evalAddress e world).2 = world := rfl

theorem address_result_independent {D : Deklaration} {space : Space D}
    (e : AddressExpr space) (first second : World D) :
    (evalAddress e first).1 = (evalAddress e second).1 := rfl

end Gabbro.Grammatik.LowLevel
