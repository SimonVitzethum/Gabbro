module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level form-specific proofs

Invert name and layout resolution and the checked local transfer. The view
must make a second borrow of the same grant unavailable. For an environment
selection, both the row membership and exact ABI matter.

- `AddressTypeMeaningAussage`
- `RegionAddressMeaningAussage`
- `ViewMeaningAussage`
- `EnvironmentMeaningAussage`
-/
