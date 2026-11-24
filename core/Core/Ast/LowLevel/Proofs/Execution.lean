module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level rule, unit and progress proofs

Use the same fixed source instruction to prove the ideal equation and the
concrete equation. The linearisation point is the local transition that
produces its result. The two private relations are empty.

- `IdealAussage`
- `EinheitAussage`
- `ImplAussage`
- `FortschrittAussage`
-/
