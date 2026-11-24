module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level elaboration and acceptance proofs

Resolve the instruction at the source occurrence and show that its one local
plan has empty memory footprint. Catalogue and region facts are in the other
proof modules.

- `ElaboriertAussage`
- `RealisiertAussage`
- `AnnahmeAussage`
-/
