module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level joint satisfiability proofs

Prove `ErfuellbarAussage` separately at each of the four indices using the
canonical ideal initialisation. For the two region operations, use a
granted, aligned RAM extent disjoint from the platform device windows.

- `.addressType`
- `.regionAddress`
- `.view`
- `.environment`
-/
