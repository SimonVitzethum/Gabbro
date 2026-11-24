module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # ActivateSpace proofs

Prove `ActivateAussage`: installing a well-formed space on this core. The
statement packet is pinned; the proof is open.

- `memObligationsKern .activateSpace`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `ActivateJointAussage`: creation then installation executes with both
  rules over the yielded well-formed space.
- `ActivateMeaningAussage`: only a well-formed space activates; a dangling
  or malformed space never becomes active.
-/

end
