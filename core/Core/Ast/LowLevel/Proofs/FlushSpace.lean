module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # FlushSpace proofs

Prove `FlushAussage`: invalidating stale translations and returning the
frames. The statement packet is pinned; the proof is open.

- `memObligationsKern .flushSpace`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `FlushJointAussage`: the creation-mapping-revocation chain runs, the
  enclosing `let` binds the token, and the shootdown executes over it.
- `FlushMeaningAussage`: only a still-pending token flushes; the cached
  translations of its range are dropped on every core at once, the token
  retires from space and binding, and the recorded frame extent returns;
  afterwards no core holds a translation of the range.
-/

end
