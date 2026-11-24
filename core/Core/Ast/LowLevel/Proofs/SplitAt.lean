module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # SplitAt proofs

Prove `SplitAtAussage`: the region split at an address. The statement packet is
pinned; the proof is open.

- `memObligationsKern .splitAt`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `MemErfuellbarAussage .splitAt`: the joint witness at the initial live
  occurrence over a one-region arrival contract.
- `SplitAtMeaningAussage`: only the owning, unborrowed caller splits;
  the point lies strictly inside; the halves are disjoint, share the
  boundary, and cover the original extent; the new tail object is
  brought to life in the authority ledger.
-/

end
