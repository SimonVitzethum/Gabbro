module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # Merge proofs

Prove `MergeAussage`: joining two adjacent regions. The statement packet is
pinned; the proof is open.

- `memObligationsKern .merge`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `MemErfuellbarAussage .merge`: the joint witness at the initial live
  occurrence over a two-region arrival contract.
- `MergeMeaningAussage`: only the owning, unborrowed caller merges;
  the slots differ and the extents are adjacent; the merged extent covers
  both inputs; the consumed slot is revoked so its old handle is dead
  while every other slot is untouched.
-/

end
