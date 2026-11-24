module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # NewSpace proofs

Prove `NewSpaceAussage`: creating an address space from an owned table
region. The statement packet is pinned; the proof is open.

- `memObligationsKern .newSpace`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `MemErfuellbarAussage .newSpace`: the joint witness at the initial live
  occurrence over a one-region arrival contract.
- `NewSpaceMeaningAussage`: only the owning, unborrowed caller creates;
  the table extent is non-empty, page-aligned and inside the physical
  width; the fresh space starts empty at generation zero and is
  well-formed, hence ready to activate.
-/

end
