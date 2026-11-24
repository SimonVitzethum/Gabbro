module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # UnmapSpace proofs

Prove `UnmapAussage`: clearing a mapping and taking the revocation token.
The statement packet is pinned; the proof is open.

- `memObligationsKern .unmapSpace`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `UnmapJointAussage`: the creation-mapping-revocation chain executes with
  both rules, clearing the table and recording the token.
- `UnmapMeaningAussage`: only the owning caller revokes; the range is
  mapped with contiguous frames, the base page-aligned and canonical;
  table entries are cleared and the generation moves on while cached
  translations deliberately linger for the later flush.
-/

end
