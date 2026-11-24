module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # MapSpace proofs

Prove `MapAussage`: installing a page mapping. The statement packet is
pinned; the proof is open.

- `memObligationsKern .mapSpace`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `MapJointAussage`: the creation-then-mapping chain executes with both
  rules, so the joint authority the map needs is really produced.
- `MapMeaningAussage`: only the owning caller maps; the virtual base is
  page-aligned and canonical, every target page is absent from the table
  and from every pending revocation, the right set is non-empty; entries
  carry the frame base plus page index with the space generation.
-/

end
