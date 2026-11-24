module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # SplitPages proofs

Prove `SplitPagesAussage`: the region split discharging whole pages. The
statement packet is pinned; the proof is open.

- `memObligationsKern .splitPages`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `MemErfuellbarAussage .splitPages`: the joint witness at the initial live
  occurrence over a one-region arrival contract.
- `SplitPagesMeaningAussage`: only the owning, unborrowed caller splits;
  the region starts page-aligned and the page count fits strictly inside;
  the first chunk holds exactly that many pages and stays page-aligned;
  disjointness, coverage and the ledger update are those of the address split.
-/

end
