module

public import Core.Ast.LowLevel.MemObligations

@[expose] public section

/-! # ProtectSpace proofs

Prove `ProtectAussage`: narrowing the rights of mapped pages. The statement
packet is pinned; the proof is open.

- `memObligationsKern .protectSpace`: the shared bundle (syntax inversion,
  derivation, parse, determinism; elaboration, realization, authority,
  ideal and implementation rules; progress, preservation, step safety,
  answer safety, locality, costs; M9 bounds, labels and flows).
- `ProtectJointAussage`: the creation-mapping-protection chain executes
  with both rules over the installed entries.
- `ProtectMeaningAussage`: only the owning caller protects; the range is
  mapped, the base page-aligned and canonical, the right set non-empty;
  rights are replaced keeping frame and generation while the cached
  translations of the range are dropped on every core at once.
-/

end
