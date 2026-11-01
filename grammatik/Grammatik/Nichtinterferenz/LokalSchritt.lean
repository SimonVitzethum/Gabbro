/-
  File:      Grammatik/Nichtinterferenz/LokalSchritt.lean
  Subject:   THE STEP OF ONE THREAD IS LOCAL, RELATIONALLY (`schrittK_rel`).

  One ghost-free thread state `k`, two memories that agree on a carrier set
  `T`; the head residue of `k` reads only inside `S ⊆ T` and calls only
  axioms the oracle answers faithfully on `T`. Then the two steps
  `kSchrittK k sp₁` and `kSchrittK k sp₂`, if both exist, end in the SAME
  ghost-free state and in memories that again agree on `T`.

  This is step consistency for one thread, stated over the function of
  `Schritt.lean` -- one case analysis over the residue, no pairing of two
  derivations. Device register reads use register locality (`RegLokal`):
  the device carriers of a register the head reads lie in `S`.
-/
module

public import Grammatik.Nichtinterferenz.LokalSchritt.Teil1
public import Grammatik.Nichtinterferenz.LokalSchritt.Teil2
