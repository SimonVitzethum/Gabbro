/-
  File:      Grammatik/Nichtinterferenz/Invariante.lean
  Subject:   THE FLOW CHECK IS AN INVARIANT OF EVERY THREAD (`knr_erreichbar`).

  If every function a thread can run passes the flow check (`nE` of its
  body for the thread's carrier set and axiom set), then on every
  reachable machine every frame of that thread -- head and stack -- has a
  residue that passes the residue form `GRest.nR`. The step is read
  through the function `kSchrittK` (`schrittK_von`): one case analysis over
  the residue, single-sided; the function a push enters is in the thread's
  call graph by the thread invariant `merkInvG_erreichbar`.
-/
module

public import Grammatik.Nichtinterferenz.Invariante.Teil1
public import Grammatik.Nichtinterferenz.Invariante.Teil2
