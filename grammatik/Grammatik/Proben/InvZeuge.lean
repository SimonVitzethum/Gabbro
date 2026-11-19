/-
  Gabbro/Grammatik/InvZeuge.lean

  **Witnesses for `ziel_ort_sperre_inv`** (table invariants, THEOREM-MAP
  §15.4).

      lock L protects konto (two slots, 0 .. 10) rank 0
      invariant gleich: konto[0] == konto[1]        -- carriers: konto
      fn haupt()  holds L, writes konto { setze(); konto[0] := 1; konto[1] := 1; return }
      fn setze()  holds L, writes konto { konto[0] := 5; konto[1] := 5; return }   -- ivPgut
      fn setze()  holds L, writes konto { konto[0] := 5; return }                  -- ivPschlecht
      fn nichts() { return }

  Thread 0 starts in `haupt`, every other thread in `nichts`. Every contract
  is `true`, so `ziel_ort_sperre` certifies BOTH programs
  (`ivPschlecht_alt`) -- the gap: `setze` of `ivPschlecht` returns with
  `konto[0] = 5`, `konto[1] = 0`, breaking the invariant it owes.

  * `ivPgut_zertifiziert`: every premise of `ziel_ort_sperre_inv` holds on
    `ivPgut` (the new obligation `InvGutS` proved per function).
    `ivGut_zeuge`: on a reached run (thread 0 calls `setze`, which writes
    both slots and returns) the logged return meets the invariant BY THE
    THEOREM, at a world where both slots hold `5`.
  * `ivPschlecht_nicht_invGutS`: the new obligation FAILS for `setze` of
    `ivPschlecht`; `ivPschlecht_verletzt`: the new conclusion fails on a
    machine reachable in three steps. A refutation, where `ziel_ort_sperre`
    certified.
-/
module

public import Grammatik.Proben.InvZeuge.Teil1
public import Grammatik.Proben.InvZeuge.Teil2
