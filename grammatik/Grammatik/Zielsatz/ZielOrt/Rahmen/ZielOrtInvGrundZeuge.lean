/-
  Gabbro/Grammatik/ZielOrtInvGrundZeuge.lean

  **Witnesses for `ziel_ort_sperre_invGrund`** (invariants at REASON
  returns, THEOREM-MAP §19.1).

      lock L protects konto (two slots, 0 .. 10) rank 0
      invariant gleich: konto[0] == konto[1]        -- carriers: konto
      fn haupt()  holds L, writes konto {
        breaking gleich {
          let x = setze() else { r => konto[0] := 1; konto[1] := 1; return }
        };
        konto[0] := 1; konto[1] := 1; return }
      fn setze() -> bool, one reason, holds L, writes konto
        { konto[0] := 5; konto[1] := 5; return R }             -- igPgut
        { konto[0] := 5; return R }                            -- igPschlecht
      fn nichts() { return }

  Thread 0 starts in `haupt`, every other thread in `nichts`. Every contract
  is `true`. `setze` never returns a VALUE, so the value-return obligation
  `InvGutS` holds for both programs, and `ziel_ort_sperre_inv` certifies the
  broken one (`igPschlecht_alt`): its `setze` leaves by the reason with
  `konto[0] = 5`, `konto[1] = 0`, breaking the invariant it owes -- and on a
  reached machine the logged reason return shows it
  (`igPschlecht_verletzt`). The new obligation `InvGutGrund` refutes it
  (`igPschlecht_nicht_invGutGrund`); the correct program meets every
  premise of `ziel_ort_sperre_invAlle` (`igPgut_zertifiziert`), and on its
  reached run the logged reason return meets the invariant BY THE THEOREM
  (`igGut_zeuge`).
-/
module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrundZeuge.Teil1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrundZeuge.Teil2
