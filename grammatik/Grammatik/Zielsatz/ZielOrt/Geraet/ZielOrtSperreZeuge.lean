/-
  File:      Grammatik/ZielOrtSperreZeuge.lean
  Subject:   WITNESSES AND PROBES for the goal theorem with lock invariants,
             `ziel_ort_sperre` (`ZielOrtSperre.lean`).

  1. Verdict probe B, reconstructed and CERTIFIED: `zP` (`ZielOrtZeuge.lean`)
     with `wrap`'s `ensures true` replaced by `konto[0] == 100` -- a contract
     over the lock-protected table at the lock boundary of `haupt`
     (`locks { wrap() }`). `fussOrtGB` is false (`zPB_fussG_falsch`, the
     finding); the new check passes with the lock `()` protecting `konto`
     (invariant `true`), every premise of `ziel_ort_sperre` holds, and on a
     reached run the `ensures` of `wrap` holds at its logged return, from the
     theorem.
  2. Verdict probe C, reconstructed and CERTIFIED: `haupt` reads the
     protected carrier inside its `locks` block
     (`locks { konto[0] = konto[0] }`).
  3. TWO THREADS WRITING THE SAME CARRIER UNDER ONE LOCK with a
     NON-TRIVIAL lock invariant (`konto[0] == konto[1]`) and a contract that
     depends on it: every thread runs `haupt(x) = locks { setze(x) }` (the
     same routine, no signature lock -- the start is exclusive); `setze`
     requires `konto[0] == konto[1]` (the caller can only prove it from the
     invariant it gets at the acquire) and ensures
     `konto[0] == konto[1] && konto[0] == x` (which re-establishes the
     invariant at the release). On a reached run thread 1 enters `setze` in
     the state thread 0 left: the `requires` holds there, from the theorem,
     over values thread 0 wrote.
  4. Corpus 104 through the new theorem (`ziel_ort_sperre_ref104`), and
     probe A refuted for the new obligation (`paP_nicht_sperre`).
-/

import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T2
