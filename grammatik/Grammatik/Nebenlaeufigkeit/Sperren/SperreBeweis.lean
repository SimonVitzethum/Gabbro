/-
  File:      Grammatik/SperreBeweis.lean
  Subject:   The replay of `ziel_ort_ganz` (`ZielOrtRahmenBeweis.lean`) with
             LOCK INVARIANTS: the sequential side runs `execStmtH`
             (`SperreSem.lean`), the records also keep the environment's move
             at every acquire, and the sequential world agrees with the
             machine world on the STABLE carriers of the frame at its current
             holdings (`stabilS`, `SperreFuss.lean`), not on the whole
             footprint.

  Changes against `KopfR`/`WarteR`/`StapelR`/`FadenR`:
  * a third record `HU` of acquires (`UEintrag`: lock, key world, the
    memory the protected carriers were taken from), functional, below the
    sequential trace, every source meeting the lock's invariant (`InvU`);
    the sequential runs quantify over the moves repeating it (`PasstU`);
  * agreement on `stabilS P S lok F.f Λ`, where `Λ` is the residue's static
    holdings: it grows at an acquire (the new record takes the protected
    carriers from the machine, `fadenS_locks`) and shrinks at a release;
  * the release steps (`fadenS_frei`, `fadenS_peelFrei`) use the second
    clause of the obligation: the head's prediction is no `logik` outcome
    (`kopfS_keineLogik`), so the release check passes at the sequential
    world, hence (the protected carriers are stable while the lock is held)
    at the machine world (`kopfS_frei_inv`).
-/

import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T1
import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T2
import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T3
