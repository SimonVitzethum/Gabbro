/-
  File:      Grammatik/RufHaeltG.lean
  Subject:   STATIC HOLDINGS ARE HELD on every reachable machine of the
             repaired call machine G (`rufG_haelt_statisch`).

  The repair (`RufMaschineG.lean`, 2026-09-13): the bare `nimmt`/`gibt`
  steps are gone, a start thread holds its signature locks from the start
  machine on, and every step that reads the thread world demands
  `HeldGenau` of the head's static holdings. Here the payoff: on every
  reachable machine, for every thread and EVERY frame on its stack (head and
  suspended), every lock the frame's static holdings name is held by the
  thread (`rufG_haelt_statisch`), in particular every signature lock of the
  frame's function (`rufG_haelt_signatur`). A lock leaves the held set only
  through a release marker the head names (`offen_schrittG`,
  `ZielOrt.lean`).

  The inductive invariant (`HaeltInvG`) has three parts: every frame's
  static holdings are held; along every frame's residue chain each node
  names the frame's signature locks and each release marker `frei L k`
  releases a lock the holdings of `k` do not name (`GRest.kette`); no
  release marker of a frame releases a lock a frame BELOW it names
  (`FreiLinks` -- the lock was taken while that frame was suspended and its
  holdings held, and `dannLocks` demands the lock is not held). Since the
  held-set relaxation (2026-09-13) a suspended caller may hold locks its
  callee does not name, so the old link (`KetteLinks`: a suspended frame
  names nothing beyond the signature locks of the frame above it) is gone.
  Only `GutO` is assumed (the oracle keeps the held locks, for `axiomCall`
  leaves and `bindAxiom`).
-/

import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T2
import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T3
