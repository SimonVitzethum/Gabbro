/-
  File:      Grammatik/ZielOrtSperre.lean
  Subject:   THE GOAL THEOREM WITH LOCK INVARIANTS -- `ziel_ort_sperre`.
             Contracts over shared state across a lock boundary, and readers
             inside `locks L { … }` blocks (verdict item 2,
             `messung/URTEIL-OPUS-2026-09-13.md`, probes B and C).

  The rule-by-rule step of the replay (`akteurS`, as `akteurR` in
  `ZielOrtRahmen.lean`) over the semantics with lock invariants, the rely,
  the start, the invariant on every reachable machine -- the replay, the
  machine lock invariant `SperrInvG` and the log -- and the theorem. The
  acquire step records the environment's move (`fadenS_locks`), fed by the
  machine lock invariant; the release steps (`fadenS_frei`,
  `fadenS_peelFrei`) use the second clause of the obligation, and give the
  machine lock invariant back (`kopfS_frei_inv`).
-/

import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.T1
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.T2
