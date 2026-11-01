/-
  File:      Grammatik/Zielsatz/PoolSym.lean
  Subject:   The symmetric worker pool (lane 245): one routine on N threads.

  The checker admits `concurrent { f, f }` (the same routine twice) IFF the
  routine is pool-safe: it holds no lock by signature, declares no reasons,
  and every carrier its thread graphs may write is guarded by a lock or
  atomic (`fusswache2.rs`, narrowed `N304`). This file is the model side of
  that condition: the separation lemma for two threads running one
  pool-safe routine (`PoolSicher` itself, with `PoolSicherW`/`EinzelnPool`,
  lives in `Zielsatz/Spec.lean`, beside `Ruhig`/`StartZulaessig`), the
  decidable pool checks, and the race-freedom and lock legs over
  multiset starts. Since fix lane F10 (2026-09-22) `Spec.lean`'s
  `AkzeptiertSpec.einzeln` IS `EinzelnPool` and `Laufzeit.einmal` admits a
  routine declared twice on several threads; the goal theorem covers pools
  (`gabbro_ziel`, witnessed in PoolZeuge.lean). This file keeps the
  separation lemmas and the "never weakened" statements of that diff
  (`akzeptiert_nodup_gleich`, `akzeptiertSpecVor_neu`, `pruefer_vor_neu`,
  `laufzeit_vor_neu`).
-/
module

public import Grammatik.Zielsatz.Faeden.PoolSym.Teil1
public import Grammatik.Zielsatz.Faeden.PoolSym.Teil2
