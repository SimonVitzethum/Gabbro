# MUSE-REPORT-344: Reviewed organisation plan B4 — FenceDrain

## What was done

New owned file `grammatik/Grammatik/X86/FenceDrain.lean` (369 lines) plus one
additive import line at the end of `grammatik/Grammatik.lean`. No other file
touched. All work reuses the ONE canonical TSO model of
`Grammatik.X86.TSO` (`TSOZustand`, `issueByte`, `loadByte`, `flushKern`,
`zaunBereit`, `zaunBereit_iff_leer`, `flush_anderer_kern`,
`flush_entfernt_kopf`, `flush_schreibt_kopf`, `flush_rahmen`,
`issue_haengt_an`, `flush_leer`, `TSOSchritt`, `TSOErreichbar`,
`zeugenSpeicher`); no second IR, no second evaluator, no source change.

New definitions (3):

- `drainKernN : TSOZustand -> Nat -> Nat -> Option TSOZustand` — bounded
  local drain: `n` oldest-first `flushKern` steps on core `c`; `none` iff
  the own buffer ran empty early.
- `drainVoll : TSOZustand -> Nat -> Option TSOZustand` — full local drain:
  exactly `(s.puffer c).length` steps.
- `mfenceZulaessig : TSOZustand -> Nat -> Bool` — local fence admission
  `Bool`, defined as `zaunBereit` (validator/profile admission, NOT a
  hardware fault and NOT a claim about any other core).
- Witness constants `fdX`, `fdY`, `fdEins`, `fdSieben`, `fdStart`, `fdS1`,
  `fdS2`, `fdS3` (two-core store-buffer trace: core 0 issues `fdX := 1`,
  core 1 issues `fdY := 7`, core 0 drains once).

New theorems (all premises used; no `Prop`-typed premise; no
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`):

- `drainKernN_null`, `drainKernN_succ` — drain iteration skeleton.
- `drain_fremd_puffer` — draining core `c` never changes another core's
  buffer (induction over `n`, via `flush_anderer_kern`).
- `drainKernN_leert`, `drain_voll_leer`, `drain_voll_bereit` — a drain of
  at least the buffer length empties the own buffer; a successful full
  drain makes the LOCAL fence ready.
- `drain_laesst_fremd` — NON-theorem (OBS-5 boundary): a local drain keeps
  every foreign pending entry pending.
- `drain_fifo_ordnung` — FIFO order under local drain (older address
  written, younger still pending with canonical byte unchanged).
- `mfence_loest_fremd_nicht` — REFUSAL, proved by `decide` on a concrete
  state: core 0 fence-ready while core 1 still forwards its own buffered
  byte past canonical memory. No local `MFENCE` claim over a foreign or
  device read satisfies this shape.
- Witness step facts, all `rfl`/`decide` on real canonical bytes:
  `fd_schritt1`, `fd_schritt2`, `fd_drain_schritt`, `fd_flush_schritt`,
  `fd_vorher_nicht_bereit`, `fd_nachher_bereit`, `fd_fremd_bleibt`,
  `fd_fremd_wartend`, `fd_speicher_aendert`, `fd_fremd_liest_alt`,
  `fd_fremd_liest_neu`, `fd_eigen_bleibt`, `fd_voll_schritt`.
- `fd_lokal_nur` — main witness: reached (`TSOErreichbar` via the two
  issue steps), memory-changing (`fdX` byte flips), local-only (own fence
  flips false->true, foreign buffer byte-identical and still pending,
  foreign load of `fdX` moves stale zero -> drained value while the
  foreign forwarded read of its OWN store is unchanged).
- Joint `_zeuge` companions instantiating ALL premises jointly on the
  non-degenerate reached memory-changing run: `drain_fremd_puffer_zeuge`,
  `drain_voll_leer_zeuge`, `drain_laesst_fremd_zeuge`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/FenceDrain.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau` (full project): `== exit 0; 0 error line(s) in the
  COMPLETE output`, `Build completed successfully (386 jobs).`
- `#print axioms` per main theorem: no axioms, or subsets of
  `[propext, Quot.sound]` (see probe output); nothing beyond the standard
  goal axioms.
- Source goal probe (scratch `.tmp/axiom-probe-344.lean`, not committed):
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` tokens in the owned
  file (only the English word "admitted" in prose, which the reviewer can
  grep).

## What remains open (see CUTS in the file)

Full final-byte/source/hardware correspondence stays OPEN: no `W`/`GX`
simulation, no lowering map, no per-access linearisation; spawn/join/
handler visibility needs the publication lemma (OPEN) — a fence alone
publishes nothing, only flushed bytes become canonical; no fairness,
progress, timing or cost claim; no interrupt/device/MMIO/DMA model; no
multi-byte atomicity and no LOCK RMW. Closes O-irq/O-spawn LOCAL half
only, as tasked.

## Note on the task text

The task's witness line ("a local fence changes only the acting core's
observability") is imprecise as written and I did not prove it in that
form: a local DRAIN observably changes canonical memory, which other
cores can then load (that is publication working). What is local-only —
and what `fd_lokal_nur` plus `drain_laesst_fremd` prove — is the fence
readiness and the foreign buffers: the drain empties only the acting
core's buffer, foreign pending entries survive byte-identical, and only
the acting core's `zaunBereit` flips. The report states this boundary
explicitly rather than hiding it in prose.
