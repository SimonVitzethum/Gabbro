# MUSE-REPORT-618: Deterministic native Lean worker/heap bounds for publication tests

Clone verified: `/home/simon/Dokumente/gabbro-muse/a618`, branch `muse/618`.
Owned files only: `crates/gabbro-check/src/beweis.rs`, this report. No Lean, model,
checker-rule, emitter, test-file or wrapper change. No network, no push.

## Reproduction (before any edit)

Full `./cargo-pruef` on the unmodified tree failed the same family as the integrated
suite at `758a8448`: `jeder_fahnen_erstname_tut_dasselbe_wie_sein_zweitname`
(`crates/gabbro-cli/tests/fahnen.rs:723`), with `1470 passed, 1 failed, 1 ignored`.
Exact values from `.tmp/cargo-test-full.log` (kept, git-ignored):

- left (`emit --proved` on `beispiele/16-by-ops-am-feld.gab`): full generated C,
  stderr `GREEN Duty16ByOpsAmFeld -- 2 statement(s), all closed by the generator`,
  exit **0**
- right (`emit --mit-beweis`, same file): stdout `""`, stderr `SETUP
  Duty16ByOpsAmFeld -- \`lean\` exited unsuccessfully and named no position --
  nothing was measured:\nlibc++abi: terminating due to uncaught exception of type
  lean::exception: failed to create thread\ngabbro emit --proved: a unit still owes
  a proof -- no C is written`, exit **3**

So a direct `lean` run died of thread starvation after lane 556's bounded retries
(3 attempts) and inside its per-model gate. The gate serialises WHEN measurements
run; it cannot shrink any single run's thread demand. Every `lean` the measurement
spawns ran unbounded (machine core count as thread pool, no heap ceiling), so one
run can still starve on a loaded machine while its twin, seconds later, is GREEN.

## Repair (`crates/gabbro-check/src/beweis.rs` only)

Deterministic bounded worker counts/heap through EVERY native Lean spawn of the
measurement, using the bound the tree already uses (`grammatik/lakefile.toml`
`weakLeanArgs = ["-j2", "-M4096"]`, `lean-probe`'s `lake env lean -j2 -M4096`):

- `LEAN_BOUND_ARGS: [&str; 2] = ["-j2", "-M4096"]` -- appended to every direct
  `lean` run in `lean_lauf` (Duty, Proofs, Gate alike) and to the `lake env lean`
  template run in `vorlage_quelle`.
- `LAKE_WORKER_ENV: (&str, &str) = ("LEAN_NUM_THREADS", "2")` -- pinned (not
  inherited) on every `lake build` of the measurement (`modell_bauen`'s
  `lake build Gabbro.Body`, `vorlage_quelle`'s `lake build Bruecke.Vorlage`) and on
  the `lean` spawns, through the environment the repo's instruments already pass to
  `lake build` (e.g. `instrumente/zaehle-kette.py`).

Bounds change resource use, never the verdict: they print nothing, alter no error
position and no message, so compared stdout/stderr stay byte-stable; retry/gate/
`ohne_ort` logic is untouched, and a persistent failure still reports exactly as
before (same SETUP text after the last attempt). No output compared, masked or
normalised; no test deleted, weakened or added outside the owned unit tests; no new
source rule, no fabricated Lean verdict, no semantics change.

New unit tests in `ressourcen_engpass_tests`:

- `die_schranken_sind_die_des_baums` -- the bounds equal the tree's own pair.
- `der_kanal_meldet_den_gemessenen_aufbaufehler` -- the verbatim reproduced stderr
  takes the apparatus path (`ist_ressourcen_engpass`, empty `fehlerzeilen`,
  `ohne_ort` SETUP on failure, none on success); a positioned error still takes the
  tree path. This is the actual failure channel, not a synthetic one.

All four `Command::new` spawns in `crates/gabbro-check/src` are in this file and
all four now carry the bounds (verified by grep; the remaining `Command::new`
uses in the tree are C toolchains and test harnesses, not Lean).

## Evidence

- `./cargo-pruef` after repair: `== exit 0; failing tests: 0`,
  `== total: 1473 passed, 0 failed, 1 ignored` (1471 + 2 new unit tests).
  Full log: `.tmp/cargo-test-full.log`. Both heavy alias tests `ok` in that run:
  `jeder_erstname_tut_dasselbe_wie_sein_zweitname`,
  `jeder_fahnen_erstname_tut_dasselbe_wie_sein_zweitname`; all five
  `beweis::ressourcen_engpass_tests` `ok`.
- Concurrent stress afterwards (built test binaries, fixed code): erstnamen 5/5
  `ok`, fahnen 8/8 `ok` (`.tmp/verify-erstnamen-618.log`,
  `.tmp/verify-fahnen-618.log`).
- `./lean-bau`: not run (no Lean file touched; owned paths are Rust-only).

## Open / what I believe may be wrong

- One green full suite does not prove the flake is gone; the pre-repair failure
  itself was intermittent (about one run in two in the observed sample). If it
  recurs, the next datum to collect is WHICH `lean_lauf` call failed (Duty,
  Proofs, Gate) -- the SETUP text does not say -- and whether `lake build` or a
  sibling `bruecke/` build raced it.
- The `lake`-side bound (`LEAN_NUM_THREADS`) rests on repo-instrument precedent;
  unlike `-j2 -M4096` on direct `lean` runs (documented `lean --help` flags, same
  as `lean-probe`), I did not independently verify that this `lake` version reads
  it. It is harmless if ignored, but the certain half of this repair is the direct
  `lean` bound. `programmlogik/lakefile.toml` carries no `weakLeanArgs` (unlike
  `grammatik/`); adding it there would bind `lake build` from the inside, but
  that file is outside my owned paths -- suggested follow-up for the owner.
- A persistent starvation on BOTH spellings can still read as an alias difference
  when the two SETUP texts differ (e.g. `
...[truncated 208 chars]