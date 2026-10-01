# MUSE-REPORT-556: Diagnose repeated intermittent CLI alias test failure

## Task

Diagnose the intermittent failure of `jeder_erstname_tut_dasselbe_wie_sein_zweitname`
(`crates/gabbro-cli/tests/erstnamen.rs:64`) seen at publications `079595de` and `ebdec41d`
(1467 passed, 1 failed, 1 ignored), then make a minimal justified repair.

Clone verified: `/home/simon/Dokumente/gabbro-muse/a556`, branch `muse/556`.
Only owned files touched: `crates/gabbro-check/src/beweis.rs` (repair + unit tests)
and this report. No Lean, model, checker-rule, emitter, or test-file change.

## Diagnosis (reproduced, not assumed)

1. **Full suite via `./cargo-pruef`, first run: 1467 passed, 1 failed, 1 ignored.**
   The failure moved to the sibling test `jeder_fahnen_erstname_tut_dasselbe_wie_sein_zweitname`
   (`fahnen.rs:723`), same family. Full output saved to `.tmp/cargo-test-full.log`.
   The exact failing pair (`emit --proved` vs `emit --mit-beweis` on
   `beispiele/16-by-ops-am-feld.gab`):
   - left: stdout `""`, stderr `SETUP Duty16ByOpsAmFeld -- ... nothing was measured:
     libc++abi: terminating due to uncaught exception of type lean::exception:
     failed to create thread`, exit **3**
   - right: stdout = full generated C, stderr `GREEN ... nothing owed`, exit **0**
2. **Isolation runs are byte-identical.** With no suite load, `emit --proved` and
   `emit --mit-beweis` on the same file both return GREEN with identical stdout/stderr.
   Dispatch is deterministic and correct: `prove|beweise` both reach
   `befehl_beweise(rest)`, `emit --proved|--mit-beweis` filter to the same flag
   (`main.rs:1386,1400`). **There is no genuine alias behavior difference.**
3. **Cause: transient Lean resource starvation under parallel load.**
   Both alias-equality tests compare two *sequential* heavyweight external-Lean runs
   byte-for-byte. Under the full parallel suite, several multi-threaded, gigabyte-heap
   Lean processes (`lake build` + 3 `lean` runs per `gabbro prove`, from the erstnamen
   `prove` pair AND the fahnen `emit --proved` pair on the same file) pile onto one
   machine, and one run intermittently dies with `failed to create thread` (SETUP)
   while its twin seconds later is GREEN. The byte-equality then reads an apparatus
   failure as an alias difference. Light pairs (check, costs, ...) never flake: they
   are in-process, no Lean. A shared-file corruption race was considered and ruled
   out: concurrent runs on the same unit write identical Duty/Gate bytes, and the
   olean remove/write/check window is microseconds wide -- the three captured failures
   (two runs, both directions, both test binaries) are all clean thread-creation
   failures, never torn files.
4. **Retry alone is insufficient (demonstrated).** A first repair (bounded retry of
   starvation-signatured Lean/lake runs) still failed both heavy tests on the next
   full run (1468 passed, 2 failed): a 5 s sleep cannot ride out minutes of overlap,
   and each retry adds another Lean process to the pile.

## Repair (`crates/gabbro-check/src/beweis.rs`, std only, no new deps)

- `ist_ressourcen_engpass(&str) -> bool`: pure gate matching only runtime starvation
  signatures (`failed to create thread`, `cannot allocate memory`, `out of memory`,
  `resource temporarily unavailable`). Every error WITH a position fails on the first
  attempt exactly as before; verdict logic and all messages are unchanged.
- `lean_lauf` / `modell_bauen`: bounded retry (`LEAN_VERSUCHE = 3`,
  `LEAN_PAUSE_MS = 5000`) gated on the above AND an empty `fehlerzeilen` (or a
  starved spawn). Rides out spikes; persistent failure reports exactly as before.
- `MessSperre` / `mass_sperre_halten` / `sperre_inhaber` / `sperre_alter`
  (+ `SPERRE_WARTE_MS = 1000`, `SPERRE_VERFALL_MS = 15 min`): cross-process gate
  (atomic directory creation, `std` only) holding **at most one measurement per model
  folder** from `lake build` through the gate run. `pruefe` acquires it first and
  holds it to the end (RAII `Drop`); the holder renews `inhaber` after each Lean
  phase, and a gate older than 15 min is taken over (SIGKILL safety). The gate
  changes WHEN a measurement runs, never WHAT it says, and prints nothing, so
  compared stderr stays byte-stable.
- Unit tests `ressourcen_engpass_tests`: `die_schranke_greift_bei_verhungern`,
  `die_schranke_schweigt_bei_baum_und_aufbau` (gate silent on positioned errors,
  missing toolchain, empty output), `die_sperre_haelt_nur_eine_messung`
  (4 threads x 3 holdings never overlap; gate released afterwards).

No new diagnostic code, no corpus/ledger change, no new language construct, no
weakened guarantee. Dispatch untouched, so a genuinely diverged alias still fails
its equality assertion deterministically; the existing `assert_ne!` liveness floors
(`erstnamen.rs:69`, `fahnen.rs:728`) are untouched.

## Evidence

- `./cargo-pruef` after repair: **exit 0; 1471 passed, 0 failed, 1 ignored**
  (1471 = 1468 + 3 new unit tests). Full log: `.tmp/cargo-test-full.log`.
- Both heavy binaries run **concurrently** afterwards: erstnamen 5/5 ok,
  fahnen 8/8 ok (`.tmp/verify-erstnamen.log`, `.tmp/verify-fahnen.log`).
- `./lean-bau`: `Build completed successfully (420 jobs).` (Lean untouched.)
- What I believe may be wrong / remains open: full source-to-binary verification
  remains OPEN per task. The 15-minute takeover bound assumes no single measurement
  phase exceeds it (measured phases are seconds to ~6 min); a far-future slower
  phase would need its own renewal call. If suite-level flakiness ever returns with
  a *different* Lean signature, extend `ist_ressourcen_engpass` -- the gate makes
  such cases deterministic load serialisation failures, not divergent pairs.

## Scope

Snapshot checked: `muse/556` at `6bb576c5` plus this repair. Owned files only.
No credentials read, no network, no push. Commit via `./commit.sh`.
