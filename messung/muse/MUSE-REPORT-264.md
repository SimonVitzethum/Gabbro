# MUSE-REPORT-264 — close OFFEN O20 (arenas under concurrency)

Lane 264, 2026-09-26. Two new checker rules (`N521`, `N522`) in a new file,
nine poison probes, row 2 measured closed without new code, no emitter
change. Untouched as ordered: `MARKE_EMIT*` (delta: none measured),
linking (Opus F), atomics Lean (Opus O25b), `lean_g.rs`, every Lean file.

## Verdict in one line

**BUILT — `N521` refuses a `reset` beside a concurrent use (no exemption),
`N522` refuses counter touches without a guarding lock held at every access
(the plain words stay), the commit ceiling counts every concurrent instance
already (pools, repeated and looped `start`s — pinned, not rebuilt), and
every gate is green.** `./cargo-pruef` 1382 passed / 0 failed (baseline
1370; +12 `paesse` tests), `./emission-pruef` ALL PASS, `./lean-bau` green,
corpus verdict diff zero on pre-existing files, `MARKE_EMIT` delta none.

## 1. What was built

**`crates/gabbro-check/src/arena_faden.rs` (new, ~800 lines, wired into both
pipelines in `lib.rs` beside `nebeneinander`).**

- Thread collection: `concurrent` members (naming multiplicity), `entry`
  targets (self-paired), `boot` dispatch (once), `start` roots (statement
  occurrences), outermost `child` regions (self-paired, gate unbounded).
- Per-function presence sets (`Direkt`: resets, counter sites with
  `locks` stacks, uses incl. `A[i]` reads and `index into A` params,
  calls-only targets), closed over calls (indirect = whole pool).
  `child` regions skipped in bodies, `start` edges never filed.
- `N521` (`melde_n521`): reset on either side beside a use on the other, one
  refusal per pair and arena, no exemption (a lock serializes the counter
  but cannot revive a consumed generation).
- `N522` (`melde_n522`): counter touches on both sides without one
  protecting lock held at every site, one refusal per pair and arena.
  Held counts as `H007` counts it (block, effects line, signature; never
  `shared`); the `protects` map is read module-resolved beside
  `sperrdaten`. `child` regions are not paired here (`N457`'s).
- Exact new items: `N521`, `N522`; `Faden`, `Direkt`, `Stelle`,
  `Genommen`, `Beruehrt`, `Sammler` (+ `block`, `anweisung`,
  `ort_gebrauch`, `domaene_gebrauch`, `tisch`, `rufe_in_expr`,
  `rufe_in_pred`, `ruf_sammeln`, `loese`), `direkt_sammeln`,
  `regionen_in`, `schliesse`, `beruehrt`, `nimmt`, `melde_n521`,
  `melde_n522`, `kleinste`, `brauchbar`, `kurz`, `pass`.
  No Lean definitions or theorems — nothing `ZEUGE`-shaped was tasked.

**Row 2: measured closed, no `arena.rs` change.** Pool namings, repeated and
looped `start` executions (bounded and unbounded) are all counted by the
F4-start-edge + F2-bound machinery already. Nine discovery probes confirmed
every shape before any edit was considered; the sentence
(`arena.wachsen_commit`) now names the executions.

**Sentences (`saetze.rs`):** `arena.reset_neben_gebrauch` (`N521`),
`arena.zaehler_ohne_sperre` (`N522`); `arena.wachsen_commit` extended
(start executions + gifts 1279/1280 + `paesse` names). `OFFEN.md` O20
gains the closure table with residuals. Consumed: codes `N521`, `N522`,
gifts 1272-1280. Returned unused: `N523`-`N525`. No example numbers taken
(positives live in `paesse.rs`).

## 2. Verification (last lines, this tree)

- `./cargo-pruef`: `== exit 0; failing tests: 0`
  (`1382 passed, 0 failed, 1 ignored`).
- `./emission-pruef`: `== exit 0`, `ALL PASS -- 42 durchgestochen, 304 von
  304 uebersetzen` (ASan not run on this machine, as booked).
- `./lean-bau`: `Build completed successfully (324 jobs).` (no Lean file
  touched; the run is the machine check behind that claim).
- Corpus verdict diff: ZERO on pre-existing files — all `beispiele/*.gab`
  still clean, every `gift/*.gab` still falls with its booked code; the
  only new verdicts are gifts 1272-1280. Only three pre-existing files mix
  threads with arenas (gifts 1132, 1146; `beispiele/154` mentions
  concurrency in a comment only): 1132 has no reset and no second thread,
  1146's region grows but resets nowhere, so both stay silent.
- Guardians: `pruefe-saetze.py` 457 codes / 55 ohne Satz (mark unmoved) /
  0 erfunden; `pruefe-kennungen.py` ALL PASS (both codes in one file);
  `pruefe-osfrei.py` clean; `pruefe-englisch.py` red as on base, German
  comment count 7965 before and after (0 added; new identifiers follow the
  German convention of `arena.rs`).

## 3. Measured probe sets (exact)

`["N521"]` solo (reset vs parameter read; transitive through a callee;
member reset vs started-root use); `["N457", "N521"]` (guarded region);
`["N522"]` solo (pool self-pair); `["H013", "N522", "N522"]`
(entry/member + handler self-pair); `["N426", "N522"]` (pool commits
twice; two sequential starts); `["N426"]` solo (128-pass looped start);
`[]` (guarded sharing, per-thread arenas, single start commits once);
`["N522", "W001"]` (untaken lock); `["E006", "E006", "W001"]`
(undeclared take, `N522` silent — the exemption is physical).

## 4. Findings (three, one deviation)

1. **`N462` resolves no arena `writes`** (`schreibtraeger` knows tables
   only), so a sharing start root beside a member was nobody's refusal --
   `N521`/`N522` keep start roots as threads for exactly this reason.
   Same measurement: the `N457`/`N462` guard disjunct is vacuous for
   arenas (`sperrdaten` resolves no arena `protects`), which is why every
   region `N521` doubles with `N457` and why `N522` reads its own
   module-resolved map without weakening either rule.
2. **`H007` owns arena READS but no counter statement**: an `A[i]` place
   under a missing lock falls there (measured beside the hull-lock probe),
   while `alloc`/`reset`/`grow` have no `H007` arm -- the holding half for
   counter sites is this pass's (`nimmt`). The `effects`-line exemption is
   shared with `H007` deliberately.
3. **Deviation disclosed: row 2 needed no code.** The task asked for
   counting each concurrent instance; the tree already counts them
   (pool namings, repeated/looped/unbounded `start`s), so the deliverable
   is nine probes pinning the count, not a rebuild. If the merger prefers
   a refusal-shaped pin for unbounded `start` re-entry beyond the `N426`
   that already fires there, that is a sentence-level choice, not a hole.

## 5. Open (not mine)

- The merger bumps nothing: `MARKE_EMIT`, `MARKE_EMIT_G` and all marks
  stand (no new example, no emitting gift, sentence mark unmoved).
- Residuals (in `OFFEN.md` O20): entry-vs-plain-boot-code pairs,
  the shared `effects`-line exemption, `H007` reads vs this pass's
  counter sites, region `N521` always doubling `N457`.
- `pruefe-vergabe.py` stays red on its stale marks (unchanged by this
  lane; `N521`/`N522` match their reservation).
- Last `./lean-bau` result line:
  `Build completed successfully (324 jobs).`
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`
  (`1382 passed, 0 failed, 1 ignored`).
