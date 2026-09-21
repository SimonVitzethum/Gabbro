# Fix lane F4 — thread starts (review G12 F2/F3, G06 F3/F5/F6), 2026-09-22

Base: `c3b95d8f` (F3) on `review-0921-integration`. Everything was built and run locally
(Simon, 2026-09-21: fisch unreachable). `free -g` beside the heavy runs: 31 GB total,
20 GB available, before `cargo test` (both runs), emission and `lake build`.

## 1. `start { f, g };` (lane 253) as checker rules

Lane 253's checker accepted the statement after name resolution only (`W003`). Now:

| rule | where | probe (poison / positive) |
|---|---|---|
| the roots are call-graph edges, so their effects, locks and incompleteness reach the starter (`E008`/`E009`) | `aufrufgraph.rs` `sammle_rufe`, `sammle_kanten` (`Start` arms replace the silent `_ => {}`) | gift 1153 (`pure` starter) / `tests/fadenstart.rs` guarded roots |
| costs: the SUM of the roots' declared costs + 2 per root (create, join); a root without a countable promise leaves the bill unknown (`K003`) | `kosten.rs` `Start` arm | gift 1154 (44 > 30) / bill at exactly 44 is clean |
| `N458` a root is an `impl fn` with a body, no parameters, no result, no `requires Held` | new `fadenstart.rs` | gift 1148 + tests (param, result, Held, extern) |
| `N459` a root twice in one statement (`start { h, h }`) | `fadenstart.rs` | gift 1149 |
| `N460` one owner per thread: no root is a `concurrent` member, `entry` root or `boot` dispatch | `fadenstart.rs` | gift 1150 / twin with the root outside the set |
| `N461` no `start` inside `locks`/`observes`/`breaking` or under `requires Held` (conservative: any held context) | `fadenstart.rs` | gift 1151 / twin with the `start` after the block |
| `N462` a started root is pool-safe: every carrier its reachable graph touches that anyone writes is guarded, atomic or per-core | `fusswache2.rs` `startfaeden` (the `N457` shape) | gift 1152 + tests (via callee, read of a written carrier) / reader of an unwritten carrier |

**Design decision (G12 F3), documented in `SYNTAX.md` (prose beside the statement EBNF) and
the `fadenstart.rs` header:** a thread has exactly one owner. Boot starts `concurrent`
members (and `entry`/`boot` roots); `start` starts its own roots; a root may not be both
(`N460`), so `concurrent { A, B }` + `start { A, B }` falls and no root runs twice. Because
started roots are in no declared pair, the pair race component never sees them; `N462`
(fail-safe pool shape) covers root-vs-root, root-vs-declared-starts and repeated instances,
so the starter needs no single-instance rule. Why the SUM for costs: nothing promises each
root a core. `start` is NOT added to the EBNF block: `start` is no vocabulary word (lane 253
spent no keyword), and adding it would be a lexer change (`pruefe-wortschatz.py` measured
the one missing terminal); the shape is given in prose.

Unchanged: the emitter refuses (`C001`), the exporter refuses (`LG004`); no model. Booked as
**OFFEN O22**. Sentence `faden.start` in `saetze.rs` (N458–N462).

## 2. Pools (lane 245/246) — Rust acceptance NOT gated; the surroundings made honest

- **Driver multiplicity (G06 F5, fixed).** `bau.rs treiberregel` keeps one root per
  OCCURRENCE; `treiber::erzeuge` writes one adapter per name and one `pthread_create` per
  occurrence; the pin (`pin_pruefe`, `pthread_create_zaehlung`, `vorkommen`) compares
  MULTISETS and counts only `pthread_create(` call sites (a count over comment mentions would
  invent threads). The pin now also runs at every `gabbro build` (it was test-only).
  `GENERATOR_KENNUNG` → `treiber-gen-2`. A failed `pthread_create` joins the threads already
  started. Test `pool_zweimal_deklariert_laeuft_zweifach`: a pool unit
  `concurrent { arbeiter, arbeiter }` builds, pins at 2, compiles under `-Werror`, runs exit 0.
- **`laufzeit/start_pool.c` (G06 F6, fixed).** Joins started threads on a partial create
  failure; `POOL_PRUEFE` runs with the lock held (documented: the check function takes no
  lock itself); header states `POOL_N` must equal the declared occurrence count. Measured:
  demo with `pruefe requires Held(L)`, `POOL_N=2`: `pool: pruefe=30 (want 30)`, exit 0.
- **`lean_g check_starts` (G06 F3, measured, then fixed).** Measured before the fix: a
  guarded pool unit EXPORTED (`starts := [⟨g_arbeiter, .nil⟩, ⟨g_arbeiter, .nil⟩]`), and so did
  `concurrent { leser, leser }`. The exporter now refuses a repeated start by name (`LG001`,
  existing code), test `refuses_duplicate_start` with a one-start positive twin. The
  MUSE-REPORT-245 claims (§1 "N is a runtime choice", §3.3 "lean_g refuses multiple starts")
  are corrected in an appended erratum (the report body stays as the audit record).
- O18 stays open for F10 (Spec swap + proved legs); its side-effects row now says what was
  fixed.

## 3. Measurements

- `cargo test --no-fail-fast`: **70 collections, 1289 passed, 0 failed, 1 ignored**
  (baseline 69 / 1266 / 0 / 1; +1 collection `gabbro-check/tests/fadenstart.rs` with 20
  tests, +1 lean_g test, +1 driver unit test, +1 driver integration test). After wiring the
  pin into the build, `gabbro-cli` re-run: 81 passed, 0 failed.
- `instrumente/pruefe-emission.sh`: **ALL PASS** (37 durchgestochen, 288/288, ASan not run on
  this machine as before). No `MARKE_EMIT*` touched.
- `grammatik`: `lake build` **281 jobs, 0 errors** (no Lean file touched).
- `pruefe-saetze.py` exit 0 (440 codes, 55 without sentence = ratchet); `pruefe-kennungen.py`
  ALL PASS; `pruefe-todo.py` 16 findings (= baseline); `pruefe-zahlen.py` 37 (= baseline);
  `pruefe-englisch.py` red as on master (7965 German comment lines, 37 feeders — the figures
  review G12 recorded); `pruefe-syntax.sh`: SYNTAX ALL PASS, EBNF 179 closed, vocabulary
  241/241, and the known red "Warnungen im Bau" stage from pre-existing warnings
  (`certstmt.rs` `DeclInfo`, snake-case test names) — the three `treiber.rs` dead-code
  warnings that stood there at base are gone.
- **Corpus diff** (base binary built from `c3b95d8f` vs this tree, error/hint codes per file
  over all 899 tracked `beispiele/*.gab`): the 892 pre-existing files are **unchanged**; the
  only differences are the 7 new gifts. On the base binary they read: 1148/1149/1150/1154
  `H011` only, 1151/1152/1153 clean — i.e. the defects passed before.

## 4. Open

- O22: `start` has no model and no lowering; `N461`/`N462` are strict (fail-safe).
- O18: the pool acceptance itself (F10).
- No SATZKARTE entry: no theorem was added (checker rules only).
