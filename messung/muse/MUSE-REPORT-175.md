# MUSE-REPORT-175 (lane 175: the footprint condition as a checker rule)

Rust lane. The flagship's decidable footprint premise -- `FussS P S (lokK P K)` with
lock invariants, thread-local carriers and lock floors (both verdicts of 2026-09-14
agree this is the premise that decides which concurrent programs are in) -- is now a
checker rule: five new codes `N290`-`N294` at ERROR level. `E245`-`E249` compute the
older, stricter `fussOrtGB` and stay hints, untouched.

## What was done

`crates/gabbro-check/src/fusswache2.rs` (new, ~950 lines), wired in `lib.rs` beside
`sperrinv` (both call sites: timed and untimed `pruefe`):

- Threads: the `concurrent` members plus the `entry`/`boot` dispatch roots -- the
  `startexklusiv.rs` pool. Call graphs are reached over `aufrufgraph.rs` (resolved
  `rufe` keys); a function with indirect calls unions the E249 candidate pool
  (address-taken, else every function) -- the surface form of `AbgK` over indirect
  calls by signature. With no declared start the unit is single-threaded
  (`ziel_ort_einfaden`): one graph over every function.
- May-write is DECLARED permission (`writes`, plus `publishes`/`allocs` resolved to
  carriers), exactly what SATZKARTE §16.6 says `GetrenntK` judges. "Written by none"
  reuses the old writer-set direction (declared or performed).
- Guard data is reused, not repeated: `sperrinv.rs` grew `sperrdaten()` (per lock the
  resolved `protects` set + invariant presence -- the `N275` resolution, which the old
  E245-E249 walk never did); only ranks are read locally. Read detection
  (`carrier_root`, `clause_roots`, `body_roots`, `calls_with_spans`) is reused from
  `wirkungen.rs` (five `fn` → `pub(crate)` visibility lifts, no behaviour change).
- Legs: `N290` contracts, `N291` body reads per site with the held set
  (signature + enclosing `locks` stack), `N292` direct callee contracts at the call
  site (incl. `let-else` calls, which the shared walker misses and `H012` reads),
  `N293` indirect admission over the candidate pool, `N294` floors: takes and callee
  takes against signature-held outers, same-lock exempt. One refusal per
  (function, carrier, leg).

`crates/gabbro-check/src/saetze.rs`: sentence `wirkungen.fusswache2` (measured).
`crates/gabbro-check/tests/korpus.rs`: `N290`-`N294` in `BENANNT`.
`crates/gabbro-check/tests/fusswache2.rs`: 8 tests (legs fire, single thread /
guard-at-access / signature guard silent, `H006`/`H012` silent where `N294` fires).

Probes: `beispiele/124-two-threads-private.gab` (the `MehrfadenZeuge` shape, admitted),
`beispiele/125-read-under-lock.gab` (probe-C shape, admitted),
`beispiele/gift/952` (`N291` shared read), `953` (`N290` contract),
`954` (`N292` callee), `955` (`N294` floor, direct take).

Docs: README (391 diagnostics, 158 sentences / 150 measured / 335 codes, 107 examples,
665 gifts, 891 tests), DONE.md (same), TODO.md (`4634` → `4677` continuations, 0 glued).
`MARKE_EMIT` deliberately untouched (see §5).

## Corpus measurement (the task's "measure first")

Measured with the built binary over all 107 `beispiele/*.gab` (105 old + 2 new):

| class | files | old E245-E249 (hints) | new N290-N294 |
|---|---|---|---|
| no declared start (single driver thread: every carrier thread-local, `lokal()` ≡ true) | 98 | 18 files fire (E247; plus E246 ×6 + E248 ×5 in `22`, E246 ×1 in `96`) | 0 files, 0 diagnostics |
| one start (`11`, `57`, `60`) | 3 | `57`: E248 ×1 | 0 files, 0 diagnostics |
| multi-start, guarded/disjoint (`59`, `108`: guarded; `109`: disjoint + guarded at access; `07`: writeless extern graphs) | 4 | `59`, `109`: E247 hints | 0 files, 0 diagnostics |
| new probes `124` (concurrent pair, private tables + invariant) / `125` (shared read under its lock) | 2 | `124`: E245 + E246 + E247 + E248 ×3; `125`: E247 ×1 | 0 files, 0 diagnostics |
| `N294` over all 21 `requires Held` files | -- | n/a | 0: holders never take, and every holder→taker call is same-lock-exempt (`104` einzahlen→lies, `01`/`09` einsammeln→blatt_loeschen) or caller-floorless (`39` dienst, `48` aufraeumen) |

Result: **old rule 21 files (hints only, E249 silent throughout); new rule 0 files,
0 diagnostics.** The weakening lands exactly where the model says: single-threaded
drivers need no footprint check (`ziel_ort_einfaden`), lock-held reads need no
signature (`H007` holds the hold), private tables need no guard (`GetrenntK`).
The two new examples are the sharpest rows: the old check refuses the witness
(`124`) and the probe-C shape (`125`); the new one admits both.

## Severity: ERROR, and why it holds

The corpus stays green, and every refusal names a real defect by construction: a
shared carrier read bare (data race `H007` would also catch at the access -- but the
footprint question is asked here), a shared contract, a call into a shared contract,
an indirect pool leaking a shared carrier, a take below a held lock (deadlock shape
both rank rules miss because their chain starts empty). So all five refuse
(`ALS_FEHLER = true`). The old hints stay hints.

The one genuine floor gap found while measuring deserves naming: `H006`/`H012`
seed their chain with enclosing `locks` blocks only, never with signature-held
locks. `requires Held(HIGH)` + `locks LOW` (or a call into a `LOW` taker) is a
lock-order inversion no existing rule sees -- `N294` fires exactly there, and the
unit tests pin both rules' silence beside it.

## Verification (all run, all green)

- `./cargo-pruef`: exit 0, 0 failing -- full build plus the whole suite, including
  the 8 new `fusswache2` tests, `beispiele` (all 107 examples zero-error, so `124`
  and `125` are admitted), `gift` (`952`-`955` fall with their codes), and `korpus`
  (`N290`-`N294` in `BENANNT`). No warnings from any lane file (`lean_g.rs` /
  `certstmt.rs` carry two pre-existing unused-variable warnings from other lanes).
- `./lean-probe grammatik/Grammatik/MehrfadenZeuge.lean`: exit 0, 0 errors.
- `./lean-bau`: exit 0, `Build completed successfully (180 jobs)`, 0 error lines
  (only pre-existing linter notes). No `.lean` file was touched by this lane.
- One fix came out of verification: the `N290`-`N292` message read
  "no other thread writes it -- and some function writes it", which is
  self-contradictory (the refusal fires exactly when another thread DOES write
  it). Now: "it is not thread-local -- another started thread writes it".
  Rebuilt, both suites re-run green.

```bash
cargo test --no-fail-fast -p gabbro-check          # via ./cargo-pruef (slot queue)
./instrumente/pruefe-emission.sh                   # NOT run: emitter untouched by this
                                                   # lane; expect MARKE_EMIT 105 -> 107
./instrumente/zaehle-gifttreffer.py                # NOT run: 955 sauber by construction
                                                   # (N294 alone); 952/953/954 begleitet
./instrumente/pruefe-kennungen.py --sprechprobe    # NOT run: N290-N294 only in fusswache2.rs
./instrumente/pruefe-zahlen.py                     # NOT run: TODO.md 4677 counted by hand
                                                   # (43 new continuations, 0 glued)
```

Expected mark movement (all reported, none touched): `MARKE_EMIT` 105 → 107 (the
two new examples emit; left for the merge to re-measure per the mark's own rule --
lanes do not book it). `MARKE_EMIT_G` stays 12 (all four gifts fall at the checker
and emit nothing).

## Boundaries (named, not silent)

- No `AbgK` refusal: the fixpoint is closed by construction over direct edges;
  indirect calls over-approximate via the pool. A closure check would need a sixth
  code; none is reserved.
- `let-else` argument reads are not body reads (same blindness as `sammle_taten`);
  `let-else` calls ARE call edges (added, `H012` precedent).
- `N294` reads hull `locks` as takes (the `H012` over-approximation); unknown ranks
  skip the function (`H014` owns them).
- Same-lock takes are exempt (the real re-take is `H003`'s); signature-held outers
  are the whole of `N294` by design, so it can never double-fire with `H006`/`H012`.
- Dead functions (in no thread graph) write nothing as far as locality goes -- the
  Lean semantics (`K` covers started threads); their writes still count for
  "written by none".
