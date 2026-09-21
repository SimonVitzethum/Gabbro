# Fix lane F3 — the `child` block as its own thread (review G11 F2–F6)

*2026-09-21/22, branch `review-0921-integration`, on top of F2 `0b507977`. Built and
measured LOCALLY (fisch unreachable, Simon 2026-09-21). All of this was latent: `C185`
(emitter) and `LG004` (exporter) refuse every `child` block. It must stand before lane 258
lifts `C185`.*

## 1. What was fixed

| # | review finding | fix | where |
|---|---|---|---|
| 1 | G11 F2 (HIGH): `fusswache2::begehe` walked `child` with the parent's held set; `child` inside `locks L` counted as holding `L`; child accesses to globals were no thread's | **`N456`** (new): a `child` inside a `locks`, `observes` or `breaking` block, or in a function holding a lock by signature (`requires Held`), falls. The held-set walkers restart the child with an EMPTY held set, the function's `effects { locks … }` line included: `fusswache2::begehe` (`N291`), `geteilt::schutz` (`H007`), `rcu_schutz` (`H009`/`H010`), `fenster_sammeln` (`H018`). **`N457`** (new): the child region is judged like a pool routine -- every table, mutable static, `state` or arena it touches, itself or through any function reachable from a call on it (indirect pool included; callee writes, `allocs`, footprints), that ANY code writes, is guarded by a lock, atomic or per-core | `clone.rs` (`kontextpfade`), `fusswache2.rs` (`kindfaeden`, `begehe`), `geteilt.rs` |
| 2 | G11 F3 (MED): the spill read set was `emit::benutzte_namen`, which skips `grow` and lock places | new exhaustive walker `clone::kindzugriff` (matches every `StmtArt` by name, no `_` arm; expressions via `crate::alle_ausdruecke`; call targets, `&f`, arenas, lock places, `sizeof`/`lenof` places). `N451`/`N452` read it; `N457` reads its names and calls | `clone.rs` |
| 3 | G11 F4 (MED): `N450` counted stack gates unit-wide | `N450` per region (`torpfade`): a stack-gate call must DOMINATE the region (stand before it on every path of the same body -- structured dominance, sub-block calls do not leak), and one call hands to ONE region statically (a second region in sequence or in a sibling branch falls). One issuance site, two message forms | `clone.rs` |
| 4 | G11 F4: the in-between code is sound only under the unstated "jump into the child" lowering | written down in PLAN-SYSCALL (binding on the lowering), the `klon.uebergabe` sentence, SATZKARTE §39, SYNTAX §12.1, `C185`'s message and the emit comment; **pin test** `tests/klon_faden.rs::c185_traegt_die_sprungannahme` asserts that 155 falls at `C185` exactly once and that the message carries the assumption -- the lane that lifts `C185` turns it red | docs, `emit.rs`, test |
| 5 | G11 F6: other child-blind walkers | audit below | — |

Also: `saetze.rs` new sentence `klon.faden` (N456/N457); `klon.uebergabe` and `klon.spill`
updated (N450 per region, jump assumption, `KlonAnnahme` -> `CloneAssume`, G11 F5);
AGENTS §7 ledger (next free N458, gift 1148); TODO O-1 row; OFFEN **O21** (new).

## 2. Probes

| gift | expects | shape |
|---|---|---|
| 1139 | `N450` | gate call only in another function |
| 1140 | `N450` ×2 | second region behind one call; gate call only in a sibling branch |
| 1141 | `N456` (+`H007`) | the review's `locks L { g = 1; child { g = 2; ausgang(0); } }` |
| 1142 | `N456` | child under `requires Held(L)` |
| 1143 | `N457` | child writes an unguarded static the parent writes |
| 1144 | `N457` | the same write through a callee |
| 1145 | `N457` | child reads a carrier the parent writes |
| 1146 | `N451` (+`N457`) | gate answer read in `grow … else` |
| 1147 | `N451` (+`E006`, `H016`) | caller `let` as a lock index (indexed locks are refused anyway today; the probe pins that the spill rule no longer leans on that) |

Positive twins in `crates/gabbro-check/tests/klon_faden.rs` (14 tests, all green): a child
taking its own lock around a guarded write checks clean; a child reading a carrier nobody
writes checks clean; two regions each behind their own call (the second reading the slot
the second call handed) check clean; plus `H007` firing on a child write in a function
whose only cover is the `effects { locks L }` line.

Gifts changed: `1109`/`1110` now call the gate before the region (per-region `N450` would
otherwise fall beside their one code); `1117` falls with `N450` beside `N452` and is no
longer `allein` (header now `-- erwartet: N452`).

## 3. Measured (local machine, `free -g`: 31 GB total, 20 GB available at every run)

- `cargo test --no-fail-fast`: **69 collections, 1266 passed, 0 failed, 1 ignored**
  (baseline 68 / 1252 / 0 / 1; +1 collection `klon_faden`, +14 tests).
- `instrumente/pruefe-emission.sh`: **ALL PASS** -- 37 pierced, 288 of 288 compile, 2
  reverse probes (same as F2). No `MARKE_EMIT` counter moved.
- `lake build` (grammatik, untouched): **281 jobs green**; `gabbro_ziel` depends on
  `[propext, Classical.choice, Quot.sound]`.
- `pruefe-saetze.py`: 55 codes without sentence (ratchet 55, unchanged; 181 sentences).
  `pruefe-kennungen.py`: ALL PASS (435 codes). `pruefe-todo.py`: 16 findings (baseline 16).
  `pruefe-englisch.py`: German comment lines 7965 before and after. `pruefe-zahlen.py`: 37
  findings before and after (only already-red counts moved: codes 433 -> 435 etc.).
- **Corpus diff** (old = F2 binary, new = this lane; every `beispiele/*.gab` and
  `beispiele/gift/*.gab`, 892 files): **10 differ** -- the 9 new gifts and `1117` (+`N450`).
  **All 127 examples unchanged**, including 155/156 (checker-clean).

## 4. Audit of child-blind walkers (item 5)

A scan (`kratz/review-0921/F3/blind2.py`) lists every function that matches `StmtArt` with
a `_` arm, names a block-carrying statement, and neither names `Child` nor descends via
`crate::unterbloecke`:

| walker | verdict |
|---|---|
| `certstmt::drucke_seq/_ende/_ende104`, `corrlean::gblock`, `gegenbeispiel::*`, `obligations_g::*` | reporting / G-export tools: `child` is refused by `C185` / `LG004` before they matter |
| `emit::funktion`, `rumpf_als_wert`, `zaehler_definition` | emitter: `C185` refuses the block |
| `m1::endet_immer` | `child` -> `false`, the safe direction (G11) |
| `m1::steige`, `m1::frische_gebrauch`, `fusswache2::stand_liest` | per-statement or per-expression, descent is elsewhere (M1 `unterblock`, `begehe`) |
| `domaene::binde`, `kosten::binde`, `parse::letform` | binding collectors; `child` binds no name |
| `zeremonie::anweisung` | a count |

`schleifen.rs` and `kosten.rs` (`schleifenzusagen`, `sperrbloecke`) already carry `Child`
arms (G11 `10814bd0`, `44d3e639`, in this branch). The deeper class is walkers that DO
descend via `unterbloecke` but carry parent context into the child. Held sets are handled
(section 1). Arena counters are moot because `N457` refuses a child touching an unguarded
arena that anyone writes. **M1 value facts about guarded globals and phase/pairing state
were NOT re-audited** (OFFEN O21).

## 5. Open, and why

- **No child thread in the model** (G11 F1, fix lane F9): `N456`/`N457` are Rust rules
  with no Lean counterpart.
- **`N457` is fail-safe, not precise**: a carrier written only before the gate call still
  counts as written, and a child that is the only writer still falls (nothing bounds how
  often the gate runs). No corpus program pays for it.
- **The jump assumption** is written down and pinned, not checked: lane 258 must keep it
  or re-check the in-between code.
- Flow facts other than held sets (O21).

Commit: see `git log` (this lane's single commit on `review-0921-integration`).
