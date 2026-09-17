# MUSE-REPORT-244 — efficiency fixes: census re-measured, nothing to fix, no code changed

Lane 244 (TODO §-1 wave D). Scope: `messung/SPEICHER-CENSUS.md` (lane 238) top-3 sites, in order, fixes only.

## Verdict in one line

The census is fresh (re-measured byte-identical, see §1) and **none of its top-3 sites is an actionable overhead**:
every non-zero delta is functional payload, deliberate, or a different implementation that is not an equivalent.
Per the exclusive scope ("measured sites only", "MUST NOT touch anything the census does not blame",
"NOT Lean", "no OS surface", "a fix that moves a verdict is not a fix") and the safety rule
(no guarantee weakened to make a wall go green), this lane changes **zero files** outside this report.
Corpus verdict diff is 0 by construction; `MARKE_EMIT*` untouched (deltas reported in §4).

## 1. Re-measurement (my numbers, gcc 13 `-std=c11 -O0`, rustc 1.97.1 `-O`, x86_64)

Scratch probes lived in `.tmp/census244/` (ignored by git) and were removed after the run.
Emission spellings read off `crates/gabbro-check/src/emit.rs` (`fn arena`, line 3866) and `laufzeit/start.c`.

| site | emitted C | Rust `repr(C)` equiv | delta | census said |
|---|---|---|---|---|
| S1 table count 2 `{stand: u32}` | 8, al 4 | 8, al 4 | 0 | 0 — confirmed |
| S5a arena u32 hi 16 (`buf[16]` + `used`, `used@64`) | 68, al 4 | 68, al 4 | 0 | +4/+0 payload — confirmed |
| S5b arena u8 hi 10 (`used@12`) | 16, al 4 | 16, al 4 | 0 | +4/+2 payload+pad — confirmed |
| S6 linear token `{uint8_t nichts;}` (emit.rs:2005) | 1, al 1 | `()` 0 | +1 deliberate | +1 — confirmed |
| S2a/S2b record slots | 8, offsets match | 8 | 0 | 0 — confirmed |
| S8 tagged (`last@8`) | 16, al 8 | 16, al 8 | 0 | 0 — confirmed |
| S3/S4 atomics | 4 / 1024 | 4 / 1024 | 0 | 0 — confirmed |
| runtime `pthread_mutex_t` / `pthread_t` (start.c:53,155) | 40 / 8 | `Mutex<()>` 8 (not an equivalent) | n/a | 40/8 orientation — confirmed |

## 2. Per-site ledger (ranked order of the census §3)

1. **Lock object, 40 B per lock — NO FIX, 0 bytes.** Not in the emitted unit (the unit only
   declares `void L_nimm(void);`); it is the hosted-POSIX runtime object in `laufzeit/start.c`.
   The 8 B Rust `Mutex<()>` is futex-based std, a different implementation, not an equivalent —
   the census itself marks it "orientation only". Shrinking it (futex word, ticket lock) is a
   runtime-implementation choice owned by lanes 245/247, not a layout fix, and not mine.
2. **Arena `used` counter, 4 B + up to 3 B alignment padding — NO FIX, 0 bytes.** The counter is
   functional payload (`alloc` bumps it, `reset` zeroes it; checker rules N210–N214 reason about
   it) and the padding is alignment-inherent, byte-identical in Rust. Removing it would weaken
   the arena discipline — forbidden by the safety rule. This is the correct shape for the
   `PLAN-DYNAMISCH.md` §6 descriptor too (`committed` + `base` are likewise functional words).
3. **Linear token, 1 B vs ZST 0 B — NO FIX, 0 bytes.** Deliberate: C has no addressable
   zero-sized type; the byte is never read. Programs that need zero bytes already have
   `linear ghost type` (S7, total erasure, 0 B). Nothing to kill.

Everything else in census §1 deltas at exactly 0 — explicitly out of scope, untouched.

## 3. emit.rs specification list for wave C

**Empty — no changes requested.** There is no emission-blamed non-zero delta: the only emit.rs-adjacent
bytes (`used` counter shape, token byte) must NOT change (see §2). Wave-C input from this lane:
pin the §1 "Emitted" column as the byte budget; any layout change that moves one of those numbers
breaks the census. `emit.rs` stays owned by lane 227 until wave C per the task.

## 4. Gates and markers

- `./cargo-pruef`: exit 0, **0 failing tests** (all `test result: ok`, 0 failed lines).
- `./emission-pruef`: exit 0, **ALL PASS — 37 executed, 286 of 286 translate**, 2 reverse probes;
  ASan stage: 36 units, no finding. (One pre-existing warning: `certstmt.rs` private-interface
  `DeclInfo`/`zeige_rumpf` — not mine, not touched.)
- `./lean-bau`: `Build completed successfully (274 jobs).` — no Lean files touched.
- Corpus verdict diff: **ZERO** (no checker/emitter/runtime file changed; nothing to re-run beyond
  the gates above, which are green on the identical tree).
- New codes: none. New probes: none (no fix needing a pin; no gift numbers taken).
- `MARKE_EMIT*` deltas: **all zero** — file untouched
  (`MARKE_EMIT=123`, `MARKE_EMIT_M=143`, `MARKE_EMIT_G=18`, `MARKE_EMIT_N=2`, `MARKE_EMIT_P=1`,
  `MARKE_EMIT_L=1`, as read in `instrumente/pruefe-emission.sh`).

## 5. New definitions / theorems

None. No Lean file created or modified; no Rust file created or modified. Rule-13 witnesses:
not applicable (no theorem added).

## 6. What remains open / believed-wrong in the task setup

1. **Assignment conflict (for the orchestrator): `PLAN-DYNAMISCH.md` §10 assigns lane 244 the Lean
   sketch `ArenaDyn.lean` + Spec-header assumption texts, while TODO §-1 wave D and this task assign
   lane 244 the efficiency fixes.** I executed the task prompt (efficiency) as authoritative and built
   neither the fixes (nothing actionable, §2) nor the Lean sketch (exclusive scope forbids Lean model
   change; reviewer rule forbids changing existing files). The `ArenaDyn.lean` work (DynForm, four
   theorems, refinement, two (d) assumption texts) is therefore **unbuilt and needs reassignment**
   to a new lane number.
2. **The efficiency budget reference ("at most proved plumbing over Rust", TODO §-1 wave D /
   PLAN-DYNAMISCH §8 X = 10%) has no static-vs-dynamic pair to measure yet**: dynamic arenas
   (`max`/`grow`) do not exist in the tree (lanes 240–242 not built). When they land, the tally
   method is ready: static checked-`alloc` immediate vs dynamic `committed` word load on
   `beispiele/98`, `99` plus the §1 budget column as the byte pin.
3. **Census cuts (accepted, not re-measured):** x86_64 Linux only (S8 al-8 row needs an aarch64
   re-measure when that platform starts); thread-stack figure is the `ulimit -s` default, not a
   per-unit constant; shapes read off emit.rs spellings, not a `gabbro emit` run per shape.

## CUTS

Nothing built, so nothing is half-proved. What is not done: any byte reduction (none exists without
weakening a guarantee — §2 is the finding); the `ArenaDyn.lean` sketch (needs a new lane, §6.1);
the static-vs-dynamic op tally (blocked on lanes 242/243, §6.2). No `#print axioms` (no theorems).
