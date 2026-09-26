# MUSE-REPORT-267 — O10 executed, O24 narrowed (no G form: costed, not built)

Lane 267 delivers 9 executed differential runs over the driver-capability
probes (OFFEN O10), one probe repair (H018), and an honest narrowing of the
string-certification half (O24): no `Ty` extension, no exporter change, no
new refusal code. Register totals are unchanged (23 CERTIFIED / 180
UNCERTIFIED, byte-identical to HEAD).

## 1. O10: "measured writable" now means "runs and does what it claims"

New script section `-- 27` in `instrumente/pruefe-emission.sh` (9 `lauf`
runs, each with hand-written driver, hand-computed expectation, gift
mutation and booked certificate line). All 9 are green through stages
1–8 (`-O0`/`-O2` equal, UBSan clean; ASan `NICHT GEFAHREN` on this host,
as for every other run):

| run | probe (rows) | expectation |
|---|---|---|
| sonde-poll-used | poll-used (#14, #15, #16, #26) | `7 100` |
| sonde-kick | kick (#9) | `52 18 7 0 0` |
| sonde-merkmale | merkmale (#5, #6) | `137438953504 1 1` |
| sonde-warteschlange | warteschlange (#7, #30 helper) | `1 8 3 65536 … 0 1 1 0 3` |
| sonde-ruecksetzen | ruecksetzen (#4) | `3` |
| sonde-ecam | ecam (#1, #2, #3 partial) | `268435712 4831838720 4 … 0 0 1` |
| sonde-region | region (#19, #20, #23) | `1 4096 8192 … 20480 512` |
| sonde-netz | netz (#10, #28, #29) | `4294967295 65535 … 61183 0 0 0` |
| sonde-besitz | besitz-zwei-typen (#17, #18, #25) | `sahsfauf 9` |

New counts: of the 24 "measured writable" rows, **21 are now executed**
(two partial: #3 transport-as-value, #30 helper-direct only), **1 is a
refusal probe** (#24, execution N/A — the refusal IS the measurement),
**1 stays composition** (#27, openly unmeasured per its own footnote),
and the 6 in-file rows (#8, #11, #12, #13, #21, #22) are reclassified as
"in the driver file, not executed" rather than counted as probed.

Honest residue (each named in the section header comment):
poll-used's empty completion (needs a concurrent u16 wrap — the bounded
wait diverges first); merkmale's low-half mask (static fake has no
selector; the mask is M101's, measured when the silent truncation fell);
`beide_warteschlangen` end-to-end (needs per-queue device state);
ruecksetzen's spin path (nothing single-threaded clears the cell mid-wait);
`beispiele/66` deliberately NOT executed (the weak ghost-token artifact;
the strong two-type form runs instead).

## 2. Probe repair: warteschlange was red before this lane

`probe-transport-warteschlange-aufsetzen.gab` failed `H018` (unguarded
DMA+doorbell handoff, rule added 2026-09-10 in `b62de25c`, after the
probe). Repaired by holding the guard, not by weakening: new
`lock EINRICHTUNG … held <= 1000 ops` across both halves, `locks
EINRICHTUNG` in both functions' effects. Now `13 items, 0 errors`.
Side finding: the `+= 1` counter idiom from gift 725 falls at `M104` on
today's checker (the gift itself reproduces it) — the lock is held
without a counter touch.

## 3. O24: why no string program becomes CERTIFIED

The task asks for a G form for `string max N` plus exporter coverage for
params/results/lets, literals, lenof, index, copy, concat, comparison.
Measured cost, then the decision:

- The G model (`grammatik/Grammatik/Typen.lean`) has NO string `Ty`:
  constructors are int/bool/opt/sum/grund/never/fl/fnptr/ptr. A G form
  needs a new `Ty` constructor plus `Val`, `Expr` forms, the `Akzeptiert`
  checker component, and every exhaustive match extended (38 `| .int`
  sites over 15 files alone, plus Semantik/MitRuhe/EinpassenVoll and the
  goal-theorem proofs), a `Spec.lean` diff, and certificate regeneration.
  That is a multi-lane model change with a review round — not one lane,
  and not without breaking `./lean-bau` green in between.
- `crates/gabbro-check/src/lean_g.rs` (5381 lines) contains ZERO string
  handling today; the Rust half is bounded, the Lean half is the long pole.
- What I verified instead (narrowing, with runs): `N465` still refuses
  strings in aggregates (measured probe, stays refused — the deliberate
  cut holds); `extern fn` with a string parameter checks AND emits the
  struct by value (no NUL, no `char*` confusion possible at the C type
  level; reads past `len` are foreign-code behaviour, i.e. trust base).
- Register before/after: **23 CERTIFIED / 180 UNCERTIFIED, identical** —
  regeneration would be a no-op; the 6 string programs (161, 1123, 1124,
  1126, 1127, 1159) stay LG002/LG003. "What would close the rest" in O24
  is now costed above; the max-approximation, Char-bridge and aggregate
  rows are unchanged.

## 4. Verification (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` —
  `== total: 1395 passed, 0 failed, 1 ignored`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (343 jobs)`).
- `./emission-pruef`: `== exit 1`, and the ONLY finding is the booked
  counter — `FUND: 153 statt 152 emittierende Dateien in messung/*/`.
  The repaired warteschlange probe emits now (it fell at H018 before),
  so the count moves by exactly one. MARKE_EMIT_M untouched per
  instructions; the merger re-measures (152 → 153).
- `MARKE_EMIT` (beispiele/), `MARKE_EMIT_G` (gift/): no delta — no new
  files, no new refusals.

## 5. What I believe is wrong in the task

- "Regenerate the certificates … so 161 and the string positives become
  CERTIFIED" presupposes the exporter change; without the `Ty` extension
  there is nothing to regenerate with. The premise and the conclusion
  belong to two different lanes (model + review, then exporter + certs).
- The reserved codes N541–N545 and gifts 1311–1320 are untouched and
  still free — no new refusal was needed for either half.

## 6. Open / for the merger

- Re-measure `MARKE_EMIT_M`: 152 → 153 (one repaired probe emits).
- O24 G form: needs a `Ty.str` model lane with Spec-diff review, then an
  exporter lane; this report costs it, it does not start it.
- O10 residue: threaded device models for the spin/wrap paths; probes for
  the 6 in-file rows; the #27 orchestration assembly.

Co-Authored-By: muse-agent-267 <muse-agent-267@noreply.invalid>
