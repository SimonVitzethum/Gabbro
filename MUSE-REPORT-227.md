# MUSE-REPORT-227 — switch lowering for integer match (TODO §-1 wave B)

Lane 227. Scope: `crates/gabbro-check/src/emit.rs` (lowering) +
`crates/gabbro-check/tests/intmatch.rs` + 5 gift probes (1072–1076) +
the census row in `instrumente/pruefe-cformen.py` the task requires.
No checker, no Lean, no `MARKE_EMIT*`, no OS surface.

## 1. What was built

**Lowering** (`emit.rs`, new items: `match_int`, `intpat_werte`, `int_grenze`,
`int_fall_text`, const `INTPAT_SPANNE`): a `match` in which ANY arm carries
lane-222 `intpat` is routed to `match_int` from `match_option`, AFTER the
tagged/reason/option lowerings. Consequences, all deliberate:

- All-variant matches are byte-identical to before: lane 222's refusal matrix
  (MUSE-REPORT-222 §3) is unchanged — tagged+int arm still refuses at the
  `tagged` exactness rule, option+int arm at the Some/None rule.
- All-integer matches over an integer scrutinee (C type read off `wert_ctyp`:
  the 8 int words plus `bool`; plain `index into T` arrives as `uint32_t`)
  lower to `switch (<expr>) { case N: { … } break; … }`, one `case` per exact
  arm, one stacked `case` per value of a range arm (`0 .. 255` inclusive,
  `0 ..< 256` exclusive). The header holds the scrutinee expression exactly
  once — a `switch` evaluates it once, so no temporary is needed even for a
  call scrutinee (unlike the `tagged` lowering).
- No `default`, no `__builtin_unreachable`: exhaustiveness is lane 228's.
  Emitting either would hand the C compiler a closedness decision no rule
  has made.
- Five `C001` refusals, all measured with probes: mixed integer/variant arms;
  non-integer scrutinee under integer arms; duplicate value across two arms
  (C rejects `duplicate case value`, so the emitter refuses instead of
  emitting what `cc` must refuse); range wider than 256 values
  (`INTPAT_SPANNE` = the canonical 256-way dense width of TODO §-1 — past it
  the spelling is an unfolding, not a lowering; split with `if` guards);
  inverted/empty ranges; bounds past `2^127` / values past `u64::MAX` /
  below `-2^63` (no C spelling).
- No new diagnostic codes: the emitter speaks `C001` only. **N411–415 are
  untouched** (left for checker lane 228 if it needs them). Gift pool
  1072–1076 is fully consumed (one probe per refusal class).

**Tests** (`crates/gabbro-check/tests/intmatch.rs`, 11 tests, all pass):
exacts, inclusive-range stacking, exclusive-bound drop, negatives over `i32`,
`u64::MAX` with `u` suffix, and 6 refusal rows (duplicate, overlap,
>256-range, inverted, mixed, tagged scrutinee). Gift files
`beispiele/gift/1072–1076` (`-- erwartet: C001`) all pass through
`jedes_gift_faellt_mit_seinem_code`.

**Census** (`instrumente/pruefe-cformen.py`, additive only): new rows
`stmt:switch-int` / `stmt:case-int`, state (iii) with `KNOWN_UNCOVERED`
entries dated 2026-09-17 naming lane 228 as lemma owner. Numeric `case N:`
(both `case N: {` and stacked bare `case N:`) classifies as `case-int`;
`switch` headers over non-bare scrutinees classify as `switch-int`
directly; bare-name integer headers are reclassified from `switch-reason`
by their first case in a per-body post-pass (both lowerings place the
first case directly under the header; anything else keeps the provisional
row — conservative). Zero count movement on today's corpus (verified by
diff: only the two booked-unseen rows appear as "may be removed"); the new
rows were proven to fire on real emission (dense/sparse/range/mid probes:
1× switch-int + N× case-int, no leaks, no unclassified).

## 2. Density choice: `switch` always — measured, loser documented

Generated (scratch, `.tmp/int227/`, not committed) with the built binary,
gcc 13.3 `-O2`:

| shape | emitted | compiled to |
|---|---|---|
| dense identity, 256 contiguous exacts | 794-line `switch` | 5 instructions, branchless (`cmpl $255` + `cmovnb`) — no table, no branch |
| mid density, 64 contiguous shuffled | `switch` | compiler-built 63-byte table in `.rodata` (`CSWTCH.1`, `movzbl`) — the jump table, earned by density |
| sparse, 8 values over 0..4·10⁹ | `switch` | compare/branch chain (`cmpl`/`je`/`ja`) — no table |

All three accept `cc -std=c11 -Wall -Wextra -Werror`. The loser — an
explicit emitter-side jump table (256 outlined functions + function-pointer
table, same dispatch): 32944 vs 1232 bytes object (**27×**), dispatch is an
indirect `jmp *(%rax,%rdi,8)` that can never simplify to `cmov`, kills
inlining, and needs non-standard C (computed goto) or outlining to spell
statement arms at all. Verdict: emit `switch`, let the C compiler earn the
table exactly where density pays. No jump-table code was added.

## 3. Verification

- `./cargo-pruef`: `== exit 101; failing tests: 1` — the single failure is
  `lane222_depth_stands_fourfold_over_corpus`, **pre-existing at HEAD and
  independent of this diff** (proven: the test walks only top-level
  `beispiele/*.gab`; this diff adds none; the walked set is byte-identical
  with/without it). Cause: merged lane-236 example `148-ftp-alg-daten.gab`
  nests 12 deep, so `12*4 > TIEFE_MAX=32`. Fixing it means bumping the
  parser constant with fuzz evidence — lane 222's business, out of scope
  here. Everything else passes, including the 11 new `intmatch` tests and
  the full `beispiele` suite with the 5 new gift probes.
- `./emission-pruef`: `== EMISSION: ALL PASS -- 37 durchgestochen, 286 von
  286 uebersetzen, 2 umgekehrte Probe(n) ==`. **MARKE_EMIT delta: 0** on all
  seven counters (123 / 18 / 143 / 2 / 1 / 1 / 0): the 5 gift probes refuse
  and never count; no top-level example added.
- `./lean-bau`: `Build completed successfully (276 jobs)` — no Lean inputs
  changed.
- `pruefe-cformen.py`: exit 1 before AND after with the identical single
  pre-existing unclassified line (lane-221 file `140-atomic-array-counter.gab`
  CAS fragment); zero count movement from this lane.
- `pruefe-saetze.py`: exit 0 (no new codes, no sentences owed).
  `pruefe-englisch.py`: red identical to stashed baseline (7961/7949,
  37/26, 5/2 — all pre-existing per MUSE-REPORT-222); this diff contributes
  zero German.

## 4. What remains open

- Lane 228: integer-match exhaustiveness (checker) + correspondence lemma
  for `switch-int`/`case-int` (moves the two census rows from state (iii)
  to state (i)); overlap semantics (which arm wins — the emitter only
  refuses duplicates).
- Wide ranges (>256 values) have no lowering — by design they belong to
  `if` guards, whose exhaustiveness design is 228's.
- Pre-existing reds for their owners: TIEFE_MAX ledger (222/236),
  cformen unclassified 140-line (221), englisch ratchets.

## 5. Where the task letter is wrong (findings, not deviations)

1. The wave-5 preamble ("INDEPENDENT REVIEWER: do not change any existing
   file") contradicts this task's deliverable 1 (the lowering in `emit.rs`,
   which the task itself calls mine until wave C). The task wins; the
   conflict is recorded here.
2. "Including the default arm": lane-222's AST has NO default-arm syntax
   (`MatchZweig` = variante/binder/intpat only) — there is nothing to
   lower, and per the task itself a missing default is not mine to add.
   Emitted switches carry no `default`.
3. "The flat comparison chain lane 222 measured at 1797 ops": 1797 ops is
   the atomic-array counter cost (TODO §0), not a match-chain measurement.
   The real density numbers are in §2 above.
4. The MUST-NOT file list forbids everything but `emit.rs`/`tests`/probes,
   while the task also orders the `pruefe-cformen.py` row ("never silent").
   The row is added (minimal, additive, zero-diff); without it every
   integer switch would misbook as `switch-reason` under lemma
   `gcorr_onGrund` — the exact silence the task forbids.
