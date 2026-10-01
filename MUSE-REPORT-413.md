# MUSE-REPORT-413: Adversarial implementation audit BUDGET-OBSERVATIONS

Lane 413, branch `muse/413`, base `0b3132b7` (unchanged during the lane).
Owned files only: `dokumente/x86/AUDIT-BUDGET-OBSERVATIONS.md` (new) and
this report. No Lean, Rust, checker, Spec, goal, emitter or model file
touched. Experimental probes kept private in `.tmp/` (git-ignored,
uncommitted).

## What happened this turn

The previous session's work was preserved (audit draft + two `.tmp/`
probes) but the audit file itself was damaged: its last write was cut
off mid-word, ending in a literal `...[truncated 3881 chars]` marker in
the middle of §5/D2. Sections §6 (stutter hunt E1-E3), §7 (prioritized
tasks) and §8 (evidence log + audit CUTS) were missing entirely.

This turn: (1) verified clone path and branch per LANE.md; (2) re-checked
every file/theorem/line citation in the preserved draft against the
tree at the same base; (3) re-ran both probes via `./lean-probe`;
(4) repaired the truncated tail with the complete D2 + §§6-8;
(5) committing audit + report.

## Corrections to the preserved draft (all verified by read/grep)

- `InvariantenOpt.lean` CUTS: `:533` -> `:517` (content confirmed:
  cost/ghost-budget transfer OPEN).
- `AufrufOpt.lean` CUTS: `:274-275` -> `:255` (budget-timing sentence
  confirmed verbatim).
- `MulDiv.lean` CUTS: `lines 527-529` -> `:521` (mapping-open sentence
  confirmed verbatim).
- `Byteschritt.lean` CUTS: `lines 473-476` -> `:452` (termination-OPEN
  sentence confirmed verbatim).
- `AccessList.lean`: `:264-265` -> `:238` CUTS, admission sentence at 265
  (both confirmed; the sentence sits inside the CUTS block).
- `TSO.lean` CUTS now pinned at `:551` (fairness sentence verbatim).
- `cas_schleife_unbeschraenkt`: `lines 270-277` -> `272-277`.
- New finding during repair: `MulDiv.lean` CUTS assigns the
  DIV/IDIV-to-`hardware` correspondence to "bridge lane 277", which has
  no row in `WORK-ALLOCATION.md` and no entry in `DIRECT-COMPILER.md`
  (grep, 2026-10-01). Booked in the audit as P3 allocation gap.

## Findings (see audit §§1-7 for evidence)

No false theorem, no hidden unsoundness. Three real edges, one
load-bearing, all landing on the same consumer (C3 CostSummary,
author 347 + reviewer 385):

- E1: failed-CAS stutter has no cost linkage (`casSchritt` failure
  returns unchanged state, `LockedOps.lean:83-96`; cost only via
  caller-supplied `casKosten versuche`, line 107; unboundedness proved
  at 272-277). Precision added vs draft: `casKosten` DOES take an
  attempt count — what is missing is the theorem linking executed
  failed stutters to that argument.
- E2 (new, found during repair): `lockKosten` has only `.xadd64` and
  `.mfence` arms (lines 100-104); CAS contributes nothing to it.
- E3: check elimination / inlining remove counted source steps with no
  cost delta (equalities `InvariantenOpt.lean:215-268`, CUTS at 517;
  `AufrufOpt.lean:255`).
- Plus P3 allocation gap (lane 277 named but unallocated) and the
  `laufBytes` fuel-`weiter` vs step-`weiter` tagging remark for lane 349.

## New definitions/theorems

None. This lane adds no Lean code by design (audit-only task).

## Verification

- `.tmp/probe413_budget.lean`: `./lean-probe` 0 errors (re-run
  2026-10-01, exit 0). Target step types take no budget/cost argument;
  shape costs compute; failed CAS is proved stutter.
- `.tmp/probe413_stops.lean`: `./lean-probe` 0 errors (re-run
  2026-10-01, exit 0; first attempt this turn hit the 300 s tool
  timeout on a cold cache, second run with a longer budget passed).
  `RufSchrittG` threads `passes`; `byteschritt` takes none;
  `md_div_halt`/`verweigert_heisst_halt` never imply a source stop.
- `./lean-bau` (full project build): NOT run. Justification: this lane
  changed zero files under `grammatik/`, `crates/`, `instrumente/` or
  any other build input — the commit adds one document plus this
  report. A 356-job build would consume shared-machine resources for
  no signal. Stated plainly so the merger can decide.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` introduced
  (no Lean files added or changed at all).

## Open / for the merger and follow-ups

- Line numbers in the audit are as-read at `0b3132b7` and will drift.
- C3 (347/385) acceptance criteria proposed in audit §7/P1.
- Lane 277 allocation gap proposed in audit §7/P3.
- Whether C3 bounds use syntactic caps, semantic progress arguments or
  profile admission, and whether gate crossings count as observable,
  are recorded as design choices for those lanes, not audited here.

Co-Authored-By: muse-agent-413 <muse-agent-413@noreply.invalid>
