# MUSE-REPORT-640: Coordinator control-plane takeover and cleanup integration audit

## What was done
Adversarial integration audit of the supplied private snapshot
`.tmp/COORDINATOR.py` (2786 lines, sha256
`0ab771798da779638f90ea12db073fdac783fce01da086c68c7c0e89271496f1`)
against the reviewed contracts `dokumente/x86/COORDINATOR-FAILOVER.md`,
`dokumente/x86/LANE-CLEANUP.md` and `dokumente/x86/AGENT-MONITOR.md`.
Owned deliverable: `dokumente/x86/COORDINATOR-CONTROL-AUDIT.md` (new).
No source, Lean, Rust, checker or emitter file was touched; no live control
directory, other clone, provider binary, config, key or real agent was read,
run or signalled. Fixtures were clone-local stdlib with `ROOT`/`HERE`/`POOL`
repointed to private scratch (import without `__main__` side effects,
stubbed identity, cross-process flock test).

## Exact names
- New document: `dokumente/x86/COORDINATOR-CONTROL-AUDIT.md` (scope, method,
  5 verified strengths with line traces, findings B1/B2/M1-M9 with severity,
  CUTS). No new Lean definitions or theorems (audit lane, nothing to prove).
- Fixture (private scratch, not committed): `.tmp/scratch640/test_snapshot.py`
  — 31/31 checks passed (takeover-predicate boundaries, whole-action EX/SH
  lock holding, epoch refusal matrix, slot flock cross-process exclusivity,
  publication/merge/failover gate markers, atomic-write markers).

## Check results
- Fixtures: 31/31 passed (see above).
- `git diff --check`: clean.
- `./lean-bau`: NOT re-run. The diff adds only two Markdown files; zero Lean,
  Rust, manifest or wrapper inputs changed, so no build signal could attach
  to this lane. Master HEAD is `47f447d0`; tree is otherwise clean.

## Findings summary (details in the audit doc)
- Deployment stays correctly refused: `failover_start` gates on merged
  620/621 AND 636/637 plus exact blob/candidate approval match. No approval
  given here.
- B1 (blocking, already gated): 15-slot cap does not survive supervisor
  death from the snapshot side; the failover doc's best-effort footnote is
  exactly what 636/637 must close.
- B2 (blocking, in 636/637 scope): loop workers (`dispatch`/`watch`/`run`/
  `stop`) never check owner/epoch; enforcement is one-directional until the
  supervisor side lands.
- M1: `dispatch` loop honors no pause marker; `AGENT-MONITOR.md` overclaims
  this for dispatch (true only for `watch`). M2: pause-marker leak without
  `finally` in `register_tasks`/`cleanup_lane_tasks`. M3-M9 are minor
  (probe outside slot accounting but manual-only; headroom inconsistency;
  zombie counting; weak `stop` identity; cleanup TOCTOU; spawn on heartbeat
  rc==2; non-atomic observer JSON).
- VORSPANN verdict: PASS — all twelve registration composers and the
  prepare/launch path build prompts from `lanes/VORSPANN.md`; deletions only
  of merged registered idle tasks with reviewer snapshots taken first.

## Open / not audited
Supervisor `instrumente/coordinator-failover.py` was not supplied; B1/B2 close
only with its reviewed 636/637 integration. Live control state deliberately
uninspected. Full compiler/bridge validation remains OPEN regardless.

## Task feedback
The task's checklist is accurate and complete as written; the embedded 636/637
scope text (snapshot line 2100) already names every hard requirement this
audit found missing. One correction to a referenced doc, not the task:
`AGENT-MONITOR.md` should say `coordinator-pause.json` is checked by the
watch loop (and start paths check `pool-paused.json`), not by "the
dispatch/watch loops".
