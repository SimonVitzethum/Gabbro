# MUSE-REPORT-595: Portable completion and workforce monitor

Lane 595. Branch `muse/595`, clone `/home/simon/Dokumente/gabbro-muse/a595` verified before work.

## What was delivered

Owned paths only: `instrumente/agent-monitor.py`, `dokumente/x86/AGENT-MONITOR.md`,
`instrumente/tests/test_agent_monitor.py`, this report. No other file touched;
no Lean, Rust, checker, emitter, Spec/goal or optimiser file changed.

1. `instrumente/agent-monitor.py` (new, ~440 lines, standard library only).
   Read-only monitor over registered lane state. CLI: explicit `--state-dir`,
   `--manifest`, `--proc-root` (real `/proc`, fixture root in tests),
   `--interval`, `--once`, `--status-out` (atomic tmp+rename JSON),
   `--events-out` (append-only JSONL with flush+fsync), `--seen-file`
   (restart-dedup store), `--pause-file`, `--model-substr`, `--max-active`,
   `--stale-secs`, `--mem-reserve-kib`, `--log-dir`, `--report-dir`.
   Observes only registered lanes (manifest `lanes` + review reviewers/authors);
   checks `model_pid`/`runner_pid` by cmdline identity (`coordinat`+lane for
   runners, `opencode`+lane for models) without printing or storing cmdlines;
   unreadable cmdlines fail closed as alive/`unknown`. Detects completions
   (transition to `report_ready` with state `candidate_refs` head where present,
   `null` otherwise), transitions, dead (active status, no live managed PID),
   reused/foreign PIDs (alive PID, identity mismatch, not counted), wrong-model
   markers, stalled heartbeats (state `updated` / log mtime vs `--stale-secs`),
   model-vs-runner counts, under-utilisation (active < max with pending lanes),
   and blockers: `resource` (MemAvailable below 8 GiB reserve), `paused`,
   `dependency` (reviewer waits for non-ready authors), `build` (terminal
   `runner_error`/`incomplete`/`needs_coordinator_fallback`/
   `stopped_for_directory_audit`), `dead`, `reused_pid`, `stalled`. Verdicts come
   only from exact `VERDICT:`/`CANDIDATE:` lines under `--report-dir`; nothing is
   inferred from a green build. Pause auto-detects sibling `pool-paused.json`
   and `coordinator-pause.json`; when paused the report states auto-actions must
   stop. Never imports or runs the coordinator, holds no locks, kills nothing,
   sends nothing, reads no environments/configs/keys. Completion events deduplicate
   across restarts via the seen file (lane + status + updated + head).
2. `instrumente/tests/test_agent_monitor.py` (new, 11 unittest cases, fixtures in
   `$TMPDIR`-adjacent clone `.tmp`, never `/tmp`): clean running model/runner
   counts, finished completion with verdict + head, no-verdict-without-report,
   dead, reused-PID mismatch, wrong-model marker, explicit pause, restart dedup,
   dependency blocker + under-utilisation, stalled heartbeat, unreadable-cmdline
   fail-closed. Result: `Ran 11 tests ... OK`.
3. `dokumente/x86/AGENT-MONITOR.md` (new): shell commands for single/continuous/
   live-tree/fixture runs, input/output reference, pause and integration contract,
   current registry assumptions from the 2026-10-01 snapshot, and limits
   (author-lane heads are `null` by design; exact identity stays with the review
   snapshot).

## Evidence (actually run, not claimed)

- `python3 instrumente/tests/test_agent_monitor.py` → `Ran 11 tests ... OK`
  (after two small fixes, both in owned files; see below).
- `python3 -m py_compile instrumente/agent-monitor.py` → clean; `--help` lists all flags.
- Smoke run against a scratch copy (clone `.tmp`, removed afterwards) of the
  private snapshot shape (246 manifest lanes, 115 peer reviews, 212 state files,
  fixture proc root): first `--once` pass reported `active=2 models=0 events=4
  paused=False`, blocker kinds `dead/dependency/stalled`; rerun emitted 0 new
  events (restart dedup holds on the real registry shape).
- No `./lean-bau` run: this lane adds no Lean file and no `Grammatik.lean` import,
  so no new Lean build is owed or claimed. No `./cargo-pruef` run: no Rust file
  touched.

## Fixes found while testing (both corrected in owned files)

- Model identity first used the manifest model basename
  (`muse-spark-1.3-contributor`) as the cmdline marker, but the live binary is
  `opencode`; corrected to match `opencode` + lane (custom `--model-substr`
  without `opencode` still overrides).
- One test assertion on `under_utilised` was written backwards; corrected to assert
  the true condition (active < max with a pending reviewer lane).

## What remains open / precise CUTS

- The monitor reports advisory status; it performs no restoration or backfill —
  that stays with the existing coordinator (bounded recovery, operator requeue
  decisions for terminal states).
- Author-lane completion events carry `head: null` because author states carry no
  hash; exact-candidate identity is established by the independent review snapshot
  (`candidate_refs` + `CANDIDATE:`/`VERDICT:` lines), never by this monitor.
- Heartbeat staleness defaults to 1800 s and log-mtime fallback needs `--log-dir`
  or a resolvable state `log` path; a slow lane below the threshold is
  indistinguishable from a stuck one.
- Registry drift (new state fields, renamed pause files, new terminal states)
  needs an owned follow-up; the monitor does not guess.

## Task notes believed wrong or worth flagging

- Nothing in the task text was found wrong. One clarification applied: "actual
  model vs runner counts" is implemented as identity-checked cmdline liveness per
  role (starting runners are not models; reused PIDs are not counted), matching the
  F5/F6 repair direction in `dokumente/x86/WORKFORCE-SCHEDULER.md`.
