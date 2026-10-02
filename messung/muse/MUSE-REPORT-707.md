# MUSE-REPORT-707: Exact independent review of lane 706 launcher repair

CANDIDATE: 706 6e0a7f8aa0bbc3d04436f670c9242a2e21b2af11
VERDICT: ACCEPT

## Scope

FIRST verified: clone `/home/simon/Dokumente/gabbro-muse/a707`, branch
`muse/707`. Owned path only: `MUSE-REPORT-707.md`. Report-only review; no
source file touched, no Lean contact, no cargo contact, no network, no push,
no live controls, no provider, no credentials read. The candidate commit is
not in this clone's history, so review ran against the pinned exact-author
snapshot (`.tmp/review/author-706/`, `SNAPSHOT.json` head
`6e0a7f8a...`), whose blob hashes match the author's report exactly:

- `instrumente/coordinator-failover.py`:
  `8e64ad8d2de52330320074db74954ceaeeddc079d9d0321a34b411aab4917511`
- `instrumente/tests/test_coordinator_failover.py`:
  `b6e96c612dfa1e61aa7cfa2f790cc657ef32ccb374e0dc61b7927f30b1660f8d`
- `dokumente/x86/COORDINATOR-FAILOVER.md`:
  `eae44949f09eb4d224c39ed20b8d50530b02fb49c81817174fec84780b8c048d`

Candidate files were copied to ignored scratch (`.tmp/rev707/`, same-layout
`instrumente/...` mirror) and executed there; the owned tree was never
modified except by this report.

## Independent reproduction (all in scratch, real subprocesses)

- Strict CLI empty-message failure reproduced: a strict stub enforcing the
  public contract (managed flags plus nonempty positional message after
  `--`, else exit 1 with MUST PROVIDE MESSAGE) rejects the pre-706 shape
  and accepts the repaired `model_argv`
  (`test_strict_stub_rejects_absent_message`, ok).
- Managed-shape argv verified exactly (`run --pure --model ... --agent
  build --format json --dir ... --title gabbro-fallback-coordinator
  [--file ...] -- FALLBACK_MESSAGE`), with and without `--file`; message
  nonempty even with stdin DEVNULL
  (`test_model_argv_matches_managed_shape_with_message`, ok).
- Full launch path through actual `run_supervise` subprocess, not string
  equality: the stub-logged child argv carries all managed tokens plus the
  exact message (`test_full_launch_path_uses_message_through_subprocess`,
  ok).
- Provider-config pointer: child env carries `OPENCODE_CONFIG` pointing at
  the fixture dummy; pointer target byte-identical afterwards; its content
  string appears in no lease, status or log; without the flag the parent
  env passes through unchanged (both pointer tests, ok). Grep over the
  candidate confirms the module never opens, reads, copies, inspects or
  prints the file (only `env["OPENCODE_CONFIG"] = str(...)`); no
  `shell=True`, no socket/urllib, no credential-shaped content in tests.
- True increasing quick-exit backoff: 16 s budget against a quick-exit
  stub gives exactly 2 launches ~10 s apart (gap >= 8 s), every attempt
  argv-valid, `backing_off` note, `consecutive_failures >= 1`,
  dispatcher stop/start exactly 1:1 per launch, no churn, no storm
  (`test_consecutive_quick_exits_back_off_monotonically`, ok, 16.0 s).
- Fresh foreground cancels retry, pause exits promptly: fresh codex
  heartbeat during backoff suppresses the pending retry (still 1 launch
  after the window); user pause then exits in < 8 s with
  `paused_no_takeover`, no further launch, dispatcher balanced
  (`test_fresh_foreground_cancels_retry_then_pause_exits_promptly`, ok).
- `next_backoff` monotonic and bounded: 5->10->20, 150->300, 1000->300
  (ok).

## Full suite and lifecycle invariants

- Full file in scratch: **Ran 35 tests in 76.0 s, OK** (27 existing + 8
  new, zero failures, first attempt). Log at ignored
  `.tmp/rev707/full-707.log` (trailing duplicate-supervisor/heartbeat
  lines are expected stdout noise from tests exercising those paths).
- The 27 pre-existing tests are byte-identical (pure append of one new
  class; verified by diff opcodes, not only by count).
- Supervisor delta vs this clone's base is exactly the launcher repair
  (90 diff lines): `--opencode-config` flag, `model_env` pointer
  forwarding, `FALLBACK_MESSAGE` + managed-shape `model_argv`,
  `PRODUCTIVE_AFTER_SECS = 60.0` + `next_backoff` + productive-reset
  block, launch branch keeping failure history, three inline doublings
  unified to `next_backoff` (semantically identical for all reachable
  inputs: backoff is always >= 5.0 outside the pinned unit test).
- All 636/637 machinery is textually untouched: same-slot lifetime,
  guardian/process-group lease, starttime identity, safe-boundary locks
  held over role transitions/drain, max-15 shared cap, turn cap 7200,
  no killing of busy tool/user/unrelated processes, explicit user pause
  vs internal marker, dispatcher ownership restore. No model
  substitution, no separate uncounted coordinator process, no dropped
  guard, no output/env/config contents, no mock-only claim of
  operational takeover (docs state NOT deployed, no takeover occurred).
- Root integration is description-only and minimal (two added argv
  pointers against the supplied snapshot, no broad overwrite, no live
  control edits in any clone). Deployment still needs fresh root scope
  approval matching the exact blob above; this ACCEPT does not deploy.

## Scoping note (not a rejection)

The task's "fresh foreground promptly cancels retry" is implemented as
suppression (no launch while the lease is fresh, measured) with failure
history retained until a productive turn or an explicit terminal path,
not as a counter reset. This satisfies the measured requirement (no
retry fires) and is the storm-safe choice; the stronger reset is not
needed. Flagged only so the record shows the reading.

## Build state

No Lean, Rust, checker or emitter file touched, so no `./lean-bau` or
`./cargo-pruef` run is claimed or needed (same standing as lane 636).
`python3 -m py_compile` on both candidate files: OK.
`git status` before this commit: clean.

## What remains open

- Deployment and any operational-takeover claim: require fresh root scope
  approval matching the exact blob above plus the live-registry checks
  named in the handoff. Nothing in this review substitutes for that.
- The author's BUILD-EVIDENCE honestly records one unidentified
  single-run flake under load; my independent full run passed first
  attempt. Not a finding against the repair.

No definition or theorem added by this lane (review-only). No part of
the lane-706 task is believed wrong.
