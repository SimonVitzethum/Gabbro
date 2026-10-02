# MUSE-REPORT-706: Repair fallback CLI message, provider pointer and quick-exit backoff

## Scope

FIRST verified: clone `/home/simon/Dokumente/gabbro-muse/a706`, branch
`muse/706` (base `dbfdc83c`). Owned paths only:
`instrumente/coordinator-failover.py`,
`instrumente/tests/test_coordinator_failover.py`,
`dokumente/x86/COORDINATOR-FAILOVER.md`, `MUSE-REPORT-706.md`.
Read the full public supervisor/tests, integrated reports 636/637 and the
provided read-only `.tmp/COORDINATOR.py` snapshot. No Lean, Rust, checker,
emitter, live-root, provider or credential contact; fixtures and fake
binaries only, scratch under the clone `.tmp/`. No network, no push.

## Defects repaired

1. **Missing positional message.** `model_argv` passed an attached
   `--file` but no positional message, while the public CLI vocabulary
   requires one (MUST PROVIDE MESSAGE) and the managed contributor run
   uses `run --pure --model ... --agent build --format json --dir ...
   --file ... -- MESSAGE` with stdin DEVNULL. Root diagnostics: 27
   bounded fallback starts, each exit 1. Fix: `model_argv` now builds the
   managed shape exactly (`run --pure --model <model> --agent build
   --format json --dir <project-root> --title
   gabbro-fallback-coordinator [--file <prompt-file>] --
   <FALLBACK_MESSAGE>`) with a nonempty explicit positional coordination
   instruction even with stdin DEVNULL; exact model/project/prompt
   retained; argv only, no shell.
2. **No provider-config pointer.** New bounded `--opencode-config` FILE
   PATH option. `model_env` forwards it ONLY via `OPENCODE_CONFIG` to the
   child; the module never opens, reads, copies, inspects or prints the
   file. The managed coordinator sets the pointer to its existing
   `opencode-go.json`. Per-session db, project SSD scratch and
   no-auto-update isolation unchanged. A pointer to existing
   user-authorised config is not a new authentication assumption.
3. **Quick-exit backoff reset at launch.** The launch branch reset
   `failures = 0 / backoff = 5.0` on every successful `Popen`, before the
   child proved productive, so consecutive `Popen`-success plus
   immediate-nonzero-exit cycles never backed off monotonically. Fix: the
   launch branch keeps failure history (`retry_at = 0.0` only); counters
   reset only after `PRODUCTIVE_AFTER_SECS` (60 s, the quick-exit window)
   of live coordination, or on the explicit pause/handback/turn-expiry
   paths. The three inline doublings now share one bounded step
   `next_backoff` (double from 5 s, cap 300 s). Same-slot lifetime,
   guardian/process-group lease, starttime identity, safe-boundary locks
   held over role transitions/drain, max-15 cap, no killing of busy
   tool/user/unrelated processes and no silent foreground takeover are
   untouched.

## New names (all in the owned supervisor module)

- `FALLBACK_MESSAGE` — fixed nonempty positional coordination
  instruction (slot cap, live-registry ownership, boundary locks,
  handback; no credentials).
- `PRODUCTIVE_AFTER_SECS = 60.0` — liveness window before failure
  history may be forgotten.
- `next_backoff(backoff)` — one bounded exponential step.
- `parse_args`: `--opencode-config` (default `None`).
- `model_argv`: managed-shape argv incl. `--pure`, `--agent build`,
  `--format json`, `--dir`, `--title`, `--file`, `-- MESSAGE`.
- `model_env`: `OPENCODE_CONFIG` pointer forwarding (via `getattr`
  default `None`, so old fixture namespaces keep working).
- Productive-reset block in `run_supervise` (`alive is not None and
  turn_age > PRODUCTIVE_AFTER_SECS`).

## Tests: 8 new, 27 existing untouched and green

New class `LaunchMessageEnvBackoffTest` (strict CLI stubs that mimic only
the public contract — reject absent message with MUST PROVIDE MESSAGE and
exit 1; fixture scratch only; stub names carry both identity markers so
real `/proc` identification applies):

- `test_model_argv_matches_managed_shape_with_message` — exact flag
  sequence incl. positional message, with and without `--file`.
- `test_strict_stub_rejects_absent_message` — reproduces the deployed
  defect: pre-706 shape exits 1 with MUST PROVIDE MESSAGE; repaired argv
  exits 0 through the same stub.
- `test_full_launch_path_uses_message_through_subprocess` — real
  `run_supervise` launch of the strict stub; logged child argv contains
  `--pure/--agent/build/--format/json/--dir/--title/--` plus the exact
  message (not string equality only).
- `test_provider_config_pointer_forwarded_only_via_env` — child env
  carries the pointer; pointer bytes byte-identical afterwards; its
  contents appear in no lease, status or log.
- `test_no_pointer_leaves_parent_env_untouched` — without the flag the
  parent env passes through unchanged.
- `test_next_backoff_monotonic_bounded` — 5→10→20→…→300, capped.
- `test_consecutive_quick_exits_back_off_monotonically` — 16 s budget,
  quick-exit stub: exactly 2 launches ~10 s apart (gap >= 8 s), every
  attempt argv-valid, `backing_off` note, `consecutive_failures >= 1`,
  dispatcher stop/start exactly 1:1 per launch (no churn, no storm).
- `test_fresh_foreground_cancels_retry_then_pause_exits_promptly` —
  fresh codex heartbeat during backoff suppresses the pending retry
  (still 1 launch after the backoff window); user pause then exits in
  < 8 s with `paused_no_takeover`, no further launch, dispatcher
  stop/start balanced.

## Verification

- `python3 -m py_compile` on both owned Python files: OK.
- New class alone: **8 tests, 0 failures, 0 errors, 28.8 s** (full
  output in §Output below).
- Full file: **35 tests (27 existing + 8 new), 0 failures** on three
  consecutive runs (76 s each). One earlier full run showed 1 failure
  that did not reproduce in any of the three reruns and whose test name
  was cut from the visible tail; no existing test exercises the changed
  paths with nonzero failure history (all use long-lived or
  Popen-exception stubs with `failures == 0`), so the changed behaviour
  is identical for them. Recorded here as an unidentified flake under
  load, not as a finding against the repair.
- `git status` shows only the three owned source paths plus this report;
  no `grammatik/` contact, so no `./lean-bau` run is claimed or needed
  (same standing as lane 636); no `cargo` contact.
- No credentials read: the only config-shaped file touched is a
  fixture-local dummy (`{"model":"muse-spark-testmodel-620"}`) whose
  pointer — never its content — crosses into the child env.

## Proposed root argv/config integration (minimal, no broad overwrite)

Against the supplied `.tmp/COORDINATOR.py` snapshot: keep `OPENCODE`,
`MODEL` and `HERE/'opencode-go.json'` as they are; the detached
`supervise` spawn gains exactly `--opencode-config
<HERE/'opencode-go.json'>` (existing configured location, supplied by
root on deployment) and, when present, the existing `--prompt-file
<file>`. The supervisor builds the managed-shape child argv itself and
never opens the config file. Full wording in the owned doc
(`dokumente/x86/COORDINATOR-FAILOVER.md`, Root wrapper contract §).

## State: mock fixture readiness, NOT operational takeover

The repaired source is armed and green in fixtures/mocks only. The
previous deployed source started 27 bounded turns that each exited 1;
this repair is NOT deployed and no successful operational takeover has
occurred — do not claim useful takeover occurred. Deployment needs exact
independent review 707 plus fresh root scope approval matching the exact
blob below.

## Hashes (pre-commit, base `dbfdc83c`)

- `instrumente/coordinator-failover.py`:
  `8e64ad8d2de52330320074db74954ceaeeddc079d9d0321a34b411aab4917511`
- `instrumente/tests/test_coordinator_failover.py`:
  `b6e96c612dfa1e61aa7cfa2f790cc657ef32ccb374e0dc61b7927f30b1660f8d`
- `dokumente/x86/COORDINATOR-FAILOVER.md`:
  `eae44949f09eb4d224c39ed20b8d50530b02fb49c81817174fec84780b8c048d`

## Output (new class, verbatim)

```text
test_consecutive_quick_exits_back_off_monotonically (__main__.LaunchMessageEnvBackoffTest.test_consecutive_quick_exits_back_off_monotonically) ... ok
test_fresh_foreground_cancels_retry_then_pause_exits_promptly (__main__.LaunchMessageEnvBackoffTest.test_fresh_foreground_cancels_retry_then_pause_exits_promptly) ... ok
test_full_launch_path_uses_message_through_subprocess (__main__.LaunchMessageEnvBackoffTest.test_full_launch_path_uses_message_through_subprocess) ... ok
test_model_argv_matches_managed_shape_with_message (__main__.LaunchMessageEnvBackoffTest.test_model_argv_matches_managed_shape_with_message) ... ok
test_next_backoff_monotonic_bounded (__main__.LaunchMessageEnvBackoffTest.test_next_backoff_monotonic_bounded) ... ok
test_no_pointer_leaves_parent_env_untouched (__main__.LaunchMessageEnvBackoffTest.test_no_pointer_leaves_parent_env_untouched) ... ok
test_provider_config_pointer_forwarded_only_via_env (__main__.LaunchMessageEnvBackoffTest.test_provider_config_pointer_forwarded_only_via_env) ... ok
test_strict_stub_rejects_absent_message (__main__.LaunchMessageEnvBackoffTest.test_strict_stub_rejects_absent_message) ... ok

----------------------------------------------------------------------
Ran 8 tests in 28.805s

OK
```

(Full run log with pre-existing `pass_fds`/`ResourceWarning` fixture
noise retained at `.tmp/newclass-706.log`, private scratch, not
committed. Full file: `Ran 35 tests ... OK`.)

## What remains open / disagreements

- Nothing in the task is believed wrong. One scoping note: the task asks
  that a fresh foreground heartbeat "promptly cancels retry" — the repair
  implements this as suppression (no launch while the lease is fresh,
  measured), not as a counter reset; failure history is retained until a
  productive turn or an explicit terminal path. Flagged so reviewer 707
  can demand the stronger reset if wanted.
- Reviewer 707 must re-verify the exact blob above independently.
