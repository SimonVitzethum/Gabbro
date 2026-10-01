# MUSE-REPORT-622: Lane prompt cleanup planner

## What was done

Implemented the lane-622 lifecycle deliverable in the isolated clone
`/home/simon/Dokumente/gabbro-muse/a622` on branch `muse/622` (verified
before starting):

- `instrumente/lane-cleanup.py` (executable, standard library only):
  dry-run-by-default cleanup planner / `--apply` CLI with generic
  `--project-root` / `--control-root` / `--pool-root` / `--proc-root`,
  plus `--manifest`, `--state-dir`, `--report-root`, repeatable `--lane`
  and `--select`, `--allow-tracked`, `--task-blob-file`, `--archive-dir`,
  `--max-candidates`, `--output`. Key functions: `sha256_hex`,
  `git_blob_sha1`, `is_pid_live` (zombie / PID-reuse guards),
  `durable_terminal`, `live_identities`, `completion_of`,
  `pending_consumers`, `candidate_specs`, `inside_root`,
  `check_candidate`, `report_evidence`, `build_plan`, `apply_plan`, `main`.
- `instrumente/tests/test_lane_cleanup.py`: 12 fixture tests, all fixtures
  under the clone `.tmp/` (never `/tmp`), covering merged vs
  `report_ready` / `incomplete` / `runner_error` / `paused` /
  `waiting_for_review` / `needs_coordinator_fallback`, durable-flag
  abandoned/final_refused, live-PID blocking, PID reuse and zombies,
  pending-reviewer protection and release, symlink and non-regular-file
  refusal, report preservation and `needs_report_evidence`, private-task
  blob/archive evidence, stale-digest refusal, idempotent second apply,
  tracked-prompt `--allow-tracked` gating, unregistered-ID refusal, and
  wrong-lane apply refusal.
- `dokumente/x86/LANE-CLEANUP.md`: completion definition, the six exact
  candidate paths, evidence and checkpoint rules, CLI examples, and the
  coordinator order (plan between serial merges plus historical sweep;
  reviewer snapshot copies the exact author task first).

No Lean definitions or theorems were added (pure tools/docs lane, no
`Grammatik.lean` change). No diagnostic codes, gift probes, or examples
minted. No pool, clone, log, report, database, or folder deletion: the tool
unlinks only exact numeric prompt files.

## Verification

- `python3 instrumente/tests/test_lane_cleanup.py`: 12 tests, OK.
- `python3 instrumente/lane-cleanup.py --help`: CLI parses, dry-run JSON
  shape verified during development.
- `python3 -m py_compile` on both Python files: syntax ok.
- `./lean-bau`: not run. The task explicitly says no Lean build is needed
  and this lane touches no Lean files, so there is no Lean result line to
  report; running the 400+ job grammar build would only contend with other
  lanes' leases.
- `instrumente/pruefe-englisch.py` and `instrumente/pruefe-vergabe.py`:
  both ratchets read broken with and without this lane's files (identical
  counts after `git stash -u`: same 8011/7949 German lines, same 42/35
  candidates and 114/93 probes). Pre-existing baseline drift, not caused by
  this lane; all new text is English.

## What remains open

- Root coordinator wiring (outside this lane's ownership): invoking the
  planner between serial merges, the historical merged-lane sweep,
  `--task-blob-file` generation from git history (or `--archive-dir`
  preparation), and the checkpoint commit of tracked `lanes/N.md` removals.
- The private `.claude/muse-arbeit/x86` registry (`manifest.json`,
  `state/`, `tasks/`) was read only through the `.tmp/COORDINATOR.py`
  snapshot present in the clone; live control-plane paths were never
  touched, per HARD RULES.

## Task issue noticed

- `.tmp/LANE.md` line 22 is longer than the 2000-character read
  truncation, so the Read tool showed it cut off mid-word
  ("waitingr..."). The full sentence was reassembled via a clone-local
  Python slice read; the intended meaning (wrong-lane and waiting-review
  must be refused) is implemented as stated. Nothing else in the task
  looked wrong.
