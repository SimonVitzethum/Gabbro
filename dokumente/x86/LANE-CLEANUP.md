# Lane prompt cleanup (lane 622)

The user asked that a lane prompt (`lanes/NNN.md`) be deleted when that lane
is over. `instrumente/lane-cleanup.py` is the small standard-library planner
for that job. It **plans by default** and only deletes on explicit `--apply`
after revalidating every gate. It never touches live work.

## What counts as over

- `merged` after exact checked integration: the registry `state/NNN.json`
  says `merged`. That is the only normal completion.
- `abandoned` / `final_refused` only with a durable terminal flag in the
  state record (`terminal`, `terminal_flag`, `durable_terminal` or
  `abandoned_final`), plus no live model/runner identity and no pending
  consumer.
- Everything else is **not final**: `report_ready`, `incomplete`,
  `runner_error`, `paused`, `waiting_for_review`,
  `needs_coordinator_fallback`, `ready`, `prepared`, `running`, `starting`,
  `starting_feedback`, `waiting_for_slot`, `waiting_for_candidate`, and an
  unknown status. A bare `abandoned` without the durable flag is not final.

Liveness is verified against a proc root (default `/proc`): a recorded
`model_pid`/`runner_pid` counts only when its directory exists, is not a
symlink, has non-empty cmdline, is not a zombie (`Z`/`X`), and matches the
recorded start time when one is stored. This guards PID reuse. A pending
review consumer (a `peer_reviews` entry whose reviewer is not itself merged
or durable-terminal) keeps the author's task protected, because the
independent reviewer snapshot must copy the exact author task first.

## Candidate paths (exact numeric copies only)

For a registered lane `N`, at most these six regular files are candidates:

1. `<project>/lanes/N.md` — tracked; removal goes through the coordinator's
   serial checkpoint/gated commit, never direct CLI git/network.
2. `<control>/tasks/N.md` — private task backup; needs git-blob or archive proof.
3. `<project>/.claude/muse-arbeit/lanes5/N.md`
4. `<project>/.claude/muse-sicherung/N.md`
5. `<pool>/lanes/N.md`
6. `<pool>/aN/.tmp/LANE.md` — the exact completed managed clone copy.

Everything else is preserved: unmerged work and clones, `lanes/VORSPANN.md`
and shared templates, reports (`messung/muse/MUSE-REPORT-N.md`), logs,
session databases, and whole folders. Reports are never deletion candidates;
a merged lane without a surviving report is held with
`needs_report_evidence` so task links in progress notes and docs keep
pointing at a report or an immutable history entry. Prompt text itself stays
reachable because old commits already contain it.

Guards on every candidate: exact numeric name, inside its configured root
(no path traversal or escape), not a symlink, a regular file (not a
directory or special file), and registered in `manifest.json`. Private task
copies additionally need evidence that the prompt is durable: a
`--task-blob-file` JSON mapping lane to git blob SHA-1, or a matching copy
under `--archive-dir`. Without that they are planned as `hold` with
`needs_git_blob_or_archive`. Tracked project prompts are planned with
`removal_via: coordinator_checkpoint` and `--apply` skips them unless
`--allow-tracked` is given (the CLI still only unlinks; the coordinator
stages and commits later).

## Use

Dry-run (default) prints a stable bounded JSON plan:

```sh
python3 instrumente/lane-cleanup.py \
  --project-root /path/to/Gabbro \
  --control-root /path/to/Gabbro/.claude/muse-arbeit/x86 \
  --pool-root /path/to/gabbro-muse \
  --lane 601 --lane 602
```

With a fake proc root and explicit manifest/state locations in tests or
rehearsals:

```sh
python3 instrumente/lane-cleanup.py \
  --project-root "$PROJ" --control-root "$CTRL" --pool-root "$POOL" \
  --proc-root "$PROC" --manifest "$CTRL/manifest.json" \
  --state-dir "$CTRL/state" --max-candidates 50
```

Apply deletes only explicitly selected approved exact paths, revalidating
symlinks, digests, completion, liveness and consumers first:

```sh
python3 instrumente/lane-cleanup.py \
  --project-root "$PROJ" --control-root "$CTRL" --pool-root "$POOL" \
  --lane 601 --apply --allow-tracked \
  --task-blob-file /path/to/blobs.json
```

Narrow further with repeatable `--select <exact path>`. `--apply` without an
explicit `--lane` refuses to delete. Digest changes between plan and apply
are refused as `stale_content_digest_mismatch`; a second apply is idempotent
(`already_absent` on revalidation). `--max-candidates` bounds the plan;
`summary.truncated` reports the bound. Plan records per-file SHA-256 and git
blob SHA-1 plus report digests as immutable audit metadata for the
coordinator. `--output` writes the JSON instead of stdout.

## Coordinator order

The root coordinator invokes this planner between serial merges, and runs a
historical sweep over already merged lanes the same way: plan, inspect the
`delete`/`hold`/`skip` rows, copy the exact author task into the reviewer
snapshot before deleting it, then `--apply` the selected lanes and commit the
tracked removals through its checkpoint. Deletion of the wrong lane, of an
unregistered ID, or of a lane with a waiting reviewer is refused and stays
refused until the gates pass.
