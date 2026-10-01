# MUSE-REPORT-402

Lane 402: independent operating Muse scheduler audit and reproducible repair
proposal. Docs-only lane; owns `dokumente/x86/WORKFORCE-SCHEDULER.md` and this
report. No Lean, Rust, checker, emitter, model, or goal file touched.

## What was done

1. Verified clone `/home/simon/Dokumente/gabbro-muse/a402`, branch `muse/402`.
2. Read the supplied snapshot `.tmp/COORDINATOR.py` in full (1283 lines;
   SHA256 `e02ed7528f86686ce675c7cf17022ff80a65f7737004af45e516cc5e1c2d216f`).
   Note: the snapshot was refreshed mid-task (an earlier 1107-line version was
   replaced after the OOM recovery re-supplied the file); the audit targets
   the 1283-line version only. A stale probe/patch pair from the interrupted
   session targeted the old version and was rewritten from scratch.
3. Wrote `.tmp/probe-402.py`: 17 source-anchor + mock-simulation probes, all
   run with `python3` only (reads the snapshot text, never executes it
   against the real machine/pool, no network/git-root/credentials).
   Result: **17/17 PASS** (S12 confirms the old date-cap class is already
   eliminated; S1-S11/S13-S16 reproduce real defects/limitations).
4. Built `.tmp/COORDINATOR-fixed.py` (1461 lines, SHA256
   `4efb0ea0a3af4196eb300895f1ac1b6623fb47cb7a28d1a29378a1aa3e407a26`)
   by minimal edits: `root_mut` (reentrant shared root lock), `spawn_mut`,
   `proc_matches`, `atomic_write_json`, `mem_available_kib` helpers; guard-first
   launch/resume; MERGE_HEAD entry check + post-fetch ref compare in merge;
   peer post-copy re-pin; cmdline identity in starts/inventory/status/recovery;
   stop merged refusal; clean single-flight contention; atomic dispatch.json
   with `needs_attention` backlog; record_policy idempotency; resume slot-copy
   guard. `python3 -m py_compile` passes on both files.
5. Verified repairs: 12-point repair-string check passes; isolated helper
   behavior tests `.tmp/test-402-fix.py` (sandboxed `HERE`, import-only):
   **6/6 PASS**. Unified diff `.tmp/COORDINATOR-402.patch` (485 lines, SHA256
   `48eebc055decb044ed2103c3ae94bc59cb95c2c5101aec642c99e837147583fa`).
6. Wrote the owned deliverable `dokumente/x86/WORKFORCE-SCHEDULER.md` (690
   lines): 15 findings F1-F15 with line anchors and severities, 6 verified
   sound properties V1-V6, the repair list, full test output, the verdict,
   and appendix A embedding the complete patch verbatim.

## New definitions/theorems

None. This lane adds no Lean code (audit + Python probes + Markdown only),
so no `_zeuge` witnesses, no `CUTS` blocks, and no `#print axioms` are owed.
No TARGET statement was given in the task.

## Last ./lean-bau result line

Not run: the commit contains no `grammatik/` change (`git status` shows only
the two owned Markdown files), so the "full queued ./lean-bau before
committing Lean" rule does not trigger. The merge gate still builds.

## Verdict (for root)

Snapshot **not safe as-is for concurrent operation** (F2 concurrent-merge
abort, F4b post-review fetch window), **safe under single-operator serial
discipline** meanwhile. Patch closes all H/M items except the F8 requeue
policy, deliberately left to the operator. Full detail in the deliverable.

## Open / believed-wrong

- `dokumente/x86/WORK-ALLOCATION.md` (lane 329) still cites the superseded
  40/20 cap against the permanent 15; flagged, not touched (not owned).
- `configure_memory_guards` `taskset -c "4-$((CORE_COUNT-1))"` assumes 5+
  cores; true here, breaks smaller hosts. Flagged, not patched (operator env).
- Probe/test scripts stay in git-ignored `.tmp` (not committed per OWN ONLY);
  their full outputs are quoted in the deliverable; the patch is embedded
  there so nothing depends on the private directory surviving clone deletion.
