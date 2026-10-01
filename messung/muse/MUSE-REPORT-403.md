# MUSE-REPORT-403

Lane 403: independent exact-candidate review of 402. Review-only lane; owns
only this report. No Lean, Rust, checker, emitter, model, or goal file
touched or owed.

## What was done

1. Verified clone `/home/simon/Dokumente/gabbro-muse/a403`, branch `muse/403`.
   Base `0b3132b7bb8bf108b3fd1613c70bc0955051f130` exists locally; working
   tree was clean before and after (no staging left behind).
2. Inspected the exact supplied material only:
   `.tmp/review/SNAPSHOT.json` (author 402, head
   `06d042d6467e482f628954f55f74271b9e1d1aa1`, 2 files, clean),
   `.tmp/review/author-402/{OWNER-TASK.md,MUSE-REPORT-402.md,BUILD-EVIDENCE.json,PATCH.diff,dokumente/x86/WORKFORCE-SCHEDULER.md}`.
   No other clone was read; the coordinator snapshot itself was not supplied
   here and was not reconstructed.
3. Checked consistency mechanically with `python3` (read-only):
   - Supplied `WORKFORCE-SCHEDULER.md` (690 lines) and `MUSE-REPORT-402.md`
     (66 lines) are line-identical to the `PATCH.diff` outer-diff content
     (the single initial mismatch was my parser dropping the `++++` line;
     corrected parse: 690/690, 0 divergences; report 66/66, 0 divergences).
   - Appendix inner patch is 485 lines, +248/-70 = net +178; 1283 + 178 =
     1461, exactly the claimed fixed-variant length. Line counts, SHAs as
     quoted, and hunk anchors are mutually consistent.
   - ASCII-only in both files; no `sorry`/`native_decide`; the two `axiom`
     hits are the phrase "goal-axiom check" (merge gates, benign).
   - Flagged doc inconsistency is real: `dokumente/x86/WORK-ALLOCATION.md`
     still cites the 40-cap (lines 7, 303-317); correctly flagged, not
     touched (not owned).
4. Reviewed repair soundness from the patch text: `root_mut` (non-blocking
   shared lock, process-local reentrancy for `publish_checked_wave` nesting),
   `spawn_mut` guard+spawn serialisation, MERGE_HEAD entry check plus
   post-fetch ref compare (F4b), peer post-copy re-pin (F4), `proc_matches`
   cmdline identity with fail-closed unreadable case (F5/F6/F14), merged-lane
   refusals in `launch`/`stop` (F1/F7), clean single-flight contention plus
   atomic `dispatch.json` with `needs_attention` surfacing (F8/F10, no
   auto-requeue by design), infallible `mem_available_kib` fail-closed to
   zero (F15), idempotent `record_policy` (F12), guarded slot copy (F13).
   All fail closed; no throughput forecast, no compiler-closure claim, no
   safety weakening (scope note correctly states ops tooling cannot move any
   `gabbro_ziel` leg). Permanent-15 policy applied; no date logic in the
   final patch (the `max_active_now` 40/20 text visible in one truncated
   `BUILD-EVIDENCE.json` preview is the stale pre-refresh patch the report
   discloses as rewritten, not the delivered appendix).
5. Checked trust boundaries: patch touches only the coordinator snapshot
   (applied by root after review); candidate itself adds only the audit doc
   plus its report. Friend paths, Spec, checker, Rust, emitter untouched.

## New definitions/theorems

None. Review lane; no code added, so no `_zeuge` witnesses, `CUTS` blocks,
or `#print axioms` are owed. No TARGET statement was given.

## Last ./lean-bau result line

Not run: neither the candidate nor this review touches `grammatik/` (two
Markdown files only / report only). The merge gate still builds.

## Open / believed-wrong

- Traceability (not merge-blocking for a docs-only candidate):
  `BUILD-EVIDENCE.json` records git/patch plumbing but no command shows the
  final probe stdout (17/17), fix-test stdout (6/6), `py_compile` result, or
  the final SHAs (`4efb0ea0`, `48eebc05`); one entry still shows the stale
  pre-refresh fixed-file SHA. The "full test output" phrasing in
  MUSE-REPORT-402 overstates section 4, which gives counts plus grep/py-
  compile summaries, not per-probe logs. Repair direction: reword to
  "summary counts", or append per-probe lines; root can re-run the quoted
  commands on application since the patch is embedded verbatim.
- The commit-message `Co-Authored-By` line is not verifiable from the
  truncated `git show --stat HEAD | head -12` in the evidence file; root
  merge gate can check `git log -1 --format=%B` directly.
- Nothing in the lane task is believed wrong. The F8 requeue policy and F9
  watch-side repair are consciously left to the operator; documented, agreed.

## Verdict section

CANDIDATE: 402 06d042d6467e482f628954f55f74271b9e1d1aa1
VERDICT: ACCEPT
