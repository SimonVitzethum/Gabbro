# MUSE-REPORT-1258: Independent exact review of candidate 1257 (PipelineSpillSplice)

## Assignment

Lane 1258: report-only independent exact review of lane 1257's candidate
(`grammatik/Grammatik/X86/PipelineSpillSplice.lean` — splice save/reload at
split points, callee-saved and arguments, follow-up of lane 1227).
Owns ONLY this file. Review checklist from the task: no
sorry/axiom/native_decide; `#print axioms` standard; existing files untouched
except one import line; every premise used; the family's accepted evaluator
lifted not copied; planted refusals really refuse; non-degenerate witness;
silicon facts against Intel SDM extracts; honest CUTS; no claim larger than
the proof (no hardware-correspondence or W/GX claim).

## What was actually done

1. Verified clone `/home/simon/Dokumente/gabbro-muse/a1258`, branch
   `muse/1258` — matches the task header, did not STOP.
2. `git diff master..HEAD --stat` in my own clone: EMPTY. My clone contains
   no candidate; master is at `17651ab7`. There is nothing to review here.
3. Read the committed copy of the author task (`lanes/1257.md`, present in my
   clone via master): target is NEW FILE
   `grammatik/Grammatik/X86/PipelineSpillSplice.lean` + one import line in
   `grammatik/Grammatik.lean` + `MUSE-REPORT-1257.md`. So I know what the
   candidate SHOULD contain, but not what it DOES contain.
4. Attempted the task-authorized read-only candidate inspection
   (`git diff master..HEAD` / `git log` in author clone
   `/home/simon/Dokumente/gabbro-muse/a1257`): the permission classifier
   rejected the tool call twice (once for listing the parent directory, once
   for `git -C .../a1257 log`). HARD RULES rule 1 also forbids touching
   anything outside my directory; the lane task's "read the candidate diff
   only in the author clone" conflicts with that, and the tool layer
   enforced the HARD RULES side.
5. Ran `./lean-bau` in my own clone as the only check available to me.

## Last `./lean-bau` result line

`Build completed successfully (658 jobs).` — green baseline of master
(without any candidate) in this clone.

## VERDICT: REPAIR

Concrete reason (procedural, not semantic): the candidate was never made
available for inspection. The task names `CANDIDATE: 1257 <full pinned HEAD>`
but supplies no HEAD hash, and the author clone is not readable from this
lane (permission rejections, see above). My own clone has an empty diff, so
every review criterion — sorry/axiom scan, `#print axioms` standardness,
premise use, evaluator lifting vs copying, refusal probes, witness
non-degeneracy, silicon facts, CUTS honesty — is UNCHECKED.

ACCEPT of an unseen candidate would be fake closure, which the task
explicitly forbids ("no fake closure", "no claim larger than the proof").
Therefore the only honest verdict is REPAIR: re-issue this review with (a)
the full pinned HEAD hash of candidate 1257 and (b) a readable snapshot of
the candidate diff inside the reviewer clone (or reviewer-side fetch
permission), then re-run the full checklist.

## Open / follow-up

- None of the candidate's content has been reviewed; a fresh review pass is
  needed once the candidate is accessible.
- No Lean or Rust files were touched by this lane; no additional build,
  test, or emission checks apply beyond the `./lean-bau` baseline above.
- Anything in the review checklist I could not perform is listed above as
  UNCHECKED, not as passed.
