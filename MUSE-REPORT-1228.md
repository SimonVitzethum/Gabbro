# MUSE-REPORT-1228: Exact review of lane 1227 (PipelineSpillHoming)

CANDIDATE: 1227 875988f01065ed5f6c320e170023e31ace131a74

VERDICT: REPAIR

## Snapshot inspected (new pin, not the stale one)

`.tmp/review/SNAPSHOT.json` now pins author lane 1227 at head
875988f01065ed5f6c320e170023e31ace131a74, base
cbc0afe00eeb8708961b13489750e41e998740d1, files MUSE-REPORT-1227.md,
grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineSpillHoming.lean,
clean true. This supersedes the previous pin
638654c2736f9dfd6e0ed5d03af60c411d9261a5, which this lane no longer judges.
Reviewer clone is /home/simon/Dokumente/gabbro-muse/a1228 on branch
muse/1228 (verified), HEAD cbc0afe0, which equals the new snapshot base.
Tree clean.

## Substantive finding (previous finding re-checked against the new pin)

The new pinned object is absent from this clone: `git show 875988f0...`
answers `bad object`. HARD RULES rule 1 forbids reading outside this
directory, so the author clone is not accessible and the repaired candidate
content (the new Lean file, the Grammatik.lean import line, the author
report) could not be examined at all. The previous REPAIR finding therefore
persists unchanged for the new pin: none of the required exact-review checks
could be performed (no banned-construct grep, no `#print axioms`
verification, no premise-use check, no evaluator-reuse check, no
refusal-probe check, no witness non-degeneracy check, no silicon-fact check
against the Intel SDM extracts, no CUTS honesty check, and no `./lean-bau`
run, since building unmodified base master would not be evidence about the
candidate). Accepting on this basis would approve unproved claims, which the
task explicitly forbids. The verdict above is therefore REPAIR, with the
concrete repair action below. Nothing was approved from the stale snapshot
and nothing substantive was changed to make formatting pass.

## Repair required

Make the new pinned candidate material (head
875988f01065ed5f6c320e170023e31ace131a74) available inside the reviewer
clone, or re-issue this review with the snapshot content attached. Once the
three snapshotted files at the new head are readable here against base
cbc0afe0, the full exact review will be performed and the verdict revisited
on the actual repaired content.

## Reference: what the candidate should contain (from lanes/1227.md)

NEW FILE `grammatik/Grammatik/X86/PipelineSpillHoming.lean` plus one import
line in `grammatik/Grammatik.lean`: decided variable homing with live-range
splitting at statement boundaries, a decided check, a homing preservation
theorem in the style of `pipeline_correct_entry`, a `pipeline_refuses_*`
refusal theorem, poison probes per refusal, a non-degenerate `_zeuge`, CUTS
and `#print axioms`. Follow-up of lane 1191; no persistent SSA IR; Rust out
of scope.

## Owned files

Only MUSE-REPORT-1228.md (this file). No Lean files touched, nothing else
written.
