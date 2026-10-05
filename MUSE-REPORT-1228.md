# MUSE-REPORT-1228: Exact review of lane 1227 (PipelineSpillHoming)

CANDIDATE: 1227 638654c2736f9dfd6e0ed5d03af60c411d9261a5

VERDICT: REPAIR

## Snapshot inspected

`.tmp/review/SNAPSHOT.json` pins author lane 1227 at head
638654c2736f9dfd6e0ed5d03af60c411d9261a5, base
cbc0afe00eeb8708961b13489750e41e998740d1, files MUSE-REPORT-1227.md,
grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineSpillHoming.lean,
clean true. Reviewer clone is /home/simon/Dokumente/gabbro-muse/a1228 on
branch muse/1228 (verified), HEAD cbc0afe0, which equals the snapshot base.
Tree clean.

## Substantive finding (why no accept)

The pinned object is absent from this clone: `git show 638654...` answers
`bad object`. HARD RULES rule 1 forbids reading outside this directory, so the
author clone is not accessible and the candidate content (the new Lean file,
the Grammatik.lean import line, the author report) could not be examined at
all. Consequently none of the required exact-review checks could be performed:
no banned-construct grep, no `#print axioms` verification, no premise-use
check, no evaluator-reuse check, no refusal-probe check, no witness
non-degeneracy check, no silicon-fact check against the Intel SDM extracts, no
CUTS honesty check, and no `./lean-bau` run (building unmodified base master
would not be evidence about the candidate). Accepting on this basis would
approve unproved claims, which the task explicitly forbids. The verdict above
is therefore REPAIR, with the concrete repair action below. This preserves the
prior blocked status while giving the machine-readable verdict the gate
requires; nothing substantive was changed to make formatting pass.

## Repair required

Make the pinned candidate material available inside the reviewer clone (or
re-issue this review with the snapshot content attached). Once the three
snapshotted files at 638654c2736f9dfd6e0ed5d03af60c411d9261a5 are readable
here against base cbc0afe0, the full exact review will be performed and the
verdict revisited on the actual content.

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
