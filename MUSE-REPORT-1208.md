# MUSE-REPORT-1208: Exact review of candidate 1207 (HwDrainGeneric) — BLOCKED, no candidate supplied

## Assignment

Lane 1208: independent exact review of lane 1207 ("Generic drain-equals-write64 induction",
NEW FILE `grammatik/Grammatik/X86/HwDrainGeneric.lean`). Own only `MUSE-REPORT-1208.md`.
Report-only review with exactly one VERDICT: ACCEPT or REPAIR.

## What I did

1. Verified working directory is the assigned clone (earlier `pwd` returned
   `/home/simon/Dokumente/gabbro-muse/a1208`, branch `muse/1208`).
2. Confirmed the working tree is clean: `git status --short` empty,
   `git diff master..HEAD --stat` empty, HEAD at `de94b21c`.
3. Read the author task (`lanes/1207.md`) to know what the candidate should contain.
4. Searched my clone for any candidate artefact: no `HwDrainGeneric.lean` under
   `grammatik/Grammatik/X86/`, no `MUSE-REPORT-1207.md` anywhere in the clone.
5. Ran `./lean-bau`: last result line is
   `Build completed successfully (634 jobs).`
   (This builds master state only; there is no candidate code in this clone.)

## New definitions/theorems

None. This is a report-only review lane; I own only this report and added no Lean code.

## VERDICT: REPAIR

Concrete reason: **there is no reviewable candidate.** The task line reads
`CANDIDATE: 1207 <full pinned HEAD>` — the pinned HEAD is a literal placeholder,
not a commit hash. Nothing of lane 1207 exists inside my clone (no new Lean file,
no author report, empty diff against master), and the author clone is outside my
lane boundary, which HARD RULES forbid me to touch. Every check the review requires
(diff read, sorry/axiom scan, `#print axioms`, premise use, evaluator lifting,
refusal behaviour, witness non-degeneracy, silicon facts, CUTS honesty, `./lean-bau`
on the candidate) needs the candidate diff; without it any ACCEPT would be fake
closure, which the task explicitly forbids.

This REPAIR is not a judgment on the author's work — the author's work never reached
this reviewer. Requested repair is on the dispatch side, not the author side.

## What remains open / what I believe is wrong with the task

1. Re-issue this review with an actual pinned commit hash for candidate 1207, plus a
   mechanism for the reviewer to obtain the exact candidate diff that does not violate
   lane isolation (HARD RULES rule 1: touch nothing outside the reviewer's directory).
   As written, the task asks the reviewer to read `git diff master..HEAD` "in the author
   clone", which the same HARD RULES forbid.
2. The `./lean-bau` gate on the candidate cannot be satisfied by a report-only reviewer
   whose tree contains no candidate code; either the candidate must be present in the
   review clone at the pinned commit, or the build expectation must be restated.
3. No hardware-correspondence or W/GX claim is evaluated here — nothing was reviewed.

## `./lean-bau` last result line

`Build completed successfully (634 jobs).`
