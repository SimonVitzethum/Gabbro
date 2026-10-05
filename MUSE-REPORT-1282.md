# MUSE-REPORT-1282: Exact review of candidate 1281 (Sign-extend-accumulator ops and register XCHG)

## Assignment

Lane 1282, clone `/home/simon/Dokumente/gabbro-muse/a1282`, branch `muse/1282`
(verified: `git branch --show-current` = `muse/1282`, HEAD `c018ba20`).
Owned file only: `MUSE-REPORT-1282.md` (report-only exact review, no Lean changes).
Review target: candidate lane 1281, NEW FILE `grammatik/Grammatik/X86/IntSignXchg.lean`
(CBW/CWDE/CDQE, CWD/CDQ/CQO, XCHG register forms incl. the 90-NOP rule, plus MOVSXD
iff not already in `NarrowOps.lean`; XCHG-with-memory refused here), connected to
`HwMaschine`/`HwSchritt` via a `HwAdapter` following `HwMulDivWidth.lean`.

## VERDICT: BLOCKED (no ACCEPT/REPAIR possible — candidate unavailable)

I give **no ACCEPT and no REPAIR verdict**, because the candidate was never made
available to this reviewer. A verdict without the candidate diff would be a claim
larger than the evidence, which the review rules forbid. Details:

1. **No pinned HEAD supplied.** `.tmp/LANE.md` line 25 reads literally
   `CANDIDATE: 1281 <full pinned HEAD>` — the placeholder was never filled with a hash,
   so there is no exact snapshot to review.
2. **Candidate files absent from this clone.** `grammatik/Grammatik/X86/IntSignXchg.lean`
   does not exist here; neither `MUSE-REPORT-1281.md` (repo root) nor
   `messung/muse/MUSE-REPORT-1281.md` exists here. `git diff master..HEAD` in this
   clone is empty (HEAD `c018ba20` is a merge of Muse 1286 work, unrelated).
3. **Author clone not accessible from here.** The task says to read
   `git diff master..HEAD` in the author clone, but HARD RULES rule 1 forbids touching
   anything outside this directory, and the one access attempt to
   `/home/simon/Dokumente/gabbro-muse/a1281` was rejected by the permission classifier.
   I did not retry or work around it.
4. **No trace of 1281 in local history.** `git log --oneline --grep="1281"` is empty;
   the author task `lanes/1281.md` IS present (read it for scope), but no author report
   and no author commit are visible from this clone.

## What was checked

- Clone/branch verification: PASS (`a1282`, `muse/1282`).
- Author task scope read from committed `lanes/1281.md` (authoritative): family, widths,
  90-NOP rule, memory-XCHG refusal, HwAdapter mechanism, witness/CUTS requirements.
- `./lean-bau` (this clone, unmodified): **green — `Build completed successfully (672 jobs).`**
  This is a baseline hygiene check only; it says nothing about candidate 1281.

## New definitions/theorems

None. Review-only lane; no Lean files created or edited.

## What remains open / needed to unblock

- Supply the full pinned HEAD hash of `muse/1281` and a readable candidate snapshot
  (exact committed diff + `MUSE-REPORT-1281.md`), reachable without leaving this clone.
- Then the full exact-review checklist from the lane task can run: sorry/axiom scan,
  `#print axioms` standard, one-import-line rule, premise use, evaluator lifting
  (no copy), planted refusals, non-degenerate witness, silicon facts vs SDM extracts,
  CUTS honesty, no W/GX overclaim — ending in exactly one ACCEPT or REPAIR.

## Suspected defect in the task

The review lane was dispatched before (or without) pinning the candidate HEAD hash;
the `<full pinned HEAD>` placeholder and the instruction to read the diff in an
off-limits clone make the review unexecutable as written. Suggest the dispatcher fill
the pinned hash and attach the exact diff snapshot to the review lane file.
