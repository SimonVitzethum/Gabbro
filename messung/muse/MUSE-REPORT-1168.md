# MUSE-REPORT-1168: Exact re-review of candidate 1167 (PipelineRegAlloc)

Lane 1168 (reviewer) — Pipeline: register allocation, spills and privacy validated.
Report-only exact re-review of the NEW pinned snapshot in `.tmp/review/`
(read inside this clone only; the author clone was never touched). The previous
ACCEPT targeted head `3bf5b441…`; that snapshot is stale after the author's
repair commit, and this report supersedes it. Nothing below approves the old
bytes — every finding was re-checked against the new pinned material.

CANDIDATE: 1167 657b8658e5d438bce4c94fe2fea027d686368219

VERDICT: ACCEPT

## What changed between the snapshots (author repair)

- New pinned head `657b8658…` (base unchanged: `062b979a…`, `clean: true`,
  same three owned files).
- The repair commit touches ONLY `MUSE-REPORT-1167.md`: it adds an
  "Integration repair" section (integration gate died with `failed to create
  thread`, Lean exit 134, zero Lean type errors; diagnosis resource
  exhaustion; no semantic change; local re-verification green; gate must
  re-run) plus an appendix. No Lean proof was changed.
- Verified directly, not taken on word: the new pinned
  `PipelineRegAlloc.lean` (434 lines) is line-for-line identical to the
  module reviewed under the old snapshot — validator, `cfgOk` bridge,
  interference and privacy legs, refusal theorem, closing theorem, probes,
  joint witness, CUTS, and all `#print axioms` lines all match. There are
  no changed proofs to re-inspect; the refusal/probe/witness findings from
  the previous review carry over byte-identically.

## Checklist findings on the NEW pinned bytes

1. **Forbidden tokens:** `rg` over the new module finds no `sorry`,
   `admit`, `axiom`, `native_decide`, `unsafe`, no `^axiom` declaration,
   and no discarded premise. Pass.
2. **Axioms:** new build evidence re-prints unchanged — defs on nothing or
   `[propext]`, closing theorems exactly
   `[propext, Classical.choice, Quot.sound]`, one helper on
   `[propext, Quot.sound]`. Standard triple throughout. Pass.
3. **Existing files:** new `PATCH.diff` touches exactly the three owned
   files; the `Grammatik.lean` hunk is still the single appended import
   line. No reserved optimiser file touched, no second IR/evaluator. Pass.
4. **Evaluator reuse and premise use:** unchanged code — the accepted
   `pipeline_correct`/`validate`/`cfgOk` lifting and the all-premises-used
   closing theorem stand as previously verified against this tree
   (`Pipeline.lean`, `PipelineWitnesses.lean`, `Stapel.lean`). Pass.
5. **Refusals and witness:** unchanged — five computation refusal probes on
   distinct validator legs plus the clash-via-theorem probe, one positive
   probe, and the joint memory-changing witness (slots 7 → 35, 9 → 6).
   Pass.
6. **Silicon and CUTS:** unchanged — 16 listed GPRs, `rsp`/`rbp` reserved,
   disjoint frame/code/table addresses by computation; spill code, finer
   liveness, callee-saved passing, and TSO freshness explicitly OPEN; no
   W/GX or hardware-correspondence overclaim. Pass.

## On the integration-gate failure story

The author attributes the gate failure to resource exhaustion (`failed to
create thread`, exit 134, zero type errors) and claims the module is
bit-identical. The second half I verified myself against the pinned bytes.
The first half (the integration log itself) is not contained in the pinned
evidence — but my verdict does not depend on it: a thread-spawn failure
with no type error is not a candidate defect, and no code repair is owed
for it. The author likewise claims no code fix and requires the gate to
re-run; I concur that integration must re-run its own gate before merge,
and this report approves the candidate module only, not any integration
result.

## Verification runs

- Author new pinned evidence: post-gate `./lean-probe` 0 errors;
  `./lean-bau` `Build completed successfully (608 jobs)`; axioms unchanged.
- Reviewer (this lane, this clone, no Lean changes of my own):
  `./lean-bau` last result line: `Build completed successfully (609 jobs).`

## Owned content

This report (`MUSE-REPORT-1168.md`) is the lane's only file. No Lean code
was written and no claim beyond the new pinned snapshot is approved.
