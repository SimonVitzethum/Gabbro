# MUSE-REPORT-1268: exact review of candidate 1267 (AVX2 SRA per-lane equation)

CANDIDATE: 1267 bb41ba853b44d49fb63d620d17101c26642ac5c9

Lane 1268, clone `/home/simon/Dokumente/gabbro-muse/a1268`, branch
`muse/1268`. Review-only lane: I own only this report; existing files
untouched. This is a re-review: my prior ACCEPT covered `ec962685`; the
new pinned snapshot (`.tmp/review/SNAPSHOT.json`, same base `c8bb4208`,
`clean: true`, same three files) pins `bb41ba85`. I reviewed the new
diff, the new evidence, and the delta — not the stale snapshot.

## Delta `ec962685` → `bb41ba85`: report only, Lean byte-identical

- The new `Avx2SraLanes.lean` blob is `8a002abc`, identical to the
  previously reviewed blob; the `Grammatik.lean` hunk is the same single
  appended import line. No Lean line changed.
- The added report section is an integration-gate failure analysis: the
  integration build elaborated the module fully (`#print axioms`
  through line 708, 0 errors) and died only at the final `Grammatik`
  aggregation with `failed to create thread`, exit 134 — diagnosed as
  resource exhaustion, not a proof defect — followed by local
  re-verification (`lean-bau` 658 jobs green, probe 0 errors, sorry
  gate 0 violations). Repair decision: no Lean change.
- I accept the analysis as stated evidence, not as my own measurement:
  it is consistent with the quoted log lines, it weakens no guarantee
  (nothing was edited to work around the failure), and it names the
  coordinator-side blocker concretely. It gives me no reason to alter
  any prior finding.

## Re-verified findings on the new snapshot (all prior checks re-run)

- Banned tokens: word-boundary grep over the new snapshot's Lean file
  for sorry/admit/axiom/native_decide/unsafe/split_ifs/norm_num/
  ring_nf/sorryAx finds nothing. `#print axioms` per main theorem and
  an honest CUTS block are present.
- Axioms (build evidence at the new HEAD, including a fresh `./lean-bau`
  ending `Build completed successfully (658 jobs)`): every theorem is at
  nothing, `[propext]`, or `[propext, Quot.sound]` — subsets of the
  standard goal axioms. `hsraWit_zeuge` is `[propext, Quot.sound]`.
- Scope: one new file plus exactly one appended import line; nothing
  redefined; accepted evaluator (`vecSraImm`, `sraLane`, `ymmSra`,
  Tier-3 gate, `HwSchritt` machinery) lifted, never copied — every
  referenced name re-verified present in `grammatik/`.
- Premise use: every premise of every theorem is used by its proof; no
  `Prop`-typed premise, no discarded hypothesis, no conclusion
  restating a premise; embedding/projection are a genuine exact pair.
- Refusals refuse: `.b8`/`.b64` have no constructor; gate, foreign-core,
  and old-event/bare-refusal adapter arms compute to `none`.
- Witness `hsraWit_zeuge` is non-degenerate: admitted word shift on core
  0 and saturating shift on core 1 (both XMM-changing, `decide`-pinned)
  plus a memory-changing embedded base-machine byte issue through `alt`
  with owner-only forwarding and unchanged canonical memory — the
  memory step honestly attributed, never claimed as an SRA effect.
- Silicon against the clone-local Intel SDM extract: COUNT > 15 clamps
  to 16 (PSRAW), COUNT > 31 to 32 (PSRAD), lanes independent with sign
  fill — exactly the stated saturation at count >= width. The author's
  two task-deviation notes re-verified (no `vecSra` in
  `VectorIntegerHardwareForms.lean`, only `vecShlQ`/`vecShrQ`; the
  register-only family admits no family-level memory witness) and both
  remain disclosed in CUTS, not worked around.
- No claim larger than the proof: no decoder/encoder, no RIP advance, no
  YMM file, no W/GX bridge, no source/budget/timing correspondence;
  silicon correspondence beyond the cited lines stays OPEN.

## Last build result

Author-supplied evidence at the new pinned HEAD: `./lean-probe`
`== 0 error(s) in the COMPLETE output; exit 0`, `./lean-bau` `Build
completed successfully (658 jobs)` (re-run after the integration
failure in the author's clone). I did not independently rebuild: the
candidate is not checked out in my clone (ownership is this report
only), so a local build would not be evidence about the candidate.

## What remains open

Nothing for this lane. Silicon correspondence beyond self-consistency,
the VEX decoder, and any W/GX bridge stay OPEN by design per CUTS.

## Substantive outcome

Exactly one machine-readable line follows.

VERDICT: ACCEPT
