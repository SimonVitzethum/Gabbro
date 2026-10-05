# MUSE-REPORT-1268: exact review of candidate 1267 (AVX2 SRA per-lane equation)

CANDIDATE: 1267 ec962685795634fce434a0260902d82abae39cc1

Lane 1268, clone `/home/simon/Dokumente/gabbro-muse/a1268`, branch
`muse/1268`. Review-only lane: I own only this report; existing files
untouched. The lane file initially carried an unfilled HEAD placeholder;
the pinned snapshot (`.tmp/review/SNAPSHOT.json`, base `c8bb4208`,
`clean: true`, exactly the three files `MUSE-REPORT-1267.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/Avx2SraLanes.lean`)
supplied the exact hash and the full diff, which is everything this
review is based on, plus the author's build evidence and the owner's
task from the same snapshot directory.

## What was checked

- Banned tokens: word-boundary grep over the new file for
  sorry/admit/axiom/native_decide/unsafe/split_ifs/norm_num/ring_nf/
  sorryAx finds nothing. No new `axiom` declaration; the file ends with
  `#print axioms` for every main theorem and an honest CUTS block.
- Axioms (author build evidence at the pinned HEAD): every theorem
  depends on nothing, `[propext]`, or `[propext, Quot.sound]` — a subset
  of the standard goal axioms. `hsraWit_zeuge` is `[propext,
  Quot.sound]`.
- Scope: `Grammatik.lean` gains exactly one appended import line; all
  other work is in the one new file (709 lines). Nothing redefined.
- Lift, not copy: `vecSraImm`, `sraLane`, `ymmSra`,
  `avx2TierZugelassen`, `HwAdapter`/`HwSchritt`/`HwWf`/`HwMaschine`
  machinery (`setKernVonFp`, `projFp`, `setTso`, `tsoAnsicht`,
  `issueByte`, `loadByte`, `hwSchritt_wf`, `setKernDaten_wf`,
  `xmmSet_gleich/fremd`, `laneGet_mk`, `laneMod_pos`,
  `avx2Tier_basis_zugelassen`, witness constants) are all referenced,
  never redefined — each name verified present in `grammatik/`.
- Premise use: every premise of every new theorem is used by its proof
  (checked by reading each proof: `hc`/`hi` discharge the `if`s,
  `hgate`/`h` discharge the gate/core tests, `hsign` selects the fill,
  `hstep`/`hmem` build the `.sra` constructor). No `Prop`-typed
  premise, no discarded hypothesis, no conclusion restating a premise.
- Refusals refuse: `.b8`/`.b64` have no `SraBreite` constructor
  (proved by `cases` + `decide`); the Tier-3 gate refusal, foreign-core
  refusal, and old-event/bare-refusal adapter arms all compute to
  `none` (`rfl`/`simp`).
- Witness `hsraWit_zeuge` is non-degenerate: an admitted word shift on
  core 0 (`0xFF00 >> 4 = 0xFFF0`, XMM-changing, `decide`-pinned), a
  saturating shift on core 1 (all-ones/zero, `decide`-pinned), and a
  memory-changing embedded base-machine byte issue through `alt` with
  owner-only forwarding and unchanged canonical memory. The family
  itself is register-only, so the memory step is honestly attributed to
  the base machine, never claimed as an SRA effect.
- Silicon against the clone-local Intel SDM extract: COUNT > 15 clamps
  to 16 (PSRAW) and COUNT > 31 to 32 (PSRAD), each lane shifting
  independently with sign fill — exactly the saturation the equation
  states at count >= width. The VEX-has-no-VPSRAQ refusal is inherited
  from accepted lane 1239 with provenance; the file's CUTS keeps silicon
  correspondence beyond the cited lines OPEN.
- The author's two "task is wrong" notes check out: (1) confirmed by
  grep — `VectorIntegerHardwareForms.lean` defines only `vecShlQ`/
  `vecShrQ`, no packed arithmetic shift exists, so SSE2 agreement is
  indeed vacuous and the proved half-identity (`ymmSra_halb`,
  `sraFolge_ymm_lo/hi`) is the correct substitute, disclosed in CUTS;
  (2) the register-only family genuinely admits no family-level memory
  witness, and the `alt`-attributed issue is the honest substitute,
  disclosed in CUTS.
- No claim larger than the proof: no VEX decoder/encoder, no RIP
  advance, no YMM file (two-XMM modelling disclosed as a choice), no
  W/GX bridge, no source/budget/timing correspondence.

## Last build result

Author-supplied evidence at the pinned HEAD: `./lean-probe
grammatik/Grammatik/X86/Avx2SraLanes.lean` ends at `== 0 error(s) in
the COMPLETE output; exit 0`, and `./lean-bau` ends at `Build completed
successfully (658 jobs).` I did not independently rebuild: the
candidate is not checked out in my clone (ownership is this report
only, and my base differs), so a local build would not be evidence
about the candidate. The `pruefe-kein-sorry` 0-violation claim is the
author's; my independent token grep over the exact new file confirms
it.

## What remains open

Nothing for this lane: the per-lane equation, saturation, separation,
half agreement, adapter/embedding, refusals, and joint witness are all
proved with standard axioms. Silicon correspondence beyond
self-consistency, the VEX decoder, and any W/GX bridge stay OPEN by
design and are named in CUTS.

## Substantive outcome

Exactly one machine-readable line follows.

VERDICT: ACCEPT
