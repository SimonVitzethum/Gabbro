# MUSE-REPORT-1204: Independent exact review of lane 1203

CANDIDATE: 1203 e53a1c8c404ebdaac5670417e50e6865a06e1103

Lane 1204 is a report-only exact review. Owned file only:
`MUSE-REPORT-1204.md`. No Lean code written by this lane.
Review basis is the exact pinned snapshot in this clone
(`.tmp/review/SNAPSHOT.json`, base `4ed3590d`, `clean: true`):
`MUSE-REPORT-1203.md`, one import line in `grammatik/Grammatik.lean`,
new `grammatik/Grammatik/X86/PipelineAtomicsBind.lean` (460 lines).
I read all three plus the owner task and the build evidence end to end.

## Checklist findings

- Forbidden tokens: none. A text search over the new file for
  `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `split_ifs`,
  `norm_num`, `ring_nf`, `intro _`, `have _ :=` finds only the English
  word "admits" in two prose comments. No new axiom declaration.
- Axiom footprint: per the recorded `#print axioms` output, every main
  theorem depends only on subsets of the standard
  `[propext, Classical.choice, Quot.sound]` (widest on the two LFENCE
  correspondence facts). Standard.
- Existing files: `Grammatik.lean` gains exactly the one appended
  `import Grammatik.X86.PipelineAtomicsBind` line; no other existing
  file is touched and no existing theorem is weakened or deleted.
- Premise use: every premise of every new theorem is consumed.
  Checked the non-obvious case `zaun_sfence_korrekt`: the premises the
  author found redundant during development were moved into the
  conclusion as derived conjuncts (`sse = true`, empty own buffer) via
  the accepted `sfence_erfolg_form`, and every binder still occurs in
  the step hypothesis or a helper application. No discarded premise.
- Lifting, not copying: all semantic work delegates to accepted
  family lemmas (`lockVoll_xadd_adapter`,
  `lockVoll_cmpxchg_erfolg_adapter`, `lockVoll_mfence_adapter`,
  `senk_xadd`/`senk_cas`/`senk_zaun`, `roundtrip_lock_mfence`,
  `roundtrip_sfence`, `roundtrip_lfence`, `sfence_erfolg_form`,
  `sfence_behaelt_tso`, `sfence_last_unveraendert`,
  `LfenceLoadNarrow_verbindung`, `pufferSetze_gleich`,
  `issue_anderer_kern`, `wort_gruppe_liest_zurueck`,
  `drain_spur_erreichbar`, `gruppe_verweigert_lock`,
  `wort_gruppe_liest_zurueck_zeuge`, `pin_sfence_verweigert_nachbarn`,
  `pilot_weist_lfence_zurueck`, `lock_weist_lfence_zurueck`). New
  definitions are only `ZaunArt`, `zaunBytes`, `valZaun`.
- Refusals really refuse: each `gift_*` / `zaun_*_ohne_sse` /
  `zaun_*_puffer_verweigert` theorem is a direct application of an
  accepted refusal lemma and elaborates in the green recorded build,
  so each refused shape is genuinely refused.
- Witness: `bind_zeuge` jointly instantiates fence pins, the MFENCE
  lowering, a written table (`witD.schreibt () ()`), and a reached
  drain run that observably changes memory (byte 0) via the accepted
  word-install witness. Non-degenerate on both sides. No new theorem
  quantifies over program syntax and the task names no `ZEUGE:` target,
  so no further witness duty applies. The multi-core aspect is covered
  at statement level (foreign-buffer frame `d != c`, `FremdFrei` over
  the drain), matching the single-core pipeline fragment.
- Silicon facts: SFENCE pin against MFENCE/LFENCE neighbours uses the
  correct `0F AE F8/F0/E8` byte patterns; SFENCE-without-SSE is the
  manual `#UD` via the accepted lemma; the word-install guard is the
  exact eight-entry group plus exclusion, with alignment explicitly
  documented as insufficient. Consistent with the accepted family.
- Scope honesty: the file CUTS state plainly what is not proved and not
  claimed (no `execBlock` correspondence for atomics, no CAS-failure
  binding, no narrow lock brackets, no seq_cst total order, fairness,
  retry bound, timing, interrupts, MMIO, DMA; no hardware-correspondence
  or W/GX claim). The claim is not larger than the proof. The missing
  block-level theorem is correctly refused, not faked: the accepted
  fragment covers integer slots only, and a block statement would need
  a forbidden second interpreter or a forbidden desired-correctness
  premise.
- Build evidence: per-commit `./lean-probe` runs (one honest mid-lane
  red probe on a misnamed register constant, repaired the same lane)
  ending in `0 error(s)`, and a final whole-`grammatik/` `./lean-bau`
  green at `627 jobs`. The pinned HEAD `e53a1c8c` is the report commit
  on top of that green state.

## Limitation of this review

I did not rebuild the candidate inside my own clone: owning only the
report forbids touching `grammatik/`. The verdict below rests on a
line-by-line read of the exact snapshot plus the recorded per-commit
probe evidence and the final green full build. My own tree stays
unmodified; `./lean-bau` there ends `Build completed successfully
(628 jobs).`

## Outcome

VERDICT: ACCEPT
