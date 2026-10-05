# MUSE-REPORT-1164: Exact re-review of 1163 (new pin)

Lane 1164 (reviewer) in clone `/home/simon/Dokumente/gabbro-muse/a1164`, branch `muse/1164` (verified: `.git/HEAD` = `ref: refs/heads/muse/1164`).

CANDIDATE: 1163 cdbb5b0350ea371cd432b82b023dfefedffcbbc8

VERDICT: ACCEPT

## What changed since the previous finding

The previous finding was pure non-reviewability (placeholder hash, no readable
diff) and claimed no content defect. That defect is cured: `.tmp/review/SNAPSHOT.json`
now pins head `cdbb5b03` over base `062b979a` with files `MUSE-REPORT-1163.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/PipelineAtomics.lean`, and
`.tmp/review/author-1163/` carries the exact diff, the owner task, the author
report and step-by-step build evidence — all inside this lane's directory, so the
full gate list below ran against the pinned content. The new pin differs from the
earlier reviewed pin `8cfa81a5` by a report-only commit (no Lean change; confirmed
from the evidence log), so the Lean content judged here is exactly what the
author's probe and full build verified.

## Gate results (all against the pinned exact diff)

- **Owned files only.** The diff touches exactly three files: new
  `grammatik/Grammatik/X86/PipelineAtomics.lean` (798 lines), one appended
  import line in `grammatik/Grammatik.lean`, new `MUSE-REPORT-1163.md`. No
  existing theorem weakened, optimiser files untouched, no second IR or source
  interpreter.
- **No forbidden tactics/claims.** Static scan of the added code: no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `split_ifs`, `norm_num`,
  `ring_nf`, no `intro _` / `have _ :=`. (The only matches for those strings in
  the snapshot are prose: rule quotations and the words "admits no step".)
- **Axioms standard.** The evidence probe prints `#print axioms` for every main
  theorem; all are subsets of `propext, Classical.choice, Quot.sound`
  (e.g. round-trip lemmas carry the full triple, the joint witness
  `[propext, Quot.sound]`). No new axiom.
- **Every premise used.** Read every proof: `hq`/`hSen` discharged by
  subst+rewrite in each correspondence theorem; `hRegel` cited in all three
  plain-access legs; `hne`/`hmiss`/`hrd`/`hIssue` all feed the invisibility
  application; `hbuf`/`hrd`/`hali`/`hwr`/`hstep` all feed the accepted locked
  steps; `hRahmen` closes the lock-section foreign frame; all thirteen GX-leg
  premises feed the reused group/rely lemmas. Refusal theorems pass every
  hypothesis to the accepted refusal lemma. No conclusion restates a premise;
  contract values stay concrete (no quantified-away parameters or results).
- **Accepted evaluator lifted, not copied.** Bytes come from reused
  `encode`/`encodeLock` via `zielBytes`; decode-back facts reuse `roundtrip` /
  `roundtripLock`; steps reuse `effAddr_load_schritt`,
  `effAddr_store_schritt`, `lock_xadd_atomar`, `cas_erfolg_schreibt`,
  `casSchritt_fehlschlag`, `mfenceDrain_*`, `ladeWort8_aus_lesungen`,
  `wLesbar_aus_gruppe`, `havoc_erhaelt_gruppenwert`. All 30+ reused names were
  confirmed to exist in this clone's tree; the four heaviest call shapes
  (`wLesbar_aus_gruppe`, `lock_xadd_atomar`, `cas_erfolg_schreibt`,
  `MfenceDrainOwn_verbindung_zeuge`) were checked argument-for-argument against
  the accepted signatures, and the witness destructuring matches the cited
  joint-witness statement component for component.
- **Refusals really refuse, with a real positive.** Seven poison equations
  (truncated/LFENCE-adjacent/LOCK-prefixed fence bytes, buffer-blocked and
  misaligned fetched LOCK, permission-failed fetched CAS) each hold by the
  cited accepted refusal lemma, plus `positiv_holt_xadd` (fetched word 10 to
  15, rax takes 10). No refusal is an unproved claim.
- **Witness non-degenerate.** `senkAtom_zeuge` holds all five lowerings jointly
  with a reached two-core drain run that observably changes memory
  (`s2.mem.bytes fdX != s3.mem.bytes fdX`), both core buffers pending, a
  written table (`witD.schreibt () ()`), and the fetched memory-changing XADD.
- **Silicon facts checked.** F0 48 0F C1 / B1 with ModRM 0x85/0x8D are the
  correct LOCK XADD / CMPXCHG [rbp+disp32] encodings; 0F AE F0 is MFENCE while
  0F AE E8 is LFENCE (refused, correctly distinguished); F0 0F AE F0 faults
  (LOCK+MFENCE is #UD, correctly classified as `ud`, never a drain). Relaxed /
  acquire loads and release stores to plain MOV matches x86-TSO (loads ordered
  with loads, stores with stores); the ordering argument is ignored by the
  lowering, which is sound because the fragment's order type has exactly the
  two accepted constructors with `seq_cst` modelled as release/acquire
  (accepted over-approximation, restated in CUTS — no total order claimed).
  CAS expects in rax, as hardware does.
- **CUTS honest, no overclaim.** The file records: no `execBlock`
  correspondence (with the reason: the pipeline fragment covers integer slots
  only and existing files are frozen), no register-address binding for
  RMW/fence byte forms, no SFENCE/LFENCE lowering, no 8-issue word install, no
  full `SchrittW`, no `seq_cst` total order, no fairness/progress/retry-bound/
  timing/cost. `schwach_ist_gX` is cited, never applied; the GX legs derive
  only what the reused lemmas give (committed-read `lies` consequent,
  rely stability). Nothing larger than the proof is claimed — in particular no
  hardware-correspondence or full W/GX bridge claim.
- **Build evidence.** Author-side evidence log shows `./lean-probe` ending at
  `== 0 error(s)` and `./lean-bau` ending at `Build completed successfully
  (608 jobs)`, including honest intermediate red states (one `DecidableEq`
  derivation error, tactic failures, one type mismatch — all repaired in later
  steps) and three apparatus-shaped process failures (`bad_alloc`, `failed to
  create thread`, stale-olean read) resolved by a drained retry with no file
  change. The final pin adds no Lean content on top of that green state.

## Observations (not verdict-grade)

- Two linter warnings about unused `simp` arguments remain in the file;
  warnings only, error count zero.
- The GX legs reuse accepted lemmas without their own dedicated joint
  premise-instantiation; the joint witness covers lowering + drain + fetched
  RMW, which satisfies the task's stated witness demand (non-degenerate,
  memory-changing step).
- No independent rebuild was run in this review clone: the candidate file is
  absent here by design (report-only lane, ownership rule), and rebuilding the
  whole project here would not be the pinned content. This ACCEPT rests on the
  exact-diff static review above plus the pinned step-by-step build evidence,
  stated plainly so the merger can weigh it.

## Remaining work for others

None from this lane: the earlier setup critique (hold review lanes until the
snapshot is registered AND readable in-scope) is resolved for this candidate
by the in-scope snapshot directory. Owned scope respected throughout: only
`MUSE-REPORT-1164.md` touched; no Lean, Rust, or existing files modified.
