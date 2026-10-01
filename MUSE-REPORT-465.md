# MUSE-REPORT-465: Independent exact-candidate review of 417

## Re-review of the repaired candidate (new HEAD)

Pinned snapshot `.tmp/review/SNAPSHOT.json` now points at author-417 HEAD
`519e6373b6548a0358c8727ed7495278174d3f25` (was `ee5d6ffd`).
Fresh substantive re-review performed on the NEW pinned files:

- The Lean content is byte-identical to the previously reviewed candidate:
  new-file blob `6dbea0d5` (same git content hash as in the old PATCH), same
  318 lines, same one-line umbrella import (`6e68b11c..dc673df7`, same hunk).
  The delta `ee5d6ffd` -> `519e6373` is report-only: the author's addendum
  on the integration-gate failure (commit message: "no Lean change").
- Every previous finding re-inspected against the new files: no changed
  proof, no new premise, no weakened conclusion, no new scope. All prior
  checks (reused-name shapes, `Befehl` without cmov, premise use,
  no-speculation discipline, no second IR, witness non-degeneracy, CUTS
  honesty, additive-only diff) stand unchanged.
- Freshly reproduced in this clone on the NEW supplied file (staged only
  the candidate module, deleted afterwards, tree verified clean):
  `./lean-probe` gives `== 0 error(s) in the COMPLETE output; exit 0`
  with the same 17 standard axiom lines (`[propext]` / none for
  value-framing-guarantee theorems, `[propext, Quot.sound]` for the store
  consumer and all four witnesses). Forbidden-keyword grep: zero hits.
- On the author's addendum (integration gate failed at the umbrella
  import-all step, "nothing repaired because nothing owned is broken"): the
  assessment is correct. The module elaborated cleanly in the integration
  build too (all 17 axiom lines print at step [397/398]); the crash
  signature (`failed to create thread`, exit 134) matches the author's
  stash experiment proving pre-existing failure on unmodified master.
  Declining to edit green proofs or delete required `#print axioms` lines
  is the right call -- that would be a fake fix. Resolution is operational
  (quiet-machine rebuild), not a Lean change. The addendum strengthens the
  evidence record; it does not alter the bounded claim.

Verdict below is pinned to the NEW HEAD. The old HEAD `ee5d6ffd` is stale
and no longer approved.

## Second re-review (HEAD `5c113423`)

Snapshot now pins `5c113423d32d6f2181d16f0ffecad7d291ddc686`
(was `519e6373`). Delta `519e6373` -> `5c113423` is again report-only:
"Addendum 2: repeated identical gate failure" (commit message confirms
"no Lean change"; BUILD-EVIDENCE entries 32-34 show a fresh module probe
exit 0 plus a byte-identical umbrella thread-spawn abort, exit 134).

- Lean content still byte-identical: new-file blob `6dbea0d5`, same
  one-line umbrella import, same file list. No changed proof, no new or
  weakened premise, no scope change. All prior findings stand.
- Freshly reproduced in this clone on the NEW supplied file (md5
  `2d8cdd0d8fbd009920e56ea27eff64c3`, staged then deleted, tree clean):
  `./lean-probe` gives `== 0 error(s) in the COMPLETE output; exit 0`
  with the same 17 standard axiom lines. Forbidden-keyword grep: zero hits.
- Addendum 2 assessment is correct and consistent with the evidence: same
  crash signature after all 17 module axiom lines print, same failure on
  unmodified master, still no owned defect, still no Lean change indicated.
  Verdict moves to the NEW HEAD; `519e6373` is now stale.

## Scope (original review, still valid)

Reviewed the exact pinned candidate files from `.tmp/review/SNAPSHOT.json`
(author 417, HEAD `519e6373b6548a0358c8727ed7495278174d3f25`):
`MUSE-REPORT-417.md`, one-line additive import in `grammatik/Grammatik.lean`,
and the new module `grammatik/Grammatik/X86/ConditionalMove.lean`
(1 def + 17 theorems, 318 lines), against the owner task, the PATCH, and the
actual accepted models in this clone (`ControlFlow.lean`, `Ausfuehrung.lean`,
`Typen.lean`).

## Method

- Read the full candidate module, the PATCH diff, the author report, and every
  entry of `BUILD-EVIDENCE.json` (including the intermediate failing probes,
  which show real incremental work, not a pasted result).
- Verified every reused name exists in this clone with a matching shape:
  `cmovAnwenden`, `cmovSchritt`, `cmovMemSchritt`, `cmovMem_feheler_bleibt`,
  `cmovSchritt_genommen`, `cmovAnwenden_flags/speicher`, `witTrue`/`witFalse`/
  `witSpeicher`, `cmov_speicher_zeuge`, `cmov_witness_unterscheidet`,
  `schritt_store64_erfolg`, `laengeOk`, `ripNach`, `effAddr`.
- Confirmed `Befehl` (Typen.lean) has no cmov constructor, so the author's
  OPEN codec/source/native-ISA position is factually correct.
- Staged ONLY the supplied candidate module file in this clone, ran
  `./lean-probe` on it, then deleted it. Working tree verified clean
  afterwards (`git status --short` empty).

## Reproduced evidence (this clone)

- `./lean-probe grammatik/Grammatik/X86/ConditionalMove.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- All 17 `#print axioms` lines print and match the author's claim exactly:
  value/framing/guarantee theorems on `[propext]` or no axioms; the store
  consumer and all four witnesses on `[propext, Quot.sound]`. Subset of the
  allowed triple everywhere; no `sorryAx`.
- Forbidden-keyword grep (word-boundary `sorry`/`admit`, leading `axiom`,
  `native_decide`, leading `unsafe`): zero hits. The only substring hits are
  English prose ("admitted"/"admission") and `#print axioms` lines.

## Semantic checks

- Taken/untaken value equations and foreign-register preservation follow
  directly from the accepted `cmovAnwenden` definition; proofs are
  `unfold`+`simp`, no hidden assumption.
- Step framing (`flags`/`speicher`/`rip`) and both refusal theorems follow
  from the accepted `cmovSchritt` shape (`laengeOk` match); every premise is
  used (hok rewrites, hstep destructured).
- `cmov_store_verbraucher` correctly threads the accepted
  `schritt_store64_erfolg`: `hbed` rewrites the selected word, `hne`
  (`base != dst`) preserves the store address via `cmovAnwenden_fremd`,
  `cmovAnwenden_speicher` aligns the memory, `h`/`hok`/`hwr` drive the store.
  The `base = src` and `dst = src` aliasing cases remain sound under the
  stated premises. All five premises used.
- No-speculation discipline respected: the register-only theorems touch no
  memory, and the memory form's untaken-path fault is reused from the accepted
  `cmovMem_feheler_bleibt`, not restated or weakened. The task's explicit
  fault requirement is satisfied.
- No second IR/machine/executor: the only new definition is the `Bool`
  validator admission `cmovLowerOk` (decoded length + flag identity). No new
  `Zustand`, decoder row, memory model, or source claim.
- Witnesses pair concrete `decide` premises on the non-degenerate reused
  states (rax=10/rbx=20, taken/untaken split) with the memory-changing run
  `cmov_speicher_zeuge` (word 20 stored at 8192, byte observably changed).
  Minor note (not a defect): `cmovLowerOk_garantiert_zeuge` instantiates the
  flag conjunct reflexively; the substantive flag-identity content is covered
  by the separate `flags_verweigert` refusal. Acceptable for a `Bool`
  admission guarantee.
- CUTS block present at file end, honest and complete: no codec row/bytes,
  no hardware correspondence, no TSO/GX/concurrency/cost/time/termination
  claim, 64-bit select only.
- Umbrella diff is exactly one additive import line at the end; no existing
  file otherwise touched. The `gabbro_ziel` axiom claim is credible by
  construction (leaf X86 addition cannot move Zielsatz), and the author's
  stash experiment (BUILD-EVIDENCE entry: identical umbrella thread-spawn
  failure with the import stashed) proves the `./lean-bau` umbrella abort is
  environmental resource exhaustion, not caused by this lane. The report does
  NOT claim full `./lean-bau` green -- it reports 392/393 + the abort
  honestly. No forged benchmark evidence.

## Defects / repair direction

None. No unused premise, no vacuity, no duplicated IR, no safety weakening,
no forged evidence, no scope violation found. Nothing to repair.

## Bounded claim accepted

Register-only conditional-select facts over the reused pilot vocabulary
(taken/untaken equations, foreign-register preservation, decoded-step
framing, bad-length refusal, `cmovLowerOk` admission with guarantee plus
accepted/refused cases, one real canonical pilot-store consumer, joint
non-degenerate witnesses), with codec/source/hardware correspondence
explicitly OPEN. Not full compiler closure; nothing in the candidate claims
it.

CANDIDATE: 417 5c113423d32d6f2181d16f0ffecad7d291ddc686
VERDICT: ACCEPT
