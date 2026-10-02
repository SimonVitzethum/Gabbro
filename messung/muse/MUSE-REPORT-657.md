# Muse Report 657: Review of author 656 (fetched conditional byte-step flag dependency simulation)

## Scope and method

Review-only task. No source edits made; this report is the only owned file.
Inspected the exact pinned snapshot `.tmp/review/SNAPSHOT.json`, the owner
task `.tmp/review/author-656/OWNER-TASK.md`, the author report
`.tmp/review/author-656/MUSE-REPORT-656.md`, the build evidence
`.tmp/review/author-656/BUILD-EVIDENCE.json`, the patch
`.tmp/review/author-656/PATCH.diff`, and the full pinned module
`.tmp/review/author-656/grammatik/Grammatik/X86/FetchedCondBranch.lean`
(592 lines). Verified every consumed accepted API by name in this clone's
`grammatik/Grammatik/X86/` tree. Reproduced the pin arithmetic
(4096+6+16=4118 taken, 4096+6=4102 fall-through, 5 truncated bytes) with a
read-only computation. Ran read-only scans for forbidden tactics.

CANDIDATE: 656 34de88ff490f365ca61ef4c1e27ee3971d7e4483

VERDICT: ACCEPT

## What the pinned work does (verified against the file)

New file `grammatik/Grammatik/X86/FetchedCondBranch.lean` plus a one-line
import in `grammatik/Grammatik.lean`; no other files touched. Contents:

- Fetch identity derived from equal actual code bytes, execute map and RIP:
  `holeFetchAux_gleich`, `geholt_gleich`, `fetchDekodiert_gleich`. The
  consumed-prefix leg reuses accepted
  `SourceCodeFrame.ausfuehrbarN_gleich` (the author's duplicate was removed
  after the full-build collision recorded in the build evidence). Nothing
  about the second execution is assumed identical.
- Main consumer `fetchedJcc_stabil`: where `fetchDekodiert` yields
  `.jumpIf32 c disp` from actual fetched bytes, agreement on exactly the
  consumed flags (`stimmtUebberein c`) plus equal code/map/RIP gives the
  same successor RIP, the same `bedingung` outcome, the derived second
  fetch, and the same `byteschritt` outcomes. The second fetch is derived
  via `fetchDekodiert_gleich`, the decode shape via accepted
  `fetchDekodiert_entspricht`, the length via accepted
  `decodeJumpIf_laenge`, the step agreement via accepted
  `jccSchritt_stabil`. All seven premises are used.
- `fetchedJcc_len_layout`: fetched length equals the carried
  `BranchLayout` length (`zweigLaenge true .weit` = 6).
- Lowering connections: `cmovLower_fetched_stabil` derives byte-step select
  stability from an admitted `cmovLowerOk` via its proved guarantee
  `cmovLowerOk_garantiert` (checked length plus flag identity; identity
  implies read-set agreement for every condition). All premises used.
  `wahlOk_fetched_notwendig` proves the two flag states take different
  fetched `je` successors via accepted `Anweisungswahl.zweig_weicht_ab`
  and the accepted `schritt_jumpIf32_*` equations. Note: despite its name
  it does not take a `wahlOk` boolean as a premise; it proves the
  divergence that makes the refusal load-bearing. True as stated, but the
  `wahlOk` link is motivational rather than formal. The `cmovLowerOk`
  connection alone satisfies the task's "one lowering optimisation"
  requirement, so this is a bound on wording, not a defect.
- CMOVcc/SETcc stay on their real `ControlCodec` byte helpers:
  `cmov_e_unverbraucht_stabil`, `setcc_e_unverbraucht_stabil` (under `.e`
  only ZF is consumed; `FlagName` has exactly `cf|pf|zf|sf|of_`, AF absent
  by construction, so the case splits are exhaustive and AF freedom is
  automatic), `cmov_setcc_len0_verweigert`. No `fetchDekodiert` path is
  forged for them; the missing path is an explicit CUT.
- Witness states use actual `encode (.jumpIf32 .e fjDisp)` bytes, never
  hand-written positives. The hand-written bytes appear only in the
  negative probe `fjFalschBytes` (mutated opcode that must refuse), which
  is legitimate planted-mutation practice.
- Concrete `decide` pins: `fj_kante_genommen` (4096 -> 4118),
  `fj_kante_ander_stabil`, `fj_kante_af_stabil`, `fj_mutation_faellt_durch`
  (ZF clear -> 4102), `fj_stumpf_verweigert`, `fj_ohneExec_verweigert`,
  `fj_falsch_verweigert`. Arithmetic reproduced independently.
- Joint witnesses: `fetchDekodiert_gleich_zeuge` (both flag variants fetch
  identically), `fetchedJcc_stabil_zeuge` (taken edge plus a store after it
  changing the data byte 0 -> 42, plus the truncation refusal),
  `cmovLower_fetched_stabil_zeuge` (admitted lowering, selected value 20
  stored and read back, plus the flag-clobber refusal). The memory-changing
  runs satisfy the lane's joint-witness demand at byte level (no source
  tables exist at this level, so the source-table clause does not apply).

## Rule and guardian checks

- No `sorry`, `admit` (one English comment word "admit no transition" only),
  `axiom`, `native_decide`, `unsafe`; no `Prop`-typed premise. The inner
  `intro n _` in `cmovLower_fetched_stabil` discards only the local
  read-membership hypothesis where full flag equality makes it unneeded; the
  theorem's own premises are all used. This proves something stronger, not
  weaker.
- `CUTS:` block present and truthful; `#print axioms` for every main
  theorem present. Final build evidence shows all axioms within `propext`,
  `Classical.choice`, `Quot.sound` with no `sorryAx`; intermediate
  `sorryAx` states in the evidence log were repaired before the final
  green run.
- Last build evidence: `./lean-bau` green, `Build completed successfully
  (458 jobs)`; `./lean-probe` on the new file 0 errors.
- One import appended to `grammatik/Grammatik.lean`; no checker, Spec,
  goal, Rust, emitter, existing-model, or friend-reserved
  `OptimizationRules`/`OptimizationWitnesses` edits. No new executor,
  decoder, or source condition language. No source-syntax leg is claimed;
  the file's CUTS honestly record no source/checker/TSO/concurrency/cost
  claim, matching the bounded byte-level consumer the owner task asked for.

## Precise accepted bounded claim

Fetch/decode identity from equal code/map/RIP; consumed-flag agreement
suffices for the same fetched `jumpIf32` successor RIP, branch outcome,
derived second fetch and `byteschritt` outcomes; fetched length is the
carried layout length; admitted `cmovLowerOk` implies byte-step select
stability; clobbering `xor` under live flags demonstrably diverts the
fetched `je` successor; `.e` consumes only ZF with exact non-consumed-flag
freedom; length 0 refuses both select steps; taken/unused-flag/mutation/
refusal pins and joint memory-changing witnesses as named above. Explicitly
not accepted and not claimed: hardware correspondence, any CMOV/SETcc fetch
path, liveness or optimiser decision procedures, multi-step chains,
TSO/GX, source, checker, Spec or goal.

## Remaining work for others

Multi-step fetched runs (`laufBytes`) with per-step read-set cover, or the
`zweigLaenge` bridge to an actual `ZweigBeleg` acceptance, as the author
suggests. Merge note: the candidate's `Grammatik.lean` hunk adds its import
against an older base; take the import union at merge (current master ends
with `ExtendedExecution`).
