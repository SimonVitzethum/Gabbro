# MUSE-REPORT-1027: exact review of author 877 (displacement peephole rule)

## Clone / branch verification

- Clone: `/home/simon/Dokumente/gabbro-muse/a1027`, branch `muse/1027` (verified via `pwd` + `git rev-parse`; HEAD `b040b155159f47629542b0083e2f0a8a607f2b4c` matches the review `SNAPSHOT.json` base).
- Reviewer owns ONLY this file. No source, no live controls touched. Reviewer-clone `grammatik/` contains no `OptPeepholeDisp.lean` and no `OptPeepholeDisp` reference (base clean, no contamination).

## CANDIDATE

CANDIDATE: 877 d97a14ee1ea7e9a1a139267e92d5f33d1764e627
- Files (from `SNAPSHOT.json` + `PATCH.diff`): `MUSE-REPORT-877.md`, `grammatik/Grammatik.lean` (one added import line), `grammatik/Grammatik/X86/OptPeepholeDisp.lean` (new, 360 lines). `clean: true`.
- Task: `OWNER-TASK.md` (lane 877, displacement peephole rule, `ZEUGE: OptPeepholeDisp_verbindung` + joint companion `OptPeepholeDisp_verbindung_zeuge`).

## Verdict

VERDICT: ACCEPT

Bounded accept (substantive verdict unchanged):

The candidate is a bounded optimiser rule lemma in the established house pattern (direct sibling: accepted lane 860 `OptFoldConst.lean`). It proves what it claims over the reused canonical vocabulary and defers everything else in precise CUTS. No repair required.

## What was checked

1. **Scope / reserves.** PATCH touches only the three listed files. No `OptimizationRules`/`OptimizationWitnesses` (friend-reserved), no source/checker/`Spec`/goal/emitter edits, no diagnostic/gift/example/CLI numbers, no `MARKE_EMIT` changes. `Grammatik.lean` diff is one import line.
2. **No banned constructs.** No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file (grep hits are English prose "admit/admitted" only). No `Prop`-typed premise. Ends with `CUTS:` block + `#print axioms` for every theorem.
3. **Architecture (byte forms, REX/width/flags, operands, faults, TSO, gates).** This lane kind is a source-level rule lemma, not a byte codec: it makes NO byte/REX/decoder claim, which is correct rather than a gap (byte rows belong to codec lanes; cf. lane 748 `CompactImm8Add`). Width is handled by the explicit `hW` bound + `dispWort_ganz` round-trip through canonical `Wort`. Flags are an opaque validator-decided `flagOk` (refuse-if-live), FP/NaN is refused via `keinNaNTausch` with the collapse proved from the accepted `ScalarFloat` row (`flt_nan_links`/`flt_nan_rechts` argument order verified against base signatures). Token-threaded ops (memory, call, check, atomic, faulting FP) are excluded by `keinToken`. No MXCSR/interrupt/TSO/silicon claim; all deferred in CUTS. No invented determinism, no zeroed/ignored defined effect.
4. **Premises used.** All four side conditions have refusal theorems; admission projects `passt` (`dispZulassen_passt`, correctly `hz.1.1.1` after the one fixed mis-projection visible in BUILD-EVIDENCE). Main connection uses `hz`, `hW`, `x`, `c`; `V/O/passes/R/rest/sigma/rho` occur in the `rfl` goals (same established shape as accepted 860). No `intro _` / `have _ :=` discard.
5. **Witness.** `OptPeepholeDisp_verbindung_zeuge` instantiates ALL premises jointly (`3 + 4 -> 7` under `⟨4, true, true, true, true⟩`, `leave` continuation) on non-degenerate `refD` (`refEin_schreibt`) beside reached memory-changing run `MB` (`refB_erreicht`, `refB_schreibt`; all three verified present in base `ReferenzB.lean`). The `_hz`/`_hW` underscores are existential-binder names, not premise discards (concrete `by decide` witnesses supplied).
6. **Negative evidence.** Four refusal theorems (one per side condition) + admitted probe + NaN-refused probe. Matches the house bar (860 has fewer probes).
7. **No guarantee weakening.** No `ensures` derived, fallback is the wider spelling never a warning, checker ranges untouched, no faulting form speculated above its guard.
8. **Claim boundary.** Report + file claim only source value/`execEnd`/bound-Bool/word-image; encoder, layout revalidation, cost booking, silicon, TSO/GX, `x - x`/FMA rows, source-to-byte all in CUTS with owning lanes.

## Reproduction

Report-only review: no candidate rebuild in this clone (owns report only). Green evidence is the pinned `BUILD-EVIDENCE.json`: `lean-probe` 0 errors, `lean-bau` "Build completed successfully (511 jobs)", axioms of both main theorems exactly `[propext, Classical.choice, Quot.sound]`. All externally referenced names verified present in this base (`flt_nan_links/rechts`, `dispWort`, `vertragVon`, `keinRuf`, `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`). Nothing suspicious found that required a queued-wrapper reproduction.

## Minor nits (bounded, not REPAIR)

- `MUSE-REPORT-877.md` count typos: "definitions (2)" lists 3 (`DispCert`, `dispPeepholeZulassen`, `dispPasstI32`); "theorems (16)" lists 17 names. True counts: 3 definitions, 17 theorems.
- `ucomiTausch_kollabiert` pins the left-NaN case (both ordered directions `false`); a right-only-NaN pin would symmetric-complete the IEEE justification but is not needed for the refusal.
- `passt` is a validator-decided Bool not formally linked to `dispPasstI32 c.disp` in the connection (sections 2 pins then stand as edge/generic facts). Same pattern as accepted 860; linking them is future hardening, not a soundness hole since nothing claims the semantic bound.
- Optional hardening: `decide` probes for the `passt`/`token`/`flag` refusals, mirroring the existing NaN probe.

## Last build result

No `./lean-bau` run in reviewer clone (report-only; no source changes to build). Candidate pinned evidence: `./lean-bau`: `Build completed successfully (511 jobs).`

## What remains open

Per candidate CUTS (not claimed): disp8/disp0 encoder rows + length function, layout `layoutOk` revalidation after shortening, `targetWork`/`expandBound` cost booking, silicon correspondence, TSO/GX bridge, `x - x`/FMA rows, source-to-byte validation.

## Task remarks

Nothing in the task appears wrong. The generic hardware-review checklist (byte forms, REX, TSO, gates) is correctly applied here as "no such claim made, soundly deferred", consistent with the accepted sibling rule lemma 860.
