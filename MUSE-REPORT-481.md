# MUSE-REPORT-481: Independent exact-candidate review of 433 (re-review of repaired candidate)

Clone verified: /home/simon/Dokumente/gabbro-muse/a481, branch muse/481. Owned deliverable is this report only. This is a fresh substantive re-review of the NEW pinned snapshot after author repairs; the previous verdict on `c1cc7b96` is superseded.

## Candidate under review

- Author lane 433, pinned HEAD `7f8781c61fee0a20ce84fee3d517d06dd3d52ac0`, base `fd14b4e5` (per `.tmp/review/SNAPSHOT.json`; HEAD not present in my clone, so review ran off the supplied `PATCH.diff` plus the supplied file copies, staged temporarily in my clone and restored afterwards).
- Files: `MUSE-REPORT-433.md` (new), `grammatik/Grammatik.lean` (one additive import line), `grammatik/Grammatik/X86/ObservationProjection.lean` (new, 331 lines). No other files touched: no source/checker/goal/Rust/emitter/Typen/execution/codec changes, no friend paths.

## Reproduction in my clone (re-run against the new snapshot)

- Copied the supplied `ObservationProjection.lean` into `grammatik/Grammatik/X86/` and appended the umbrella import, then ran `./lean-probe grammatik/Grammatik/X86/ObservationProjection.lean`: **0 errors**. Axiom report matches the author's evidence exactly: `beobAusgang_verweigert`/`beobGleich_refl`/`V0_*` axiom-free; everything else depends only on `propext` and/or `Quot.sound` — subsets of the `gabbro_ziel` standard set, no new axioms.
- Afterwards removed the staged files and restored the umbrella from backup; `git status` clean before writing this report.

## What changed between `c1cc7b96` and `7f8781c6` (every previous finding re-inspected)

- The new PATCH carries the new-file blob `9e643b30` for `ObservationProjection.lean` — the identical Git blob hash as the previously reviewed candidate — and the umbrella hunk is the same single additive import line. The supplied file copy is byte-identical to the PATCH body (verified by extraction and comparison). **Lean content is unchanged**; no proof was edited, weakened, or added.
- The only delta is `MUSE-REPORT-433.md`: a new section "Repair pass after integration-gate failure" analysing the coordinator merge-build failure (`397/398 Building Grammatik`, `failed to create thread`, exit 134), noting the integration log printed all fourteen `#print axioms` lines (module elaborated successfully; only the single-process umbrella step failed), performing no Lean change, and naming the blocker as coordinator-side thread/memory headroom for the ~397-import umbrella elaboration with remedies outside the lane's owned files.
- Assessment of the repair: correct handling. An environmental thread-spawn failure cannot be fixed by editing verified-green proofs, and editing them would only invalidate the isolated review. The author's claim that the module built cleanly inside the integration build (axiom lines printed) is consistent with the evidence. No new defect introduced, no previous finding left unaddressed — there were no open findings; the re-review confirms none have appeared.

## Correctness checks (against actual accepted models, not just green output)

- Dependencies are real: `ripNach`, `regSet`, `regSet_fremd`, `schritt`, `schritt_movImm64`, `schrittRegister`, `laengeOk`, `lauf`/`zeugeProg`/`zeugeZustand`, `byteschritt`/`ketteStart`/`ohneExecStart`/`ByteAusgang` all resolve to the accepted `Ausfuehrung`/`Byteschritt` vocabulary in my clone. Imports are exactly `Typen`, `Speicher`, `Ausfuehrung`, `Byteschritt`. No second IR, no second executor, no duplicated semantics.
- Main theorem `movImm64_tot_erhaelt_beob`: genuine preservation fact (conclusion over successor states `s' t'`, not a premise restated). Every premise is used in the proof (hok/hbef via the two `schritt_movImm64` rewrites, hs/ht via cases, hgleich destructured into all four legs, htot to derive `r ≠ dst`). No `Prop`-typed premise, no `forall rho`/`forall v` contract quantification, no discarded premise.
- Joint witness `movImm64_tot_erhaelt_beob_zeuge`: instantiates all premises together on concrete twins, applies the main theorem (not a restatement), and proves a real dead-register difference (`by decide`). Non-degenerate: twins differ really in `rax` (0 vs 99) and in one hidden byte. Memory-changing execution is covered by `zeige_beob_speicher_aendert_sich` (accepted `lauf` chain, visible cell 0 -> 42, live `rbx` 42, all `by decide` over real definitions). Negative case `zeige_fehler_beobachtbar` is a real fault-vs-success split (`ketteStart` steps, `ohneExecStart` refuses). No vacuity, no forged evidence.
- Design judgments are sound: RIP and flags are included in `BeobGleich` (hiding them would falsely equate states with different futures); faults project to one coarse `fehler` with no false granularity; liveness is an explicit per-point premise the consumer must establish. CUTS block states exactly what is open (other pilot forms, fault identity, run-level observation, source bridge).
- Forbidden patterns (re-scanned on the new snapshot): no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`/`have _ :=` (the one grep hit class is `#print axioms` lines only). File ends with CUTS plus per-theorem `#print axioms`. English natural language (non-ASCII hits are standard Lean symbols only). Imports unchanged: exactly `Typen`, `Speicher`, `Ausfuehrung`, `Byteschritt`; no friend paths.

## Full-build status

- Author reports `./lean-bau` red only at the final umbrella step (`failed to create thread`, exit 134), with a clean-tree control failing identically, and all 394 module targets including the new one building. Build evidence shows repeated identical failures across runs plus the stash-control. I did not rerun full `./lean-bau` in my clone (different, newer base; heavy queued build), but the failure signature is unambiguously environmental (thread spawn, not elaboration), the control experiment is documented, and my own module-level reproduction is green. The HARD RULE 8 deviation (keeping green-verified work despite red umbrella) is explicitly disclosed in the author's report with reasoning; I concur it is the right call here.
- No Rust work claimed or needed; no corpus files touched.

## Defects found

None material. No repair direction to give.

## Verdict

ACCEPT of the precisely delivered bounded claim: canonical target observation projection shape plus the pilot dead-register internal-move preservation fact with joint witness, memory-changing run, scratch-hidden probe, and negative observable-fault case. Not a claim of full compiler closure, and the report does not present it as one.

CANDIDATE: 433 7f8781c61fee0a20ce84fee3d517d06dd3d52ac0
VERDICT: ACCEPT
