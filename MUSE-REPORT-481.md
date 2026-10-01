# MUSE-REPORT-481: Independent exact-candidate review of 433 (second re-review of repaired candidate)

Clone verified: /home/simon/Dokumente/gabbro-muse/a481, branch muse/481. Owned deliverable is this report only. This is a fresh substantive re-review of the NEW pinned snapshot after author repairs; the previous verdicts on `c1cc7b96` and `7f8781c6` are superseded.

## Candidate under review

- Author lane 433, pinned HEAD `e708c266c7bece404de5054db76cc7320096f7c0`, base `fd14b4e5` (per `.tmp/review/SNAPSHOT.json`; HEAD not present in my clone, so review ran off the supplied `PATCH.diff` plus the supplied file copies, staged temporarily in my clone and restored afterwards).
- Files: `MUSE-REPORT-433.md` (new), `grammatik/Grammatik.lean` (one additive import line), `grammatik/Grammatik/X86/ObservationProjection.lean` (new, 331 lines). No other files touched: no source/checker/goal/Rust/emitter/Typen/execution/codec changes, no friend paths.

## Reproduction in my clone (re-run against the new snapshot)

- Copied the supplied `ObservationProjection.lean` into `grammatik/Grammatik/X86/` and appended the umbrella import, then ran `./lean-probe grammatik/Grammatik/X86/ObservationProjection.lean`: **0 errors**. Axiom report matches the author's evidence exactly: `beobAusgang_verweigert`/`beobGleich_refl`/`V0_*` axiom-free; everything else depends only on `propext` and/or `Quot.sound` — subsets of the `gabbro_ziel` standard set, no new axioms.
- Afterwards removed the staged files and restored the umbrella from backup; `git status` clean before writing this report.

## What changed between `7f8781c6` and `e708c266` (every previous finding re-inspected)

- The new PATCH carries the new-file blob `9e643b30` for `ObservationProjection.lean` — the identical Git blob hash as both previously reviewed candidates — and the umbrella hunk is the same single additive import line. The supplied file copy is byte-identical to the PATCH body (verified by extraction and comparison). **Lean content is unchanged**; no proof was edited, weakened, or added.
- The only delta is `MUSE-REPORT-433.md`: a second added section "Second gate failure, identical evidence" recording another byte-identical coordinator gate failure (all fourteen axiom lines print, then step 397/398 dies with `failed to create thread`, exit 134), a local `./lean-probe` re-run at 0 errors, and no Lean edit. Build evidence grew from 20 to 22 entries corroborating the commit sequence (`c1cc7b96` -> `7f8781c6` -> `e708c266`).
- Assessment: correct handling again. The blocker (coordinator-side merge-build resources for the ~397-import umbrella elaboration) is unchanged and outside the lane's owned files; editing verified-green proofs cannot fix it. No new defect introduced, no previous finding left unaddressed — there were no open findings across either prior review; this re-review confirms none have appeared.

## Earlier delta `c1cc7b96` -> `7f8781c6` (kept for audit)

- Lean blob `9e643b30` identical then as now; only delta was the first "Repair pass after integration-gate failure" report section. Assessment stands as written in the prior review.

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

CANDIDATE: 433 e708c266c7bece404de5054db76cc7320096f7c0
VERDICT: ACCEPT
