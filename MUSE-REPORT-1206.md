# MUSE-REPORT-1206: Exact review of candidate 1205 (per-family reached fetch instances)

Lane 1206, report-only independent exact review.
Clone `/home/simon/Dokumente/gabbro-muse/a1206`, branch `muse/1206` verified.
Own file only: this report. No Lean or other source changes made.

## Candidate

- Author lane 1205, pinned HEAD `99f2ecab59c7da1772e7b0b7d39ea3eceaff5bdc`, base `4ed3590d85cf770cb098132aed8ee9752e29e013` (from `.tmp/review/SNAPSHOT.json`).
- Files: `MUSE-REPORT-1205.md`, `grammatik/Grammatik.lean` (one added import line), `grammatik/Grammatik/X86/HwBildInstanzen.lean` (new, 1617 lines).
- Reviewed the exact snapshot under `.tmp/review/author-1205/` (PATCH.diff + file copies), not the live author clone. No files outside this clone were touched.

## Checks (all against the snapshot)

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: strict word-boundary grep over `HwBildInstanzen.lean` finds zero hits. (Substring hits are only "admits" in prose and `#print axioms` lines.) Intermediate `sorry`/errors visible in `BUILD-EVIDENCE.json` are transient development states; the final `lean-probe` is 0 errors and the final `lean-bau` is green.
- `#print axioms` standard: 23 lines at end of file. Author evidence: `inst_fetch_*` depend on `[propext]` only, everything else on `[propext, Quot.sound]`, no `Classical.choice`. Both are within the goal's standard set (`propext`, `Classical.choice`, `Quot.sound`).
- Existing files untouched except one import line: `PATCH.diff` shows `grammatik/Grammatik.lean` gains exactly `import Grammatik.X86.HwBildInstanzen` and nothing else; no other existing file is modified.
- Every premise used: the concrete per-family theorems are closed (no premises). The three adapter theorems each consume their `h` via `simp [h]`; `instSchritt_wf` consumes both `h` and `hwf` in `hwSchritt_wf m m' e h hwf`. No `intro _` / `have _ :=` anywhere. No `Prop`-typed premises, no contract quantification.
- Family evaluator lifted, not copied: the file defines no decoder/evaluator/loader/adapter of its own (strict grep for `def` of `mulDivSchritt|mulLow|mulHighU|mulFlagsU|encodeShift|stepExt|adapterInteger666|hwBildStart|hwWf_aus|hwSchritt_wf` is empty). Images reuse the accepted encoders (`mulDivEncode`, `encodeShift`, `encodeSetCC`, `encodeCmov`, `fpEncodeMovsdRR`, `encodeVector`); successors are built only from accepted apply/step functions (`md_mul_erfolg` via `stepExt_muldiv_ok`, `shiftSchritt_weiter` via `stepExt_shift`, setcc/c Mov byte-step applications, `fpSchritt_movsdRR` via `stepExt_fp`, `stepVector_pxor` via `stepExt_vec`). The adapter is `adapterInstanzen := adapterInteger666` reused by name, with agreement/refusal/halt theorems proved by unfolding plus the hypothesis.
- Planted refusals really refuse: per family, `inst_dunkel_fetch_F` proves `fetchExt … = none` by `decide` (genuinely computed, not assumed), `inst_dunkel_verweigert_F` follows by `hwByteschrittReg_verweigert`, and `inst_kern1_verweigert_F` by `hwBild_ohne_exec_verweigert` with a `decide` side condition. Core 1 idles on the non-executable data page, so both refusal legs are live.
- Witness non-degenerate: each `instZeugeProp_F` is a 12-way conjunction containing owner forwarding (`instLoadEigen = 42`), foreign-old (`instLoadFremd = 0`), drain-to-shared (`instNachFlush = 42`, i.e. 0 → 42 in ACTUAL shared memory), foreign-new (`instFremdNachFlush = 42`), plus both refusal legs on a two-core machine. `inst_zeuge_F` joins all 12; `instAlle_zeuge` joins all six families. The memory change is proved about `s.mem.bytes`, not about a local projection.
- Silicon facts: no new encodings or flag rules are defined here; byte lengths (muldiv 3, shift/setcc/cmov/fp 4, vec 5) and observed values (MUL rax=42/rdx=0, SHL rax=42, SETcc rax=1 taken, CMOV rax=9 taken, MOVSD low=7, PXOR low lane `0xFFFFFFFFFFFFFFF8`) flow through the accepted encoders/evaluators and are additionally checked by `decide`d fetch/RIP/value theorems. The one documented silicon assumption (MUL keeps incoming SF/ZF/PF for architecturally undefined flag bits, as in `MulDiv.lean`) is named in CUTS, not smuggled into a proof.
- CUTS honest, no overclaim: the file CUTS block (lines 1552–1591) claims only self-consistency of the accepted subsets, explicitly disclaims hardware correspondence, per-access W/GX simulation, whole-word atomicity beyond reused guards, source/IR/ABI/loader/entry/budget links, LOCK RMW, and the full W/GX bridge. The report's open section matches. One interpretation point is disclosed rather than hidden: the six pinned rows are register-only, so each witness's memory-changing step is the TSO issue/drain stage (the family's own store forms must use the issue path, never the `reg` plug). That is stated in every witness doc and in CUTS. It satisfies the review's non-degeneracy bar (a real shared-memory 0 → 42 change on two cores) and is not presented as a family store step.

## Verification run

- `./lean-bau` in this clone (no source changes, report only): `Build completed successfully (630 jobs).` (Candidate's own base built 627 jobs per its evidence; the count differs because this clone sits on a newer master. Candidate final `lean-probe` 0 errors and candidate `lean-bau` green are taken from its committed build evidence.)

## What remains open

- Nothing for this lane: review-only, no implementation was owned or attempted.
- For the project: the CUTS-listed gaps above (hardware correspondence, W/GX bridge, source/entry/budget links) stay open by design.

## Notes on the task

- The lane file's candidate placeholder resolves via `.tmp/review/SNAPSHOT.json` to the pinned head named below; no correction to the task itself is needed.
- No new definitions or theorems were added by lane 1206.

## Verdict

CANDIDATE: 1205 99f2ecab59c7da1772e7b0b7d39ea3eceaff5bdc

VERDICT: ACCEPT
