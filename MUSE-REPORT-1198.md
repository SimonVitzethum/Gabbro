# MUSE-REPORT-1198: exact review of lane 1197 (block-level table reads, scaled-index addressing)

CANDIDATE: 1197 c3da85d5bce725a2dfb7379dbd4bda09f7a44d7b
VERDICT: REPAIR

Reviewed material (all in-clone): `.tmp/review/SNAPSHOT.json` (head above, base
4ed3590d, files MUSE-REPORT-1197.md + Grammatik.lean import line +
PipelineBlockTables.lean, clean true), `.tmp/review/author-1197/PATCH.diff`
(1808 lines), the snapshot copy of `PipelineBlockTables.lean` (1666 lines),
author report and `BUILD-EVIDENCE.json`, `lanes/1197.md`. The candidate is NOT
applied in this clone (this lane owns only this report), so no candidate build
was run here; `./lean-bau` below is master state without the candidate.

## Repair reasons (concrete)

R1 — Missing `_zeuge` for the correctness theorems (HARD RULES 13).
`senkSkalLesen_korrekt` (file line 509, quantifies over `TabAnker D` and an
`Expr`), `senkStmtSkal_korrekt_slot` (1187), `senkStmtSkal_korrekt_durch`,
`senkStmtSkal_korrekt` (1481) all take universal syntax premises and have no
`_zeuge` companion. The author declares this OPEN in CUTS and in the report,
which is honest but does not satisfy the rule. The refusal witnesses exist
and are non-degenerate (see Passes), but the correctness witnesses over a
scaled anchor with concrete `WorldRep`/`EnvRepr` proofs are absent.

R2 — The task-required fetched-bytes closing theorem is missing.
`lanes/1197.md` demands a correctness theorem in the style of
`pipeline_correct_entry` (source `execBlock` result related to the byte-level
run on the loaded image). Committed is statement-level correctness against
the `execStmt` outcome plus the straight-line shape lemma
(`senkStmtSkal_gerade`); there is no `senkBlockSkal_korrektBytes` over
`laufBytes`/`CodeAt` (zero matches in the file; `laufBytes`/`CodeAt` appear
only in the reuse-list prose). The file header still promises "the
correctness theorem over fetched bytes" while CUTS lists it OPEN — the header
overclaims. Either prove the closing theorem (the author sketches the
missing transport lemma from `envGet_set_idx`) or narrow the header to what
is proved.

R3 — No full-project build evidence for the candidate, stale base.
`BUILD-EVIDENCE.json` contains only `./lean-probe` runs and one `git status`;
there is no `./lean-bau` entry, so the claimed `Build completed successfully
(627 jobs)` is unevidenced. The snapshot base 4ed3590d predates this clone's
master (which builds 687 jobs without the candidate). Rebase onto current
master and attach a green `./lean-bau` result line before integration.

R4 — Axiom lists not independently verifiable from here. The file ends with
`#print axioms` for every main theorem (lines 1629-1666, good), but the probe
evidence excerpts carry no `info:` output lines, and the candidate cannot be
built in this review clone. Standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) are therefore taken on the author's word; the merge gate must
re-check them mechanically at integration.

## Passes (checked, no finding)

P1 — No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in code. Grep over
the snapshot file finds these tokens only inside the prose word "admitted"
(scale/stride/load-form admissions, each refused elsewhere by a named
theorem) and inside `#print axioms` lines.
P2 — Existing files untouched except the single appended
`import Grammatik.X86.PipelineBlockTables` line in `grammatik/Grammatik.lean`
(PATCH confirms; the diff touches exactly the 3 snapshotted files).
P3 — Accepted evaluator lifted, not copied. The file reuses lane-1159
anchors/layout/world (`TabAnker`, `ankerBasis`, `ankerZeile`, `feldOff`,
`WorldRep`), pipeline machinery (`PipeCfg`, `cfgOk`, `abbOf`, `EnvRepr`,
`kanon`, `lauf_anhang`), addresses (`skaliertAddr`, `skalaOk`,
`basisKeinForm`, `adrOk`) and machine steps. No second IR, no second source
interpreter, no per-program rule.
P4 — Refusals really refuse, witnesses non-degenerate. Seven refusal shapes
(non-variable index, missing base/row/field, non-1/2/4/8 stride, `rsp`
index, wrong base register) plus seven `.durch` corollaries, each theorem
proved by `simp`/`rfl` on the lowering definition and each with a joint
`_zeuge` combining the `none` refusal (`rfl`) with the table-writing program
(`zeV.schreibt false = true`) and the memory-changing run (`zeRunChange`).
Spot-checked `senkSkalLesen_nichtvar_slot_zeuge` and
`senkSkalLesen_ohne_basis_zeuge`.
P5 — Silicon. No new encodings are invented: scale factors 1/2/4/8 come from
the reused `skalaOk`, the doubling soundness (`Z = 2 ^ skalExp Z`) is proved
in-file (`skalExp_sound`), and excluding `rsp` as the index register matches
the SIB encoding (index field 100b means no index). Pilot `load64`/`addReg64`
forms are reused, not redefined. No hardware-correspondence or W/GX claim is
made; CUTS stays inside the proved boundary.
P6 — CUTS honest (Done vs two OPEN items, matching the file), premises
spot-checked as used (`hbnd` consumed in both arms of
`senkSkalLesen_korrekt`), English throughout.

## Build and task notes

- `./lean-bau` on this clone (master, candidate NOT applied): last result
  line `Build completed successfully (687 jobs).`
- New definitions/theorems by this lane: none (report-only review).
- On the lane-1197 task text: nothing wrong found. It names no explicit
  `ZEUGE:` target line, but HARD RULES 13 applies mechanically to the
  syntax-quantified correctness theorems anyway, hence R1.
- What remains open for the author: R1 witnesses, R2 closing theorem (or
  header narrowing), R3 rebase plus evidenced full build; then re-review.
- An earlier revision of this report (committed as b9500e19) recorded that no
  candidate was visible; that was superseded when the `.tmp/review`
  snapshot was found in-clone. This revision is the full exact review.
