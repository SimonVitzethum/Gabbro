# MUSE-REPORT-1256: Exact review of candidate 1255 — ACCEPT (content review, all checks pass)

CANDIDATE: 1255 5723f622baa7a434d2064000c49d132bed7d93cb

VERDICT: ACCEPT

## Assignment

Lane 1256: independent exact review of author lane 1255 ("Pipeline calls:
three-or-more-statement callee bodies"). Pinned snapshot
`.tmp/review/SNAPSHOT.json`: head
`5723f622baa7a434d2064000c49d132bed7d93cb`, base
`515546d0e2430c0d416ede74e3add0166e88e2de`, files
`MUSE-REPORT-1255.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/PipelineCallsN.lean`, clean flag true.
Delivery is AS FILES under `.tmp/review/author-1255/` (`PATCH.diff`,
the changed files at repository paths, `OWNER-TASK.md`,
`BUILD-EVIDENCE.json`); the author clone and pinned git objects are
deliberately not readable from this lane. Checklist per the lane file:
no sorry/axiom/native_decide, standard `#print axioms`, import-line-only
diff, premise use, evaluator lift, refusal probes, non-degenerate
witness, silicon facts, honest CUTS, no claim beyond the proof.

## Correction of my earlier rounds (withdrawn verdicts)

My three previous reports returned a procedural REPAIR because the pinned
git objects were missing from this clone ("bad object"). That premise
has been corrected by the coordinator: git objects are NEVER readable
from a reviewer clone, and "bad object" is not a finding about the
candidate. Those three verdicts judged reviewability under since-corrected
instructions, inspected nothing, and claimed no defect in the author's
code. They are WITHDRAWN in full and replaced by the content review
below. Nothing from them is preserved as a finding.

## What was done (content review of the delivered files)

1. Verified work location: clone `/home/simon/Dokumente/gabbro-muse/a1256`,
   branch `muse/1256`. Matches the lane file. Proceeded.
2. Read the pinned snapshot, `OWNER-TASK.md` (lane 1255 task: new file
   `PipelineCallsN.lean` plus one import line; follow-up generalising
   single-assignment callee bodies to three-or-more-statement bodies),
   the full `PATCH.diff` (913 lines: new 121-line author report, one
   `+import Grammatik.X86.PipelineCallsN` line after line 644 of
   `grammatik/Grammatik.lean`, new 771-line
   `grammatik/Grammatik/X86/PipelineCallsN.lean`), the author's
   `MUSE-REPORT-1255.md`, and `BUILD-EVIDENCE.json` (probe/build trail
   with intermediate failures honestly recorded and fixed).
3. Read the delivered 771-line candidate Lean file in full (all seven
   sections plus CUTS and `#print axioms`).
4. Banned-construct scan: strict regex over
   `\b(sorry|admit|native_decide|unsafe|split_ifs|norm_num|ring_nf)\b`,
   `^axiom `, `intro _$`, `have _ :=` on the delivered file: ZERO
   matches. The loose hits are English doc words ("admitted" in
   comments) and the `axiomCall` Stmt constructor in a pattern match.
   `PATCH.diff` likewise contains none outside the author's own
   "No sorry..." sentence.
5. Ran the authorised check on the delivered file itself:
   `./lean-probe .tmp/review/author-1255/grammatik/Grammatik/X86/PipelineCallsN.lean`.
   First output line: `== 0 error(s) in the COMPLETE output; exit 0`.
   The complete `#print axioms` output (45 names) matches the author's
   evidence exactly and stays inside the standard set: at most
   `propext`, `Classical.choice`, `Quot.sound`; 7 names axiom-free
   (`nwProg`, `nwBytes`, `nwChunk1/2/3`, `nwCode`, `nwDaten`,
   `nw_laenge_bytes`). No copy of the file into my tree was needed or
   made (write tooling restricts this lane to its owned files); the
   probe elaborates the delivered path directly against this clone's
   newer tree, which is the stronger check: every reused name resolves
   here too.
6. Premise-use audit by reading every proof: `rufExecN_teile`
   (unpacking, each conjunct used); all six refusal theorems (each
   hypothesis rewritten into the goal); `istAssignBlock_cons_inv`;
   `assignChunkN_lauf` (hc, hfremd via `calleeFremd_mem`, hT cast,
   hlo/hhi/hp/hE/hwr via `einzelChunk_lauf`); `assignBlockN_lauf_aux`
   (hle fuels both branches, hassign splits every case, hlow/hW/hE/hsrc
   threaded through head chunk and induction hypothesis);
   `assignBlockN_lauf` (all five hypotheses forwarded);
   `rufExecN_korrekt` (hval unpacked; hsep/hfremd/hW/hE/hsrc into body
   induction; hcode/hrip into `lauf_zu_laufBytes`). No `Prop`-typed
   premise, no discarded hypothesis, no conclusion restating a premise,
   no contract quantification, no non-memory-changing "semantics".
7. Lift-not-copy audit: every load-bearing step applies an accepted
   theorem by name (`einzelChunk_lauf`, `worldRep_store`,
   `lauf_zu_laufBytes`, `validate_sound`, `optimise_nil`,
   `ketteLauf_lauf`, `senkBlock_assign`, `constInt?_sound`,
   `repOk_int`, `calleeFremd_mem`, `codeAt_von`, plus the
   `rufWit_*`/`pw*`/`cw*` witnesses). The file's own `cases s with`
   enumerates all 27 `Stmt` constructors, confirmed by the green probe.
   No second machine, loader, decoder row, or source interpreter.
   `OptimizationRules` is opened for `optimise_nil` reuse, not edited;
   `PATCH.diff` confirms no reserved file is touched.
8. Refusal audit: four poison probes each prove a genuine `= false`
   equation on concrete data — one-statement body (`cwBody/cwBytes`
   via length refusal, side condition closed by `decide`), body with a
   check (`pwSrc/pwBytes` via shape refusal, `decide`), red-zone call
   (frame refusal), tampered byte (`nwBytes.set 0 0` via byte refusal,
   `decide`). The green probe means every `decide` side condition
   really held.
9. Witness audit: `nwBody` is three `assignSlot`s; `nw_quelle` proves
   the REAL `execBlock` run moves row 0 `7 -> 35 -> 42` and row 1
   `9 -> 6` (every step memory-changing); the joint
   `rufExecN_korrekt_zeuge` conjoins the table write (`pwHw`), the
   admitted frame, validated bytes by computation (`nw_rufExecN`),
   represented world/environment, reached source run, reached byte run
   with all six callee-saved registers preserved, composed chunk runs,
   and observably changed frame-save bytes. Non-degenerate.
10. CUTS/silicon audit: the CUTS block explicitly keeps one/two-statement
    bodies, checks, loops, calls, floats, certificates, TSO/GX, time,
    spills, loader/entry/relocation, and any silicon correspondence
    beyond the accepted producers OUT of the claim. Bytes come from the
    reused `encodeAll` and are accepted only by recomputation
    (`validate` + `decide`). No W/GX or hardware-correspondence claim
    exists to reject.

## New definitions / theorems

None by this lane. The candidate's new names (author lane 1255):
`istAssignStmt`, `istAssignBlock`, `blockLaenge`, `istDreiPlus`,
`rufExecN`, `rufExecN_teile`, `istDreiPlus_verweigert_form`,
`istDreiPlus_verweigert_kurz`, `rufExecN_verweigert_rot`,
`rufExecN_verweigert_form`, `rufExecN_verweigert_kurz`,
`rufExecN_verweigert_bytes`, `istAssignBlock_cons_inv`,
`assignChunkN_lauf`, `assignBlockN_lauf_aux`, `assignBlockN_lauf`,
`rufExecN_korrekt`, `nwV6`, `nwV42`, `nwBody`, `nwProg`, `nwBytes`,
`nw_laenge`, `nw_drei`, `nw_rufExecN`, `nwChunk1/2/3`, `nwMemBytes`,
`nwCode`, `nwDaten`, `nwMem`, `nwStart`, `nw_laenge_bytes`, `nw_code`,
`nw_worldRep`, `nw_envRepr`, `nw_rip`, `nw_quelle`,
`nw_chunks_laufen`, `nwProbe_kurz/form/rot/bytes`,
`rufExecN_korrekt_zeuge`.

## Last `./lean-bau` / `./lean-probe` result lines

- `./lean-probe` on the delivered candidate file:
  `== 0 error(s) in the COMPLETE output; exit 0` (measured by this lane,
  just now, against this clone's tree).
- `./lean-bau` on the clean master baseline (this lane's tree, without
  the candidate import): `Build completed successfully (658 jobs).`
  The full-project build WITH the candidate import line was measured by
  the author (`Build completed successfully (644 jobs)`, in
  `BUILD-EVIDENCE.json`) and not re-measured here: adding the local
  import line is outside this lane's owned files, and the standalone
  probe already elaborates the complete candidate module green against
  this newer tree.

## Reasons for ACCEPT (concrete)

1. The delivered module elaborates with 0 errors and its 45
   `#print axioms` outputs are all within the standard set
   (`propext`, `Classical.choice`, `Quot.sound`), matching the author's
   evidence exactly. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
   no banned tactics, no discarded premises.
2. The diff shape is exactly as tasked: one new Lean file, one import
   line, one author report. No existing file weakened, no reserved
   optimiser file touched.
3. Correctness is proved against the REAL source run (`execBlock`) and
   the FETCHED byte run (`laufBytes`), reusing the family's accepted
   evaluator chain (`einzelChunk_lauf`, `worldRep_store`,
   `validate_sound`, `lauf_zu_laufBytes`, `ketteLauf_lauf`) by name —
   lifted, not copied — with callee-saved preservation across the whole
   three-or-more-statement body.
4. All four refusal paths fire on concrete planted data (short body,
   check body, red zone, tampered byte), each as a proved `= false`
   equation; the joint witness is non-degenerate (table written,
   every source step memory-changing, reached byte run preserving all
   six callee-saved registers).
5. CUTS are honest and the claim stays inside the proof: no TSO/GX,
   time, silicon-correspondence, loader, or optimiser-certificate
   claims. No desired-correctness premise, no weakened guarantee.
6. The author's report addenda answer the earlier procedural rounds
   without touching proved code, and `BUILD-EVIDENCE.json` shows the
   genuine development trail including fixed intermediate errors.

## What remains open

Nothing for this lane. The candidate is accepted as reviewed. Its own
CUTS (pairs, checks, loops, calls, floats, certificates, TSO/GX, time,
spills, loader/entry, silicon correspondence) stay open as stated and
belong to future lanes.

## Task correctness note

The lane task's original review method (diff in the author clone) is
unreachable by design for an isolated reviewer; the file-delivery
correction resolves this. Suggest keeping the delivery layout
(`PATCH.diff` plus files at repository paths plus build evidence) for
future report-only exact reviews.
