# MUSE-REPORT-1142: exact review of candidate 1141 (HwIsaFamilies)

## Identity
- Review lane: 1142, clone `/home/simon/Dokumente/gabbro-muse/a1142`, branch `muse/1142`, HEAD `84c19acaf66e0f147235b0f5fb6f01c43e86e8a6` (verified via `pwd`, `git branch --show-current`, `git rev-parse HEAD`).
- Pinned snapshot: `.tmp/review/SNAPSHOT.json` names one candidate: author 1141, head `c2eefa9e65ff92c1fd8e4139df1434ca6c48ef67`, base `48a4be7c1c333a602ce0d0816979d154ae1bd959`, files `MUSE-REPORT-1141.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwIsaFamilies.lean`, clean true. Vendored copies under `.tmp/review/author-1141/` (`PATCH.diff` 1220 lines, `MUSE-REPORT-1141.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, snapshot `grammatik/` tree). Review read the snapshot copies only; nothing outside this clone.
- Owned files: only `MUSE-REPORT-1142.md`. No other file created or modified.

CANDIDATE: 1141 c2eefa9e65ff92c1fd8e4139df1434ca6c48ef67

## Checklist (all checked against the pinned snapshot)
1. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` — PASS. Word-boundary grep over the snapshot finds only the HARD-RULES text in `OWNER-TASK.md`; the new Lean file and the diff contain none. No `split_ifs`/`norm_num`/`ring_nf`.
2. `#print axioms` standard — PASS. Author build evidence lists every main theorem at `[propext]` or `[propext, Quot.sound]`; the file ends with `#print axioms` per main theorem (21 lines).
3. Existing files untouched except one import line — PASS. Diff touches exactly 3 files: new `MUSE-REPORT-1141.md`, one appended `import Grammatik.X86.HwIsaFamilies` line in `grammatik/Grammatik.lean` (hunk at line 601-604), and the new `HwIsaFamilies.lean`.
4. Every premise used; no Prop-typed premises; no contract quantification — PASS. No `intro _` / `have _ :=` in the new file. Spot-checked `adapterIsa_reg_stimmt` and `adapterIsa_gibAus_kein_speicher`: every hypothesis (`h`, selection equations) is consumed by the proof; conclusions are genuine existentials/equations, not restated premises.
5. Accepted evaluator lifted, not copied — PASS. Imports are the accepted modules (`HardwareExecution`, `ISA`, `ExtendedExecution`, `ISAWitnesses`); `stepI`/`stepExt`/TSO equations are applied via the accepted selection lemmas (`stepExt_*`, `issue_kein_speicher`, `coreSchritt_speicher`, `shiftSchritt_speicher`, `schritt_*_speicher`, `md_*`, `stepNarrow_*`, `setCCAnwenden_speicher`, `cmovAnwenden_speicher`), never redefined.
6. Planted refusals really refuse — PASS. Concrete refusal theorems: bad length (`adapterIsa_schlechte_laenge`, length 0), divide trap (via `stepI` and `stepIE`), memory forms on the register path, missing read/write permission; final `./lean-bau` green (601 jobs).
7. Witness non-degenerate — PASS. `isaFamM0` has two cores (core 0 steps, core 1 idles on the data page); chained reached steps M0->M1->M2->M3 change rax/rdx/rip; owner-only forwarding (`isaFamLoadEigen = 42` vs `isaFamLoadFremd = 0`); flush drains 0 -> 42 into actual shared memory; `isaFam_zeuge` joins wf, all three step observations, the store refusal, and the forwarding/foreign/flush facts.
8. Silicon facts — PASS within the claimed scope. SDM headings (MOV/LEA/NOT/NEG/TEST/JMP/ADD with volume/page) are cited as provenance only; CUTS explicitly disclaims hardware correspondence and silicon proof. No green proof of a wrong silicon fact found.
9. CUTS honest, no overclaim — PASS. CUTS names as OPEN: byte-decoder agreement, any `Byteschritt` connection, per-access W/GX simulation, whole-word atomicity (left to word-grouping owners), LOCK/interrupts/further faults/timing. No W/GX or hardware-correspondence claim anywhere.
10. `./lean-bau` — PASS per author `BUILD-EVIDENCE.json` final entry (`Built Grammatik`, 601 jobs, success); my own base-tree run this turn also green (`exit 0; 0 errors`, 606 jobs on unmodified base — base only, reported for completeness).

## Note on the earlier procedural finding
The previous revision of this report recorded a procedural REPAIR because no pinned HEAD was supplied and the candidate was unreachable. The pinned `.tmp/review/SNAPSHOT.json` with vendored exact copies resolves that: this substantive review supersedes the procedural finding (it does not overturn any finding against the work — there was none, since the work had not been seen). Keeping the old procedural refusal now would be the fake outcome, not granting it.

## Last `./lean-bau` result line
Author evidence: `Build completed successfully (601 jobs)` with the candidate applied. Own base-tree run: `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (606 jobs)`.

## What remains open
- Serial integration/publication of candidate 1141 (coordinator-side; not this lane's call).
- Nothing open on the review itself.

VERDICT: ACCEPT
