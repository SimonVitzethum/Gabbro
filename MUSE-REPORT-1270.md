# MUSE-REPORT-1270: Exact review of candidate 1269 (TsoGxCrossDecl)

## Candidate identity

- Author lane 1269, pinned HEAD `885ced69f3d7730ca4e45db33662f3de2813db8a`, base `c8bb4208`.
- Reviewed from the in-clone snapshot `.tmp/review/author-1269/` (`PATCH.diff`,
  `MUSE-REPORT-1269.md`, `BUILD-EVIDENCE.json`); no files outside this clone read.
- Candidate files: `grammatik/Grammatik/X86/TsoGxCrossDecl.lean` (new, 267 lines),
  `grammatik/Grammatik.lean` (+1 import line), `MUSE-REPORT-1269.md`. Clean tree.

## Checks performed

- Forbidden tokens: `PATCH.diff` contains `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  only in the report's prose sentence and `#print axioms` lines; the new Lean code has none.
  No `split_ifs`/`norm_num`/`ring_nf`, no `intro _` / `have _ :=`, no `(h : Prop)` premise.
- Scope: existing files untouched except the single appended import (mechanical
  merge note: candidate appends after `TsoGxChecker`; current master ends with `Avx2State`,
  so the merger places the import at the file end via the usual union).
- Lifting, not copying: every observable reuses accepted witnesses — lane 1253's
  `startFragment_zeuge` (entry/call prefix from `RufStartG`, `0 -> 5`), lane 1187's
  `brueckenLauf_erreichbar_zeuge` (bridged fragment run, `0 -> 42`, target drain
  `witM.bytes witA != witM'.bytes witA`), and `witHT` for the fragment carrier type.
  Verified the cited signatures exist in this tree (`TsoGxStart.lean:89`,
  `TsoRunInduction.lean:187`, `SourceMemory.lean:371`, `CarrierTraceBridge.lean:777`)
  with matching arity (20-component obtain).
- Shape facts verified against accepted defs: `eD.count = 1`, `eD.typ = .int 0 100`,
  `eD.geteilt = false` (`ZielOrtEinfadenZeuge.lean:72-86`); same triple for `witD`
  (`SourceMemory.lean:371-382`); `ctProg.rumpf = .ret .keine` (`CarrierTraceBridge.lean:777-781`).
  All claimed `rfl`s are genuine.
- Premise use: `crossCertOk_gleich` consumes `hok` via `of_decide_eq_true`;
  `crossCert_gibt_joint` destructures all seven certificate equations and rewrites each
  one into its conjunct (`hS0/hE5/hSE/hW0/hW42/hWE/hEq` all consumed). Certificate carries
  data only (six `Nat`/`Bool` fields), so rule 4 is respected.
- Witness non-degeneracy: `crossCert_joint_zeuge` instantiates all premises jointly —
  passing decided check, written table on each side (`eSetze`/`ctHw` schreibt facts),
  reached runs with observable memory change (`0 -> 5` logged entry world, `0 -> 42`
  fragment world, plus a memory-changing target drain). Meets the hard bar; two-core
  TSO conjuncts of the reused witness are not carried, which is fine for this G/W
  consumer (see follow-up note).
- Axioms: per `BUILD-EVIDENCE.json`, small facts on `propext` or none;
  `crossCert_gibt_joint` and `crossCert_joint_zeuge` on exactly
  `propext, Classical.choice, Quot.sound` — the standard goal set, inherited from the
  reused witnesses. No hardware-correspondence, W/GX-simulation, `valX86_sound`, timing,
  fairness or progress claim; CUTS states the paired-runs boundary and the exact
  obstruction (no single-declaration joint run without a declaration morphism, which
  would need a desired-correctness premise). No claim larger than the proof.
- No unsupported desired-correctness premise, no weakened guarantee, no fake closure:
  the partial-closure point (paired runs, values `5 != 42` by `decide`) is declared as a
  FINDING in CUTS and report, exactly as the owner task permits.

## Last `./lean-bau` result line (own clean tree, baseline)

`Build completed successfully (658 jobs).`

Candidate-side build per evidence: `lean-bau` green (658 jobs), `lean-probe` on the new
file `== 0 error(s) in the COMPLETE output`. Own-tree checks above corroborate every
name the candidate depends on.

## VERDICT: ACCEPT

## What remains open / follow-ups (not merge blockers)

1. Import-line placement at merge (mechanical union, see above).
2. The decided `Bool` checks supplied numbers against hardcoded witness constants while
   shape agreement lives in separate `rfl` theorems; a future lane may package shape as
   one `Bool` over the structures for a single decided gate. Not required: the
   declarations are fixed defs.
3. Carrying one two-core TSO conjunct into the joint witness would document multi-core
   relevance; the hard non-degeneracy bar is already met on both sides.

## What I believe is wrong in the task

Nothing blocking. The owner task's CONTEXT/MECHANISM boilerplate describes a
hardware-family `HwAdapter` connection while the TASK paragraph asks for the GX-refinement
certificate consumed by G/W/GX; the author's reading (TASK paragraph governs, no
`HwAdapter`, same as lanes 1215/1251) is correct.
