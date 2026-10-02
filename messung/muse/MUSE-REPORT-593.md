# Muse Report 593: Independent exact-candidate connection review of 575

## Task
Independently review the exact committed candidate of lane 575
(unified extended decoder and executable byte-step) against its owner
task: one selected-profile byte-facing execution path over canonical
`Codec.decode` / `Ausfuehrung.schritt` plus one new-form family per
accepted helper, with actual-memory fetch/execute permission, disjoint
prefix dispatch, exact evaluation selection, and a mixed reached run
changing actual memory from fetched bytes.

## Candidate under review
CANDIDATE: 575 ca1f16af1f17aec28416f12ad871522be65e43a3
VERDICT: ACCEPT

Sources inspected: `.tmp/review/SNAPSHOT.json`,
`.tmp/review/author-575/OWNER-TASK.md`,
`.tmp/review/author-575/MUSE-REPORT-575.md`,
`.tmp/review/author-575/BUILD-EVIDENCE.json`,
`.tmp/review/author-575/PATCH.diff`, and the full candidate file
`.tmp/review/author-575/grammatik/Grammatik/X86/ExtendedExecution.lean`
(829 lines). Review branch verified: `/home/simon/Dokumente/gabbro-muse/a593`,
branch `muse/593`.

## Interface resolution (all real, no guesses)
Every external name used by the candidate resolves to an accepted
module in this tree with a matching signature (checked by grep, not
by trust):
- `Codec.decode`, `Ausfuehrung.schritt` / `laengeOk`, `zeugeFlags`;
  `Byteschritt.geholt` / `ausfuehrbarN` / `fetchDekodiert` discipline.
- `ScalarFloat.laufAlt` (lifts `schritt` onto `FpZustand`, preserves
  XMM: `laufAlt_xmm`) — the candidate's pilot arm is this lift, not a
  redefined evaluator.
- `NarrowCodec.decodeNarrow/encodeNarrow/stepNarrow`,
  `MulDivCodec.decodeMulDiv/mulDivEncode`, `MulDiv.mulDivSchritt`,
  `ShiftCodec.decodeShift/encodeShift/shiftLaenge/shiftSchritt`,
  `ControlCodec.decodeSetCC/decodeCmov/encodeSetCC/encodeCmov/
  setccSchrittBytes/cmovSchrittBytes` (4-byte length confirmed by the
  accepted `encodeSetCC_len`), `ScalarFloatCodec.fpDecode/
  fpEncodeMovsdRR/fpEncodeMovsdSpeichere`, `ScalarFloat.fpSchritt/
  FpZustand`, `VectorCodec.decodeVector/encodeVector/stepVector/
  stepVector_profil_verweigert` (premises `laengeOk`, `vecEintritt`
  discharged by `rfl` on closed values), `FeatureProfile.BereitProfil`,
  `Gleitprofil.kontextReset` (via transitive import), `Vektor.vecJoin`.

## Connection substance (not decorative)
- `decodeExt` is a sequential fallback (pilot, narrow, muldiv, shift,
  SETcc, CMOVcc, scalar FP, packed integer). The eight dispatch
  theorems (`decodeExt_kanonisch` … `decodeExt_nichts`) are proved by
  `unfold` + `rw` with the stated refusal hypotheses; every premise
  is used. Dispatch is disjoint by construction (later arms run only
  on earlier `none`).
- Ten whole-chain pins evaluate the COMPLETE fallback on closed bytes
  by `decide` (one per family: ret, mov32, mul, shl-imm, setcc, cmov,
  movsd, pxor, empty, unknown opcode), plus seven explicit
  `pin_pilot_weist_*` refusals proving no pilot form is shadowed. No
  forged decoded input anywhere.
- `stepExt` delegates every arm to its accepted evaluator; 17
  `stepExt_*` selection theorems route each arm (including divide
  trap to `halt`, every refusal to `verweigert`) by `rfl`-equation +
  `rw`, each using all its premises. No duplicated IR or executor,
  no correctness conclusion hidden in a premise.
- `fetchExt` / `extByteschritt` take ONLY state and readiness
  profile; a forged `ExtInstr` cannot inject an instruction. Admission
  (`extZugelassen`) mirrors the `fetchDekodiert` discipline and
  `fetchExt_erfolg` extracts all four facts (decode equation, length
  equation, length guard, execute permission).
- Reached witness: image = pilot `store64` (7 B) ++ FP
  `movsdSpeichere` (8 B); two byte-steps from ACTUAL fetched bytes
  store 42 into two real data cells (0 -> 42, proved by `decide`),
  RIP 4096 -> 4111; the second fetch works because `geholt` takes
  the executable prefix (8 B remain). Joint
  `extWit_zwei_schritte_zeuge` adds initial-zero evidence and the
  past-image refusal. Planted refusals: past-image RIP (closed `rfl`
  computation) and packed-integer without OS state (via the accepted
  validator theorem, correctly applied). Non-degenerate:
  memory-changing reached execution plus refusals, jointly
  instantiated.

## Hygiene
- No `sorry` / `admit` tactic / `axiom` / `native_decide` / `unsafe`
  (the only matches are English words "admitted"/"unadmitted" in doc
  comments). No `Prop`-typed premises. CUTS block and `#print axioms`
  for all eight main theorems present.
- Reproduced in this clone: candidate file copied into
  `grammatik/Grammatik/X86/`, `./lean-probe` →
  `== 0 error(s) in the COMPLETE output; exit 0`, axioms
  `[propext]` to `[propext, Quot.sound]` only, matching the author's
  BUILD-EVIDENCE (full `./lean-bau`, 458 jobs green). Scratch copy
  removed afterwards; tree left clean.
- Diff scope: one new file + one additive umbrella import line in
  `grammatik/Grammatik.lean`. No source checker / Spec / goal /
  emitter / friend-optimizer paths touched. No existing theorem
  weakened.

## Bounded accepted claim
ONE unified byte-facing execution path over the accepted helpers:
pilot (all 14 forms) plus narrow, muldiv, shift, SETcc/CMOVcc,
scalar SSE2 DOUBLE and packed integer, each through its accepted
decoder and evaluator only; fetch/execute-permission gating per the
`fetchDekodiert` discipline; a mixed pilot/FP reached run changing
actual memory from fetched bytes with joint witness and planted
refusals. Explicitly NOT claimed (disclosed in CUTS): hardware
correspondence; LOCK; SIMD beyond PXOR/PADDQ and four scalar-DOUBLE
rows; source/IR/TSO/GX/ABI/loader/entry/budget connection; divide
`halt` carried, not proved.

## Notes (not repairs)
- The author discloses that an end-to-end narrow memory run from
  fetched bytes is absent (narrow dispatch and step selection are
  proved and pinned). This matches the task's "or" wording
  (pilot-integer/FP or narrow/store) since the pilot-store + FP-store
  run is shown. Follow-up material, not a verdict blocker.
- Producer/consumer interface as stated by the author is accurate:
  `decodeExt`, `extLen`, `stepExt`, `fetchExt`, `extByteschritt`,
  consumer contract via `fetchExt_erfolg` / `extByteschritt_weiter`.
  Measurable next step: loaded-image runner (owners 559-561) or a
  W-bridge consumer reading `stepExt` footprints.

## Minimal repairs
None required.
