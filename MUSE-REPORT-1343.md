# MUSE-REPORT-1343: Opcode ledger 0F 40-7F

## What was done
New file `grammatik/Grammatik/X86/OpcodeLedger0F40.lean` (own namespace
`Gabbro.Grammatik.X86.OpcodeLedger0F40`, self-contained schema, no dependence
on other ledger lanes) plus one import line in `grammatik/Grammatik.lean`.
One row per second byte 64-127 with `LStatus`, `LEintrag`, `ledger`,
witness theorems for every `modelliert` row reusing accepted round trips,
summary theorems (counts, exact ordered coverage, nodup), CUTS block and
`#print axioms` lines.

New definitions/theorems: `LStatus`, `LEintrag`, `ledger`, `wit_cmov_o/no/b/
ae/e/ne/be/a/s/ns/p/np/l/ge/le/g` (16), `cmovSecond_ops`, `wit_s32_addss/
subss/mulss/divss/cvtss2sd` (5), `wit_intvec_6f/73/7f` (3), `intVecSecond_ops`,
`anzahl_modelliert` (= 24), `anzahl_fehlt` (= 40), `anzahl_rest_leer`,
`ledger_ops`, `ledger_nodup`, plus repair pins `kap_cmov_alle`, 5 `kap_s32_*`,
3 `kap_ohne_intvec_*`, 6 `kap_nichts_*`.

## Result
- 24 rows `modelliert`: 0F 40-4F via `ControlCodec.decodeCmov`; 0F 58/59/5A/
  5C/5E scalar-SS rows via `ScalarFloat32HardwareForms.s32Decode`; 0F 6F/73/
  7F selected rows via `VectorIntegerHardwareForms.decodeIntVec`.
- 0 rows `zurueckgestellt`/`verweigert`/`ungueltig64` (no invalid-64 forms in
  this region; refusals would be `kapDecode` facts and are not claimed).
- 40 rows `fehlt` (the product). Most compiler-relevant first: packed FP
  arithmetic/logic 0F 54-57/5B/5D/5F and packed halves of 58/59/5C/5E
  (auto-vectorized loops emit these constantly); PCMPEQB/W/D 0F 74-76
  (memcmp/strlen workhorse) and PUNPCK/PACK 0F 60-6D (widening/narrowing);
  PSHUFD 0F 70 and shift groups 0F 71/72 (lane shuffles); MOVMSKPS 0F 50
  (branch-on-mask); MOVD 0F 6E/7E (scalar moves); SQRT/RSQRT/RCP 0F 51-53
  (common in FP code); MIN/MAX 0F 5D/5F (clamps); HADD/HSUB 0F 7C/7D
  (reductions); EMMS 0F 77 (rare legacy); VMREAD/VMWRITE 0F 78/79
  (privileged, rare); reserved 0F 7A/7B (#UD, no fault path modelled).
- Key structural finding (CORRECTED after review 1344, which was right):
  the `kapDecode` chain DOES take this region's CMOV rows (first arm
  `decodeMulDivWidth` -> `decodeExt` -> `decodeCmov`, accepted pin
  `pin_ext_cmov`) and its scalar-prefix FP rows (second arm `s32Decode`,
  with `decodeMulDivWidth` refusing first). Checked in-file: `kap_cmov_alle`
  (all 16 conditions x all registers, exact `breit (.ext (.cmov ...))` arm),
  `kap_s32_addss/subss/mulss/divss/cvtss2sd` (exact `s32` arm).
  Outside the chain (checked `= none` pins): the 3 IntVec rows
  (`kap_ohne_intvec_6f/73/7f`) and 6 representative unmodelled shapes
  (`kap_nichts_movmskps/addps/punpcklbw/pcmpeqb/emms/vmread`). The original
  "covers NONE" claim was false; it is withdrawn.

## Verification status
`./lean-probe grammatik/Grammatik/X86/OpcodeLedger0F40.lean` after repair:
`== 0 error(s) in the COMPLETE output; exit 0`. Axioms printed:
`wit_cmov_e: [propext]`, `wit_s32_addss: [propext]`,
`wit_intvec_6f: [propext, Classical.choice, Quot.sound]`,
`kap_cmov_alle`, `kap_s32_addss`, `kap_ohne_intvec_6f`, `kap_nichts_emms`:
each `[propext, Quot.sound]`; counts/coverage/nodup axiom-free.
`./lean-bau` (full project) was NOT run from this lane (long serial slot,
shared with other lanes); the merger rebuilds before committing per the
merge script in AGENTS.md section 5.

## Repair history (review 1344, verdict REPAIR)
- Material defect accepted: the "kapDecode covers NONE of 0F 40-7F" finding was
  false (missed the transitive `decodeMulDivWidth` -> `decodeExt` path and the
  `s32Decode` arm). Fixed with checked pins, not prose: exact-arm membership
  for all 16 CMOV + 5 scalar rows, `= none` pins for the 3 IntVec rows and 6
  unmodelled shapes. File header and CUTS corrected in the same commit.
- Minor: HADD/HSUB `grund` corrected to "F2/66 prefix" (HADDPS=F2, HADDPD=66;
  no F3 form exists).

## What remains open / believed-wrong
- Nothing in the task description looks wrong, but the pasted CONTEXT/
  MECHANISM paragraphs describe a different lane (HwAdapter family
  connection) and do not apply to a ledger; they were ignored except for
  the cited file names.
- Partial-row overstatement is inherent to one-row-per-byte: documented in
  `grund` fields and CUTS.
- Opcode map is a NAMED assumption (Intel-only provenance, no AMD manual
  in clone); no `herstellerabhaengig` marking needed in this region.
