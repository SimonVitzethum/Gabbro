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
`ledger_ops`, `ledger_nodup`.

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
- Key structural finding: the `kapDecode` chain in `HwKapsteinDecoder.lean`
  covers NONE of 0F 40-7F (no `decodeCmov`/`decodeIntVec` arm; s32 arm covers
  only scalar prefix forms). All byte paths for this region are family
  decoders outside the unified chain.

## Verification status
`./lean-probe grammatik/Grammatik/X86/OpcodeLedger0F40.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`. Axioms printed:
`wit_cmov_e: [propext]`, `wit_s32_addss: [propext]`,
`wit_intvec_6f: [propext, Classical.choice, Quot.sound]` (inherited from the
accepted IntVec round trip via `simp`), counts/coverage axiom-free.
`./lean-bau` (full project) was NOT run from this lane (long serial slot,
shared with other lanes); the merger rebuilds before committing per the
merge script in AGENTS.md section 5.

## What remains open / believed-wrong
- Nothing in the task description looks wrong, but the pasted CONTEXT/
  MECHANISM paragraphs describe a different lane (HwAdapter family
  connection) and do not apply to a ledger; they were ignored except for
  the cited file names.
- Partial-row overstatement is inherent to one-row-per-byte: documented in
  `grund` fields and CUTS.
- Opcode map is a NAMED assumption (Intel-only provenance, no AMD manual
  in clone); no `herstellerabhaengig` marking needed in this region.
