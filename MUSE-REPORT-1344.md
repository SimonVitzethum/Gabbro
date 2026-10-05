# MUSE-REPORT-1344: Exact review of candidate 1343 (opcode ledger 0F 40-7F)

## VERDICT: REPAIR

## Candidate

- Author lane 1343, pinned head `cc28bfa4`, base `574ac3d7` (per `.tmp/review/SNAPSHOT.json`).
- Changed files (3, all within the author's owned set): `MUSE-REPORT-1343.md` (new),
  `grammatik/Grammatik.lean` (one added line `import Grammatik.X86.OpcodeLedger0F40`),
  `grammatik/Grammatik/X86/OpcodeLedger0F40.lean` (new, 330 lines).
- Review conducted from clone `/home/simon/Dokumente/gabbro-muse/a1344`, branch `muse/1344`.
  The pinned author commit was never read (`git show/log/diff` on it not used);
  only the delivered files under `.tmp/review/author-1343/` were inspected.

## Checks performed

- Banned tactics: `sorry`/`admit`/`native_decide`/`unsafe`/`sorryAx` and `axiom`
  declarations: no matches in the candidate file. PASS.
- Axioms (author BUILD-EVIDENCE.json, trusted as author evidence, see blocker below):
  `wit_cmov_e: [propext]`, `wit_s32_addss: [propext]`,
  `wit_intvec_6f: [propext, Classical.choice, Quot.sound]`,
  counts/coverage/nodup axiom-free. Standard. PASS.
- Existing files: `PATCH.diff` confirms the only existing-file change is the single
  import line in `grammatik/Grammatik.lean`. PASS.
- Evaluator lifted, not copied: all 24 witnesses call the accepted decoders
  (`decodeCmov`, `s32Decode`, `decodeIntVec`) and reuse the accepted round trips
  (`roundtrip_cmov`, `s32Roundtrip_*`, `roundtrip_movdqaLd/psllqImm/movdqaSt`,
  `cmovSecond_ops`/`intVecSecond_ops` by `rfl`). Every referenced name was verified
  to exist in the tree (`ControlCodec.lean`, `ScalarFloat32HardwareForms.lean`,
  `VectorIntegerHardwareForms.lean`). PASS.
- Every premise used: the witness theorems take no premises; the agreement lemmas
  reuse hypotheses via `simpa`. No `intro _`/`have _ :=` discards. PASS.
- `verweigert`/`ungueltig64` rows: zero, with `anzahl_rest_leer` proving the lists
  empty. Vacuously satisfied; region 0F 40-7F genuinely has no invalid-in-64-bit
  forms (unlike the one-byte BCD/segment-register forms), and the reserved 0F 7A/7B
  rows are honestly marked `fehlt` ("no fault path modelled") rather than claimed
  as refused. PASS.
- Summary theorems: `anzahl_modelliert = 24`, `anzahl_fehlt = 40`,
  `ledger_ops` (`List.range' 64 64` by `rfl`), `ledger_nodup` (by `decide`).
  16 + 5 + 3 = 24 modelled, 24 + 40 = 64 rows. PASS.
- Opcode map against the SDM (64-bit mode): all 64 second-byte mnemonics verified
  correct (40-4F CMOVcc, 50 MOVMSKPS, 51 SQRT, 52 RSQRT, 53 RCP, 54-57 AND/ANDN/OR/XOR,
  58-5F arithmetic/convert, 60-6D PUNPCK/PACK/PCMPGT, 6E/6F MOVD/MOVQ, 70 shuffle,
  71/72/73 shift groups, 74-76 PCMPEQ, 77 EMMS, 78/79 VMREAD/VMWRITE, 7A/7B reserved,
  7C/7D HADD/HSUB, 7E/7F MOVD/MOVQ). PASS with one prose nit (see minor).
- No hardware-correspondence, W/GX, timing, fault, or loaded-image claim. PASS.
- CUTS block and `#print axioms` lines present. English only. PASS.
- `./lean-bau` on the clean review clone: `== exit 0; 0 error line(s)`,
  `Build completed successfully (696 jobs)`. PASS (baseline; candidate file not present).

## Material defect (grounds for REPAIR)

The candidate's key structural finding is factually false. Report:
"the `kapDecode` chain in `HwKapsteinDecoder.lean` covers NONE of 0F 40-7F ...
All byte paths for this region are family decoders outside the unified chain."
File header (lines 8-9) and CUTS make the same claim
("`kapDecode` covers none of 0F 40-7F").

Counter-evidence from accepted files:

1. `kapDecode` (`HwKapsteinDecoder.lean:45-70`) tries `decodeMulDivWidth` FIRST.
   `decodeMulDivWidth` (`HwMulDivWidth.lean:38-45`) tries `decodeExt` FIRST.
   `decodeExt` (`ExtendedExecution.lean:64-91`) has an explicit `decodeCmov` arm
   (line 82), with a proved pin `decodeExt (encodeCmov .e .rax .rcx) = some ...`
   (line 219). Hence `kapDecode` accepts all 16 CMOV canonical witness byte
   strings via its first arm. The claim "no `decodeCmov` arm" is true only of the
   literal `kapDecode` match and misses the transitive path one level down.
2. `kapDecode`'s second arm is `s32Decode` (line 50). The candidate's own
   `wit_s32_*` theorems prove `s32Decode` accepts the five scalar witnesses
   (F3 0F 58/59/5A/5C/5E). Hence `kapDecode` accepts them regardless of arm 1.
   The report even contradicts itself: the same sentence admits the "s32 arm
   covers only scalar prefix forms", which ARE in-region bytes.
3. The IntVec rows (0F 6F/73/7F) are the only ones plausibly outside the chain,
   but that was not checked either (`decodeExt` has a separate `decodeVector`
   arm, `VectorCodec.decodeVector`, whose overlap with `decodeIntVec` rows the
   candidate never examines).

For a lane whose stated purpose is "find the gaps nobody has listed", reporting
21 already-chain-connected rows as "outside the unified chain" is a false gap:
it directs follow-up connection work at targets that need none. The checked
ledger itself (rows, witnesses, counts) is unaffected and looks correct.

## Minor issues (fix in the same repair)

- Rows 124/125 `grund`: "horizontal add (F2/F3 prefix ...)". HADDPS is F2,
  HADDPD is 66; no F3 form exists. Correct to "F2/66 prefix".
- BUILD-EVIDENCE shows the author's first `./lean-probe` attempt hit the 600 s
  timeout with no output before the second passed; worth a remark, not a defect.

## Required repair (small, precisely scoped)

1. Correct the three `kapDecode`-coverage statements (file header, CUTS bullet,
   report finding): `kapDecode` accepts the CMOV canonical bytes (via
   `decodeMulDivWidth` -> `decodeExt` -> `decodeCmov`) and the scalar-prefix FP
   bytes (via the `s32Decode` arm, possibly `decodeExt`/`fpDecode` first).
2. Check and state precisely which rows are actually outside `kapDecode`
   (IntVec rows vs `decodeVector`; the 40 `fehlt` rows), ideally as checked
   membership/refusal pins using the accepted agreement lemmas
   (`kapDecode_breit`, `decodeMulDivWidth_prefers_ext`, `kapDecode_s32`,
   `kapDecode_nichts`) rather than prose.
3. Fix the HADD/HSUB `grund` prefix text.
4. Re-run `./lean-probe`, keep 0 errors, re-commit.

## Blocker / honest partial status

- The candidate file could NOT be independently re-probed in this clone: this
  lane's enforced file policy allows edits only to `MUSE-REPORT-1344.md`,
  `arbeitsprotokoll/.commitmsg` and `.tmp/*` (excluding `.tmp/review/*`), so the
  mandated "copy the candidate file into your own clone" step is denied
  (`cp` and equivalent writes into `grammatik/` are rejected). The candidate's
  green-probe claim rests on the author's BUILD-EVIDENCE.json (0 errors plus
  exact axiom prints, internally consistent). `./lean-bau` above is therefore
  the clean-tree baseline only, not an integrated build of the candidate.
- No witness non-degeneracy issue applies: the ledger theorems quantify over no
  program syntax (rule 13 vacuous); decoder witnesses are the task-mandated form.
- New definitions/theorems reviewed (all in `OpcodeLedger0F40.lean`):
  `LStatus`, `LEintrag`, `ledger`, 16 `wit_cmov_*`, `cmovSecond_ops`,
  5 `wit_s32_*`, 3 `wit_intvec_*`, `intVecSecond_ops`, `anzahl_modelliert`,
  `anzahl_fehlt`, `anzahl_rest_leer`, `ledger_ops`, `ledger_nodup`.
- Nothing in the owner task text itself found wrong, except that its
  CONTEXT/MECHANISM paragraphs describe a different (HwAdapter-connection) lane,
  as the author also noted; the TASK paragraph is the authoritative spec and the
  candidate follows it.
