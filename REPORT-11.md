# Report 11 — Sequential Sail Arm: integer data-processing

Clone: `/home/simon/Dokumente/gabbro-arm/work/11`, branch `arm/11`.
Status: **deliverables done, committed, green.**

## What was built

Execute-level semantics (`decoded fields -> Eff Unit`) for all assigned AArch64
integer data-processing instructions, in six new files under `arm/Arm/Isa/`
(wired into `arm/Arm.lean`):

- `IntCore.lean` — Nat-level shared helpers + `decide` examples.
- `IntMasks.lean` — Sail `DecodeBitMasks`.
- `Integer.lean` — add/sub, logical, variable shifts, movewide, ADR/ADRP.
- `IntBit.lean` — bitfield, EXTR, CLZ/CLS, RBIT, REV, CNT/CTZ/ABS.
- `IntMul.lean` — MUL/MADD/MSUB, widening SMADDL/UMADDL/SMSUBL/UMSUBL,
  UDIV/SDIV, UMULH/SMULH.
- `IntCond.lean` — CSEL/CSINC/CSINV/CSNEG, CCMP/CCMN (reg + imm).

Method: pure Nat cores (all values `< 2 ^ w`, `BitVec` only at the `Eff`
boundary via `ofNat`/`toNat`) proved by `decide` on decode-derived examples,
each family with a planted wrong case; thin `Eff` read-compute-write wrappers
over the same cores. 102 theorems, 0 with premises (all closed examples, so no
witness burden and no unused-premise risk).

## New definitions (exact names)

Helpers: `pow2 mask trunc sintOf addWithCarry nzcvOf wrNZCVn rdNZCVn condHolds
ShiftTy decodeShiftNoRor decodeShift shlW shrW asrW rorW shiftReg
ExtTy decodeExt extLen extUnsigned extendReg
clzW clsW rbitW byteOf revGo revW popW absW
hbitGo hbit repGo replicateChunk decodeBitMasks
addSubFlags rdSPorX wrSPorX LogicOp logicPure logicNZCV MovKind movWidePure adrPure
andNotW orW bitfieldPure extractPure ctzPure
mulAddSubPure wideMulPure divPure mulHiPure
condSelectPure condCmpPure`.

Exec wrappers (24): `execAddSubImm execAddSubShift execAddSubExt execAdcSbc
execLogicalImm execLogicalShift execShiftVar execMovWide execAdr
execBitfield execExtract execClzCls execRbit execRev execCntPop execCtz execAbs
execMulAddSub execWideMul execDiv execMulHi
execCondSelect execCondCmpReg execCondCmpImm`.

Theorems (102, all `by decide`): per-family value examples plus one planted
wrong case each, e.g. `addWithCarry_ex1/ex2/sub/wrong`, `addSubFlags_add/adds/
subs/adc/sbc/wrong`, `condHolds_eq/eq_off/nv/al/wrong` (NV behaves as AL per the
Sail code — bit 0 of `0b1110` is clear, so no inversion),
`shiftReg_lsl/lsr/asr/ror/wrong`, `extendReg_uxtb/sxtb/uxth_sh/wrong`,
`clzW_one/zero/top/wrong`, `clsW_neg1/zero/wrong`, `rbitW_one/byte/wrong`,
`revW_32/16/wrong`, `popW_ex/wrong`, `absW_neg1/min/wrong`,
`hbit_ex/one`, `replicateChunk_ex/wrong`,
`decodeBitMasks_one/reserved/rot/bitfield/wrong`,
`logicPure_and/orn/eor/wrong`, `logicNZCV_zero/neg`,
`shiftVar_lslv/rorv/wrong`, `movWidePure_z/n/k/wrong`,
`adrPure_adr/adrp/wrong`,
`bitfieldPure_ubfm/sbfm/bfm/wrong`, `extractPure_ex/ror/wrong`,
`ctzPure_ex/zero/wrong`,
`mulAddSubPure_madd/msub/mul/wrong`, `wideMulPure_s/u/wrong`,
`divPure_u/s/zero/ovf/wrong`, `mulHiPure_u/s/sneg/wrong`,
`condSelectPure_csel/csinc/csinv/csneg/wrong`,
`condCmpPure_taken/add/skip/wrong`.

## Findings during the work (all resolved, kept as evidence)

- `hbit` first kept the *smallest* set bit (counted down while overwriting);
  the `decodeBitMasks` examples caught it. Fixed to keep the largest.
- `bitfieldPure_sbfm`: my hand value `0xFF0000FF` was wrong silicon thinking;
  Sail's `(top & ~tmask) | (bot & tmask)` gives full `0xFFFFFFFF` for SXTB.
  The `decide` check caught it; expectation corrected.
- Sail `ConditionHolds(0b1110)` (NV) returns *true* (behaves as AL); an initial
  "NV never holds" theorem was corrected to match the source.

## Semantic decisions (all in comments + CUTS)

- `wrX 31` = XZR discard, `rdX 31` = 0; SP forms use `rdSys`/`wrSys "SP"`.
- Division by zero yields 0 (defined, no trap — as the source says).
- `DecodeBitMasks` refusal = `none`; `opc == 0b11` (BFM), REV `opc == 0b00`,
  SMULH/UMULH `Ra`, and the CSSC gate are decode-side (agent 15) — noted, and
  the execute signatures take validated discriminants so invalid combos are
  unrepresentable.
- `#print axioms` for representative theorems in every file: no axioms or
  `[propext]` only (standard).

## Last build

`./arm-bau`: `Build completed successfully (12 jobs)`, exit 0, 0 error lines.

## Open / CUTS

- The 24 `Eff` wrappers are unproved plumbing over `decide`-checked cores; no
  `Eff`-level test interpreter exists (decoder/bridge agents' business).
- No decoder written (agent 15 owns it); no coverage ledger touched.
- Frozen `Basic.lean`/`Monad.lean` untouched, no change proposed.
