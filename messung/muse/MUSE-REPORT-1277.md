# MUSE-REPORT-1277: Bit test family BT/BTS/BTR/BTC

Lane 1277, clone `/home/simon/Dokumente/gabbro-muse/a1277`, branch `muse/1277`.
Candidate HEAD this report covers: `e79c3b6609cd5cb6932360d5d8e3c529eccf1790`
(8 commits, all on `muse/1277`, nothing pushed).

## What was done

NEW FILE `grammatik/Grammatik/X86/IntBitTest.lean` (2161 lines, incl. CUTS
and `#print axioms` per main theorem) plus one `import Grammatik.X86.IntBitTest`
line appended to `grammatik/Grammatik.lean`. No other file touched. No
diagnostic (`N`), gift, or example numbers minted; no Rust changes.

Structure follows the accepted families: `ShiftCodec.lean` (decode, encode,
round-trip, value dispatch, family step) and `HwMulDivWidth.lean` (dispatcher
preferring `decodeExt`, `HwAdapter` register plug with exact agreement,
two-core witness). Existing definitions are reused unchanged (`mergeRegNarrow`,
`trunc`, `maske`, `effAddr`, `schrittRegister`, `ripNach`, `regSet_fremd`,
`issueListe` + its lemmas, `setKernDaten`/`setTso` + their `wf` lemmas,
`decodeExt`/`stepExt`, `parseLe32_leBytes32`, `codeReg_regCode`,
`merkmalZugelassen_heisst_beide`); nothing is redefined.

Delivered, by section:

- §1-§5 value semantics: `BtOp` (bt/bts/btr/btc), `btOpcode` (163/171/179/187),
  `btGruppe` (4/5/6/7), width-index `btIndex` (offset modulo width) with
  `btIndex_schranke`, selected bit `btBit`, one-bit mask `btMaske`, raw value
  `btRoh`, architectural write-back `btSchreibe` (the accepted
  `mergeRegNarrow`: 8/16-bit merge, 32-bit zero-extends). Proved: `bt_bts_setzt`
  (BTS sets), `bt_btr_loescht` (BTR clears), `bt_btc_kehrt_um` (BTC complements,
  CF keeps the old bit), `bt_bts_frame`/`bt_btr_frame`/`bt_btc_frame` (every
  other in-range bit kept), via the accepted `getLsbD` bridge
  (`testBit_toNat`, `getLsbD_and/or/not/ofNat`) plus two mask-bit lemmas proved
  from core `Nat.testBit` facts (`btMaske_bit_gleich` by induction with
  `Nat.testBit_succ`; `btMaske_bit_anders` via `Nat.testBit_two_pow_of_ne`;
  `btMasken_bit`, `btMasken_bit_lt` for the width masks).
- §6 codec: `BtWeite` (w16/w32/w64 -- no 8-bit form exists, so none is
  modelled), `BtForm` (reg/imm/memReg/memImm), canonical `encodeBt` (REX always
  present with X = 0, 0x66 exactly for 16-bit, ModRM mod 3 register-direct /
  mod 2 base+disp32 with SIB exactly when needed), byte-parsing `decodeBt`
  with `decodeBtRex`, `opcOp`/`gruppeOp` back-maps (`opcOp_btOpcode`,
  `gruppeOp_btGruppe`, `opcOp_mod256`, `rexBt_rund`, `btOpcode_toNat`,
  `btImmByte`).
- §7 round trips and pins: `roundtripBtReg` (3072 combinations by kernel
  `rfl`), `roundtripBtMemReg16/32/64` (op symbolic, 256 cases each),
  `roundtripBtImm`, `roundtripBtMemImm`, `btLaenge` with `btLaenge_encode` and
  `btLaenge_ok` (lengths 4..11, within 1..15), SDM byte pins
  (`pin_bt_btc_rax_rcx`, `pin_bt_w16_rax_rcx`, `pin_bt_bts_edx_5`,
  `pin_bt_mem_btr`, `pin_bt_mem_sib`, `pin_bt_dekode`), truncation pins
  (`sonde_bt_abgeschnitten`) and planted refusals (`sonde_bt_verweigert`:
  LOCK, 66+REX.W, REX.X, REX.R group row, mod-0/mod-1, bad group digit,
  bad opcode, wrong SIB).
- §8 register step: `BtDecodiert`, `btSchritt` (length-checked; reg/imm forms
  write back the routed value with `btFlags`; memory forms refuse),
  `btSchritt_laenge`, `btSchritt_mem_verweigert`, `btSchritt_memImm_verweigert`,
  `btSchritt_reg/imm`, `btSchritt_speicher/rip`, `btSchritt_cf_reg/imm`
  (CF = old bit), `btSchritt_zf_reg/imm` (ZF preserved), `btErlaubt` (CF
  pinned, ZF kept, OF/SF/AF/PF free) with `btSchritt_erlaubt_reg/imm`,
  `btSchritt_fremd_reg/imm`.
- §§9-11 dispatcher and unified step: `BtHwInstr`, `decodeBtHw` (unified chain
  first), `decodeBtHw_prefers_ext/bt/nichts`, no-shadowing pins
  (`ext_weist_btreg64/32/16/imm/mem_zurueck`, all `decide` -- no collision
  with any accepted row), arm pins (`pin_btHw_reg64/imm32/mem64`),
  `btHwLen`, `btHwSchritt` with `btHwSchritt_ext/bt_ok/bt_verweigert`
  (BT never halts).
- §12 machine adapter: `adapterBitTest : HwAdapter BtDecodiert` (register
  plug; memory forms admit no successor at any length) with
  `adapterBitTest_wf/ok/proj/verweigert_bei_laenge/verweigert_memReg/verweigert_memImm`.
- §13 footprint: `btOffsetInt` (signed, via `BitVec.toInt`), `btByteVersatz`
  (`/` floors), `btBitImByte`, `btVersatz_rekon` + `btBitImByte_schranke`
  (both by `omega`), `btEffAddr` (base + disp32 + signed byte displacement,
  wrapping mod 2^64) with `btEffAddr_null`, `btWeiteBytes`, `btFuss` with
  `btFuss_laenge`, `probe_bt_versatz` (`decide`: 20 -> byte 2 bit 4;
  -1 -> byte -1 bit 7; -9 -> byte -2 bit 7).
- §14 TSO events: `btLadeListe` with `btLadeListe_verweigert` (one unreadable
  byte refuses the whole word), `btEintraege`/`btMemSchreibe` (issue fold with
  length-mismatch refusal) with `btMemSchreibe_mem` (buffer only) and
  `btMemSchreibe_puffer` (appends entries), `btByteMaske`/`btByteRoh`,
  `btSetByte` with `btSetByte_laenge`, `btMemZielReg`/`btMemZielImm`,
  projection helpers (`setTso_mem/puffer/kerne`, `setKernDaten_mem/kerne_c`),
  `decodeBt_lock` (LOCK refuses on any suffix, general proof).
- §15 memory RMW effect: `btMemEffekt` (footprint load, single-byte modify,
  buffered write-back, CF set, RIP advanced) with `btMemEffekt_wf/cf/rip/mem`.
- §16 joint witness `btWit_zeuge` (23 conjuncts): core 0 BTS rax (8 -> 10,
  CF keeps 0) and core 1 BTR rbx (15 -> 14, CF keeps 1) through the adapter;
  memory BTS on both cores through TSO events (CF keeps 0, memory still reads
  0, 4 entries pending); issue/forwarding (owner only)/drain with shared memory
  changing 0 -> 42; effective addresses 8194 (offset 20) and 8191 (offset -1);
  decode arm pin, LOCK refusal instance, set/reset law instances,
  well-formedness. Non-degenerate: both cores write, the drain changes actual
  shared memory.

## Verification

- `./lean-probe grammatik/Grammatik/X86/IntBitTest.lean`: 0 errors, 0 warnings.
- `./lean-bau` (full project, incl. the new import): exit 0, 0 error lines,
  `Built Grammatik (659 jobs)`, `Build completed successfully (659 jobs)`.
- `#print axioms` for every main theorem (59 lines at end of file): all within
  `propext`, `Classical.choice`, `Quot.sound` (subsets thereof); no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe` anywhere in the file.
- Every premise of every theorem is used (no `intro _`, no unused hypotheses).

## Open / not claimed (see CUTS in the file)

No hardware correspondence (self-consistency only); no SIB-index/scale,
mod-0/mod-1, RIP-relative, or 8-bit forms (refused); no per-access W/GX bridge
and no whole-word atomicity beyond byte drains; no source/ABI/loader/budget
link; no word-level correspondence between the byte-level memory path and the
word evaluator beyond witness instances; no timing/power claims.

## Task remarks (things I believe are wrong or needed decisions)

1. "Widths 8/16/32/64 as the architecture defines" -- the architecture defines
   16/32/64 (no 8-bit BT form exists). Modelled as `BtWeite` (w16/w32/w64);
   8-bit is absent by construction, not by a checked refusal.
2. "The signed bit offset addresses ANY byte" holds for register offsets
   (task) via floor division; the imm8 memory offset is modelled UNSIGNED
   (byte value, `n / 8`, `n % 8`) as the canonical reading -- flagged as an
   open silicon question in CUTS, not verified.
3. MECHANISM item (2) asks agreement with "the family's accepted evaluator" --
   none existed (the task itself measures: no model yet). The evaluator
   (`btSchritt`/`btRoh`) is defined in-file and the adapter agreement theorems
   lift it unchanged.
4. "Intel SDM extracts supplied to the clone (see MUSE-REPORT-660)" -- no SDM
   extracts and no MUSE-REPORT-660 exist in this clone. Silicon facts
   (0F A3/AB/B3/BB, 0F BA /4../7, CF = selected bit, ZF unaffected, rest
   undefined, 16/32/64 sizes, REX.W/66 roles, LOCK RMW, signed memory offset)
   are taken from architecture knowledge and recorded as provenance/assumptions
   only; nothing beyond self-consistency is claimed.
5. `ArchitecturalFlags.lean` could not take a new `FlagKlasse` constructor
   (existing files frozen); the BT flag row lives as `btErlaubt` (CF pinned,
   ZF kept, rest free) in the file's style instead.
6. The concrete step preserves incoming OF/SF/AF/PF (like the accepted
   `mulFlagsU` modelling choice); the class leaves them free, so no consumer
   can depend on the kept values. ZF preservation is proved, not just kept.
7. Tactic/toolchain notes for reviewers: full `simp` (not `simp only`) is
   required wherever closed byte/natural literals must evaluate (the global
   simpset does it; `simp only` leaves e.g. `102 % 2^8 == 240` stuck);
   `simp`'s closing `rfl` does not unfold default-transparency defs
   (`codeReg` on literals) nor decide `if c = c` (used projection lemmas
   instead); large case splits need heartbeat budget (`roundtripBtReg`: 3072
   kernel-`rfl` goals; memory round trips: 3 x 256 simp goals). The
   `unusedSimpArgs` linter misfired once (flagged a `decide`-fact as unused
   that the proof needs); the final file has zero warnings.
8. No TARGET/`ZEUGE:` lines were given, so rule 13 required nothing; the joint
   `btWit_zeuge` is provided per the MECHANISM paragraph instead.
