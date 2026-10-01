# MUSE-REPORT-563: Multiply/divide byte decoder and execution connection

## What was done

New file `grammatik/Grammatik/X86/MulDivCodec.lean` (~850 lines) connects a
canonical register-direct MUL/IMUL/DIV/IDIV subset to the accepted MulDiv
execution (lane 336, reviewed lane 374) via actual byte decoding. Additive
umbrella import appended to `grammatik/Grammatik.lean`. No other file touched.

## Exact names

Definitions: `mulDivEncode`, `decodeF7Modrm`, `decodeImulModrm`,
`decodeImulRex`, `decodeNachRex`, `decodeNachRexR`, `decodeMulDiv`,
`idivNegReg`, `idivNegZustand`, `idivNegTeilerReg`, `idivNegTeilerZustand`,
`idivMinReg`, `idivMinZustand`, `mulCodecSpeicher42`.

Theorems — encoding/lengths: `mulDivEncode_len`, `mulDivEncode_len_ok`;
round trips: `roundtrip_mulRax`, `roundtrip_divRax`, `roundtrip_idivRax`,
`roundtrip_imul2`, `roundtrip_muldiv`, `roundtrip_muldiv_len_ok`;
arbitrary-input length soundness: `decodeF7Modrm_len`,
`decodeImulModrm_len`, `decodeImulRex_len`, `decodeNachRex_len`,
`decodeNachRexR_len`, `decodeMulDiv_len_ok` (stronger than the pilot codec,
which leaves this open); step admission: `decodiert_laenge_ok`;
decode-to-execute: `decode_exec_mul`, `decode_exec_imul`,
`decode_exec_div_ok`, `decode_exec_div_halt`, `decode_exec_idiv_ok`,
`decode_exec_idiv_halt`, `decode_div_verweigert_heisst_halt`,
`decode_idiv_verweigert_heisst_halt`; frame: `decode_mul_speicher`,
`decode_div_flags`, `decode_mul_rip`; pins: `pin_mulRax_rcx[_dekode]`,
`pin_divRax_r8[_dekode]`, `pin_idivRax_rcx[_dekode]`,
`pin_imul2_r9_r15[_dekode]`; refusals: `md_decode_nichts_leer`,
`md_decode_nichts_rex_allein`, `md_decode_nichts_modrm_fehlt`,
`md_decode_nichts_zweitop_fehlt`, `md_decode_nichts_imul_modrm_fehlt`,
`md_decode_nichts_ohne_rex`, `md_decode_nichts_rex_x`,
`md_decode_nichts_rex_r_gruppe3`, `md_decode_nichts_falsche_nummer`,
`md_decode_nichts_speicher_modus`, `md_decode_nichts_zweitop_falsch`,
`md_decode_nichts_imul_speicher_modus`; signed probes:
`probe_idiv_negativ` (-7/2 = -3 r -1), `probe_idiv_neg_teiler`
(7/-1 = -7 r 0), `probe_idiv_min_halt` (INT_MIN/-1 traps + guard),
`probe_idiv_null_halt`; joint witness: `muldiv_codec_zeuge` (MUL bytes
decode and step to 42, 42 changes real memory observably, DIV-by-zero
traps with guard refusal, truncated bytes refuse — jointly).

Reuse (no duplication): `rexByte`/`modrmReg`/`codeReg`/`natByte` from
`Codec`; `regSet`/`ripNach`/`laengeOk`/`read64`/`write64`/witness memory
from `Ausfuehrung`; `mulLow`/`mulHighU`/`mulFlagsU`/`mulFlagsS`/
`divWeitU`/`divWeitS`/`zugelassen`/`okWerte`/`istHalt`/`mdZustandMul`/
`mdZustandNull` and all `md_*` step equations plus
`verweigert_heisst_halt` from `MulDiv`; `read64_nach_write64`/
`writeBytesN_hit`/`addrOff_null` from `Speicher`.

## Last check results

- `./lean-probe grammatik/Grammatik/X86/MulDivCodec.lean`: 0 errors, exit 0.
  Axioms per theorem: none, `[propext]`, `[propext, Quot.sound]`, or
  `[propext, Classical.choice, Quot.sound]` — all within the goal set.
- `./lean-bau`: exit 0, 0 error lines, `Build completed successfully
  (428 jobs)`. Whole project green.

## What remains open (see CUTS in the file)

Hardware correspondence of the encodings; memory-form and
immediate/one-operand-IMUL forms; source correspondence and
physical-fault/source-stop transfer (`hardwareHalt` only names the stop
class); permission-checked fetch integration (lane 575 consumes
`mulDivEncode`/`decodeMulDiv`/`roundtrip_muldiv`/`decodeMulDiv_len_ok`/
`decodiert_laenge_ok`/`decode_exec_*` as its producer interface); TSO/GX;
costs. No new assumptions, no checker codes taken.

## Task remarks

Nothing in the task statement was wrong. One judgment call to record: a
set REX.R bit over a Group-3 opcode is refused as non-canonical (keeps
one encoding per operation for the validator); real hardware may ignore
that bit instead — booked in CUTS as a subset choice, not a hardware
claim. No source-syntax premises occur, so rule 13 required no
`_zeuge`; `muldiv_codec_zeuge` is provided anyway per the task sentence
(nondegenerate: memory-changing store plus planted refusals, jointly).
