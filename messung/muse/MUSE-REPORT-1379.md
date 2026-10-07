# MUSE-REPORT-1379: SSE4.2 string compares, PCMPGTQ and CRC32

Lane 1379, clone `/home/simon/Dokumente/gabbro-muse/a1379`, branch `muse/1379`.
Owned files only: `grammatik/Grammatik/X86/SseFourTwo.lean` (new, ~1500 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was done

Connected the SSE4.2 family (register-direct rows only) to the coherent
machine, in the style of `SseFourOne.lean` / `HwMulDivWidth.lean`:

- **Op type** `Sse42Op`: `strRR` (4 arts `estri/estrm/istri/istrm` + imm8),
  `pcmpgtqRR`, `crc32` (r64 flag + source width). Canonical encoders
  (`encodeSse42`): 7-byte string rows, 6-byte PCMPGTQ, 6/7-byte CRC32.
- **Decoder** `decodeSse42` (parses bytes, never encode-equality) with
  per-row round trips (`roundtrip_str/pcmpgtq/crc`, combined
  `roundtripSse42`; imm8 up to byte normalisation `sse42Norm`,
  CRC on the 5 admitted width rows `crcZulaessig`).
- **Old-chain pins**: `kap_weist_estri/estrm/istri/istrm/pcmpgtq/crc32_zurueck`
  (all `decide`); planted refusals (memory ModRM, truncation, REX.W
  vectors, uncovered thirds, missing F2, r64+word).
- **Semantics** from the SDM extracts (clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  edition 093US): full imm8 matrix (`modusVonImm`, Tables 4-2/4-3/4-4/4-7:
  `strBool/strRes1Bit/strRes2Bit`, explicit saturated lengths,
  implicit null scan, ECX index / XMM0 mask, overloaded flags),
  signed-qword `vecPcmpgtq`, reflected CRC32 `crcWert` (poly
  11EDC6F41H, DEST[63:32] := 0) with known-answer check
  `crc32_check_wert` (`"123456789"` -> `0xCBF43926`, verified by
  `decide`).
- **Step** `stepSse42` on `FpZustand` with frame theorems (RIP, memory,
  per-shape flags, CRC value, XMM preservation).
- **Extended chain** `kapDecodeSse42` (old chain first, exact agreement
  `kapDecodeSse42_alt/neu/nichts`, three `decide` pins).
- **Adapter** `adapterSse42 : HwAdapter Sse42Dec` (wf preservation,
  exact agreement, memory/buffer preservation, three refusals).
- **Witness** `sse42_zeuge`: core-0 compare (`8>7` -> all-ones, `7>7`
  -> 0), core-1 CRC accumulation, string equal-any + ranges spots,
  TSO issue/forwarding/drain 0 -> 43, `HwWf`, bad-length refusal,
  decoder refusal. Non-degenerate (XMM lanes + memory change).
- CUTS block and `#print axioms` per main theorem; all axioms within
  `propext`/`Quot.sound` (subset of the standard triple, no `sorryAx`).

## Verification (actual, queued wrappers)

- `./lean-probe grammatik/Grammatik/X86/SseFourTwo.lean`: **0 errors**.
- `./lean-bau`: green, 716 jobs, "Build completed successfully".
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file.

## Findings (silicon-first corrections during the work)

1. The task text names the CRC32 polynomial "CRC-32C" (truncated line);
   the SDM page gives polynomial **11EDC6F41H** (CRC-32/ISO-HDLC) with
   DEST[63:32] := 0 always. The file follows the SDM; the discrepancy
   is recorded in CUTS.
2. `F1` + REX.W **is** a qword source (operand-size rule), not a refused
   row; only (r64, word), (r64, dword) and (r32, qword) have no SDM row.
   `crcZulaessig` admits exactly the 5 table rows; `encodeSse42`
   aliases refused width rows onto admitted bytes (documented in CUTS).
3. My 64-bit signed test value `4294967295` was positive, not negative;
   replaced with a true signedness discriminator (max-positive vs
   min-negative), which `decide` now checks.
4. Proof-shape notes (for other lanes): a Prop-`if` REX classifier and
   nested tuple-literal matches blocked kernel `rfl` reduction while
   `decide` passed; literal-match dispatch in exact `SseFourOne` shape
   reduces under `rfl`. Multi-field nested `{ ... with ... }` updates
   were rejected by the parser; the step uses positional construction
   (and the accepted `schrittRegister` shape was avoided only for that
   syntactic reason -- semantics are identical).

## Open / maintainer wiring

- Wire-in: add the `decodeSse42` arm behind every earlier arm of
  `HwKapsteinDecoder.kapDecode` (existing files untouched per lane rule).
- NOT claimed (see CUTS): memory ModRM forms, REX.W vector rows,
  VEX/EVEX, SIB/addressed operands, LOCK path, faults, source/IR/ABI/
  loader/entry/budget links, per-access W/GX simulation, timing/power,
  hardware correspondence beyond self-consistency.
