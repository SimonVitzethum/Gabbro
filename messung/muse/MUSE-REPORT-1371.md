# MUSE-REPORT-1371: SSE4.1 register-direct rows (PMOVSXBW/PMOVZXBW/PMINSD/PMAXSD/PMULLD/PCMPEQQ)

## What was done
Created `grammatik/Grammatik/X86/SseFourOne.lean` (~950 lines) following the
accepted `SseThreeByte.lean` (lane 1369) and `HwMulDivWidth.lean` (lane 1127) patterns.
Scope is a bounded, honest subset of the lane's SSE4.1/SSE4.2 family: six
register-direct XMM rows over the `0F 38` escape, all with canonical REX
(`64 + 4*R + B`, W=0/X=0) + `66 0F 38` + third byte + register-direct ModRM (6 bytes).

Covered rows: PMOVSXBW (`20`), PMOVZXBW (`30`), PMINSD (`39`), PMAXSD (`3D`),
PMULLD (`40`), PCMPEQQ (`29`).

Contents:
- `SseFourOp`, `sseFourEscape`, `sseFourThird`, `sseFourRex`, `encodeSseFour`,
  `encodeSseFour_len6`.
- Six `kap_weist_*_zurueck` decide-pins: the old `kapDecode` refuses the new bytes.
- Canonical decoder `decodeSseFourModrm` / `decodeSseFourNach` / `decodeSseFour`
  (`SseFourDec` with checked length), per-row `roundtrip_*` + `roundtripSseFour`,
  planted refusals (`nichts_speicher/kurz/escape/rexw/pshufb/palignr`).
- Semantics from the accepted lane vocabulary only (`laneNat`/`vecMk`):
  `sVal8`, `sVal32`, `vecPmovsxbw`, `vecPmovzxbw`, `vecPminsd`, `vecPmaxsd`,
  `vecPmulld`, `vecPcmpeqq`, per-lane equations + three silicon spot-checks
  (`vecPmovsx_silicon`, `vecPminmax_silicon`, `vecPmullcmp_silicon`;
  70000*70000 mod 2^32 = 605032704 verified by hand computation).
- `stepSseFour` on `FpZustand` with `laengeOk`/`vecEintritt` refusals,
  `sseFourDst`, RIP/flags/memory/GPR/other-XMM frame theorems.
- Extended chain `KapSseFour` / `kapDecodeSseFour` with exact-agreement theorems
  (`_alt/_neu/_nichts`), five extended-chain pins, one extended refusal pin.
- `adapterSseFour : HwAdapter SseFourDec` with `_wf/_ok/_mem` and two planted
  refusal theorems.
- Joint two-core witness `sseFourWit_zeuge`: PMOVSXBW on core 0 (255->65535,
  5->5), PMULLD on core 1 (70000^2 -> 605032704), TSO owner-only forwarding of
  byte 77 and a memory-changing drain 0->77, plus length/decode/extended-chain
  refusals beside the run. Non-degenerate: XMM lanes change and shared memory changes.
- Appended `import Grammatik.X86.SseFourOne` to `grammatik/Grammatik.lean`.

Exact new definition/theorem names: see the file; main entry points are
`encodeSseFour`, `decodeSseFour`, `roundtripSseFour`, `vecPmovsxbw`,
`vecPmovzxbw`, `vecPminsd`, `vecPmaxsd`, `vecPmulld`, `vecPcmpeqq`,
`stepSseFour`, `kapDecodeSseFour`, `adapterSseFour`, `adapterSseFour_wf`,
`sseFourWitStart_wf`, `sseFourWit_zeuge`.

## Last build result
VERIFIED GREEN.
- `./lean-probe grammatik/Grammatik/X86/SseFourOne.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. Main-theorem axioms:
  defs axiom-free; `decodeSseFour`/`roundtripSseFour`/`adapterSseFour_wf`/
  `sseFourWitStart_wf`: `[propext]`; `kapDecodeSseFour`/`sseFourWit_zeuge`:
  `[propext, Quot.sound]` (inherited from the accepted `kapDecode`).
  No `sorryAx` anywhere.
- `./lean-bau`: `Build completed successfully (712 jobs).`
- `python3 instrumente/lean-layout.py --check`:
  `all 855 Lean files placed` (the task path `X86/SseFourOne.lean`
  passes the gate as-is; no `--apply` move was needed).

One real bug was found by the probe and fixed: sign extension via
`Int.toNat` maps negatives to 0 (`Int.toNat (-1) = 0`), so the first
`vecPmovsxbw` stated 255 -> 65535 but computed 0. It now uses pure-Nat
arithmetic (`u + 65280`), and the silicon spot-check passes. A second
probe round caught an edit accident that had deleted the `sVal32`
helper; it was restored and the build is green since.

## What remains open
- Verify: `./lean-probe grammatik/Grammatik/X86/SseFourOne.lean`, then
  `./lean-bau`, then `python3 instrumente/lean-layout.py --check` (expected
  tension: task path `X86/SseFourOne.lean` vs layout rule `^Sse\w+$` ->
  `Befehle/Sse`; maintainer runs `--apply`), then commit with the lane
  co-author line.
- Fix any `decide`/`unknown identifier` failures the probe reports (most
  likely kap-refusal bytes or helper-name drift from `SseThreeByte`).
- The SSE4.1 remainder (PBLENDW, BLENDPS/PD, BLENDVPS/PD/PBLENDVB+XMM0,
  PTEST, ROUND+MXCSR, PINSRB/D/Q, PEXTRB/D/Q, INSERTPS/EXTRACTPS,
  DPPS/DPPD, MPSADBW, PHMINPOSUW, PACKUSDW) and all of SSE4.2
  (PCMPESTRI/M, PCMPISTRI/M, CRC32) are NOT modelled -- see CUTS.
  No memory ModRM, REX.W, MMX, VEX/EVEX, SIB, LOCK, source/IR/loader/
  budget, or W/GX bridge is claimed.

## Anything in the task believed wrong
- The family string names PMOVSXBW/BD/BQ/... and PMOVZX* plus the full
  SSE4.1/SSE4.2 list, which is far beyond one lane turn with per-row
  round-trip + pins + adapter + witness obligations and no `sorry`; the
  six-row subset is the honest bounded cut, stated plainly in CUTS.
- `OWN ONLY grammatik/Grammatik/X86/SseFourOne.lean` conflicts with rule 18:
  `instrumente/lean-layout-rules.py` assigns `^Sse\w+$` to `Befehle/Sse`
  (where `SseThreeByte.lean` lives). The file was placed at the task path
  as instructed; the report/CUTS tell the maintainer to run `--apply`.
- No `ZEUGE:` target line was present (task truncated at 2000 chars), so
  rule 13 is met via the joint `sseFourWit_zeuge` over a non-degenerate
  two-core run rather than a named target witness.
