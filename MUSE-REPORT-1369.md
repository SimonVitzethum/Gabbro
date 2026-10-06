# MUSE-REPORT-1369: SSSE3 three-byte forms over 0F 38 / 0F 3A

## What was done

NEW FILE `grammatik/Grammatik/X86/SseThreeByte.lean` (namespace
`Gabbro.Grammatik.X86`, ~1030 lines) plus one import line appended to
`grammatik/Grammatik.lean`. It connects five admitted SSSE3
register-direct XMM rows to the coherent machine and the capstone
chain: PSHUFB (`66 0F 38 00 /r`), PABSB/W/D (`66 0F 38 1C/1D/1E /r`)
and PALIGNR (`66 0F 3A 0F /r ib`). Canonical REX (`64 + 4*R + B`,
W=0/X=0, always emitted) is required, exactly like the accepted
`VectorCodec` rows.

- §1 encoding: `SseThreeOp`, `sseThreeEscape`, `sseThreeThird`,
  `sseThreeRex`, `encodeSseThree` (6 bytes, 7 for PALIGNR),
  `encodeSseThree_len6/len7`, and five `decide`-pins that the old
  `kapDecode` refuses the new canonical bytes
  (`kap_weist_pshufb/pabsb/pabsw/pabsd/palignr_zurueck`).
- §2 decoder: `SseThreeDec`, `decodeSseThreeModrm/Nach`,
  `decodeSseThree`, per-row round trips
  (`roundtrip_pshufb/pabsb/pabsw/pabsd/palignr`, all `cases`-`rfl`)
  plus `roundtripSseThree`, and eight planted decoder refusals
  (`sseThree_nichts_speicher/kurz/escape/movbe/mmx/rexw/ohne_imm/blendv`).
- §3 semantics from the accepted lane vocabulary only
  (`laneNat`/`vecMk`; no accepted shuffle/abs/align evaluator exists,
  same construction as the accepted `ymmAndn`): `pabsLane`,
  `vecPabs/vecPshufb/vecPalignr`, per-lane equations
  (`laneNat_pabs/pshufb/palignr` via the accepted `laneGet_mk`),
  and four `decide` silicon spot-checks (`pabsLane_silicon`,
  `pabsLane_silicon16`, `vecPshufb_silicon`, `vecPalignr_silicon`:
  INT_MIN wrap, bit-7 zeroing, shift/zero-past-32).
- §4 step on the shared `FpZustand` (same `xmmSet`/`ripNach`/
  `vecEintritt` discipline as `stepVector`): `stepSseThree`, length
  and profile refusals, five per-form equations.
- §5 frames: `sseThreeDst`, `stepSseThree_rip/flags/speicher/gpr/fremd`
  (flags/memory/GPRs untouched, other XMM kept, RIP advances).
- §6 extended chain over the old one (never edited):
  `KapSse` (`alt`/`neu`), `kapDecodeSse`, agreement
  (`kapDecodeSse_alt/neu/nichts`), five `decide` neu-arm pins
  (`kapSse_pin_pshufb/pabsb/pabsw/pabsd/palignr`), old-chain pins
  for MOVBE/BLENDVPS and the joined refusals
  (`kapSse_nichts_movbe/blendv`). Maintainer wiring: add the
  `decodeSseThree` arm behind every earlier arm of
  `HwKapsteinDecoder.kapDecode` (position of the `avx2` arm: last).
- §7 adapter: `adapterSseThree : HwAdapter SseThreeDec`
  (register path via `setKernVonFp`, `none` on refusal),
  `adapterSseThree_wf/ok/mem/verweigert_bei_laenge/verweigert_bei_profil`.
- §8 reached two-core witness `sseWit_zeuge` joining 13 facts:
  shuffle lane (1 vs 0 before), abs lanes (1 and 5), owner-only
  forwarding (99 vs 0), drain changing shared memory (0 to 99),
  `HwWf`, a bad-length adapter refusal, and the MOVBE/BLENDVPS
  chain refusals.

Last `./lean-bau` result line: `Build completed successfully (709 jobs).`
`./lean-probe` on the new file: 0 errors. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` in the file (mechanically grepped; one hit is
the English word "admissions" in a comment). `#print axioms`: no axioms
for `encodeSseThree/vecPabs/vecPshufb/vecPalignr/stepSseThree/
adapterSseThree`; `propext` alone for decoder/roundtrip/Wf theorems;
`propext + Quot.sound` for `kapDecodeSse`/`sseWit_zeuge` (same
footprint class as the accepted `kapW_*` theorems).

Silicon provenance (checked, clone-local
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
Intel SDM 325462-093US Sep 2026): opcode rows PABSB/W/D p.4-176
(`66 0F 38 1C/1D/1E`), PALIGNR p.4-216 (`66 0F 3A 0F`, Operation
`temp1 := ((DEST << 128) OR SRC) >> (imm8*8)`), PSHUFB p.4-422
(zero on bit 7, low 4 bits select). No AMD manual in the clone: no
AMD provenance claimed; these rows are fully defined on both
vendors and touch no undefined flag. No VEX/EVEX/MMX/memory forms
are admitted, so no vendor-divergent behaviour is modelled.

## Open / not claimed

- The SSE4.1 remainder (PMOVSX/ZX, PMINS/PMAX, PMULLD, BLEND,
  PTEST, ROUND, PINSR/PEXTR, DPPS/DPPD, INSERTPS/EXTRACTPS), the
  SSE4.2 string family + PCMPGTQ + CRC32, AES, MOVBE, PHADD/PHSUB
  saturation, PSIGN and PMULHRSW stay refused (MOVBE/BLENDVPS pins
  beside the run). Memory ModRM, MMX (NP) and REX.W forms refused.
- No VEX/EVEX/SIB, no LOCK path, no source/IR/ABI/loader/entry/
  budget link, no per-access target-to-W/GX simulation, no
  timing/power claims (see file CUTS).
- No rule-13 `_zeuge` was owed (no premise quantifies over program
  syntax, no ZEUGE target named); `sseWit_zeuge` is provided anyway
  per the MECHANISM paragraph.

## What I believe is wrong in the task

1. The FAMILY sentence is cut off (`A... (line truncated to 2000
   chars)`): the full required set never arrived. I modelled the
   visible SSSE3 core (PSHUFB, PALIGNR, PABS); the rest of the
   0F 38 / 0F 3A space stays a finding for follow-up lanes.
2. Layout conflict: the task fixes the path `X86/SseThreeByte.lean`
   and OWN ONLY lists it, but `lean-layout-rules.py` (`^Sse\w+$`
   to `Befehle/Sse`, which does not exist) makes `--check` report
   `NOT PLACED`. I kept the task path (rule 1 / OWN ONLY wins; the
   merge gate runs `--apply` after every merge per AGENTS.md §3).
3. MECHANISM asks for "two cores where the family touches memory",
   but this family is register-only by silicon: no admitted form
   has a memory operand. The witness runs the family on two cores
   (XMM-changing) and reuses the accepted TSO equations for the
   buffered-store/forward/drain half; this is stated in the file.
4. The "widths 8/16/32/64 MERGE/ZERO-extend, REX byte registers"
   boilerplate is about GPR forms; this family writes whole XMM
   registers only (upper YMM unmodified, legacy SSE) and no GPR.
5. Apparatus, not task: the permission layer rejected several
   file-operation shell calls mid-lane (`ls`, `tail`, `test -f`,
   `python3 -c`); I used the dedicated file tools instead and
   reserved the shell for the queued wrappers. `lean-probe`/
   `lean-bau` needed retries past 600-900s slot contention, then
   went green. No files outside the clone were touched; no network,
   no push.
