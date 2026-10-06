# MUSE-REPORT-1355: SSE/SSE2 moves, loads, stores and unpack

## What was done

NEW FILE `grammatik/Grammatik/X86/Befehle/Sse/SseMoves.lean`
(namespace `Gabbro.Grammatik.X86`, flat like the other family files),
plus the `import Grammatik.X86.Befehle.Sse.SseMoves` line in
`grammatik/Grammatik.lean`. The 27-row family `SseMoveOp`:
MOVUPS/MOVUPD/MOVAPS/MOVAPD loads and stores (0F 10/11/28/29),
the MOVSD store (F2 0F 11), MOVLPS/MOVHPS loads and stores plus
MOVLHPS/MOVHLPS (0F 12/13/16/17), UNPCKL/UNPCKH PS/PD (0F 14/15),
MOVNTPS/MOVNTPD/MOVNTDQ/MOVNTI, MOVD/MOVQ register forms
(66 0F 6E/7E, F3 0F 7E, 66 0F D6).

- §1 encoder: canonical REX (W=0) + legacy prefix + 0F + opcode +
  ModRM (mod=3 reg, mod=2 base+disp32 with the pilot SIB rule).
- §2 decoder `decodeSse`/`SseDecodiert` with explicit lengths.
- §3 round trip on every row (10 register rows, 17 memory rows in
  both SIB shapes).
- §4 new extended chain `kapDecodeSse` over the accepted
  `kapDecode` (agreement × 3, 9 refusal pins, 1 chain pin, 6 planted
  decoder refusals, 1 overlap pin).
- §5 register semantics `sseRegSchritt` on the shared `FpZustand`
  (unpack interleaves over `laneNat`/`vecMk`, half moves and MOVQ
  over `vLo`/`vHi`/`vecJoin`, MOVD store over the accepted
  `mergeRegNarrow .b32`), 10 selection theorems, 8 unpack lane
  facts, memory discipline.
- §6 `adapterSseMoves : HwAdapter SseDecodiert` with
  well-formedness, agreement, projection and refusal theorems.
- §7 joint witness `sseHw_zeuge`: UNPCKLPS on core 0, MOVLHPS on
  core 1, owner-only TSO forwarding and a drain that changes shared
  memory 0 → 42, beside memory-row and bad-length refusals.
- CUTS block and `#print axioms` for the 9 main theorems.

## Last build results

- `./lean-probe grammatik/Grammatik/X86/Befehle/Sse/SseMoves.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (plus harmless
  unused-`simp`-arg linter warnings).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (709 jobs)`).
- `python3 instrumente/lean-layout.py --check`: all 852 Lean files
  placed (after `--apply`, see below).
- Axioms (`lean-bau` output): `decodeSse`/`sseWitStart_wf`
  `[propext]`, everything else `[propext, Quot.sound]` — a subset
  of the goal standard, no new axioms. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (verified by grep; only the English word
  "admit" inside "admit no successor" comments).

## Findings (product)

1. The task's "MOVSS/MOVSD stores do not decode" premise is half
   wrong: the accepted `s32` family already decodes the MOVSS store
   (`movssSpeichere`, F3 0F 11, with fetched execution). Measured
   by `decide`: `kapDecode` accepts those bytes. This lane covers
   no MOVSS row (the `.movssSt` constructor was built, then
   removed); `pin_kap_movssSt_s32`/`pin_kapSse_movssSt_s32` prove
   the extended chain keeps the accepted arm. The MOVSD store
   (F2 0F 11) is genuinely missing and is covered here.
2. The ledger-1341 `fehlt` rows 0F 10/11/28/29, 0F 14/15,
   0F 12/13/16/17, 0F 2B/C3 and 66 0F E7 are taken by the new
   `decodeSse` arm; 9 `kap_weist_*_zurueck` pins prove the accepted
   chain refuses them.
3. Placement: the task path `X86/SseMoves.lean` violates HARD RULE
   18 (`^Sse\w+$` → `Befehle/Sse`). The file was created at the
   task path, then relocated with the prescribed
   `python3 instrumente/lean-layout.py --apply` (moved 1 module,
   rewrote the 1 owned import, updated `lean-layout-map.json`;
   references in 0 other text files). The header comment inside the
   file still names the old path (edit permission is pinned to the
   task paths); a maintainer may fix that one line.
4. Non-temporal stores are decoded but admit no register step and
   no TSO modelling here: their weaker ordering is recorded as
   absent, never as TSO (CUTS). Memory-form machine connection
   through §3/§6 TSO events is OPEN.

## What remains open

Memory-form steps on the coherent machine, aligned-form `#GP`
beyond refusal, MXCSR interaction, VEX/EVEX, MOVD/MOVQ memory
forms, and everything listed in the file's CUTS block. No
hardware correspondence beyond self-consistency; no W/GX bridge.

## Task feedback

The CONTEXT/MECHANISM paragraphs describe this lane kind
correctly (unlike the ledger lanes' reports); the operative gap
was the truncated FAMILY line (cut at "ordering is weaker than
TSO,..."). No premise was added, no conclusion weakened. Rule 13
needs no `_zeuge`: no theorem quantifies over program syntax and
the task names no `ZEUGE:` target; `sseHw_zeuge` is the reached
non-degenerate witness (two cores, memory-changing drain).
