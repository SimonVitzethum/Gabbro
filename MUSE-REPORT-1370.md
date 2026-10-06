# MUSE-REPORT-1370: Exact review of candidate 1369 (SSSE3 three-byte forms)

## Scope verified

- Clone `/home/simon/Dokumente/gabbro-muse/a1370`, branch `muse/1370`, clean at review start.
- Under review: author lane 1369 at the pinned head from
  `.tmp/review/SNAPSHOT.json` (base `880e743912590626f26a6b17faa22b2a40071077`), from FILES only
  (`.tmp/review/SNAPSHOT.json`, `.tmp/review/author-1369/PATCH.diff`,
  copied sources, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`). Never read the
  author clone; never ran git on the pinned hash.
- Changed files: `MUSE-REPORT-1369.md`, `grammatik/Grammatik.lean` (exactly
  one added line `import Grammatik.X86.SseThreeByte`), new file
  `grammatik/Grammatik/X86/SseThreeByte.lean` (1029 lines). Existing files
  otherwise untouched. PASS.

## Checks performed

- Banned constructs: grepped candidate file for `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`/`split_ifs`/`norm_num`/`ring_nf`/`sorryAx` as
  code. Only hits are English prose ("admitted", "admits") and
  `#print axioms` lines. No tactic/decl use. PASS.
- Axioms: ran `./lean-probe` on the candidate file in place
  (`.tmp/review/author-1369/.../SseThreeByte.lean`, no copy into the tree,
  clone stays clean): `== 0 error(s) in the COMPLETE output; exit 0`.
  `#print axioms` output matches the report exactly: no axioms for
  `encodeSseThree`/`vecPabs`/`vecPshufb`/`vecPalignr`/`stepSseThree`/
  `adapterSseThree`; `propext` for decoder/roundtrip/Wf; `propext +
  Quot.sound` for `kapDecodeSse`/`sseWit_zeuge`. Within the goal's allowed
  set (`propext`, `Classical.choice`, `Quot.sound`). PASS.
- Premise use: no `intro _` / `have _ :=`; spot-checked per-form step
  equations (`hok`, `hfp`, `h` all consumed in `simp`), frame theorems
  (`hok`, `hfp`, `hstep`, `hq` all consumed), adapter theorems (`hwf`/`h`
  consumed). No `forall rho`/`forall v` contract quantification; no
  Prop-typed premises; no conclusion restating a premise. PASS.
- Evaluator reuse: no `vecPshufb`/`vecPabs`/`vecPalignr`/`pabsLane`
  definition exists elsewhere in `grammatik/Grammatik/X86` (only
  `ymmAndn` in `Avx2Ops.lean`, the cited construction pattern). The three
  functions are built from accepted `laneNat`/`vecMk` with per-lane
  equations via accepted `laneGet_mk`; step/adapter reuse `xmmSet`/
  `ripNach`/`vecEintritt`/`laengeOk`/`projFp`/`setKernVonFp`/`HwAdapter`/
  `HwWf`. Lifted, not copied. PASS.
- Planted refusals: 8 decoder refusals (`speicher`/`kurz`/`escape`/
  `movbe`/`mmx`/`rexw`/`ohne_imm`/`blendv`) plus 5 old-chain `decide` pins
  and extended-chain pins/refusals (`movbe`/`blendv`) are machine-checked
  (`rfl`/`decide`/lemma composition), not asserted. PASS.
- Witness: `sseWit_zeuge` joins 13 facts — shuffle lane 0->1 change,
  abs lanes (1, 5), owner-only forwarding (99 vs 0), drain changing shared
  memory (0 to 99), `HwWf`, bad-length adapter refusal, MOVBE/BLENDVPS
  refusals. Two cores run family steps; memory changes via the TSO
  drain half. Non-degenerate (XMM change + memory change). PASS.
- Silicon: opcode rows confirmed in clone-local Intel SDM 325462-093US
  extracts (`66 0F 38 1C` line 72298, `66 0F 3A 0F` line 74369, PALIGNR
  composite `((DEST<<128) OR SRC)>>(imm8*8)` line 74482); PSHUFB
  bit-7-zero/low-4-select, PABS unsigned-with-INT_MIN-wrap, PALIGNR
  zero-past-32 are consistent with the cited pages and covered by `decide`
  spot-checks. No flags/memory/GPR effects claimed (frame theorems prove
  preservation). No AMD provenance claimed. PASS.
- CUTS/honesty: file ends with CUTS block + 12 `#print axioms`; report
  claims only the 5 admitted rows, refuses MMX/memory/REX.W/other third
  bytes, names silicon assumptions, disclaims hardware correspondence,
  W/GX, source/loader/budget links. No over-claim. PASS.

## Build status (honest)

- `./lean-probe` candidate file: `== 0 error(s) in the COMPLETE output;
  exit 0` (verified by this reviewer, axioms listed above).
- Author BUILD-EVIDENCE: `./lean-bau` green, `Build completed successfully
  (709 jobs).`
- This reviewer's `./lean-bau` on the clean clone: NOT completed — timed
  out twice under slot contention (600s probe slot first attempt, then
  1200s and 1800s build waits with no output; other lanes hold the Lean
  slot). This is apparatus contention, not a candidate finding; the
  candidate's own file probes green here and its integrated build is in
  evidence. No red build was observed anywhere.
- `python3 instrumente/lean-layout.py --check` on clean base: already
  `NOT PLACED: SystemDecode.lean` before any candidate content, so layout
  is pre-existing non-clean; the task-fixed path vs `^Sse` rule conflict
  the author reports is real and goes to the merge gate's `--apply`, not
  to this verdict.

## Open / not claimed (carried forward)

- SSE4.1 remainder, SSE4.2 string family + PCMPGTQ + CRC32, AES, MOVBE,
  PHADD/PHSUB saturation, PSIGN, PMULHRSW stay refused by design.
- No VEX/EVEX/SIB/LOCK, no source/IR/loader/entry/budget link, no
  target-to-W/GX simulation, no timing/power claims.
- Maintainer wiring: add the `decodeSseThree` arm behind every earlier arm
  of `HwKapsteinDecoder.kapDecode` (documented in file §6).
- Base drift note: candidate branched at `880e7439`; current master tail
  has two extra imports (`BeweisAtomar`, `SystemDecode`). Merger unions
  the added import line at the new tail.

## What I believe is wrong in the task

- The FAMILY sentence arrived truncated (`A... (line truncated to 2000
  chars)`), so the full required row set never reached the author. The
  author modelled the visible SSSE3 core (PSHUFB, PABSB/W/D, PALIGNR) and
  refused the rest with pins. Judging the missing truncated-away rows
  against this candidate would punish a harness failure; they belong to
  follow-up lanes, not to this verdict.

## Machine-readable verdict (substantive verdict unchanged: accept)

CANDIDATE: 1369 31b606f95100f917d1f8fd08e55ff9ce24da63cb
VERDICT: ACCEPT
