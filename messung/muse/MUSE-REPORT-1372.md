# MUSE-REPORT-1372: exact review of candidate 1371 (SSE4.1 register rows)

CANDIDATE: 1371 8154a4e3ad6d59e4ab8e1496eb1c79aaf0a8c44f
VERDICT: ACCEPT

## What was done

Report-only independent exact review of lane 1371. Clone verified
`/home/simon/Dokumente/gabbro-muse/a1372`, branch `muse/1372`. The pinned
author hash was never read via git (no `git show/log/diff` on it); the
candidate was reviewed as delivered FILES under `.tmp/review/author-1371/`:
`SNAPSHOT.json` (author 1371, base `b1082d44`, 3 files, clean), `PATCH.diff`,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json`, the new module
`grammatik/Grammatik/X86/SseFourOne.lean` (990 lines, read in full), and
`MUSE-REPORT-1371.md`.

Checks performed:
- Banned tokens: grepped the candidate for
  `sorry|admit|axiom|native_decide|unsafe|sorryAx`. All 25 matches are benign:
  the English word "admitted" and the required `#print axioms` lines. No
  `sorry`, `admit`, `axiom` declaration, `native_decide`, `unsafe`, `sorryAx`.
- Discarded premises: grepped for `intro _`, `have _ :=`, `forall rho`,
  `forall v`. No hits. Frame theorems (`stepSseFour_rip/_flags/_speicher/_gpr`,
  `_fremd`, `adapterSseFour_wf/_ok/_mem`, `kapDecodeSseFour_alt/_neu/_nichts`)
  use every hypothesis.
- Existing files: `PATCH.diff` shows exactly one added line in
  `grammatik/Grammatik.lean` (`import Grammatik.X86.SseFourOne`); no other
  existing file touched.
- Evaluator reuse (lifted, not copied): every accepted definition the
  candidate builds on was confirmed present in this clone's tree --
  `laneNat`/`vecMk`/`laneGet_mk` (`Kern/Vektor.lean`),
  `xmmSet`/`xmmSet_fremd` (`Befehle/Gleitkomma/ScalarFloat.lean`),
  `ripNach`/`laengeOk`/`vecEintritt` (`vecEintritt ... := b.osXmm`,
  `Befehle/Vektor/VectorCodec.lean`), `HwAdapter`/`projFp`/`setKernVonFp`/
  `setKernDaten_wf` (`Hw/Grundlage/HardwareExecution.lean`),
  `kapDecode` (`Hw/Kapstein/HwKapsteinDecoder.lean`), TSO
  `issueByte`/`loadByte`/`flushKern` (`TSO/Kern/TSO.lean`). The candidate
  defines no competing model; semantics (`vecPmovsxbw`, `vecPmovzxbw`,
  `vecPminsd`, `vecPmaxsd`, `vecPmulld`, `vecPcmpeqq`) are built from the
  `laneNat`/`vecMk` vocabulary only. Its step/adapter/extended-chain
  structure mirrors the accepted `Befehle/Sse/SseThreeByte.lean`, including
  the same `vecEintritt`-only gating (no `HwFeatureGates` CPUID bit -- same
  as the accepted predecessor, so no new deviation).
- Silicon facts against the Intel SDM row data named in the file header
  (325462-093US): `66 0F 38 20` PMOVSXBW, `30` PMOVZXBW, `39` PMINSD,
  `3D` PMAXSD, `40` PMULLD, `29` PCMPEQQ -- all correct rows of the `0F 38`
  map; sign rule `u + 65280` for `u >= 128`, zero extension, signed
  min/max via `sVal32`, PMULLD low 32 bits, PCMPEQQ all-ones-on-equal --
  all correct; no flag/memory/GPR effect is correct for these forms.
  Arithmetic spot-check by hand: 70000^2 = 4900000000;
  4900000000 - 2^32 (4294967296) = 605032704, matching
  `vecPmullcmp_silicon` and the witness. REX handling admits only
  40/41/44/45 (W=0/X=0 canonical); REX.W, memory ModRM, wrong escapes and
  foreign third bytes are refused by `rfl` theorems. No vendor-specific or
  undefined behaviour is pinned.
- Witness `sseFourWit_zeuge` is non-degenerate: two cores (core 0
  PMOVSXBW 255->65535 and 5->5, core 1 PMULLD 70000^2->605032704 as XMM
  lane changes), plus TSO owner-only forwarding of byte 77 and a drain
  that changes shared memory 0->77, with `HwWf` and refusal pins beside
  the run.
- CUTS is honest: claims only the six register-direct rows with
  self-consistency, names the opcode/sign-rule transcription as assumption,
  disclaims hardware correspondence, the SSE4.1 remainder, all of SSE4.2,
  memory/SIB/LOCK/VEX, source/loader/budget links and any W/GX bridge.
- Build evidence: author's `BUILD-EVIDENCE.json` final round shows
  `./lean-probe ... == 0 error(s), exit 0` with standard axioms only
  (defs axiom-free; `decodeSseFour`/`roundtripSseFour`/`adapterSseFour_wf`/
  `sseFourWitStart_wf` on `[propext]`; `kapDecodeSseFour`/`sseFourWit_zeuge`
  on `[propext, Quot.sound]` inherited from `kapDecode`; no `sorryAx`)
  and `./lean-bau` 712 jobs green. Own baseline `./lean-bau` on the
  untouched `muse/1372` tree: `Build completed successfully (712 jobs).`

## Last build result

`./lean-bau`: `Build completed successfully (712 jobs).` (baseline, own
tree untouched; candidate not merged here).

## What remains open (follow-up, not repair)

- The six-row cut is honest but narrow: SSE4.2 (PCMPESTRI/M, PCMPISTRI/M,
  CRC32) is entirely unmodelled despite the lane title; memory ModRM forms,
  REX.W, PBLENDW/BLEND*/PTEST/ROUND*/PIN*/PEXTR*/INSERTPS/EXTRACTPS/
  DPPS/DPPD/MPSADBW/PHMINPOSUW/PACKUSDW remain open per CUTS.
- Layout: task path `X86/SseFourOne.lean` vs rule `^Sse\w+$` ->
  `Befehle/Sse` (confirmed in `instrumente/lean-layout-rules.py:43`);
  maintainer runs `lean-layout.py --apply` after integration, as the
  author already notes. Wiring note (add `decodeSseFour` arm last in
  `kapDecode`) is stated for the maintainer.
- Per-family CPUID gating through `HwFeatureGates` (owner-task phrase)
  is absent here, exactly as in accepted `SseThreeByte`; a coordinator
  decision whether family modules need it.
- Report nit: `MUSE-REPORT-1371.md` mentions `sVal8`; the file defines
  only `sVal32`.

## Anything in the task believed wrong

- Nothing blocking. The `lean-probe`-after-copy step prescribed by the
  review task could not be executed here (file copy into the clone was
  refused), so this ACCEPT rests on the full 990-line read, the grep
  checks above, and the author's recorded zero-error probe evidence --
  stated plainly. A merge gate re-probe is the natural second check.
