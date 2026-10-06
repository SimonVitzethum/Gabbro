# MUSE-REPORT-1352: exact review of candidate 1351 (MOV/TEST/LEA/PUSH/POP/NOP/frame)

Reviewer lane 1352, clone /home/simon/Dokumente/gabbro-muse/a1352, branch muse/1352
(verified). Under review: author lane 1351 at pinned head
c120e7310f15b54081b340c5a7ab3a989b71dd6b (machine-readable lines in the
verdict section below).
Delivered files reviewed: `.tmp/review/SNAPSHOT.json`,
`.tmp/review/author-1351/PATCH.diff`,
`.tmp/review/author-1351/grammatik/Grammatik/X86/IntMovTest.lean` (1993 lines),
`.tmp/review/author-1351/grammatik/Grammatik.lean` (712 lines),
`.tmp/review/author-1351/OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
`MUSE-REPORT-1351.md`. No `git show/log/diff` on the pinned hash was used.

## Checks performed (all against the delivered files + own-clone tree)

- Forbidden tokens: full-file grep for `sorry|native_decide|axiom|unsafe|admit`
  finds only three English-prose "admit" (lines 1387, 1606, 1721, 1933:
  "admit no event") and 42 `#print axioms` lines. No `sorry`/`sorryAx` token,
  no `admit` tactic, no `axiom` declaration, no `native_decide`, no `unsafe`.
- Axioms: author BUILD-EVIDENCE final `./lean-bau` lists every main theorem at
  `[propext]` or `[propext, Quot.sound]` incl. `mt_zeuge`; no `sorryAx`,
  no `Classical.choice`. (An intermediate `sorryAx` on `mt_zeuge` is explained
  in the author report as error-recovery after a `-` + `/` block-comment parse
  break, fixed by rewording; final list is clean.)
- Existing-file diff: the delivered `Grammatik.lean` is base + exactly one
  appended line 712 `import Grammatik.X86.IntMovTest`. Nothing else touched.
- Evaluator reuse, not copies: the new file imports the accepted producers
  (NarrowOps, ShiftLogic, AddressEncoding, HwAddressed, HwStackCalls,
  Ausfuehrung, HardwareExecution, HwKapsteinDecoder) and calls `mergeRegNarrow`,
  `moveNarrow`, `andW`, `adrEff`, `parseAdrTail`/`encodeAdr`, `hwAddrStore`/
  `hwAddrLoad`, `concIssue`/`concLoad`, `schrittRegister`/`ripNach`/`laengeOk`/
  `regSet`; it defines none of them (grep for redefinition: no hits).
  `andW` is used for TEST with AF free as the accepted definition provides.
- Ownership exclusions verified to exist in-tree: `decodeSx90/86/87`
  (IntSignXchg.lean:581/604/615), `decodeCoreLea` (IntegerCore.lean:508,
  REX.W-only mod-2-SIB slice), `decodeLea` (AddressEncoding.lean:782),
  `decodeC`/`decodeCore`/`decodeNarrow` arms of `kapDecode`
  (HwKapsteinDecoder.lean:45-70). The `intro c f _` shape of `mtWitM0_wf`
  matches the accepted canonical pattern (HardwareExecution.lean:99,553).
- Every premise used: all theorems read use every hypothesis (agreement,
  wf-preservation, refusal and witness lemmas discharge each `h` by
  rewrite/simp/case-split; no `intro _` / `have _ :=` discard found).
- Planted refusals genuinely refuse: `mtPushW/popW/leaveW_laenge_verweigert`
  (bad length), `mtAdapterReg_laenge_verweigert`, `adapterMt_verweigert`,
  plus pinned `pin_mt_fremd_verweigert` incl. `decodeMovTest [0x90] = none`,
  and the `pin_kap_*` refusal/acceptance matrix plus `probe_kap_*` boundary
  probes, all `decide`-closed against the real `kapDecode`.
- Extended chain is old-first by construction (`kapDecodeMitMt`, lines
  1350-1357) with universal agreement `kapDecodeMitMt_kap` (ALL byte strings
  the old chain decodes) and take-where-refused / joint-refusal theorems.
  Shadowing is impossible by construction, not by witness.
- Witness non-degenerate: two cores; core-0 push buffers 8 entries
  (`mtWit_puffer8`), RSP drops to slot, RIP advances, shared slot still zero;
  forwarded pop restores RSP and observes the word; eight-flush drain changes
  shared memory byte 0 to `0x08` (`mtWit_spuelung`) observed by core 1
  (`mtWit_fremd_neu`); owner-only forwarding exhibited both sides
  (`mtWit_weiterleitung` vs `mtWit_fremd_alt`); MOV value, TEST ZF and the
  adapter register lift are jointly closed in `mt_zeuge` beside the planted
  refusal. Memory-changing reached run: yes.
- Silicon spot-checks: ENDBR64 F3 0F 1E FA; INT3 CC; UD2 0F 0B; LEAVE C9;
  RET-imm C2+imm16; PUSH/POP only b16/b64 (FF /6, 8F /0); TEST AI64/RImm64
  sign-extend imm32 (`sext .b32`, lines 1275-1291); movMImm64 carries imm32;
  forced-REX for byte codes 4-7; 8/16-merge and 32-zero-extend via accepted
  `mergeRegNarrow`. No AMD provenance claimed; undefined behavior (AF) left
  to the accepted definition. No error found.
- CUTS honest (lines 1908-1948): claims canonical-subset self-consistency
  only; disclaims silicon correspondence, general memory round trip,
  target-to-W/GX simulation, LOCK/RMW, interrupts, source/ABI/loader/entry/
  budget. No hardware-correspondence or W/GX claim anywhere (only disclaimer
  mentions). Maintainer wiring point named (kapDecode last arm).

## Known residuals (disclosed, not repair-grade)

- 90H (XCHG 90+r, 1-byte NOP 90) and 86/87 decode nowhere in the extended
  chain (the new decoder refuses with pin; `kapDecode` has no Sx/XCHG arm).
  Refusal is the correct call: XCHG carries implicit-LOCK semantics and the
  coherent machine under construction refuses LOCK/RMW; forcing it here would
  duplicate `decodeSx` or drag LOCK scope into this lane. Follow-up belongs
  to the locked-RMW connection, not this family.
- General REX.W / 66H LEA likewise unconnected (the new decoder takes bare 8D
  only; old chain takes only the mod-2-SIB REX.W slice via `decodeCoreLea`,
  and accepted `leaGemeinsam_verweigert` shows `decodeExt` refusing one
  REX.W form). Disclosed in CUTS; maintainer work at the named wiring point.
- Layout conflict documented by the author: task mandates
  `grammatik/Grammatik/X86/IntMovTest.lean`, rule 36 would place `Int*`
  under `Befehle/Ganzzahl`; merge gate runs `--apply`. Not a defect.
- My clone base is newer than the pinned base (own `Grammatik.lean` has
  721 lines vs pinned-base 711); the one-line append will need its usual
  trivial rebase at merge.

## Build status (honest)

- `./lean-probe` on the delivered file: exceeded 600 s, no result
  (cold `.lake`, serial slot shared with other lanes).
- `./lean-bau` in own clone: exceeded 3600 s with no result line (same cause).
- Author BUILD-EVIDENCE final entries: `./lean-bau` exit 0, 0 error lines,
  `Build completed successfully (709 jobs).`; `./lean-probe` 0 errors.
  The finding below rests on the complete static verification above plus that
  evidence; the merge gate rebuilds `grammatik/` locally before committing,
  which covers the missed independent re-execution.

## Machine-readable verdict

CANDIDATE: 1351 c120e7310f15b54081b340c5a7ab3a989b71dd6b
VERDICT: ACCEPT

The accepted state carries no unsupported desired-correctness premise, no
weakened guarantee, no fake closure. New definitions/theorems added by this
reviewer: none (report-only review; no Lean changes made, working tree left
clean except this report).
