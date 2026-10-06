# MUSE-REPORT-1368: Exact review of candidate 1367 (LOCK RMW family)

## VERDICT: ACCEPT

CANDIDATE: lane 1367, pinned HEAD `27dc0244c18bde40021726249ab809bc1bcf65d9`
(base `880e743912590626f26a6b17faa22b2a40071077`, from `.tmp/review/SNAPSHOT.json`;
hash itself never inspected per lane rule). Changed files: `MUSE-REPORT-1367.md`,
`grammatik/Grammatik.lean` (one appended import line), new
`grammatik/Grammatik/X86/LockedAllRmw.lean` (1134 lines).

## What was checked

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a1368`, branch `muse/1368`.
- Forbidden tokens over the delivered file: no `sorry`, `admit`, `axiom`
  declaration, `native_decide`, `unsafe`, `sorryAx`, `split_ifs`, `norm_num`,
  `ring_nf` (remaining matches are English "admitted/admits"). 20 `#print axioms`
  lines present.
- `./lean-probe` run by me on the delivered candidate path
  (`.tmp/review/author-1367/grammatik/Grammatik/X86/LockedAllRmw.lean`):
  `== 0 error(s) in the COMPLETE output; exit 0`. Axiom output is exactly
  `[propext]` (data/round-trip pins) or `[propext, Quot.sound]` (chain/step/
  witness theorems) — a subset of the goal-theorem triple, no `sorryAx`.
  This reproduces the author's BUILD-EVIDENCE on my newer tree (my
  `Grammatik.lean` has 712 import lines vs the author's base with 709).
- `./lean-bau` on my tree: `== exit 0; 0 error line(s) in the COMPLETE output`,
  last line `Build completed successfully (709 jobs).`
- Patch scope: report + exactly one appended line
  `import Grammatik.X86.LockedAllRmw` at the end of `grammatik/Grammatik.lean`
  + the new file. No other existing file touched.
- Reuse, not duplication: every reused name verified present in my tree with a
  matching shape — `kapDecode`, `kapW_lock`, `kapKette_lock`
  (`Hw/Kapstein/HwKapsteinDecoder.lean`), `hwLockSchritt`, `hwLockWitStart`,
  `hwLockWitStart_wf`, `hwLockWit_nach1_wort`, `adapterLockRmw_wf`
  (signature `(m) (c) (a) (m') (h) (hwf)`, call site passes `m c _ m' h2 hwf`),
  `rexLockBits`, `codeReg`, `natByte`, `byteNat`, `rexByte`, `leBytes32`,
  `parseLe32`, `trunc`, `addB`, `HwAdapter` (single field `schritt`).
  Value layer arms call the accepted evaluators; the 17+2 agreement theorems
  are `rfl`.
- Every premise used: all hypotheses (`h`, `h1`, `h2`, `hwf`, `hm`) are
  rewritten/cased on; no `intro _`, no `Prop`-typed premise; conclusions are
  genuine liftings, not restated premises.
- Planted refusals really refuse, machine-checked: eight `kap_weist_*`
  `decide` pins (old chain refuses every new row), `lockAllAufLock_ablehnung`
  / `_schmal` / `_ohne_lock`, `hwLockAllSchritt_ud` / `_abgelehnt`, and the
  closed step refusals `hwLockAll_add32_nichts`, `hwLockAll_ud_nichts`,
  `hwLockAll_xaddPlain64_nichts` — all inside the 0-error probe.
- Witness non-degenerate: `lockAll_zeuge` replays the accepted two-core run
  through the family plug (word 10 to 15 on core 0, 15 to 22 on core 1 after
  the drain, old words through rax on both cores, owner-only forwarding of
  the foreign byte) beside Group-1, UD and unlocked-XADD refusals and new-arm
  chain evidence. Memory-changing steps on two cores, as required.
- Silicon spot checks against the clone-local Intel SDM extract
  (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`): LOCK=F0H;
  LOCK with non-memory destination is #UD (candidate: `regZiel` marker, step
  refuses); XADD 0F C0/C1, CMPXCHG 0F B0/B1, CMPXCHG8B 0F C7 /1, BTS/BTR/BTC
  0F AB/B3/BB, imm8 group 0F BA /4 BT /5 BTS /6 BTR /7 BTC, FE /0 INC /1 DEC,
  F6 /2 NOT /3 NEG, direction-bit rule (01 = wide memory destination) all
  match the tables. Canonical ModRM 0x85 = mod 2 / digit 0 / rm 5
  ([rbp+disp32]) correct; 0x8D / 0x9D likewise. No AMD provenance claimed;
  CUTS names Intel SDM only.
- CUTS honest: no hardware correspondence beyond self-consistency, no
  execution of Group-1/INC/DEC/NEG/NOT/bit-test/CMPXCHG8B rows, no universal
  round trip (ten closed rows), no W/GX bridge, no timing/progress claims.
  Maintainer extension point named
  (`decodeLock` in `TSO/Verriegelt/LockedInstructionExecution.lean`).
- Layout: `grammatik/Grammatik/X86/` holds 15 entries in my clone; the new
  file makes 16 of 20. No rule-18 breach.

## Non-blocking notes (not REPAIR reasons)

1. Doc claim "REX.W overrides 66H, like silicon": in `lockAllPraefixAux` a 66H
   byte arriving AFTER a REX byte resets the width to b16. Consequence is
   conservative (any non-b64 form is refused by the adapter), but the sentence
   is order-accurate only for LOCK/66H/REX.W in canonical order.
2. `lockAllWertCmp` is defined but has no agreement theorem and is wired into
   no step (the executed compare-exchange semantics stays entirely inside the
   accepted step). Dead helper for a future producer; harmless.
3. Unlocked register-only XADD/CMPXCHG (mod 3, no LOCK) decode to `none`
   rather than parsing: conservative non-coverage of legal instructions, safe
   direction.

## Method limitation, stated honestly

The permission layer rejected my shell file copy (`cp` + `>>`), so the
candidate file was NOT copied into `grammatik/` for an integrated `lean-bau`
WITH the candidate. Instead `./lean-probe` ran directly on the delivered
`.tmp/review/...` path, which elaborates identically (imports resolve through
the `grammatik/` lake environment, independent of the file location), and
passed with 0 errors. The final committed tree therefore contains only this
report; no `grammatik/` content was added or modified by this lane
(`git status` clean except this report).

## Open

Nothing open on this review. Integration (merge + maintainer extension of
`decodeLock`/`kapDecode`) is the coordinator's serial path, not this lane's.
