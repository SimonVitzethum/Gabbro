# MUSE-REPORT-1280: Exact review of candidate 1279 (BSF/BSR/POPCNT/BSWAP)

CANDIDATE: 1279 cf407e527e7b4053af372175670d6875cc446890
VERDICT: ACCEPT

The candidate meets every checkable requirement: exact owned scope,
no forbidden tactics or new axioms (standard axioms only), accepted
evaluator lifted unchanged, refusals that really refuse, a
non-degenerate two-core witness with a memory-changing drain, silicon
facts matching the supplied SDM extract, honest CUTS with no
hardware-correspondence or W/GX claim. The general memory-row
decode/encode composition stays open with a documented, specific
tactic-budget obstruction; register rows are general and both
composition halves are proved, so this is a named gap, not a silent
weakening.

Clone `/home/simon/Dokumente/gabbro-muse/a1280`, branch `muse/1280`
(`.git/HEAD` reads `ref: refs/heads/muse/1280`; verified first, no mismatch).
Owned file: only this report. No Lean or Rust code added or changed by
this lane.

Review basis: the clone-local snapshot `.tmp/review/author-1279/`
(`SNAPSHOT.json`: author 1279, head
`cf407e527e7b4053af372175670d6875cc446890`, files
`MUSE-REPORT-1279.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/IntBitScan.lean`, clean true). The author clone
itself was not touched (HARD RULES 1). The full 1700-line candidate file,
the complete `PATCH.diff` (1845 lines), `MUSE-REPORT-1279.md`,
`BUILD-EVIDENCE.json` and `OWNER-TASK.md` were read; the cited SDM
extract (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`) and
every reused accepted definition were checked in this clone's tree.

## Scope

Exactly the three owned files: new `MUSE-REPORT-1279.md` (124 lines),
one added line `import Grammatik.X86.IntBitScan` in
`grammatik/Grammatik.lean` (`PATCH.diff` lines 131-139), new
`grammatik/Grammatik/X86/IntBitScan.lean` (1700 lines). No other existing
file is touched. `IntBitScan.lean` is absent from this clone's working
tree, so there is no overlap with the accepted `BitScan`/`BitCount`/
`ByteSwap` modules.

## Checks

- Forbidden tactics/axioms: text search over the whole candidate file
  finds no `sorry`, `admit` (tactic), `axiom` declaration,
  `native_decide`, `unsafe`, `sorryAx`, `split_ifs`, `norm_num`,
  `ring_nf`, `intro _` or `have _ :=`. The only matches for the
  admit-substring are English prose ("admitted"/"admits" in comments).
  The single `intro c f _` (`bsHwWitStart_wf`,
  `IntBitScan.lean:1395`) discards a proof hypothesis (an equation) and
  mirrors the accepted file's own idiom (`hwWf_aus_zugelassen`,
  `HardwareExecution.lean:99`). No premise has type `Prop` itself.
- Axioms: `BUILD-EVIDENCE.json` records all `#print axioms` outputs
  within `propext`/`Classical.choice`/`Quot.sound` (several strictly
  smaller; `scanProfilUrteil`/`istVerzoegertScan` axiom-free). No new
  axioms. `gabbro_ziel` files untouched; the additive import cannot move
  its axioms (merge gate re-checks).
- Premises used: spot-checked `modrmMitDst_id` (uses `hfeld` via the
  closing `omega`), `bsParseModrm_mem_ok` (`hmod`/`hsib`/`hlen`),
  `bs_ohne_merkmal_kein_ok` (`h`/`hok`/`hq`/`hstep`, `subst z`),
  `adapterBitScan_proj` (all five), the `profil_urteilt_*` family.
  No conclusion restates a premise; no contract parameter is quantified
  away; memory claims go through the register/TSO vocabulary.
- Evaluator lifted, not copied: every value law is a one-line
  application of an accepted lemma whose name and signature I verified
  in this tree (`bsfIdx`/`bsrIdx`/`scanZF`/`bitGesetzt`,
  `bsfIdx_schranke/bit/min`, `bsrIdx_schranke/bit/max` in
  `BitScan.lean`; `popCount`/`popWort`, `popCount_schranke`,
  `popCount_wort_schranke`, single-field `PopcntMerkmal.popcnt` in
  `BitCount.lean`; `bswap32`/`bswap64`, `bswap32_zeroExt`,
  `bswap32_invol_bounded`, `bswap64_invol` in `ByteSwap.lean`;
  `mergeRegNarrow`, `nimmBytes`-adjacent `narrowTruncMod`,
  `HwMaschine`/`HwWf`/`HwAdapter`/`projZustand`/`setKernVonFp`/
  `setKernDaten_wf`/`HwRegAusgang`, `decodeExt`/`extLen`/
  `pin_ext_pilot_ret`, `issueByte`/`loadByte`/`flushKern`,
  `laengeOk`/`ripNach`/`regSet`/`regSet_gleich`, `codeReg`/
  `regHigh`/`regLow`/`regLow_lt`, `zeugeSpeicher`/`zeugeFlags`/
  `basisHw`/`basisBereit`/`kontextReset`). New definitions
  (`bsScanNach`, `bsSchritt`, `adapterBitScan`, `bsHwRegSchritt`)
  are built directly on these plus the accepted narrow merge.
- Refusals really refuse: 16 kernel-checked `bs_nichts_*` decode
  equations (`decide`), plus dispatcher-level `bsHw_nichts_lock`/
  `bsHw_nichts_tzcnt`, plus feature (`bs_popcnt_verweigert`,
  `bs_ohne_merkmal_kein_ok`), length (`bs_laenge_misslungen`) and
  memory (`bs_bsf/bsr/popcnt_mem_misslungen`) theorems. `decide`
  closes only if the computed value is really `none`. 9
  `ext_weist_*` pins (7 family rows + LOCK + TZCNT shapes) prove the
  unified chain refuses every new byte string; three dispatcher
  selection theorems are exact.
- Witness non-degenerate: `bsHw_zeuge`
  (`IntBitScan.lean:1570-1602`) joins scan on core 0 (index 4, ZF
  clear), count on core 1 (8, ZF clear), in-place swap (flags kept),
  owner-only forwarding of byte 42, a drain changing actual shared
  memory 0 to 42, zero-source preservation (sentinel `0xAB`, ZF set)
  and feature/length/memory/decode refusals. Two cores, a
  memory-changing step, owner-only forwarding: meets the task's
  witness bar for a register-path family (memory sources are refused
  by design; the two-core memory interaction is shown through the
  TSO vocabulary, as in the `HwMulDivWidth` model).
- Silicon against the supplied SDM extract: BSF 0F BC / BSR 0F BD /
  POPCNT F3 0F B8 / BSWAP 0F C8+rd opcodes correct; ModRM:reg
  destination and REX.W/R handling correct; zero-source destination
  UNMODIFIED (extract ll. 42739, 42822) with the older-processor
  footnote named in CUTS; BSF/BSR flag row ZF=source-zero,
  PF=whole-word-popcount parity, rest cleared (extract ll.
  42755-42758, 42837-42840) including the defined-PF correction;
  POPCNT all-cleared with ZF=SRC-zero plus CPUID.01H:ECX.POPCNT[23]
  and LOCK #UD (extract ll. 83613-83627); BSWAP flags none, LOCK #UD,
  16-bit undefined so refused (extract ll. 42904, 42933-42937);
  F3-on-scan decoded as deferred TZCNT/LZCNT with a profile rule that
  never executes here. REX-before-66H accepted, REX-after-66H refused
  (conservative). No silicon fact contradicted.
- CUTS honest (`IntBitScan.lean:1604-1676`): no hardware
  correspondence, no W/GX, no timing, no source/IR/loader/entry/budget
  link claimed. Open items named with specific obstructions (general
  memory-row decode/encode composition exceeds the tactic budget at
  `whnf`, halves proved generally plus kernel-checked pins;
  TZCNT/LZCNT deferred; memory execution/SIB/REX.X/mem-REX.B open;
  POPCNT ZF-vs-count-zero equivalence inherited open from
  `BitCount`). The claim is not larger than the proof.
- Build evidence: `BUILD-EVIDENCE.json` last entries:
  `./lean-probe grammatik/Grammatik/X86/IntBitScan.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (including all
  `#print axioms` outputs); `./lean-bau`:
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (659 jobs).` Only read-only git
  commands intervene between that build and the final commit
  `cf407e52`, so the built tree is the committed tree.

## Notes (not blocking)

- Report counts are off by one: 21 `#print axioms` lines
  (`IntBitScan.lean:1678-1698`), not 22; 16 `bs_nichts_*` decode
  refusals, not 17. `popNull` is named as lifted (header, CUTS) but
  never referenced in code; only `popCount`/`popWort` and the
  `PopcntMerkmal` gate are actually reused.
- Reviewer build: `./lean-bau` re-run in this review clone
  (report-only lane, no Lean code touched):
  `Build completed successfully (676 jobs).` Green; the review tree
  itself builds. The candidate file is not part of this tree (it lives
  only in the snapshot), so this confirms the lane adds no breakage;
  candidate build status rests on the author's recorded green build
  above plus snapshot `clean: true`, and the merge gate rebuilds
  `grammatik/` mechanically before committing.

Machine-readable verdict and reasons are at the top of this report.
