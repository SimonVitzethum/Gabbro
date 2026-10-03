# MUSE-REPORT-1099: exact review of planner candidate 1098

Lane 1099, clone `/home/simon/Dokumente/gabbro-muse/a1099`, branch `muse/1099`.
Report-only review: no Lean, Rust, instrument, or docs file touched, so
`./lean-bau` state is unchanged (nothing to re-run for this lane; no `_zeuge`
obligation arises — no theorems added).

CANDIDATE: 1098, pinned HEAD `69e016835d6f7abf118aea62eeee8afbc69d7bcc`
(resolved from `.tmp/review/SNAPSHOT.json`; the LANE.md task names the lane
but not the hash), base `03491267`, files `MUSE-REPORT-1098.md` +
`dokumente/x86/ARBEITSPLAN-AKTUELL.md`, snapshot `clean: true`.
The reviewed bytes are `.tmp/review/author-1098/PATCH.diff` (531 lines);
the report inside it is identical to `MUSE-REPORT-1098.md` there.

## 1. What I verified (all inside this clone, read-only)

- Snapshot integrity: PATCH adds exactly the two owned files, both
  docs-only. No source/private/root/network surface.
- Collision check: none of the six proposed modules
  (`AuxiliaryCarryRows`, `DeviceCommonExecution`,
  `ComposeAcceptedConsumers`, `IntegerAccessFootprints`,
  `ScalarFloat32FetchedSteps`, `VectorIntegerFetchedSteps`) exists under
  `grammatik/Grammatik/X86/`. No overlap with merged work.
- Dependency existence: every accepted module the proposals depend on
  exists — `ConcurrentIntegerExecution`, `ArchitecturalFlags`,
  `IntegerHardwareForms`, `HardwareExecution`,
  `DeviceBusHardwareExecution`, `MemoryTypeHardwareExecution`,
  `InterruptDescriptorHardware`, `ComposeDecodeExec`,
  `AddressedHardwareExecution`, `ExceptionPriorityHardware`,
  `ScalarFloat32HardwareForms`, `ScalarFloatHardwareForms`,
  `FpControlHardwareForms`, `VectorIntegerHardwareForms`,
  `WordAccessGrouping`, `WordAtomicity`, `TSOHistory`,
  `VectorFootprints`, `ExtendedExecution`.
- Acceptance evidence: `DIRECT-COMPILER.md` records integration of 660
  (line 1073), 704 (1110), 730 (1183), 720 (1187), 728 (1190), 738 (1192),
  824 (1196), and gate rejections of 698/718/722 (1122–1124) plus 752/757
  (1139/1144) — all inside the cited 1050–1198 window. Old lane files
  (650/651/660/…) are absent, consistent with post-merge cleanup; the
  candidate's present-means-registered reading method is stated openly.
- Technical references spot-checked real: `intHwFlagsLogik` /
  `inthw_logik_af_none` (`IntegerHardwareForms.lean:58/68`);
  `vecShlQ_satt_vs_maske` (`VectorIntegerHardwareForms.lean:226`, saturate
  statement as cited); `s32Rechne` kernel routing via
  `Gleitprofil.fadd32/fsub32/fmul32/fdiv32` plus CVTSD2SS narrowing
  (`ScalarFloat32HardwareForms.lean:156-179, 240-292, 567, 1811` region);
  `af : Option Bool` (`Typen.lean:30`); PR-1 `MUST-FIX: none found`
  (`UPSTREAM-PR-1-OPTIMIZER-REVIEW.md:79`); PR-2 `REJECT as-is` with §8
  MUST-FIX (`UPSTREAM-PR-2-ISA-REVIEW.md:12-14,296`); 740/742 repair
  authors with 741/743 as their exact reviewers (lanes read); 752/757/
  759–768 lane files absent; 672 owns `HardwareInterrupts.lean` (held),
  673/684/685 untouched by every proposal; friend-reserved optimiser
  files untouched; slot budget 6 authors + 6 reviewers = 12 of 15 with 6
  within the at-most-8 limit.
- No fake closure: full source-to-final-bytes validation stays OPEN in
  every proposal; fiat values, weakened consumers, second executors,
  desired-simulation premises and 744-API assumptions are all explicitly
  forbidden; pending extensions, CUTS, joint non-degenerate `_zeuge` and
  planted refusal probes are required per author with full paired review
  texts and no lane numbers. No unsupported desired-correctness premise
  and no weakened guarantee found.

## 2. Defects found

- D1 (factual, in register-ready text): proposal F anchors both its task
  text and its review text on "the eight accepted decoder families named
  in `lanes/718.md`". That file contains no such enumeration: line 21
  lists NINE producer modules to read (ExtendedExecution575,
  IntegerHardwareForms666, ScalarFloatHardwareForms668,
  LockedInstructionExecution662, IndirectControlHardwareForms680,
  FpControlHardwareForms682, CpuFeatureHardwareForms688,
  ArchitecturalFlags692, MemoryTypeHardwareExecution694) plus
  "pilot/extended byte families". The count "eight" is not verifiable
  from the cited file, so author and paired reviewer would share an
  unanchored inventory and the reviewer's "covers the eight 718
  families" check is not executable as written.
- D2 (staleness): the candidate base `03491267` (merge 974) is one merge
  behind this clone's tip `b040b155` (merge 975). The candidate already
  demands a live-registry re-check at registration; the rebase delta must
  be included in it.

Not defects: the live registry (`manifest.json`, `state/`, dispatch,
watch, B01–B11 lists, PIDs) is not visible from any clone, so
de-duplication against live holds/queues cannot be closed by this
review. The candidate states this limitation twice and gates
registration on a live re-check. That gate is mandatory, not optional.

## 3. Verdict

VERDICT: REPAIR

Precise repair list (mechanical, one planner turn, no rescope):

1. Proposal F: replace "the eight accepted decoder families named in
   `lanes/718.md`" in BOTH the task text and the review text with the
   exact verifiable inventory (list the producer decoder families from
   `lanes/718.md:21` by name, or verify-and-pin the intended count of
   eight against the file and cite where each family is named). The
   reviewer's coverage check must reference the same corrected list.
2. Re-pin the proposal to current master tip (re-verify §1 disjointness
   against the 975 delta) and keep the existing live-registry re-check
   gate at registration (holds 672/673 + 684/685, B01–B11, worker
   identities, 698/718/722 repair and 744/745 landing state).

## 4. What remains open / notes for the coordinator

- After the two repairs above, no further review cycle is needed from
  this lane; the paired-reviewer gates then carry the per-author risk.
- `ArchitecturalFlags.lean:34-42` as cited in proposal A is the import
  block (`Ganzzahl`/`ShiftLogic`/…); the citation is usable as the
  helper-reuse anchor, no repair needed.
- Six authors each appending one import line to `grammatik/Grammatik.lean`
  must integrate serially at publication (candidate already notes this).
- Task oddity (not verdict-relevant): the LANE.md review task pins the
  candidate lane but not its hash; the hash had to be resolved from
  `.tmp/review/SNAPSHOT.json`. Future review tasks should carry the full
  pinned HEAD inline.

No Lean theorems added by this lane; `./lean-bau` not re-run (no build
inputs touched — review-only turn).
