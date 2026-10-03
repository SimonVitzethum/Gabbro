# MUSE-REPORT-978: exact review of author 828 (stack-to-ABI closing)

CANDIDATE: 828 1e1d0bea34a29493694a3d4ab52508d3d4b30818
VERDICT: ACCEPT (bounded: one checked composition step as claimed; no wider closure granted)

## Scope of this review

Report-only exact review. Owned file: this report. No source, control,
network, or other-clone access. Inspected in-clone: pinned
`.tmp/review/author-828/` snapshot (`SNAPSHOT.json`, `OWNER-TASK.md`,
`MUSE-REPORT-828.md`, `BUILD-EVIDENCE.json`, `PATCH.diff` — 403 lines,
3 files), the candidate Lean file at its snapshot path, every consumed
producer definition/theorem in the base tree at the snapshot base, and
the official local Intel instruction reference
(`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`).

## Base / identity checks

- Clone `/home/simon/Dokumente/gabbro-muse/a978`, branch `muse/978`: match.
- `git rev-parse HEAD` = `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4` =
  snapshot `base`. Exact base match.
- Patch file list is exactly `MUSE-REPORT-828.md`,
  `grammatik/Grammatik.lean` (one appended import), and new
  `grammatik/Grammatik/X86/ComposeStackAbi.lean` (294 lines; snapshot
  copy is 294 lines). No Spec/goal/checker/emitter/diagnostic/gift/
  example/CLI/MARKE_EMIT/optimiser content anywhere in the patch.
- `Grammatik.lean` tail in base ends with
  `import Grammatik.X86.ExceptionPriorityHardware`, matching the patch
  context; the appended import cannot conflict.
- Grep over the candidate Lean content: no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe` (only hits are the HARD-RULES/task prose).

## Reproduced evidence (independent, queued wrappers only)

- `./lean-probe .tmp/review/author-828/grammatik/Grammatik/X86/ComposeStackAbi.lean`
  (exact snapshot content, imports resolving against the base tree):
  `== 0 error(s) in the COMPLETE output; exit 0`, with axioms
  `rotZoneImRahmen`/sondes/`abi_slot_verweigert`: none;
  `ComposeStackAbi_verbindung`, `_zeuge`,
  `abi_fehlalign_verweigert`: `[propext, Quot.sound]` — identical to
  the author's claimed axiom lines. All are subsets of the standard
  `gabbro_ziel` set.
- `./lean-bau` on the unmodified base: `== exit 0; 0 error line(s)`,
  `Build completed successfully (508 jobs)` (509 with the candidate
  module, per author evidence). Base green confirmed.
- Every producer call shape was checked against its definition:
  `push_pop_wiederhergestellt` (StackUnwind.lean:46),
  `belegung_gerettet_schranke` (:407),
  `sichere_lade_rundreise` (Stapel.lean:92),
  `sichereWort_ausserhalb` (Stapel.lean:104),
  `schritt_push64_erfolg` / `schritt_pop64_reg`
  (Ausfuehrung.lean:301/:331), `callGeprueft_fehlalign`
  (CallAlign16.lean:101), `lauf` (Ausfuehrung.lean:741),
  `writeBytesN_hit` / `addrOff_null` (Speicher.lean:115/:70),
  `rufAlignOk` (CallAlign16.lean:40), `rspImRahmen`
  (StackUnwind.lean:30), witness family `zeugS`/`zeugS1`/`zeugS2`/
  `zeugM1`/`zeugSpeicherRW`/`zeugOben`/`zeug_push_schreibt`/
  `zeugOben_lesbar`/`zeug_push_liest` (StackUnwind.lean:370-453).
  All argument orders and implicit/explicit binders match; no
  re-proof or duplicated executor exists in the candidate.

## Architecture checks (beyond Lean green)

- Byte forms / decoder: candidate adds no decoder row and no byte form;
  nothing to fault. Execution facts come only from the accepted
  `schritt`/`lauf`.
- Hardware order vs Intel reference: PUSH "Decrements the stack pointer
  and then stores the source operand on the top of the stack"
  (:89704); POP "Loads the value from the top of the stack ... and
  then increments the stack pointer" (:83282). The reused model
  (`schrittPush` sets rsp to `rsp-8` with the stored memory;
  `schrittPopReg` loads then advances past the word) follows the same
  order. No pre-fault-effect claim is made; fault ordering stays with
  the producers, correctly unclaimed here.
- Register/width/flag semantics: no new register, width, REX, or flag
  claim. `hdst : dst ≠ rsp` correctly excludes the `pop`-into-`rsp`
  (`schrittPopTop`) shape, so the unwind producer applies soundly.
- The bridging premise `hslot` (frame slot address = word below the
  top) is an equation between two accepted-definition terms over the
  same state and memory — the stated producer/consumer interface, not
  a desired hardware-correctness assumption — and it is discharged by
  `decide` on the shared witness (`abi_slot_unten`: slot 19 =
  8032+152 = 8184 = 8192-8). The generic theorem quantifies over all
  states satisfying it; the witness proves joint satisfiability. No
  fake closure.
- All 15 premises of `ComposeStackAbi_verbindung` are consumed by the
  proof (fit/position feed the slot bound; `hslot` bridges both
  stores; save/readability feed both round-trips; step premises feed
  the unwind; alignment/red-zone feed the transfers). No `Prop`-typed
  premise, no `intro _` / `have _`, conclusion is a 7-conjunct
  composition result, not a renamed premise.
- Witness is non-degenerate as the task requires: observable memory
  change (zero becomes 42 at the slot, proved via `writeBytesN_hit` +
  `addrOff_null`) and a reached 2-step `lauf [push, pop]` run to
  `zeugS2`. The source-syntax table clause of HARD RULE 13 does not
  apply to this machine-state theorem; the author states this honestly.
- Negative mutations are genuine: `abi_slot_verweigert` (slot 20 of a
  20-slot frame saves `none`) and `abi_fehlalign_verweigert`
  (misaligned `call32` gate refuses via the accepted refusal theorem).
- Red-zone honesty: the checked rule is in-frame containment of the
  128 bytes below rsp; System V leaf/async-signal clobber semantics,
  TSO/store-buffer/GX, source correspondence, and
  loader/entry/relocation/cost/final-image are all explicitly OPEN in
  CUTS, with the call/ret leg left to `CallAlign16_verbindung` and the
  fetched nested leg to lane 569 by name. The claim boundary is
  exactly as narrow as proved — this is why the verdict is bounded
  ACCEPT rather than a whole-call closure.

## What remains open (not a defect)

Whole-call theorem folding all three legs, TSO/GX bridge, source
correspondence, red-zone clobber semantics, loader/entry/relocation/
cost/image acceptance — all listed in CUTS and untouched by this
candidate.

## Believed-wrong items in the task

None. The target `ComposeStackAbi_verbindung` + `_zeuge` was provable
as stated within the owned files.
