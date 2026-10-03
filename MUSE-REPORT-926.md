# MUSE-REPORT-926: Exact review of author 776 (LOCK CMPXCHG success path)

Lane 926, clone `/home/simon/Dokumente/gabbro-muse/a926`, branch `muse/926`
(verified: HEAD `56537272a31df3de5d9b7898bbade91c3de817b8`, equals the
snapshot base). Owned file only: `MUSE-REPORT-926.md`. No source touched,
no live controls used.

CANDIDATE: 776 450f855d2da2325be138b6e933e2c3f796c87654
VERDICT: ACCEPT (bounded: exactly the success-path connection as stated in its CUTS)

## What was reviewed

Exact pinned snapshot from `.tmp/review/SNAPSHOT.json`: base `56537272`,
head `450f855d`, files `MUSE-REPORT-776.md`,
`grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/LockCmpxchgSuccess.lean` (new, 310 lines).
Supporting material: `.tmp/review/author-776/OWNER-TASK.md`,
`MUSE-REPORT-776.md`, `PATCH.diff` (confirms the 3-file scope: no
source/checker/Spec/goal/emitter edits, no new numbers, no MARKE changes),
`BUILD-EVIDENCE.json` (11 commands), plus the accepted base modules in this
clone (`LockedOps.lean`, `LockedInstructionExecution.lean`, `Wort.lean`,
`Speicher.lean`, `Ausfuehrung.lean`) and the local manual snapshot
(`intel-instruction-reference.txt`, SDM 325462-093US Sep 2026).

## Architecture verification (manual-grounded)

- Byte forms: `pinCmpxchg` = F0 48 0F B1 8D 00 00 00 00, i.e. LOCK +
  REX.W + 0F B1 with ModRM 0x8D (mod=2 base-plus-disp32, reg=001=rcx,
  rm=101=rbp), length 9, 6 trailing bytes of the 15-byte fetch window.
  Matches the manual `REX.W + 0F B1/r CMPXCHG r/m64, r64, MR`
  (txt l.46979-46981; operand encoding `ModRM:r/m (r,w)`,
  `ModRM:reg (r)`, l.46989-46991). Only this row is claimed; 8/16/32-bit
  rows and CMPXCHG8B/16B stay explicitly open. Correct and bounded.
- Operands: destination `[rbp+0]` read/write, source `rcx`, implicit
  comparator `rax` — all pinned as premises (`hrd`, `hsrc`, `hgleich`,
  `hwr` with the `hsrc` rewrite to `hwr2`). Conclusion keeps RAX untouched
  and installs the source word, exactly the manual success leg
  (`IF accumulator = TEMP: ZF := 1; DEST := SRC`, txt l.47010-47014).
- Flags: `(sub64 dest rax).2` with `dest == rax`, so ZF set and
  CF/PF/AF/SF/OF per the comparison — matches "Flags Affected"
  (txt l.47023-47025). CMPXCHG defines all status flags via the comparison;
  no undefined flag is invented or zeroed (`sub64` carries defined AF).
- LOCK/faults: LOCK-on-register-dest is the accepted `#UD` shape in the
  base module (reused, not redefined); `#GP/#SS/#PF/#AC` paths are gated by
  the premises (`read64`/`write64`/`lesbar8`/execute window), never taken.
  Misalignment refuses as selected-profile contract (`ausgerichtet8`),
  explicitly "never as a hardware fault" — silicon #GP/#AC behaviour is not
  claimed. Sound abstraction, honestly bounded.
- Memory order/TSO: the outcome reuses the accepted
  `lockSchrittVoll_cmpxchg_erfolg` equation through the fetched dispatcher
  (`lockByteschritt_weiter`): one RMW event, read footprint = write
  footprint = full word `Fuss tgt`, own buffer empty before and after,
  `neuestens = none`, direct canonical-memory operation, preserved
  permission maps, frame outside the footprint, exact read-back. The fence
  claim is correctly local (other cores untouched, cf. accepted `zeugZaun`).
- W mapping: discharged as projection onto exactly one accepted
  `casSchritt` success (`lockVoll_cmpxchg_erfolg_adapter`), i.e. the unit
  the W `rmw` field consumes — not a constructed `SchrittW`. The report and
  CUTS disclose this; building the lowering here would duplicate the
  bridge owners' explicitly OPEN work. Accepted as the agreed interface
  level, not a defect. The failure-path write-back mismatch stays resolved
  in the base module, untouched here.

## Proof-hygiene verification

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: grep over the new
  file finds only English-word false positives ("admits", "admitted").
  `#print axioms` (build evidence) is at most `[propext, Quot.sound]`, a
  subset of the `gabbro_ziel` standard.
- Every premise of `LockCmpxchgSuccess_verbindung` is used: `hf` routes the
  fetched step, `hbuf`/`hali`/`hrd`/`hgleich`/`hsrc`/`hok`/`hwr` feed the
  accepted success equation, `hwr`+`hles` give permissions/read-back/frame,
  `hsrc` rewrites the adapter write. No `intro _`, no discarded premise,
  no conclusion restating a premise, no `Prop`-typed premise.
- `cmpxchg_erfolg_ohne_schatten` (common-dispatcher-first, no shadowing) and
  `cmpxchg_erfolg_kein_split` (via accepted `rmw_nur_mit_lock`) are genuine
  thin lemmas over accepted vocabulary, not desired-correctness premises.
- Witness `LockCmpxchgSuccess_verbindung_zeuge` is joint and non-degenerate:
  real fetched bytes (`lockFetch_zeugCmpxchgOk`, length 9), word 10 at 8192,
  `rax` 10, `rcx` 7, empty own buffer, memory observably 10 -> 7 with
  `ev.istRmw = true`. Three `decide` refusal pins (pending own store,
  misaligned 8193, truncated `F0 48 0F` prefix) are real negative mutations.
- CUTS block is precise: no W/GX refinement, failure path untouched, 64-bit
  word row + mod=2 addressing only, alignment as profile contract, no
  timing/progress/retry claims, no source/checker/goal change.

## Bounded acceptance

ACCEPT covers exactly: the LOCK CMPXCHG 64-bit success case as the single
fetched RMW access with local barrier shape and single-`casSchritt`
projection, plus routing/no-split lemmas, the joint memory-changing witness,
and the three refusal pins. Everything else (W/GX lowering, failure path,
other widths/addressing, misaligned-silicon behaviour, timing) remains OPEN
per the file's own CUTS. No repairs required; no guarantee weakened; no fake
closure found.

## Status notes

- Report-only lane: no Lean/Rust file touched, so no `./lean-bau` /
  `./cargo-pruef` run was applicable and none was made; the candidate's own
  evidence (`lean-probe` 0 errors, `lean-bau` green over 485 jobs after
  documented virtual-address flakes on the aggregator) was inspected but not
  re-executed here — the merge gate rebuilds anyway. No suspicious case
  surfaced that needed reproduction.
- Nothing in the owner task text is believed wrong. One scoping remark: the
  task phrase "mapping to the W rmw field" is satisfied at projection level;
  this matches the accepted adapter pattern and the bridge's OPEN ownership,
  and is disclosed — accepted, not a finding.
