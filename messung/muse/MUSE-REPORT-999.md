# MUSE-REPORT-999: Exact review of author 849 (unwind-table closing)

## Clone / branch verification

- Clone `/home/simon/Dokumente/gabbro-muse/a999`, branch `muse/999`: match.
- Snapshot base `b040b155159f47629542b0083e2f0a8a607f2b4c` equals this
  clone's HEAD; tree clean before review.
- Review sources (read-only, not applied): `.tmp/review/SNAPSHOT.json`,
  `.tmp/review/author-849/OWNER-TASK.md`, `PATCH.diff`,
  `grammatik/Grammatik/X86/ComposeUnwindTable.lean` (candidate file),
  `MUSE-REPORT-849.md`, `BUILD-EVIDENCE.json`, plus local reference
  manuals (Intel SDM 325462-093US snapshot) and the accepted base-tree
  modules `Stapel.lean`, `StackUnwind.lean`, `Speicher.lean`.

## CANDIDATE

CANDIDATE: 849 835bdb46175c2b31725f53c66e6c46e70ec0e0ec

Files: `MUSE-REPORT-849.md`, `grammatik/Grammatik.lean` (one import line
appended), new `grammatik/Grammatik/X86/ComposeUnwindTable.lean` (272 lines).

## VERDICT

VERDICT: ACCEPT

Acceptance is bounded; see scope notes below.

## What was checked

1. **Architecture, not just green.** The module closes one producer/consumer
   interface: unwind-table rows (`UnwindEintrag`: code range `start`/`len`,
   claimed depth `tiefe`, saved `slot`) describe; the checked frame-layout
   consumer (`Rahmen` extent, `Belegung` callee-save range, actual
   `Speicher` bytes) admits via decided `unwindPasst`. Admission conjuncts
   verified by hand: rip in `[start, start+len)` (empty rows never pass),
   `tiefe = r.tiefe`, `spill <= slot < spill + gerettet` (consistent with
   accepted `Belegung.gerettetIdx`), `slot < schlitzZahl`. Refusal precedes
   any memory touch (`unwindLese` branches on admission before `ladeWort`),
   so misdescribing rows have no pre-fault memory effect.
2. **No second interpreter/executor, no re-proofs.** The only consumer step
   is accepted `ladeWort`; the hit composes accepted
   `sichere_lade_rundreise`. No decoder, fetch, TSO, or source fact is
   assumed or re-proved.
3. **Proof mechanics.** `unwindPasst_schranke` projection index
   (`h.2.2.2.2.2`) lands on the frame-slot conjunct; all three refusal
   lemmas discharge exactly the conjunct they name (`hne` on depth,
   `Nat.not_lt.mpr hob` on the slot bound, both `haus` disjuncts via
   `omega` on the range). Every premise of every theorem is used; no
   `intro _`, no discarded hypothesis. No `sorry`/`admit`/`axiom`/
   `native_decide`/`unsafe` anywhere in the 272-line file; `decide` is used
   only on ground Bool goals.
4. **Target theorem is genuine, not a restatement.** `ComposeUnwindTable_verbindung`
   delivers both a hit through an actual save (`some v`) and a refusal of
   the same row with depth off by a full 16-byte slot pair (`r.tiefe + 16`,
   provably unequal by `omega`) — a real misdescription, not an impossible
   premise.
5. **Witness is joint and non-degenerate.** `ComposeUnwindTable_verbindung_zeuge`
   instantiates all premises together on `rahmenZeuge` (4 slots),
   `zeugenBelegung849` (two callee-save words), value 42 (`v != 0` by
   `decide`), shows the byte-level change (zero becomes 42 via
   `writeBytesN_hit` + `addrOff_null`, the exact accepted-Stapel idiom),
   and delivers hit plus planted refusal. Two further planted probes cover
   range (`0x2000` outside `[0x1000, 0x1010)`) and slot (9 of a 4-slot
   frame) refusals. Admission ground facts close by `decide`.
6. **Name cross-check against base.** Every reused name was confirmed present
   in this base tree with a matching shape: `Rahmen`/`schlitzZahl`/
   `schlitzAddr`, `Belegung` (`spill`/`gerettet`), `sichereWort`/`ladeWort`,
   `sichere_lade_rundreise`, `lesbar8`, `speicherZeuge`/`rahmenZeuge`,
   `zeuge_lesbar8`/`zeuge_schreibbar8`, `writeBytes`/`writeBytesN_hit`,
   `addrOff_null`, `read64_nach_write64`.
7. **Build evidence.** `BUILD-EVIDENCE.json` records 13 queued
   `./lean-probe` runs ending at 0 errors with the full axiom printout
   (every theorem within `[propext, Quot.sound]`), plus a 511-job
   `./lean-bau` green run. The log also shows one honest intermediate
   1-error state (unsolved goals at line 88) repaired before commit.
   The patch was NOT applied to this clone (report-only review owns no
   source), so acceptance rests on this evidence plus the hand checks above.
8. **Scope hygiene.** Only owned files touched; no diagnostic/gift/example/
   CLI numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits,
   no friend-reserved optimiser files. CUTS block is precise: no decoder/
   fetch/TSO bridge, no `.eh_frame` byte correspondence, single row and
   single frame (no cascade), `none` as transition absence (no termination
   claim), async/concurrency OPEN, owning lanes named generically.

## Bounded acceptance / follow-up (non-blocking)

- The file header lists `rahmenOk`, `Belegung.passt`, and `KetteOk` among the
  composed definitions, but the code never references them: admission does
  not require a checked frame or a fitting layout. Soundness is unaffected
  (every admitted read still returns a genuinely saved in-frame word, and
  the witness layout fits), but a follow-up should either admit under
  `rahmenOk`/`Belegung.passt` or correct the header list. Left as a note,
  not a repair demand.
- Byte-level hardware checklist items (REX/width/flags/MXCSR/interrupt
  gates) do not apply to this interface; the missing `.eh_frame` parse and
  multi-frame cascade are honestly OPEN in CUTS.

## What remains open

Nothing in lane 999's scope: the review is complete. The OPEN items above
belong to the codec/execution/bridge/validator-skeleton lanes behind
`decodeExt`, `schritt`/`extByteschritt`, the TSO bridge, and `valX86`.
