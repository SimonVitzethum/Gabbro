# MUSE-REPORT-1282: exact review of the sign-extend/XCHG family candidate

CANDIDATE: 1281 5f0ac54a14bc53590dad8475c47b52be28b51fab
VERDICT: REPAIR

## Materials and procedure

Clone `/home/simon/Dokumente/gabbro-muse/a1282`, branch `muse/1282`, verified.
Reviewed the pinned snapshot only (`.tmp/review/SNAPSHOT.json`: head as in the
candidate line above, base `738366545afbddf7ac664db92804703db24f8868`,
`clean: true`): `PATCH.diff` (3 files), the full new file
`grammatik/Grammatik/X86/IntSignXchg.lean` (1621 lines, read end to end),
`MUSE-REPORT-1281.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`.
An earlier turn recorded BLOCKED for lack of a pinned snapshot; that status is
superseded by this review. No verdict was given before this report.
Own tree `grammatik/` is untouched by this lane; `./lean-bau` on the clean tree:
`Build completed successfully (672 jobs).`
Cross-checked accepted-helper semantics (`sext`, `negB`, `trunc`,
`mergeRegNarrow`, `ext_weist_wdvor98/99_zurueck`) against this clone's tree;
silicon rows checked against the supplied `.tmp/HARDWARE-REFERENCES/` extract.
Reviewer added no definitions or theorems.

## Checks that pass

- Forbidden tokens: grep over the snapshot file is clean (no `sorry`, `admit`,
  `axiom` declarations, `native_decide`, `unsafe`, `intro _`, `have _ :=`,
  `split_ifs`, `norm_num`, `ring_nf`; the only hits are English "admit*" in
  comments). 19 `#print axioms` lines present; build evidence shows
  `propext`-only or `propext + Quot.sound` for every main theorem: a subset of
  the standard goal axioms.
- File discipline: the diff touches exactly the three owned files; the
  `Grammatik.lean` hunk is a single appended import line. No accepted file is
  edited.
- Premise use: spot-checked `sx_cwde/cdqe/cdq/cqo_ist_vor98/99`,
  `sxXchgSchritt_bei_a_neq` (uses `hne`), `sxXchg64_ist_reg` (all of
  `a c s t n q` used), the `wdVor98/99_flags/memory` lemmas, the three
  dispatcher-agreement theorems and all selection theorems. Every premise is
  consumed by its proof.
- Lift, don't redefine: CWDE/CDQE/CDQ/CQO arms ARE the accepted `wdSchritt`
  arms on the same length, with four `cases <;> simp` agreement theorems; the
  64-bit register exchange IS the accepted `XchgForm.reg` swap
  (`sxXchg64_ist_reg`, plus `pin_xchgAkzeptiert_dekode` pinning shared bytes in
  the accepted decoder). A grep for redefinitions of accepted names
  (`wdSchritt`, `xchgSchritt`, `decodeXchg`, `decodeExt`, `stepExt`,
  `mergeRegNarrow`, `sext`, `HwAdapter`, …) is empty; the author renamed their
  own `xchgSchritt` to `sxXchgSchritt` after the build caught the collision.
- Refusals refuse: 9 planted `decide` pins (LOCK on 90/98, 86/87 memory ModRM,
  MOVSXD without REX.W, three `66`+REX.W combinations, truncated 87), generic
  memory-ModRM theorems covering every failing `mod` value, a generic LOCK
  theorem over the accepted prefix parse, and the 9-row `sxGrundTabelle` with
  its checked `sxTabelle_verweigert`. The build evidence shows intermediate
  failing pins (wrong REX.R/B rows, truncation, recursion depth) fixed before
  the final green `lean-bau` (659 jobs), i.e. the pins were genuinely exercised.
- No shadowing: 16 `decodeExt … = none` rows for the new bytes, plus reuse of
  the accepted `ext_weist_wdvor98/99` rows (verified present in
  `HwMulDivWidth.lean`); the dispatcher tries the unified chain first with
  prefer/sx/nothing agreement theorems, a pilot pin and 6 family-arm pins.
- Round-trips: 15 generic `cases … <;> rfl` round-trips with suffix plus 3
  encoder pins; the encoder reuses accepted `wdRex`/`codeReg`/`modrmReg`.
- Machine connection: an `HwAdapter SxDecodiert` plug preserving `HwWf` via the
  accepted `setKernDaten_wf`, exact agreement and projection theorems, reuse of
  the accepted `HwRegAusgang`, and a provably dead halt arm
  (`sxSchritt_kein_halt`; no divide and no memory access on admitted forms).
- Witness: `sxHw_zeuge` joins 12 conjuncts — CBW on core 0, exchange and MOVSXD
  on core 1, owner-only forwarding, a drain changing shared memory 0 to 42,
  well-formedness, bad-length refusal and LOCK refusal. Non-degenerate under
  the lane's own bar (two cores, memory-changing step).
- CUTS: present and honest about scope (self-consistency only, no silicon
  proof, no W/GX bridge, no timing, documented over-refusals, no
  source/loader/entry/budget link).
- Silicon spot-checks that pass: opcodes 98/99/90+r/86/87/63 with correct
  prefix bytes; CBW/CWDE/CDQE/CWD/CDQ/CQO value semantics against the canonical
  `sext`/`negB`/`mergeRegNarrow` (verified definitions, not just pins); bare-90
  NOP; LOCK refusal (extract: `#UD` if LOCK is used); XCHG-memory refusal with
  the implicit-LOCK rule left to the locked families (extract confirms
  automatic locking); flags-None everywhere; genuine 87-form 32-bit
  self-exchange zero-extends on both sides exactly as a true exchange does;
  MOVSXD requires REX.W in 64-bit mode.

## The defect: REX-prefixed 90H self-exchange mis-executes the NOP alias

The supplied extract states, in the XCHG NOTE, that `XCHG (E)AX, (E)AX` with
encoded instruction byte `90H` is an alias for NOP regardless of data-size
prefixes, including REX.W; its NOP table lists `66 90H` as the recommended
2-byte NOP. The candidate instead decodes REX-without-W-prefixed `90` with no
B extension (bytes 40/42/44/46 followed by 90) to `.xchgRax32 .rax`, whose step
zero-extends EAX into RAX and clears RAX bits 63:32. Concrete divergence: with
RAX holding `0x1122334455667788`, silicon leaves RAX unchanged while the
candidate's step yields `0x0000000055667788`. The behavior is pinned as intended
(`pin_sx4090_dekode`, the encoder pin, the round-trip), so this is a wrong
definition with green proofs, not a proof-shape issue. Two nearby rows are
behaviorally harmless but mislabeled against the same NOTE (`66 90` as a
16-bit self-exchange and `48 90` as a 64-bit self-exchange are both the
identity, hence observably NOP) and should collapse to `.nop` in the same edit;
that edit also converts the currently refused-but-valid `4C/4D 90` and
`66`+REX.W `90` rows into correct NOPs. The CUTS silicon list never cites the
NOP-alias NOTE, and there is no `decodeExt = none` row for the `[64, 144]`
bytes the family claims.

## Concrete repair demand

Route every `90H` encoding that resolves to the rax self (all prefix
combinations, including the 40/42/44/46 and REX.W rows) to `.nop`; never emit a
zero-extending event from a `90H` byte. Keep the genuine 32-bit self-exchange
reachable only through `87 C0` (or document its removal), and update the
encoder, the affected pins and round-trips, the CUTS block (cite the NOP-alias
NOTE and re-audit the over-refusal list), and the no-shadow rows so every
claimed byte string is covered. Re-establish a green full build with unchanged
standard axioms.

## Open and task notes

The author's declared SDM limitation stands for rows beyond XCHG/NOP; those
two sections were checked from the supplied text extract here. The owner task's
"90 alone is NOP" under-specifies prefixed 90H; future family tasks should cite
the alias NOTE directly. The redundant-REX encoding knowledge in the author
report (kernel depth, `simp` continuations) is useful apparatus detail.
