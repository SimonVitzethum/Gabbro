# MUSE-REPORT-991: Exact review of author 841 (width-ledger closing)

CANDIDATE: 841 17f30511b8755d8990db508a9e09895bab941c7e
VERDICT: ACCEPT (bounded: exactly what the file's CUTS block states, no more)

## Clone/branch verification

- Clone `/home/simon/Dokumente/gabbro-muse/a991`, branch `muse/991`, clean tree at
  `b040b155`. Matches the lane task. No other clone touched; no network, no push.
- Pinned snapshot (`.tmp/review/SNAPSHOT.json`): author 841, head
  `17f30511b8755d8990db508a9e09895bab941c7e`, base `e7c75908`, clean, 3 files:
  `MUSE-REPORT-841.md`, `grammatik/Grammatik.lean` (one import line),
  `grammatik/Grammatik/X86/ComposeWidthLedger.lean` (341 lines, reviewed in full).
- PATCH.diff header matches the same file set. Scope discipline holds: no diagnostic,
  gift, example or CLI numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/
  emitter edits, no friend-reserved optimiser files.

## What the candidate does

New width-conversion ledger over the accepted narrow rows: `WidthConv`
(`zeroExt`/`signExt`/`truncTo`/`mergeTo` with explicit `Breite`, `unknown Nat`),
`convApply` (known rows reuse canonical `trunc`/`sext` and accepted
`mergeRegNarrow`; unknown rows answer `none`), `ledgerAdmitted`
(known `true`, unknown `false`), `convNeedsGuard` (unknown `true`, known `false`).
Exactness lemmas close every known row to its accepted lemma; TARGET theorem
`ComposeWidthLedger_verbindung` composes decoder coverage (`narrowDecktAb`) with
execution (`stepNarrow`) and the ledger over arbitrary admitted inputs; companion
`ComposeWidthLedger_verbindung_zeuge` is the joint witness.

## Independent verification (real evidence, not Lean-green alone)

- Forbidden constructs: word-boundary grep for
  `sorry|admit|axiom|native_decide|unsafe` over the candidate file: zero matches
  (only English words "admitted"/"admission"). No `intro _` / `have _ :=` discards.
- Producer existence and meaning, checked in my own clone by reading the sources:
  `narrowDecktAb` (`NarrowCodec.lean:268`) is exactly the 4-way disjunction
  (mov32rr/3, movzx8/4, movsx8/4, store32/7-or-8) that the candidate's `rcases`
  dispatches — full coverage, no silent narrowing. `stepNarrow_mov32_rahmen`,
  `stepNarrow_movzx8_rahmen`, `stepNarrow_movsx8_rahmen`,
  `stepNarrow_store_erfolg`, `stepNarrow_store_verweigert`, `narrow_store_witness`
  (`NarrowCodec.lean:683-878`, signatures read in full) and `mergeRegNarrow`,
  `mergeRegNarrow_b64/b32`, `extendNarrow`, `extendNarrow_zero/sign`,
  `storeNarrow_success/refused` (`NarrowOps.lean`) all exist with the exact
  statements the candidate claims.
- Reproduced through queued wrappers: `./lean-probe NarrowCodec.lean` → 0 errors;
  `./lean-probe NarrowOps.lean` → 0 errors; every reused lemma depends only on a
  subset of `[propext, Classical.choice, Quot.sound]`.
- Intel SDM (local `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  EFLAGS cross-reference Table A-2 — `MOV` row blank (no flags affected),
  `MOV control, debug, test` row `—`, `MOVSX/MOVZX` row with no set/modified
  entries — confirms the MOV flag discipline the frame lemmas state and the
  candidate reuses. 32-bit destination clearing the upper half and extension
  landing through extend-plus-merge match the accepted lemmas, which the
  candidate reuses by name rather than re-proving.
- Pin cross-check: candidate `pin_conv_sign` (`sext .b8 0x80 = 0xFFFFFFFFFFFFFF80`,
  full 64-bit sign extension) vs accepted `narrow_movsx_witness`
  (`0xFFFFFF80`, the 32-bit-merged register value). Both correct at their widths,
  and the connection theorem never equates the register with the raw `sext` — it
  states register = `mergeRegNarrow .b32 dst (extendNarrow …)`, with the source
  conversion exactness as a separate conjunct. No truncation lie, no confusion.
- Premise use: `hok`, `hdeck`, `hstep` all used in every branch of `verbindung`
  (coverage dispatch, frame lemmas, fault-contradiction leg). The conclusion is a
  genuine composition (coverage × execution frame × ledger exactness over arbitrary
  inputs), not a premise renamed; `convApply` is a pure ledger function reusing
  canonical operations, not a second executor/interpreter.
- Witness: `d = store32 rbx rax 0 / 7` on `narrowWitState` — length, coverage and
  step premises proved jointly; data cell 8192 goes `0 -> 4` (reached,
  memory-changing, non-degenerate); ledger truncation exact; unknown width
  valueless; both step refusals (`narrow_schritt_laenge_null`,
  `narrow_schritt_speicher_verweigert`) hold by their exact accepted statements.
- BUILD-EVIDENCE is honest: it shows red intermediate probes (an `Exists.intro`
  mismatch, a store-branch case split, one wrong pin literal `0xFFFFFF80` caught
  by `decide`) fixed before commit; final `./lean-probe` 0 errors,
  `./lean-bau` exit 0 with 509 jobs, all `#print axioms` within the standard
  `gabbro_ziel` set.
- Undefined hardware state is soundly abstracted: unknown widths answer `none`
  with refused admission and a loud guard — no invented determinism, no
  zeroing/ignoring of defined effects. This matches the accepted
  `SignKind.unknown` / `narrowGuard` discipline. Pre-fault effects: a failed
  `writeBreite` yields step `none` (no partial state). No TSO/atomicity,
  feature/MXCSR or interrupt-enable claims are made.

## What remains open (candidate's CUTS, accepted as bounded)

16-bit extension rows (refuse in NarrowCodec, lane 562), narrow loads, narrow ALU
flag snapshots (MOV discipline only), `Byteschritt` fetch wiring, TSO/GX bridge,
source correspondence, ABI/image/entry/relocation/cost claims, silicon
verification. Missing producer legs named with owners (lanes 562–566, 567–569,
570), none assumed. Claim boundary is precise.

## Anything in the task believed wrong

Nothing. The task's "unknown widths fall back loudly" is realised as
`none` + refused admission + loud guard rather than a default extension; that
reading is correct and consistent with `NarrowOps`.

## Review method

Report-only exact review. Owned file is this report alone; no source or live
controls touched. No unsupported desired-correctness premises, no weakened
guarantees, no fake closure found.
