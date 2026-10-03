# MUSE-REPORT-898: Exact review of author 748 (compact ADD with imm8)

Lane 898, clone `/home/simon/Dokumente/gabbro-muse/a898`, branch `muse/898` (verified).
Review-only lane. Own file: `MUSE-REPORT-898.md`. No source or live-control changes.

## Machine-readable result

CANDIDATE: 748 f50afecfd56929253ff917effd621c4ec0910322
VERDICT: ACCEPT

Bounded acceptance: exactly the `REX.W + 83 /0 ib` register-direct
ADD r64, imm8 row; see boundaries below. Substantive verdict unchanged.

## What was reviewed

Exact pinned snapshot from `.tmp/review/SNAPSHOT.json` (base
`23b9a42fb44f2365b636cf8a9c440a2dfd8cae50`, files `MUSE-REPORT-748.md`,
`grammatik/Grammatik.lean` one import line, `grammatik/Grammatik/X86/CompactImm8Add.lean`,
`clean: true`), with `.tmp/review/author-748/OWNER-TASK.md`,
`MUSE-REPORT-748.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`, the snapshot copy
of `CompactImm8Add.lean` (657 lines), and the official local reference
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt` plus
`REFERENCES.json` (Intel SDM combined vols 1-4, edition 325462-093US,
September 2026; AMD unavailable, no AMD claim made).

## Architecture findings (independent, against canonical vocabulary)

- Byte forms: encoder `rexByte 0 (regHigh dst)` + 131 + `(192 + regLow dst)` +
  imm byte, length 4. Decoder admits only REX 72/73 (R=0, so the /0 digit is
  untouched), opcode 131, ModRM mod=3 with reg-field 0, then imm8. REX.R
  (76/77), missing REX.W (64), bare opcode, imm32 opcode 129, digits /1 and /7,
  memory mod=2, accumulator row 05, and all truncations refuse with `none`
  (proved `compactAdd_sonde_abgeschnitten`, `compactAdd_sonde_nachbarn`).
  Construction matches `Codec.rexByte`/`modrmReg 0` shape. Correct.
- REX/register/width: `rexByte`/`regHigh`/`regLow`/`codeReg` used in the
  canonical direction (B-bit extends the r/m destination; R fixed 0 for the /0
  digit). Pinned `ADD rax, 5 = 48 83 C0 05` and `ADD r9, -1` with B-bit set,
  both with decode pins. Correct.
- Semantics: `immSext n = sext .b8 (BitVec.ofNat 64 n)` reuses canonical
  `sext` (low 8 bits sign-extended; four pins 7f/80/ff/00 by `decide`).
  Out-of-range `Nat` truncates inside `immSext`, but every claimed path is
  guarded (`encodeCompactAdd` returns `none` outside i8 with proved cause;
  `roundtripCompactAdd` and `CompactImm8Add_verbindung` require `n < 256`;
  decoder only feeds `byteNat i < 256`). No silent truncation on any proved path.
- Value/flags: `addImmOp`/`addImmFlags` reuse `trunc`/`cfAdd`/`ofAdd`/
  `zfTest`/`negB`/`parityEven`; at `.b64` the value and CF/OF/SF/ZF/PF are each
  proved equal to the accepted `add64` outputs (no second evaluator). AF is
  `none` at every width. `Flags.af : Option Bool` with `none` = undefined
  (per `Wort.lean` header), so this forgets rather than invents; the owner task
  explicitly orders "AF stays none" and CUTS books the deliberate gap against
  the manual's "AF set" line. Bounded acceptance, not a repair item.
- Operands: register destination + imm8 source, no implicit operand, no CF
  input (Operation `DEST := DEST + SRC`, not ADC). Correct; no LOCK, no memory
  operand, no MXCSR/feature gate needed for integer ADD.
- Faults/memory order/TSO: the register step goes through accepted
  `schrittRegister` only; frame theorem proves memory untouched, RIP advances
  past the decoded length, length mismatch refuses. No #GP/#PF/#AC surface for
  this form. The memory handoff reuses the accepted pilot `store64` step
  sequentially with `write64`/`lesbar8`/`read64_nach_write64`. No TSO entry for
  the register form; per-access TSO bridge explicitly left open in CUTS. Sound.
- Dispatch: pilot `decode` admits no opcode 131 (`decodeRex` falls to `none`;
  verified in `Codec.lean`), so `pilot_verweigert_compactAdd` holds; the
  compact decoder refuses all 14 pilot `Befehl` rows (`compactAdd_verweigert_pilot`
  exhausts exactly the 14 constructors in `Typen.lean`). Neither decoder
  rewritten. Correct.
- Witness: `CompactImm8Add_verbindung_zeuge` jointly inhabits every premise
  (imm 5 < 256, ADD step 10 -> 15, write + readability at the data cell,
  `rax = 15`, `af = none`) with an observably memory-changing reached run
  (data byte 0 -> 15 via ADD-then-store on `zeugenSpeicher`) plus a planted
  length refusal (`add_kette_speicher`). Non-degenerate. Negative mutations
  are real `decide` refusals, not vacuous.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the snapshot
  source (only English "admitted REX" and doc mentions); no `Prop`-typed
  premise; sampled premises all used (`hn` via decode/encode facts, `hadd` via
  frame, `hwr`/`hrd` via store/read-back); CUTS block plus `#print axioms`
  for every main theorem present; name collision (`sonde_abgeschnitten` vs
  `ShiftCodec`) already repaired by rename. Scope respected: no diagnostic/
  gift/example/CLI numbers, no MARKE changes, no source/checker/Spec/emitter
  edits, no friend-reserved optimiser files.

## Build evidence

Author's queued-wrapper evidence ends green: `./lean-bau` ==
`exit 0; 0 error line(s)`, `Built Grammatik (483 jobs)`; every `#print axioms`
within `propext`/`Classical.choice`/`Quot.sound`. Earlier intermittent
final-link `olean` read failures and the one real defect (name collision) are
documented with the fix. This reviewer ran no build (report-only lane on a
different HEAD; no source controls touched), so the "last `./lean-bau`" line
above is the candidate's pinned evidence, not a re-run here.

## Boundaries (not claimed, per CUTS)

No silicon verification; AF deliberately `none`; memory-destination 83 rows,
16/32-bit rows, 81 imm32 row and accumulator rows still refuse; no
`fetchDekodiert`/`decodeExt` routing yet; no source correspondence and no
TSO/W/GX bridge; `none` is absence of transition, not a halt claim; 64-bit
(REX.W) selected profile assumed.

## Task feedback

Nothing in the owner task is judged wrong. The ZEUGE parenthetical's
source-terms wording was reasonably interpreted as a jointly inhabited
memory-changing reached run for a hardware row, which the companion provides.
The "per-width identity" sentence is satisfied as written for the covered
REX.W row (width-generic defs, AF-none at every width, five b64 identities);
narrow-row flag identities belong to their future rows.
