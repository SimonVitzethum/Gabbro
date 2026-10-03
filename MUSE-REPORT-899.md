# MUSE-REPORT-899: Exact review of author 749 (compact SUB with imm8)

Lane 899, clone `/home/simon/Dokumente/gabbro-muse/a899`, branch `muse/899` (review-only lane; owns only this report).
Author clone/task reference: `/home/simon/Dokumente/gabbro-muse/a749`, branch `muse/749`.

## CANDIDATE

CANDIDATE: 749 e15182fe41f5caeb3fe104e2da20ccfc09558107

Snapshot pin (`.tmp/review/SNAPSHOT.json`): author 749, base
`23b9a42fb44f2365b636cf8a9c440a2dfd8cae50`, files
`MUSE-REPORT-749.md`, `grammatik/Grammatik.lean` (one appended import),
`grammatik/Grammatik/X86/CompactImm8Sub.lean` (new, 568 lines), clean true.
Reviewed the exact pinned PATCH (683 diff lines) and the snapshot file copy
(`.tmp/review/author-749/grammatik/Grammatik/X86/CompactImm8Sub.lean`, read in full),
the owner task (`.tmp/review/author-749/OWNER-TASK.md`), the author report
(`MUSE-REPORT-749.md`) and the queued-wrapper build evidence
(`BUILD-EVIDENCE.json`). No source or live-control changes made by this lane.

## VERDICT

VERDICT: ACCEPT

Bound: acceptance is bounded to exactly one row (REX.W + 83 /5 ib, SUB r/m64, imm8, mod=3); see CUTS below.

## What was reviewed

Scope claimed: exactly one row — REX.W + 83 /5 ib, SUB r/m64, imm8,
register-direct (mod=3) — reusing the accepted `IntegerHardwareForms`
immediate row (encode/decode/step/fetch/byte-step, `immWort`, `immPasst8`,
`imm8Erweitern`, `immDecLaenge`, `immDecBreiteOk`, `stepImm_speicher`) and
canonical `Wort.sub64`/`cfSub`/`afSub`, `Zustand`/`Speicher`, pilot `schritt`,
`NarrowOps.narrowTruncMod`, `RelocatedExecution.bit31_equiv`. No new syntax,
decoder, evaluator, state type, diagnostic/gift/example/CLI number, or
MARKE_EMIT change. `Grammatik.lean` diff is one appended import line.

Architecture checks (independent, against the official local bundle
`.tmp/HARDWARE-REFERENCES/REFERENCES.json`, Intel SDM 325462-093US Sep 2026,
verified 2026-10-02, plus the extracted `intel-instruction-reference.txt`):

- Byte forms: `48 83 E8 01` (`sub rax, 1`), `... FF` (`sub rax, -1`,
  sign extension at decode), `49 83 E9 01` (`sub r9, 1`, REX.W+B), wide
  `48 81 E8 00 01 00 00` (`sub rax, 256`, imm32-LE) — all correct per the
  pinned Intel row (txt line 96950: `REX.W + 83 /5 ib SUB r/m64, imm8 MI
  Valid N.E. Subtract sign-extended imm8 from r/m64`; operand encoding MI at
  lines 96965-96970; `DEST := (DEST - SRC)` line 96993; flags `OF SF ZF AF PF
  CF set according to the result` line 96996). ModRM bytes check out
  (E8 = mod 3 / digit 5 / rm 0; E9 = rm 1 + REX.B; D8/D0 = digits 3/2 for the
  SBB/ADC refusal pins). Compact-choice iff (`kompakt_sub_feuert`, length 4
  iff fits) and every-decoded-byte-fits (`imm8Erweitern_passt`, case split at
  128 via the reused truncation/bit-31 bridges) close the smuggling direction.
- REX discipline: W=1 required (both W=0 pins refuse), REX.B accepted and
  pinned (r9), REX.R refused (`4C ...` pin) — correct because REX.R extends
  the ModRM.reg field, which here is the fixed /5 digit, so REX.R leaves the
  row. Missing-REX refusal correct for this 64-bit-row decoder; the generic
  digit-5-at-b32 refusal (`subkompakt_32_verweigert`, over all ModRM arms and
  both widths) keeps the 32-bit neighbour closed.
- Source/destination/implicit operands: MI encoding (ModRM:r/m read+written,
  imm8 source), destination is the register, no implicit operands — matches
  the manual's operand table. Register-direct only (mod=3); memory-operand
  form explicitly out of scope in CUTS.
- Flag semantics: full `sub64` snapshot equality plus CF borrow (`cfSub`)
  and DEFINED AF nibble borrow (`afSub`) in `subkompakt_schritt`; TARGET
  `CompactImm8Sub_verbindung` concludes value, CF, AF, RIP+4, memory
  untouched. SUB has no undefined flags in the manual (all six defined), so
  there is no undefined state to abstract; OF/SF/ZF/PF identity is carried by
  the proved full-snapshot equality one lemma away. Borrow probe
  (`0-1` borrows, `5-1 = 4` without borrow, AF `some false`) is correct.
- Pre-fault effects / memory order / faults: register-direct emits no data
  memory access (proved via the accepted `stepImm_speicher`; memory equality
  in the TARGET conclusion), so no data permission is consulted and no data
  fault arises; fetch comes from actual executable memory through the
  accepted `fetchIntHwImm`. Exception tables (#GP/#SS/#PF/#AC for memory
  operands, #UD for LOCK-on-non-memory) concern the memory/LOCK forms that
  are explicitly OPEN, not the claimed register-direct row.
- TSO/atomicity: no memory access means no TSO event; sequential fact over
  one `Speicher` only, GX refinement explicitly left with the TSO bridge
  (CUTS). No LOCK claim (CUTS lists no LOCK prefix).
- Feature/MXCSR/interrupt gates: none needed — SUB is base integer ISA with
  no CPUID gate in the manual row, no MXCSR interaction, no interrupt-enable
  dependence. Correct to assert none.
- Canonical execution interaction: no new dispatcher; fetched-byte
  connection goes through the accepted fetch + byte step
  (`fetchIntHwImm`/`intHwImmByteschritt`); `ExtendedExecution` non-dispatch
  honestly declared as remaining with its owner.

Proof hygiene (from the pinned file text):

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (text scan of the
  snapshot file; only false-positive substring `admit` inside the English
  word "admits"). No `Prop`-typed premises, no `intro _`/`have _ :=`
  discards found. Every premise of `subkompakt_schritt`
  (hok/hlen/hb/h/hstep) and of `CompactImm8Sub_verbindung`
  (hfetch/hfit/hstep) is used by its proof. Conclusion is not a restated
  premise; no contract quantification or invented semantics.
- Witness: `CompactImm8Sub_verbindung_zeuge` jointly instantiates fetch
  (`subkompakt_holt`, by `decide` over actual image bytes), fit (by
  `decide`), byte step (`subkompakt_weiter`, `rfl`), all five TARGET
  conclusion equations via the TARGET itself, register change 5 -> 4
  (`decide` inequality), a reached pilot `store [rbx], rax` changing the
  data-cell byte observably 0 -> 4 (`subkompakt_kette_speicher`), and two
  negative mutations (SBB digit, prefix-less). Non-degenerate by the lane
  standard (register-changing reached execution plus memory-changing
  reached store). Additional refusal pins (ADC, REX.R, W=0 compact/wide,
  truncated tail) and chain pins (bytes/fetch/RIP) present.
- CUTS block precise: states the reused producers, the exact row covered,
  manual provenance (Vol. 2B 4-685/4-686, SUB-Subtract), and the OPEN list
  (no hardware correspondence beyond stated canonical subset; no mem form;
  no 16/32-bit 83, 81/80 rows, no LOCK; no TSO/GX bridge; no
  source/ABI/image/entry/relocation/cost; dispatcher composition with its
  owner). `#print axioms` for every main theorem; per BUILD-EVIDENCE all
  are subsets of `[propext, Classical.choice, Quot.sound]`.

Evidence (author's queued-wrapper runs, BUILD-EVIDENCE.json):

- `./lean-probe grammatik/Grammatik/X86/CompactImm8Sub.lean`: `== 0 error(s)
  ...; exit 0` (final; axioms listed per theorem, standard subset).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (483 jobs)`. Two earlier `lean-bau` runs
  failed only at the aggregate step on missing unrelated oleans
  (`ZielOrtInvGrundZeuge`, then `VectorIntegerHardwareForms`); unmodified
  files, green on re-run — transient parallel-build race as reported.
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  `== 0 error(s) ...; exit 0`, `gabbro_ziel` on exactly
  `[propext, Classical.choice, Quot.sound]` (first attempt hit the known
  `failed to create thread` machine ceiling; retry passed).
- Author report claims match the PATCH and evidence; no over-claim found.

## Bounded acceptance / notes (not REPAIR blockers)

- The TARGET concludes CF/AF but not OF/SF/ZF/PF individually; the full
  six-flag identity is proved in `subkompakt_schritt` (flags equality), so
  nothing defined is zeroed or ignored — bounded statement shape, accepted.
- No explicit LOCK/F0, 0x66, or REX.X refusal pins; these neighbours sit
  outside the claimed register-direct row and are correctly listed as OPEN
  (no LOCK prefix). A future pin (e.g. F0 refusal) would strengthen but is
  not required for this row's closure.
- This reviewer could not re-execute the queued wrappers: the `bash` tool
  call was permission-rejected in this session, so no independent
  `./lean-probe`/`./lean-bau` run was possible from lane 899. Verification
  rests on the author's quoted queued-wrapper outputs in BUILD-EVIDENCE.json
  plus full-text inspection of the pinned snapshot. Recommend the merger
  re-run `./lean-bau` + `./lean-probe` on the exact candidate HEAD before
  integration (standard gate in any case).

## What remains open

Per the file's CUTS (endorsed): hardware correspondence (silicon) unproved;
memory-operand SUB form; 16/32-bit 83 rows, 81/80 rows, LOCK prefix; TSO/GX
bridge; source/ABI/image/entry/relocation/cost transfer; `ExtendedExecution`
dispatcher composition. Nothing in the task text was found to be wrong.

## Lane status

Review complete. Report-only lane: no source files touched, no numbers taken,
no live controls modified. This report (`MUSE-REPORT-899.md`) is the owned
deliverable; commit via `commit.sh` (bash permission was rejected at review
time — if the commit tool call below fails, the file content above is the
complete deliverable and the blocker is the tool permission, not the review).
