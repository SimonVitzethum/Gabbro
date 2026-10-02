# MUSE-REPORT-701: Exact review of author 700 (multiply/divide widths, immediate IMUL)

Clone verified: `/home/simon/Dokumente/gabbro-muse/a701`, branch `muse/701`.
Review-only lane. No source file touched; this report is the only owned file.
(Task text names `MUSE-REPORT-693.md` once; that is a copy-paste typo. This
lane owns `MUSE-REPORT-701.md` per HARD RULES and the lane title.)

CANDIDATE: 700 37bb95b0fcd0afa5840894575375ebb8e6b3276d

VERDICT: ACCEPT (bounded; bounds in §6, none repair-blocking)

## 1. What was reviewed

- Full owner task (`lanes/700.md`, lines 1-23 incl. the 2377-char USER PRIORITY
  line) and full reviewer task (`lanes/701.md`), read in sequential ranges.
- Exact pinned snapshot `.tmp/review/author-700/`: `OWNER-TASK.md` (22 lines),
  `MUSE-REPORT-700.md` (105 lines), `PATCH.diff` (2184 lines), the candidate
  module `grammatik/Grammatik/X86/MulDivWidthHardwareForms.lean` (2058 lines,
  read 1-300 / 301-650 / 651-1050 / 1051-1450 / 1451-1800 / 1801-2058),
  `BUILD-EVIDENCE.json` (212 lines), `SNAPSHOT.json` (pinned HEAD above,
  base `a6315567`, files exactly: report + `grammatik/Grammatik.lean` +
  the new module, clean).
- Patch scope confirmed: additive umbrella import only
  (`+import Grammatik.X86.MulDivWidthHardwareForms` in `Grammatik.lean`),
  one new module, one report. Nothing else touched.
- Official local manuals `.tmp/HARDWARE-REFERENCES/`: `REFERENCES.json`
  (Intel SDM 325462-093US Sep 2026, sha256-verified 2026-10-02; AMD
  unavailable, no AMD claim made) and the extracted
  `intel-instruction-reference.txt`. Spot-checked every cited entry:
  MUL table (~line 70674), IMUL forms (~58200), DIV (~50157), IDIV (~58043),
  CBW/CWDE/CDQE (~44283), CWD/CDQ/CQO (~49874). All opcode/operand/#DE/
  LOCK-#UD/sign-extension statements used by the candidate match the text.

## 2. Architecture check (not just Lean green)

- Byte forms: F7 /4 /6 /7 (MUL/DIV/IDIV), 0F AF /r (IMUL2), 6B /r ib and
  69 /r id (IMUL3 compact/dword), 98/99 (dividend preparation). Default-32
  with REX.W promotion; 0x66 refuses everywhere (16-bit OPEN); F6 refuses
  (8-bit OPEN); /5 refuses; mod != 3 refuses; LOCK refuses (#UD per every
  cited entry); doubled REX refuses; short immediates refuse. 16 planted
  `wd_nichts_*` refusals, all `decide`-closed.
- Hand-verified encodings against the manual: REX bytes 68 (R), 73 (W+B),
  77 (W+R+B); ModRM 0xC1/0xE0/0xCF shapes; imm -3 = 253, -128 = 128,
  100000 = A0 86 01 00, -70000 = 90 EE FE FF little-endian. All pins correct.
- Width semantics: 32-bit reads truncate, writes zero-extend
  (`wdSchreiben w32 = trunc .b32`); 64-bit identity. CDQ modeled as
  0xFFFFFFFF/0 zero-extended into RDX (correct for a 32-bit write in 64-bit
  mode); CQO as full-64 broadcast on bit 63; CWDE as trunc32(sext16(RAX));
  CDQE as sext32. All match the cited description rows.
- Implicit operands: EDX:EAX / RDX:RAX dividends read from the pre-state;
  EAX/EDX (quotient/remainder) written on success. 32-bit dividend value
  `s64aus32 = sVal(EDX)*2^32 + low` is the correct signed composition.
  Reads precede writes, so aliases (src == rax/rdx) resolve from pre-state.
- Flags: CF/OF via the accepted `mulTragU/S` validity relations
  (`wdMulFlagsU/S_gueltig` against `MulGueltigU/S`); all other bits kept
  with AF `none`, explicitly documented as an undefined-kept modelling
  choice, not hardware truth. DIV/IDIV preserve all flags. No invented
  determinism: the halt arm (`hardwareHalt`) carries no state and makes no
  register claim, grounded in the manual leaving #DE destinations undefined;
  `wd_halt_ist_kein_ok` pins halt != ok.
- Division: truncation toward zero (`tdiv`/`tmod`), #DE on divisor zero and
  quotient overflow for both widths and signs; zero-extension fact
  `divWeitU32_antwortet_zero_ext` proved. 64-bit arms reuse accepted
  `divWeitU/S`, `mulLow/mulHighU`; no evaluator duplicated, no canonical
  name shadowed (checked: zero redefinitions of sVal/mulLow/mulTrag/
  divWeitU-S/holeFetchAux/ausfuehrbarN/Zustand/Register/laengeOk/ripNach).
- Fetch/execute: independent byte parser (never encode-equality), generic
  `decodeWd_len_ok` over arbitrary inputs (exact consumption, 1..15),
  per-layer length facts, `decodiertWd_laenge_ok` into the step, 14
  `decodeWd_exec_*` theorems covering all twelve arms, permission-checked
  fetch (`holeFetchAux` + length consistency + `laengeOk` +
  `ausfuehrbarN`) with `wdByteschritt` weiter/halt/verweigert.
- TSO/atomicity/memory order: correctly absent. All admitted forms are
  register-direct (mod=3); no memory access, no TSO/source/cost/time claim;
  CUTS says so explicitly.
- Feature/MXCSR/interrupt gates: none apply to these integer forms; none
  claimed. Correct.

## 3. Premises, witnesses, mutations

- Every step equation uses all its premises (`hok`, `h`, `hqr` via the
  unfolding `simp`; every `decodeWd_exec_*` uses `hdec` through
  `decodiertWd_laenge_ok`). No `Prop`-typed premise, no `forall rho/v`
  contract smuggling, no `intro _` / `have _ :=` (zero occurrences), no
  conclusion-restating-premise. No theorem quantifies over program syntax,
  so no mechanical `_zeuge` obligation; the joint witness
  `wd_zeuge_gemeinsam` instantiates generics on concrete bytes/states
  (reuses `pin_wdmul_ecx_dekode` for `decodiertWd_laenge_ok`).
- Joint witness: compact `7 * -3` decode + step (-21), high-register 64-bit
  compact step (21), negative 32-bit division (-7/2 = -3 rem -1), genuine
  `write64`/`read64` RAM transfer with observed byte change, 64-bit
  INT_MIN/-1 halt, `laengeOk 2`, LOCK/0x66/short-imm refusals. The author
  discloses it is a conjunction plus the fetched end-to-end
  `probe_wd_bytesschritt`, not a multi-step sequential run, because
  IMUL/DIV touch no memory. That is the maximal honest evidence for
  register-only forms; the literal task phrasing ("run must end in a real
  RAM change") is unsatisfiable for such forms, and the report says so
  plainly. Accepted as disclosed bound, not fake closure.
- Value probes (`decide`): compact/high-reg/neg-div/pos-div/mul32/
  overflow-halt/CWDE/CDQE/CDQ/CQO/fetched-byteschritt. Negative mutations:
  overflow halt, LOCK, 0x66 on three forms, F6, /5, mem-mode, REX.R/X over
  Group 3, double REX, bad 0F second byte, truncated REX/66/imm tails.

## 4. Reproduced evidence (queued wrappers, this clone)

- `./lean-probe .tmp/review/author-700/grammatik/Grammatik/X86/MulDivWidthHardwareForms.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (first line trusted).
  Axiom prints are subsets of `[propext, Classical.choice, Quot.sound]`
  (e.g. `divWeitU32: [propext, Quot.sound]`), i.e. the standard goal axioms.
- Author BUILD-EVIDENCE records the same 0-error probe plus full
  `./lean-bau: Build completed successfully (469 jobs)`. Consistent.
- Static scan of the snapshot file: `sorry` 0, `axiom` command 0,
  `native_decide` 0, `unsafe` 0 (the 17 `admit` hits are the English word
  "admitted"); `#print axioms` x41; trailing `CUTS:` block with exact manual
  line provenance; `end Gabbro.Grammatik.X86` present.

## 5. Why not REPAIR

- No forbidden tactic/axiom, no unused premise, no desired-correctness
  premise, no weakened guarantee, no silicon/fault/TSO claim beyond the
  model, no checker/diagnostic number taken, CUTS precise with an explicit
  obstruction for 8/16-bit forms (no sub-registers/partial merge in
  `Register`). The three candidate-noted repairs during authoring (CDQ
  broadcast, imm-tail lengths, two pin bytes) were caught by `decide` pins
  and fixed before commit.

## 6. Bounded acceptance (follow-ups, not blockers)

1. Overlap without agreement proof: w64 MUL/DIV/IDIV/IMUL2 coincide with the
   accepted `MulDivCodec` family (also wired into `decodeExt`/`stepExt`),
   but no theorem proves `wdSchritt` agrees with `mulDivSchritt`/`stepExt`
   on the overlap, and the new forms are not wired into `ExtInstr`. The
   owner task's OWN ONLY forbids 700 from touching `ExtendedExecution`,
   so integration belongs to organisation lane 558. Bound: treat 700 as a
   producer family pending 558 integration; a bridge/admission follow-up
   should prove overlap agreement or establish decode precedence.
2. REX.X refusal over-approximates silicon (X is ignored in mod=3); safe
   direction for a validator, documented as non-canonical subset. 558 may
   widen.
3. Generic immediate round trip OPEN (four pins: -3, -128, 100000, -70000);
   suggest follow-up pins at the form-switch boundary (+127/-129).
4. No full-build re-run in this clone (candidate not merged here; OWN ONLY
   forbids applying its patch). Green status rests on the author's
   committed 469-job build plus my independent 0-error probe of the exact
   snapshot file.

## 7. Task remarks

Nothing in the owner task is wrong. Two notes: (a) the reviewer task's
`MUSE-REPORT-693.md` is a typo for `MUSE-REPORT-701.md`; (b) the "joint run
ending in RAM change" phrasing cannot be literal for register-only forms;
the author's disclosed conjunction + fetched step + real memory transfer is
the right evidence shape.
