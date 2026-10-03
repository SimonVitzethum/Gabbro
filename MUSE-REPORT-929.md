# MUSE-REPORT-929: Exact review of author 779 (XCHG ordering need)

## Clone / branch verification

- Clone path matches task: `/home/simon/Dokumente/gabbro-muse/a929`.
- Branch at session start: `muse/929` (verified via shell before the shell
  gate started rejecting commands; see blocker note below).
- Own file only: this report. No source file was created, edited, or deleted
  by this lane. The candidate module does NOT exist in this clone
  (`grammatik/Grammatik/X86/Xchg*` globs empty): review is of the exact
  pinned snapshot in `.tmp/review/author-779/`, never merged here.

## CANDIDATE / VERDICT

- CANDIDATE: 779 `aa8feb6217b05bf25a3744c641deb9be539cbd66`
  (base `56537272a31df3de5d9b7898bbade91c3de817b8`, from
  `.tmp/review/SNAPSHOT.json`; files `MUSE-REPORT-779.md`,
  `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/XchgOrderNeed.lean`).
- VERDICT: ACCEPT (bounded: the two canonical REX.W+0x87 rows with
  barrier-carrying memory exchange, explicit neighbour refusals, and the
  proved bare-register-XCHG admission refusal; no full W/GX bridge claimed
  and none accepted).

## What was inspected

1. `.tmp/review/author-779/OWNER-TASK.md` (task text, ZEUGE line).
2. `.tmp/review/author-779/grammatik/Grammatik/X86/XchgOrderNeed.lean`
   (541 lines, read in full).
3. `.tmp/review/author-779/PATCH.diff` (646 lines: head, import hunk, full
   new-module body, CUTS tail — exactly 3 files, no other tree changes).
4. `.tmp/review/author-779/MUSE-REPORT-779.md` and `BUILD-EVIDENCE.json`
   (final `./lean-bau`: exit 0, 0 errors, 485 jobs, `Built Grammatik`;
   per-theorem `#print axioms` within propext/Classical.choice/Quot.sound).
5. Local manual `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
   XCHG section lines 137936-138034, plus `REFERENCES.json`
   (Intel SDM 325462-093US Sep 2026; AMD unavailable, no AMD claim made).
6. Base-tree canonical providers actually referenced: `TSOZustand`,
   `pufferSetze`, `issueByte`, `flushKern`, `zaunBereit`,
   `zaunBereit_iff_leer`, `TSOErreichbar` (TSO.lean); `read64`, `write64`,
   `writeBytes`, `lesbar8`, `Fuss`, `zeugenSpeicher`,
   `read64_nach_write64` (Speicher.lean); `regCode`, `codeReg`, `natByte`,
   `byteNat`, `leBytes32`, `parseLe32`, `parseLe32_leBytes32`, `regHigh`,
   `regLow`, `rexByte`, `modrmReg`, `modrmMem` (Codec.lean); `dispWort`,
   `regSet_gleich` (Ausfuehrung.lean); 6-field `Flags` (Typen.lean —
   matches `xwFlags`).

## Architecture findings (each checked against the local Intel text)

- Byte rows: REX.W+87 /r for r/m64,r64 (MR) and r64,r/m64 (RM) confirmed
  (manual lines 137953/137955). Both table rows share ONE byte form and
  XCHG is a symmetric swap, so the single `.mem base src` form covers both
  roles with no byte-form gap. ModRM mod=2 (0x80 base in `modrmMem`) and
  mod=3 (0xC0 base in `modrmReg`) match the claimed rows; SIB 0x24 exactly
  on regLow=4 mirrors the pilot convention.
- Operation TEMP:=DEST/DEST:=SRC/SRC:=TEMP and Flags Affected None
  confirmed (lines 137990-137996); `xchgSchritt` swaps and leaves `flags`
  untouched. No invented determinism, no zeroed defined effects.
- Auto-LOCK on a memory operand regardless of LOCK prefix/IOPL confirmed
  (lines 137971-137975). The model answers with an atomic canonical-memory
  swap gated on the acting core's empty store buffer (Vol. 3A 11.2.3.9
  shape); under an empty own buffer the TSO read IS the canonical read, so
  bypassing the buffer there is sound. CUTS honestly bounds this as a LOCAL
  barrier (no foreign drain, no multi-lock total order, no W/GX simulation).
- 90H XCHG (E)AX,(E)AX = NOP alias confirmed (lines 137984-137986); the
  REX.W+90+rd row is refused (`decodeXchg_alias90_verweigert`, `rfl`) and
  listed in CUTS. Bounded non-claim, not a silent hole.
- `#UD` for LOCK prefix with a non-memory destination (manual #UD rows):
  the decoder refuses every F0-led row (`decodeXchg_lock_verweigert`,
  `rfl`). Conservative and sound.
- REX subset {0x48,0x49,0x4C,0x4D} (W=1, X=0): sufficient for the claimed
  rows (SIB-0x24/no-index shapes force X=0); all other REX bytes refuse via
  `rexXchgBits` = none. Sub-64-bit rows are out of scope and named in CUTS.
- mod=0/1 rows refuse through the final `else none`; truncated input
  refuses (`decodeXchg_abgeschnitten_verweigert`, `rfl`).
- Permissions: `read64`/`write64` returning `none` is the refusal path
  (page-fault shape, no invented halt), pinned by
  `xchg_mem_verweigert_ohne_leserecht/_ohne_schreibrecht`.
- Footprint `xchgFuss` = 8 `Fuss` bytes for memory, `[]` for registers;
  `encodeXchg_len` keeps every encoding inside the 15-byte cap.
- No feature/MXCSR/interrupt-enable gates are needed for XCHG (no SIMD, no
  FPU, no privilege-gated form in the claimed rows); fairness, interrupts,
  devices, MMIO/DMA, split-lock/tearing/timing are named open in CUTS.
- No second memory model and no source interpreter: state is canonical
  `TSOZustand`, memory ops are canonical `read64`/`write64`. The step
  function is new but memory-free of duplication; the owner task's
  "ExtendedExecution dispatcher" reuse is partially answered by reuse of
  canonical state/ops rather than a dispatcher call — acceptable inside the
  stated claim boundary (single-step connection + decode tie at the
  witness), and CUTS names what is NOT a full execution connection.

## Proof-hygiene findings

- No `sorry`, `admit` (as tactic), `axiom`, `native_decide`, `unsafe`
  (regex sweep of the candidate file; only English words "admitted"/
  "admission" and `#print axioms` lines match the loose pattern).
- No `Prop`-typed premises; every premise of `XchgOrderNeed_verbindung`
  (`hbuf`, `hrd`, `hles`, `hwr`, `hstep`) is used by the proof; the
  conclusion (swap installed, flags kept, fence-ready, order-carrying,
  read-back) is strictly stronger than any single premise.
- Target witness present: `XchgOrderNeed_verbindung_zeuge` inhabits ALL
  premises jointly on a non-degenerate REACHED run — TSO issue+flush moves
  byte 100 (`xw_tso_aendert`, `decide`; `xw_erreichbar` via issue/flush)
  and the swap observably moves the word at 8192 from 0 to 7
  (`xw_mem_aendert`, `decide`). Not a degenerate/empty run.
- Negative coverage is proved, not just run: barrier gate
  (`xchg_mem_verweigert_bei_puffer`), both permission refusals, LOCK /
  90-alias / truncation refusals, and `xchg_reg_ohne_schranke` (bare XCHG
  succeeds with a FULL buffer, hence must never stand where order is
  needed) together with admission-false on `.reg`.
- Scope discipline: PATCH touches exactly the 3 registered files; import
  appended at the end of `Grammatik.lean`; no diagnostic/gift/example/CLI
  numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits.
- Honest scoping note (agreed with author report): "refusal of
  bare-XCHG-as-optimisation" is an admission predicate plus a proved
  no-barrier fact, not a compiler-pass change — consistent with the lane's
  no-optimiser-touch constraint, and stated plainly on both sides.

## Reproduction note

No suspicious case needing re-execution was found (all refusal/roundtrip/
witness facts are `rfl`/`decide` closed and the recorded build evidence
shows the full-project green build). Independent re-execution through the
queued wrappers was NOT possible from this lane: shell invocations
(`./lean-bau`, `./lean-probe`, `git log/status`, `./commit.sh`) are
rejected by the permission gate at review time (see blocker). Verification
therefore rests on full source inspection, manual cross-check, and the
author's recorded complete-output evidence — stated as a boundary, not as
a re-measured green run.

## Blocker (precise)

`default.bash` calls are rejected ("The user rejected permission to use
this specific tool call") for `git status`, `git show`, `./lean-bau`,
`./lean-probe`, and `./commit.sh` alike (two early calls succeeded, then
all later ones were rejected, including the commit step). Consequence:
this report is WRITTEN but could NOT be committed through
`arbeitsprotokoll/.commitmsg` + `./commit.sh`, and no fresh `./lean-bau`
result line from the reviewer exists. The honest partial status is:
review complete, verdict fixed (ACCEPT, bounded), report file complete,
commit pending on shell access. A coordinator with shell access can commit
`MUSE-REPORT-929.md` verbatim on branch `muse/929` with the standard
trailer `Co-Authored-By: muse-agent-929 <muse-agent-929@noreply.invalid>`.

## Open / not claimed (carried from candidate CUTS, endorsed)

Round trip is checked data, not silicon fidelity; barrier local to the
acting core; REX.W+90+rd row, explicit LOCK row, sub-64 widths, segment
overrides, HLE, mod=0/1 rows, split-lock/tearing/timing, fairness,
interrupts/devices, and any W/GX simulation stay open.
