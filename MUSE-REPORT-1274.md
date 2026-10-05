# MUSE-REPORT-1274: Independent exact review, rotates ROL/ROR/RCL/RCR

CANDIDATE: 1273 77780bb91164d02f09c8e9be61a344e96b82f149

## Identity and material
- Reviewer clone `a1274`, branch `muse/1274`, tree clean; this report is my only file.
- Reviewed material (staged in-clone at `.tmp/review/author-1273`, pinned above):
  `PATCH.diff` (2782 lines, 3 files), snapshot `grammatik/Grammatik/X86/IntRotate.lean`
  (2605 lines), `MUSE-REPORT-1273.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`.
- Base per snapshot: `738366545afbddf7ac664db92804703db24f8868`, snapshot flag clean.

## Checks performed (all on the pinned snapshot text)
1. Banned tokens: grep over the new Lean file for sorry/admit/native_decide/sorryAx/unsafe
   finds only four English-word hits in doc comments ("admitted"/"admit no successor",
   lines 1096, 1965, 2026, 2035). No `axiom` declarations anywhere. Pass.
2. File touch audit via PATCH.diff: exactly three files — new `MUSE-REPORT-1273.md`,
   one appended `import Grammatik.X86.IntRotate` line at the end of
   `grammatik/Grammatik.lean`, new `grammatik/Grammatik/X86/IntRotate.lean`. Pass.
3. Axiom ledger: a `#print axioms` line per main theorem (100+ entries, ending with
   `rotHw_zeuge`), plus the CUTS block. Structural presence verified; kernel outputs
   rely on author-recorded evidence (see limitation L1). Pass on structure.
4. CUTS block (line 2396): honest — claims dispatcher/adapter-level connection only,
   disclaims hardware correspondence and any W/GX bridge, names open subset refusals,
   the multi-byte drain gap, and the missing decodeExt/stepExt hookup. Pass.
5. Lift-not-copy: count mask is `schiebeZaehler` reused from Ganzzahl (line 59);
   Breite/Wort/trunc/codeReg/regHigh/regLow/Flags/TSOZustand/HwWf/HwAdapter all reused
   through imports; only family structs (RotOp, RotQuelle, RotOperand, RotForm,
   RotDecodiert, RotPraefix, RotNachweis) are new. No duplicated machine, register
   file, or TSO model. Pass.
6. Premise hygiene: no `intro _` / `have _ :=` / wildcard-bind discards in the file.
   Spot-read theorems use all hypotheses. Pass.
7. Refusals that really refuse: 12 named decode refusals (lock, digit four, mod 0/1,
   66h-on-byte, REX.W-on-byte, REX.R, REX.X, unknown, empty, lone-opcode, short-imm),
   each a proven `= none` decide-statement; LOCK refused at dispatcher
   (`rotHw_nichts_lock`, `[240, 209, 192]` pin); bad-length and memory-operand adapter
   refusals proven (`rotHw_schlechte_laenge_verweigert`,
   `rotHw_mem_adapter_verweigert`). Pass.
8. Witness `rotHw_zeuge` (line 2359): joint over two cores (ROL on core 0 with
   RAX/CF/OF pins, ROR on core 1 with RBX/CF/OF pins), a memory-form value pin, two
   owner-only forwarded family bytes (owner sees 3/128, foreign sees 0), a drain that
   changes real shared memory 0 to 3, HwWf of the start state, and three refusals
   beside it. Non-degenerate with a memory-changing step. Pass.
9. Silicon spot checks I could verify from architecture knowledge: opcode bytes
   208/209/210/211/192/193 for D0/D1/D2/D3/C0/C1; digits 0-3 to ROL/ROR/RCL/RCR with
   digit 4+ refused; masked counts via the accepted mask; RCL/RCR modulo bits-plus-one;
   CF as last bit out; OF defined only at masked count 1 with incoming OF kept
   otherwise (`getD vor.of`); count 0 keeps all flags (`rotFlags_null`); 8/16-bit
   merge shape with 32-bit zero extension in the family step. Pass, except item R1.
10. Encoder/decoder agreement: canonical encoder emits at most one prefix byte class
    per form (66h for b16, REX.W for b64, never combined); generic register and memory
    round trips per width and count source plus 5 SDM byte pins. Pass in-model.

## R1 (the single repair item)
`rotBreite` (line 1086) tests `p.op16` before `p.w`, so a byte stream carrying BOTH
66h and REX.W decodes as 16-bit. On silicon REX.W overrides 66h (64-bit operand).
This is the unsafe direction (mis-decode, not refusal), sits inside the task's
explicit REX.W/legacy-prefix scope, and is not named in CUTS, which lists the other
subset choices. All other subset choices refuse; only this combination silently
disagrees. Concrete fix: give REX.W precedence in `rotBreite` (or refuse the
combination explicitly) plus one decide probe pin; the encoder never emits the
combination, so no round trip or pin breaks. This is a finding about the definition,
not the proof shape, and the claim is not larger than the evidence.

## Limitations (recorded, not verdict drivers)
- L1: no independent kernel re-execution. The pinned files are not in my build tree
  and my lane owns only this report, so `./lean-bau` was not run here; a green build
  of my own clean master would evidence nothing about the pinned head. Author-recorded
  evidence: final `./lean-probe` 0 errors, `./lean-bau` "Build completed successfully
  (659 jobs)", snapshot clean true. The `decide` pins and axiom outputs rest on that
  record, cross-checked structurally by me.
- L2: no SDM extracts in this clone; silicon cross-checks above use stable
  architecture facts (opcode map, REX.W precedence, count masks, CF/OF rules).

## What remains open after this review
- Author repair of R1, then re-stage of the snapshot for a closing check.
- The CUTS-owned items (decodeExt/stepExt hookup, per-access bridge, multi-byte
  drain agreement, silicon re-check against the supplied extracts) stay future work
  by design.

## Task remarks
- The first launch lacked the pinned hash and any in-clone candidate access, which
  forced an honest blocked interim report (commit `fccc0d8d`, kept in history). The
  staged snapshot plus pinned hash resolved it; recommend always staging both before
  launching exact reviewers.

VERDICT: REPAIR
