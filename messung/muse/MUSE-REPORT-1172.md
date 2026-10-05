# MUSE-REPORT-1172: Exact review of candidate 1171 (linking, relocations, final mapping)

## Scope and identity

- Reviewer clone verified: `/home/simon/Dokumente/gabbro-muse/a1172`, branch `muse/1172` (clean).
- Author lane 1171, pinned HEAD `91eff7e4363c251cd0ce2324c6654c55a626de35`, base `062b979a6271b7b3044ab06be3f3cde411a0d4f1` (from `.tmp/review/SNAPSHOT.json`).
- Reviewed files (from snapshot + `PATCH.diff`): `MUSE-REPORT-1171.md` (new), `grammatik/Grammatik.lean` (+1 import line), `grammatik/Grammatik/X86/PipelineLink.lean` (new, 587 lines).
- Method: read the candidate diff only (snapshot `PATCH.diff` + `grammatik/` copy under `.tmp/review/author-1171/`); no code copied into this clone; no new Lean definitions by the reviewer.

## Checks performed

1. **Banned tactics/axioms:** grep over the candidate file for `\bsorry\b`, `\bnative_decide\b`, `\bsorryAx\b`, `^axiom `, `^unsafe ` finds nothing. (One false-positive substring `admit` inside the English word "admits" in a doc comment; not a tactic.) PASS.
2. **`#print axioms` standard:** candidate build evidence lists every main theorem within `[propext, Classical.choice, Quot.sound]` or a subset (e.g. `verknuepft_korrekt`: propext + Quot.sound; `verknuepft_korrekt_zeuge`: all three; refusals: none or propext only). No extra axioms. PASS.
3. **Existing files untouched except one import line:** `PATCH.diff` shows the only tracked-file edit is `+import Grammatik.X86.PipelineLink` in `grammatik/Grammatik.lean`; no edits to `OptimizationRules.lean`/`OptimizationWitnesses.lean`, no other existing-file changes. PASS.
4. **Every premise used:** `verknuepft_korrekt` consumes all 8 premises (patch/img/decode via `ComposePatchBytes_feld_verbindung`; well-formedness+membership via `verknuepft_wx`; find+bound via `verknuepft_byte_geladen`; range via `linkPatch_bereich`; frame via `linkPatch_rahmen`). `loeseSymbol_fremd_verweigert` uses both `hne` and `ih`. `verknuepft_rel32_schliesst` forwards all premises. No `intro _` / `have _ :=` discard. PASS.
5. **Family evaluator lifted, not copied:** no second decoder/loader/executor/ISA/IR in the file; patching goes through `Relokation.patchAt`/`patchRel32`/`patchAbs64` + `patchAt_*` facts, re-decode through `ComposePatchBytes_feld_verbindung`, mapping through `geladenByte_datei`, W^X through `wohlgeformt_wx`, run through `RelocatedExecution.ruf_schritt_zeuge`. All named producers verified present in this tree (`ComposePatchBytes.lean:157`, `Bild.lean:283`, `LoadedExecution.lean:62`, `Relokation.lean:234/476/520/539`, `RelocatedExecution.lean:946`). PASS.
6. **Planted refusals really refuse:** seven `decide`-proved refusals — overlap (`patchZwei … = none`), overrun (`linkPatch` 4-byte operand at offset 2 of a 3-byte image `= none`), out-of-range disp (`2^31 = none`), unlisted symbol id 7 (`= none`), W+X image (`wohlgeformt = false`), forged opcode byte 6 (`decode = none`), hole address `0x1800` (`transferOk = false`). Genuine negative evaluations, not vacuous. PASS.
7. **Witness non-degenerate:** `verknuepft_korrekt_zeuge` jointly instantiates all link premises on a two-unit link (5-byte jump unit + 1-byte `ret` unit, disp +16 applied at offset 1, re-decoded with B's byte as rest, image well-formed, coverage true, section found, in-range, outside-operand index 5) and conjoins a reached memory-changing run (`ruf_schritt_zeuge`: return address stored, `m.bytes … ≠ …`). Two cores N/A: concurrency is explicitly OPEN, no multi-core claim made. PASS (with noted split below, disclosed by the author).
8. **Silicon facts vs Intel SDM extract (edition 325462-093US, `.tmp/HARDWARE-REFERENCES/`):** opcode `233 = 0xE9` is JMP rel32, `195 = 0xC3` is RET (extract lines confirm `E9 cd JMP rel32`, `C3 RET`, `RET C3`); rel32 4 bytes / abs64 8 bytes widths match; range gate via `rel32Passt` (out-of-range `2^31` refused). No sign/zero-extension confusion (rel32 dispatches through the accepted `rel32Bytes`, not a new codec). PASS.
9. **CUTS honest, no overclaim:** file CUTS (lines 527–566) explicitly leave OPEN source correspondence, `valX86_sound` / full source-to-final-byte closing, hardware correspondence (model `Speicher`, not silicon), TSO/GX, concurrency, budget/work, multi-unit convergence, abs64 re-decode, rel8, conditional agreement, non-jump/call/conditional sites, loader execution/entry/OS. Report matches. No W/GX or silicon-correspondence claim. PASS.

## Build

- Candidate evidence (`BUILD-EVIDENCE.json`): `./lean-probe …/PipelineLink.lean` → `== 0 error(s) … exit 0`; `./lean-bau` → `== exit 0; 0 error line(s)`, `Build completed successfully (608 jobs)`.
- Reviewer base check in this clone: `./lean-bau` → `Build completed successfully (608 jobs).` (last result line; whole project green without the candidate applied, as required by OWN-ONLY).

## Task fidelity notes (not defects)

- Coverage union is stated at `Bild` level (`bildDeckung` over the two linked sections = conjunction of the units' section coverages), the exact form the validator consumes; per-byte decoder concatenation is deliberately not re-proved. Disclosed in the author report; matches the task's validator-facing requirement.
- The memory-changing run reuses the accepted call-class `ruf_schritt_zeuge` while the patch witness is a jump — the same split the accepted `ComposePatchBytes_verbindung_zeuge` uses. Disclosed; precedent-consistent.
- The overlap refusal exercises the underlying `patchZwei` primitive rather than two stacked `linkPatch` calls; consistent with the file's single-operand scope and its CUTS.

## What remains open

Nothing blocking this candidate. The candidate's own CUTS list stays open by design (source correspondence, `valX86_sound`, silicon correspondence, TSO/GX, concurrency, budget/work, wider link scope) for follow-up lanes.

## Verdict

CANDIDATE: 1171 91eff7e4363c251cd0ce2324c6654c55a626de35
VERDICT: ACCEPT
