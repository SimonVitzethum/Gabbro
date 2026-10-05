# MUSE-REPORT-1274: Independent exact review, rotates ROL/ROR/RCL/RCR

CANDIDATE: 1273 9341ac956e863b93c7b71bba56ff5303f67ec9eb

## Identity and material
- Reviewer clone `a1274`, branch `muse/1274`; this report is my only file.
- This is a re-review. The previous head `77780bb9` got REPAIR with one finding R1;
  that result is stale. The new pinned head `9341ac95` is one commit ahead
  ("repair R1 - REX.W overrides 66h in rotBreite", evidence record line 328).
- Reviewed material (staged in-clone at `.tmp/review/author-1273` for the new head):
  `PATCH.diff` (3 files), snapshot `grammatik/Grammatik/X86/IntRotate.lean`
  (2616 lines, +11 vs the previous snapshot), `MUSE-REPORT-1273.md` (notes the
  repair and the earlier review outcome), `OWNER-TASK.md`, `BUILD-EVIDENCE.json`.
- Base per snapshot: `738366545afbddf7ac664db92804703db24f8868`, snapshot flag clean.

## Re-review of finding R1 (repaired, verified)
- `rotBreite` wide case now tests `p.w == 1` first (line 1093, b64) and `p.op16`
  second (line 1094, b16): REX.W takes precedence, the silicon direction. Byte
  case unchanged (66h and REX.W both refused). Exact fix as requested.
- New decide pin `pin_rot_rexw_ueber_66` (line 1566) with an explicit doc comment
  crediting the review finding: `[102, 72, 209, 192]` decodes 64-bit, length 4.
- CUTS updated (lines 2457-2459) to name the precedence and its pin; the axioms
  ledger gained the matching `#print axioms` line (line 2552 in-file).
- Author evidence: re-probed green and `./lean-bau` green (659 jobs) after the
  repair, recorded in the evidence commands and the commit message. The encoder
  never emits the combination, so no round trip or pin could break; the pin
  proves the new behavior directly.
- No other semantic change: the delta old-to-new head is the reorder, the pin,
  its ledger line, and the CUTS/report notes.

## Carried-over checklist (re-confirmed on the new snapshot text)
1. Banned tokens: only the same four English-word doc-comment hits
   ("admitted"/"admit no successor", now lines 1097, 1973, 2034, 2043). No `axiom`
   declarations, no sorry/native_decide/sorryAx/unsafe. Pass.
2. File touch audit via the new PATCH.diff: exactly the same three files — new
   `MUSE-REPORT-1273.md`, one appended import line in `grammatik/Grammatik.lean`,
   new `grammatik/Grammatik/X86/IntRotate.lean`. Pass.
3. Axioms ledger per main theorem including the new pin, ending with
   `rotHw_zeuge`; CUTS block present and honest (dispatcher/adapter level only,
   no hardware correspondence, no W/GX bridge, open items named). Pass.
4. Lift-not-copy unchanged: `rotMaske` reuses `schiebeZaehler`; machine, register
   file, TSO, flags all reused; only family structs are new. Pass.
5. Premise hygiene unchanged: no discarded-hypothesis patterns. Pass.
6. Refusals unchanged and real (12 named decode refusals plus LOCK, length, and
   adapter-memory refusals as proven statements). Pass.
7. Witness `rotHw_zeuge` unchanged: joint over two cores with distinct family
   steps and value/flag pins, memory-form value, owner-only forwarded bytes,
   drain changing shared memory 0 to 3, HwWf, three refusals. Non-degenerate
   with a memory-changing step. Pass.
8. Silicon spots unchanged (opcodes, digits, masks, CF/OF-at-1, count-0 keeps
   flags) plus the now-correct 66h+REX.W combination. Pass.
9. Codec agreement unchanged (encoder emits no combined prefix; round trips and
   pins intact). Pass.

## Limitations (recorded, not outcome drivers)
- L1: no independent kernel re-execution. The pinned files are not in my build
  tree and my lane owns only this report, so the build wrappers were not run
  here; a green build of my own clean master would evidence nothing about the
  pinned head. Kernel-checked claims rest on author-recorded evidence
  (final probe 0 errors, full build 659 jobs green post-repair), cross-checked
  structurally by me.
- L2: no SDM extracts in this clone; silicon cross-checks use stable
  architecture facts.

## What remains open
- The CUTS-owned future work (decodeExt/stepExt hookup, per-access bridge,
  multi-byte drain agreement, SDM re-check) stays future work by design.

## Task remarks
- Nothing further wrong in the task. Staging the new snapshot with its pinned
  hash made this re-review possible without touching any foreign directory.

VERDICT: ACCEPT
