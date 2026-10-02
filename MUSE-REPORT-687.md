# MUSE-REPORT-687: Exact review of author 686 (SSE2 integer and memory byte forms)

Lane 687, clone `/home/simon/Dokumente/gabbro-muse/a687`, branch `muse/687`.
Review-only lane. Owns only this report; no source file touched, no live
control used. Working tree clean except this report (verified by
`git status --short` before commit).

CANDIDATE: 686 bb8e5470cbb605d56c2a80602b350db5bce67a91

VERDICT: ACCEPT

Scope note (not part of the verdict line): bounded acceptance covers exactly
the 15 selected rows; the full hardware model stays OPEN per the candidate
CUTS, which is the correct claim boundary, not a silent closure.

## What was reviewed

The exact pinned snapshot in `.tmp/review/author-686/` (SNAPSHOT.json pins
head `bb8e5470`, base `f65be989`, clean, 3 files), OWNER-TASK.md (full text
recovered past the 2000-char preview cut by direct line slicing),
PATCH.diff, BUILD-EVIDENCE.json, and the candidate module
`grammatik/Grammatik/X86/VectorIntegerHardwareForms.lean` (2348 lines,
151 theorems, 41 defs/inductives). Spot-checked against the official local
manuals (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
Intel SDM 325462-093US) and the live producer APIs in this clone's
`grammatik/Grammatik/X86/` (Vektor, VectorCodec, VectorFootprints,
VectorHardwareProfile, ExtendedExecution, Speicher, Codec, Byteschritt,
Ausfuehrung, OverlapRefusal).

## Findings (all checked, no repair needed)

1. No forbidden tactics: zero word-boundary hits for `sorry`, `admit`,
   `axiom` (declaration), `native_decide`, `unsafe`; the 12 `admit` and 17
   `axiom` substring hits are English prose ("admitted rows") and
   `#print axioms` lines. No `intro _` / `have _ :=` discards.
2. Opcodes exact per SDM: PADDB/W/D/Q `66 0F FC/FD/FE/D4`, PAND/POR/PXOR
   `66 0F DB/EB/EF`, PSLLQ-reg `66 0F F3`, PSRLQ-reg `66 0F D3`,
   imm group `66 0F 73 /6|/2`, MOVDQA `66 0F 6F/7F`, MOVDQU `F3 0F 6F/7F`
   (verified at manual offsets, e.g. PADD table at Vol. 2B 4-200,
   PSLLQ `66 0F F3 /r`, MOVDQU `F3 0F 6F/7F`). REX subset is W=0/X=0
   only (bytes 64/65/68/69) and a canonical REX is always required;
   REX-less, REX.W/X, VEX, bare-0F, truncation and ModRM-confusion shapes
   are explicitly refused by proved `none` theorems. Refusing hardware-legal
   neighbors is the sound (admit-subset) direction and is documented.
3. Shift saturation correct: `vecShlQ`/`vecShrQ` zero the word for
   `COUNT > 63` with the count taken as `vLo` (low 64 bits =
   `COUNT_SRC[63:0]`), matching the manual's
   `LOGICAL_LEFT_SHIFT_QWORDS` pseudocode; `vecShlQ_satt_vs_maske`
   pins count-64-zeroes vs masked-shift-by-zero, plus a step-level
   negative (`intVec_neg_satt_null`) with a proved-nonzero operand.
   No scalar masked-count substitution.
4. Admission correct: `vektorLegacyZugelassen` = tier `paketInt128` AND
   silicon SSE2 AND CR0.EM/TS clear AND CR4.OSFXSR AND OS bit, with NO
   XCR0 input; `vektorLegacy_verfeinert` proves the accepted stronger
   674 gate implies it (via the existing `vektorHw_braucht_*` /
   `vektorHw_verfeinert` lemmas, all present in this tree), and
   `vektorLegacy_strikt` witnesses strictness (XCR0-SSE-clear admits
   legacy while the old gate refuses). Old over-strength is stated as a
   safe over-approximation, never as hardware fault. Task requirement met.
5. Execution honest: `stepIntVec` on shared `FpZustand`, lane arithmetic
   reuses `vecAdd`/`vecAnd`/`vecOr`/`vecXor` (per-lane effects at all four
   PADD widths via producer lemmas; logicals at `.b64`, width-independence
   honestly noted as unproved in CUTS), memory rows through the two ordered
   canonical chunk accesses (`vecWrite_aufgeteilt`, torn state stands, no
   atomicity claimed), alignment via producer `vektorGpFehler`
   (`a.toNat % 16 != 0`, verified in source), flags/GPRs/other-XMM
   preserved per row, imm8 round trips state `imm % 256` (no false exact
   claim), shared PXOR/PADDQ rows agree with accepted `decodeVector` /
   `stepVector` by `rfl`-level lemmas (byte-identical encodings,
   machine-checked). `decodeComboIV` chains `decodeExt` first with 7
   pinned `decodeExt`-refusal theorems (one per opcode group): no
   shadowing either way.
6. Witnesses genuine and non-degenerate: `intVec_joint_zeuge` chains four
   decoded steps (movdqu load, wrapping paddb lane0 `0x01+0xFF`, psllq
   imm8, movdqa store) with a `decide`-closed memory change at byte 18,
   frame byte 32 preserved (`vecWrite_rahmen`), xmm7 sentinel and flags
   preserved; `intVec_fetch_bridge_pin` goes through actual code bytes
   (`geholt`). Negatives cover saturation, #GP alignment, read AND write
   permission, feature gate, high registers (xmm8/xmm15 positive),
   VEX/bare-0F/truncation/ModRM confusion, overlap/tearing via the reused
   `vecFuss_teilueberlapp_verweigert`. Step-level control-register
   negatives exist only as equation-level refusals (`ohne_kontrolle` /
   `ohne_osxmm`); the step path funnels through the same gate lemma, so
   this is adequate, noted as residue, not a defect.
7. Scope discipline: PATCH touches exactly the 3 owned files (report,
   additive umbrella import line, new module); no producer, source,
   checker, Spec, goal, emitter or friend-reserved file touched;
   `simdFreigabe` untouched (single CUTS mention); CUTS lists the 15
   admitted rows, refused-by-absence neighbors, unmodelled YMM-upper /
   MXCSR / paging / interrupt / TSO / GX / source / budget state, and
   observed-absence flag provenance for MOVDQA/MOVDQU. No guarantee
   weakening, no desired-correctness premise, no fake closure.
8. Axioms/build: BUILD-EVIDENCE.json records final `./lean-probe` 0
   errors and `./lean-bau` green ("Build completed successfully (466
   jobs)"); all `#print axioms` outputs are within
   `[propext, Classical.choice, Quot.sound]`. Reproduction boundary
   (honest): as a report-only reviewer owning no source I did not
   re-apply the patch into this clone's build tree; verification is
   static inspection of the pinned snapshot plus the author's queued
   wrapper evidence plus independent manual/producer spot checks above.
   No suspicious case requiring a live re-probe was found.

## Last build result line

Author-evidence (BUILD-EVIDENCE.json, final entry): `./lean-bau` green,
"Build completed successfully (466 jobs)". Own tree: no Lean file changed
by this lane, so no own build was required; tree clean at `76c45e03`.

## What remains open (not claimed, correctly)

Full hardware-model closure (non-selected rows incl. memory-source
arithmetic and the 6F/7F register-move shape, YMM upper bits, MXCSR,
paging/privilege/interrupts, fault priority, TSO/GX per-access bridge,
source correspondence, budget/progress/call-log). All recorded in CUTS.

## Task notes

Nothing in the owner task or lane task is believed wrong. The owner's
honest recording of MOVDQA/MOVDQU flag provenance as observed absence
(rather than a quoted manual sentence) is the right call.
