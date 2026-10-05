# MUSE-REPORT-1338: exact review of candidate 1337 (opcode ledger 80-BF)

CANDIDATE: 1337 c4434047fd69729d8004094b2e31f11741e2e0e6

## VERDICT: ACCEPT

## What was checked

Review clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1338`, branch
`muse/1337` author material used only as delivered files under
`.tmp/review/author-1337/` (SNAPSHOT.json, PATCH.diff, copied tree,
OWNER-TASK.md, BUILD-EVIDENCE.json). The pinned hash was never queried
(`git show/log/diff` on it untouched); `bad object` never arose.

Candidate file `grammatik/Grammatik/X86/OpcodeLedger1Byte80.lean` (1113 lines,
own namespace `Gabbro.Grammatik.X86.OpcodeLedger80`) read in full. Findings:

1. No `sorry`/`admit`/`axiom` declaration/`native_decide`/`unsafe`
   (dedicated grep over the candidate tree; the only `axiom` hits are the
   15 `#print axioms` lines). No `split_ifs`/`norm_num`/`ring_nf`.
2. `#print axioms` standard: count theorems depend on no axioms at all;
   `abdeckung_vollstaendig`, `modelliert_tag_ok`, `abgewiesen_tag_ok` and the
   pins depend only on `[propext, Quot.sound]` (subset of the goal triple,
   no `Classical.choice`). Verified live, see (8).
3. Existing files untouched except one appended import line: PATCH hunk
   `@@ -694,3 +694,4 @@` adds exactly
   `+import Grammatik.X86.OpcodeLedger1Byte80` to `grammatik/Grammatik.lean`.
   SNAPSHOT file list (report, Grammatik.lean, new ledger file; `clean: true`)
   matches the PATCH.
4. Every premise used, vacuously: all ~250 theorems are closed `by decide`
   with no premises; no Prop-typed premise, no `intro _`/`have _ :=`
   discard, no TARGET statement to hold fixed, no program-syntax premise,
   so rule 13 (inhabitation/`_zeuge`) is N/A. The ledger's "witnesses" are
   canonical byte strings with one checked theorem each, which is what the
   TASK paragraph asks for; the two-core/memory-step witness language of
   the CONTEXT/MECHANISM paragraphs belongs to a different lane kind
   (HwAdapter connection) and is N/A here.
5. Accepted evaluators lifted, not copied: the file only imports
   `HwKapsteinDecoder` (`kapDecode`), `IntCarryForms` (`decodeCarry`),
   `XchgOrderNeed` (`decodeXchg`), `AddressEncoding` (`decodeLea`) and
   states facts about them; no decoder is redefined. The 15 deferred pins
   (`pin_carry_*`, `pin_xchg_reg/mem`, `pin_lea`) check family-accepts /
   chain-refuses, so `zurueckgestellt` is a checked fact, not a comment.
6. Planted refusals really refuse: every non-`modelliert` row (all 195:
   `zurueckgestellt`, `verweigert`, `ungueltig64`, `fehlt`) carries a
   checked `kapDecode witness = none` theorem, and the two list-level
   agreement theorems (`modelliert_tag_ok`, `abgewiesen_tag_ok`) tie every
   row's recorded tag to the chain. Exact-once region coverage
   (`abdeckung_vollstaendig`: nodup ledger keys, 238 rows, all keys
   expected, nodup expectation) is checked, not asserted.
7. Silicon facts in the reason strings match the architecture:
   82Hx causes #UD in 64-bit mode; 9A invalid (CALL entry); Group 1A
   defines only /0 POP (8F /1-7 reserved); Table B-8 sreg3 110/111
   reserved (8C/8E /6-7); SAHF/LAHF marked `herstellerabhaengig`
   (CPUID LAHF_SAHF_64-gated) and kept FREE; vendor-neutral, no AMD
   provenance claimed (provenance stated as clone-local Intel SDM text
   only). Modelled-row family tags corroborate the author's probe
   evidence (TEST r64 = kern `testReg64`; B8 imm32 = kompakt
   `movImm32Zx`; REX.W B8 = breit `movImm64`; REX.W 89/8B = breit/
   kompakt MOV forms) and were re-verified live, see (8).
8. Live re-verification in this clone (current master `d72d633a`,
   i.e. NEWER than the author's base `574ac3d7`, so this also proves the
   candidate is not stale against the merged 1341/1342 ledgers):
   `./lean-probe .tmp/review/author-1337/grammatik/Grammatik/X86/OpcodeLedger1Byte80.lean`
   -> `== 0 error(s) in the COMPLETE output; exit 0`.
   `./lean-bau` (base, candidate not yet merged in) ->
   `Build completed successfully (707 jobs).`, exit 0, 0 errors.
9. CUTS honest and no over-claim: decoder ledger only; no execution
   semantics, no HwSchritt link, no W/GX bridge; prefix scope
   (ohne/REX.W whole region + REX.B over B8-BF + LOCK over 86/87 +
   66-prefix over 98/99; other REX combos, 67/F2/F3, VEX/EVEX not keyed),
   ModRM.mod/SIB/disp variants via witness + reason note only, and
   frequency grades declared judgement, not measurement. The report's
   `fehlt` product list (pervasive bare Group-1/TEST/MOV/LEA/NOP/POP,
   common MOV-imm8/string/LOCK-XCHG, deferred carry/XCHG/LEA wirings,
   28 design refusals, 40 invalid-in-64) matches the checked counts
   43/14/28/40/113 (total 238).

## Merger notes (not conditions)

- The candidate branched from `574ac3d7`; master has since appended 13+
  imports to `grammatik/Grammatik.lean` (1341/1342). The single import line
  must be re-appended at the CURRENT end (the merge script's Grammatik.lean
  import-union covers this).
- No `OpcodeLedger1Byte80.lean` exists in master (glob confirms only
  0F40/0F80/0FC0/1Byte00/1ByteC0/0F00), so there is no module collision.
- The author's remark on the owner task is endorsed: CONTEXT/MECHANISM
  describe an HwAdapter lane contradicting the TASK paragraph and the
  OWN ONLY list; delivering the ledger per TASK was the correct call,
  as was honouring the truncated line 25 by following the visible spec.

## Open / not claimed by this review

- I did not independently re-derive every SDM opcode-table cell by hand;
  silicon checking is per-reason-string plausibility against known x86-64
  facts plus the checked decoder facts. Full opcode-map completeness
  beyond `erwartetSchluessel` (e.g. whether the key space itself omits a
  legal prefix class the task wanted keyed) is taken as the author's
  stated scope limit in CUTS, which is explicit about what is not keyed.
- Final post-merge `lean-bau` with the import appended remains the
  merge gate's job; pre-merge evidence (probe green + base green) is
  complete from the review side.

New definitions/theorems by this lane: none (report-only review).
Last `./lean-bau` result line: `Build completed successfully (707 jobs).`
Anything in the task believed wrong: the CONTEXT/MECHANISM vs TASK
mismatch noted above; review executed per TASK + HARD RULES.
