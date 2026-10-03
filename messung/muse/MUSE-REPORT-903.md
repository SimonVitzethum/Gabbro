# MUSE-REPORT-903: exact review of author 753 (accumulator short ALU forms)

CANDIDATE: 753 cae1f67fad7b3fa4c7f7fc12531187b654e84e4b
VERDICT: ACCEPT

Acceptance is bounded: scope as stated in the candidate CUTS, no repairs required.

## Task

Review exact author 753 (Hardware completion: accumulator short ALU forms:
REX.W + 05/2D/3D, ADD/SUB/CMP RAX with sign-extended imm32, flag identity,
validator-decided short-vs-ModRM choice, pinned bytes, byte-facing execution
through the accepted ExtendedExecution dispatcher). Target theorems:
`CompactArithRax_verbindung` + companion
`CompactArithRax_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was inspected

- Pinned snapshot files in `.tmp/review/author-753/`: `OWNER-TASK.md`,
  `MUSE-REPORT-753.md`, `PATCH.diff` (1102 lines), `BUILD-EVIDENCE.json`,
  `grammatik/Grammatik.lean` (import line), full new module
  `grammatik/Grammatik/X86/CompactArithRax.lean` (990 lines, read in full).
- Official local manuals in `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`:
  Intel SDM combined volumes 1-4, edition 325462-093US September 2026,
  sha256 `a4a62e6a…f321`, verified 2026-10-02; Intel-profile scope, no AMD
  snapshot, no silicon claim).
- Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a903`,
  branch `muse/903`. Owned file only: this report. No source touched,
  no live controls used.

## Architecture findings (each checked, not just Lean-green)

- Byte forms: canonical `REX.W 0x48 ++ op ++ imm32 LE`, length 6. Opcodes
  05/2D/3D confirmed VERBATIM against the local reference text:
  `REX.W + 05 id  ADD RAX, imm32 ... sign-extended to 64-bits` (line 38710),
  `REX.W + 3D id  CMP RAX, imm32` (line 45280),
  `REX.W + 2D id  SUB RAX, imm32` (line 96941). Round trip
  (`roundtripRax`, general over op and suffix) plus three closed pins
  (ADD 1, SUB 256, CMP -1/0xFFFFFFFF) with pinned decodes.
- REX strictness: only 0x48 admitted; other REX bytes refuse
  (`rax_nichts_rex_anders`). Real hardware ignores REX.R/X/B bits on these
  ModRM-less forms, so this is OVER-refusal (incompleteness), which is the
  sound direction. Bounded acceptance, not a repair item. 16-bit (0x66) and
  32-bit (no REX) neighbours likewise refuse; 8-bit neighbours 04/2C/3C
  refuse explicitly. All honest under-approximations, documented in CUTS.
- Width/operands: 64-bit only, RAX implicit destination, imm32
  sign-extended via accepted `dispWort`. Source/destination/implicit
  operands match the SDM rows.
- Flags: SDM states for all three ops that OF/SF/ZF/AF/CF/PF are all set
  according to the result (lines 38765, 96996, 45330) — NO undefined flags
  exist here, so there is no undefined-state abstraction to get wrong.
  The module reuses the accepted `add64`/`sub64` snapshots and proves
  exact identity against the accepted ModRM arms
  (`rax_add/sub/cmp_flag_identitaet`: same flags AND same RAX value /
  register preservation, via `schritt_addReg64/subReg64/cmpReg64` with the
  sign-extended immediate staged in RCX). No invented determinism; AF is
  `some` exactly as the accepted arithmetic computes it, stated in CUTS.
- Pre-fault effects / memory order / permissions: the short steps touch no
  memory (`stepRax_speicher_bleibt` proved by case split over all three
  ops), so no permission is consulted and no fault/memory-ordering outcome
  exists on this path. Fetch still requires execute permission
  (`raxZugelassen_ausfuehrbar` over `ausfuehrbarN`) under the
  `fetchDekodiert` length-equation discipline. Correct.
- TSO/atomicity: register-only steps have no TSO footprint by construction
  (memory provably unchanged); the connection run's only store is the
  accepted pilot `store64` step. No per-access TSO bridge content is
  claimed; CUTS says so explicitly. No LOCK prefix is admitted (decoder
  requires 0x48 first), so no atomicity claim is needed.
- Feature/MXCSR/interrupt gates: none apply to integer ADD/SUB/CMP; the
  FpZustand lift (`stepRaxFp`) keeps XMM/FP control untouched and the
  connection theorem concludes `t2.xmm = t.xmm ∧ t2.fp = t.fp`. Correct.
- Canonical interaction: `decodeRaxCombo` tries accepted `decodeExt`
  first, short rows only on refusal (`decodeRaxCombo_kanonisch/erweitert/
  nichts`). Non-shadowing proved in BOTH directions and GENERAL:
  `pilot_weist_raxkurz_zurueck` (all short encodings refused by pilot
  `decode`, over any suffix), `narrow_weist_raxkurz_zurueck` (REX-set
  argument), `decodeRax_verweigert_pilot` (all 14 pilot forms refused by
  the short decoder, over any suffix), plus `pin_combo_pilot_ret`
  (accepted `ret` still decodes through the combo). Whole-chain refusal of
  short windows is pinned per closed form only
  (`ext_weist_add/sub/cmp_zurueck` by `decide`); the general
  arbitrary-immediate statement stays open and is HONESTLY listed in CUTS.
- Validator choice (`wahlSchritt`): Bool selects 6-byte short form vs
  ModRM route (mov imm into scratch + reg form, scratch `tmp ≠ rax`
  premise). `wahlStimmtUeberein` proves same RAX, same flags, same memory
  on both routes. Covers ADD only; SUB/CMP choice routes are not claimed.
  Bounded, matches the delivered theorems; no hidden premise.
- Premise use: every theorem's premises are consumed by its proof
  (checked by reading: flag identities rewrite all of h1/h2; the
  connection consumes hrax/hfetch1/hstep1/hfetch2/hwr/hstore/hles). No
  `Prop`-typed premise, no `intro _`/`have _ :=` (mechanical grep clean),
  no desired-simulation assumption: all connection premises are
  first-order facts jointly discharged in the witness.
- Witness: `CompactArithRax_verbindung_zeuge` is non-degenerate and
  memory-changing on closed values — RAX 41 → 42 from fetched bytes
  (6-byte short ADD + 7-byte spilling store = 13 image bytes at 4096),
  data cell 8192: byte 0 proved pre-state, word 42 proved post-state via
  `read64_nach_write64`. All eight connection premises discharged jointly
  (`hfetch1`/`hfetch2` by `decide` on actual bytes, `hwr`/`hstore` by the
  accepted write/store equations in witness shape). Genuine reached run,
  not an empty/deenerate one.
- Negative mutations: empty input, truncated tail, missing REX, wrong REX
  (0x49), ModRM opcode after REX, all three 8-bit neighbours — all refuse
  by `rfl`. Adequate for the claimed byte neighbourhood.
- Hygiene: mechanical grep over the pinned file finds NO `sorry`,
  `sorryAx`, `native_decide`, `unsafe`, or `axiom` declaration (only
  `#print axioms` lines and English "admitted"); `#print axioms` for all
  31 named theorems stays within propext/Classical.choice/Quot.sound per
  the pinned probe outputs (worst case `pin_combo_add` adds
  Classical.choice). Intermediate `sorryAx` seen in one mid-development
  probe was removed before the final commit; final probes are clean.
- Patch scope: exactly 3 files (`MUSE-REPORT-753.md`, one import line
  `import Grammatik.X86.CompactArithRax` appended to
  `grammatik/Grammatik.lean`, new module). No diagnostic/gift/example/CLI
  numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits,
  no friend-reserved optimiser files. CUTS block precise and complete;
  claim boundary ("canonical subset grounded in cited SDM tables, not
  silicon verification") is correct and matches REFERENCES.json scope.
- Build evidence (pinned `BUILD-EVIDENCE.json`): final `./lean-bau`
  `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed
  successfully (483 jobs)`; per-theorem `lean-probe` axiom lines all
  standard. One transient aggregate-root toolchain read error on the first
  `lean-bau` attempt was retried green and is apparatus noise, credibly
  reported. I did NOT re-run `./lean-bau`/`./lean-probe` myself:
  re-running them on this clone would build this clone's tree (which does
  not contain the candidate), and copying the candidate into this tree
  would violate OWN-ONLY; verification therefore rests on the pinned
  per-step build evidence plus the full line-by-line inspection above.
  Nothing inspected was suspicious enough to require re-execution.

## Last build result

Candidate-pinned final: `./lean-bau`: `== exit 0; 0 error line(s) in the
COMPLETE output`, `Build completed successfully (483 jobs)` (from
`.tmp/review/author-753/BUILD-EVIDENCE.json`). No build run in this
review clone (report-only lane; see above).

## What remains open (accepted bounds, all stated in candidate CUTS)

- SUB/CMP have step + flag-identity proofs but no fetched byte-level run
  (run pins ADD only).
- Whole-chain refusal of short windows pinned per closed form, not general
  over all immediates.
- REX over-strictness (only 0x48; hardware ignores R/X/B here) and no
  16/32-bit forms: completeness gaps, sound direction.
- Validator choice route proved for ADD only.
- No per-access TSO bridge content, no source/ABI/entry/budget/cost
  claims, no silicon correspondence.

## Notes on the task

- The task text is sound and needed no correction; the `ZEUGE:`
  inhabitation requirement is genuinely met (joint, non-degenerate,
  memory-changing).
- One task-wording observation: "validator-decided short-vs-ModRM choice"
  is delivered for ADD only — acceptable as a bounded increment, but a
  follow-up lane should state explicitly whether SUB/CMP choice routes
  are wanted.
- No guarantee weakening, no fake closure, no unsupported
  desired-correctness premises found. Nothing in the task asked for
  anything the candidate misrepresents.
