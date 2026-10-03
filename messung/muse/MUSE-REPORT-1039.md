# MUSE-REPORT-1039: Exact review of author 889 (Optimiser rule: division guard rule)

## Candidate and verdict

CANDIDATE: 889 9056176b48e6c2367de2eca043a8b245ac7efd5d
VERDICT: ACCEPT

- Author lane 889 at the pinned commit above; base b040b155 (matches this
  clone's HEAD at review time).
- Assessment: accept, bounded by the scope limits stated below.

## What was reviewed

Exact pinned snapshot/task/PATCH from `.tmp/review/author-889/`:

- `OWNER-TASK.md` (lane 889 task: DESIGN section 7 LICM row + section 3/3A
  obligations; `ZEUGE: OptDivGuard_verbindung` with joint companion).
- `PATCH.diff` (502 lines): exactly 3 files — `MUSE-REPORT-889.md` (new),
  `grammatik/Grammatik.lean` (one appended import line, additive only),
  `grammatik/Grammatik/X86/OptDivGuard.lean` (new, 400 lines).
- `MUSE-REPORT-889.md` and `BUILD-EVIDENCE.json` (probe history + final
  `./lean-bau` green at 511 jobs).
- Full text of the candidate module (all 400 lines read).
- Base modules the candidate reuses: `X86/MulDiv.lean` (refusal lemmas,
  `md_div_halt`/`md_idiv_halt`/`md_div_erfolg`, `falle_nie_rein`),
  `Semantik.lean` (`eval`, `Expr.orte`, `execEnd`/`Endblock.bind`),
  `Syntax.lean` (`weiter`/`div`), `ReferenzB.lean` (witness lemmas).
- Official local reference: `.tmp/HARDWARE-REFERENCES/` (Intel SDM combined
  volumes 1-4, edition 325462-093US, verified 2026-10-02; AMD unavailable,
  so no vendor-difference claim is possible or made).

Owns only this file. No source, import, or control file was touched.

## Architecture check (not just Lean green)

- No new decoder, byte tag, or evaluator: the target leg reuses the accepted
  `mulDivSchritt`/`divWeitU`/`divWeitS` vocabulary. The four reused refusal
  lemmas and the three step theorems were verified to exist in base
  `MulDiv.lean` (lines 82-104, 227-259, 331), and `./lean-probe` on that
  base file reproduces 0 errors here.
- Intel SDM cross-check (local extracted text, edition 093):
  DIV Vol. 2A 3-264 / IDIV Vol. 2A 3-448 — #DE when the divisor is 0 and
  when the quotient overflows (lines 50207-50241, 50257-50290, 58107-58183);
  "The CF, OF, SF, ZF, AF, and PF flags are undefined" for both
  (lines 50250, 58145); "A program-state change does not accompany the
  divide error, because the exception occurs before the faulting
  instruction" (line 165141). The candidate's `hardwareHalt`-with-no-state
  modelling and its never-speculate/never-hoist rule match all three points.
  64-bit RAX:RDX implicit-operand forms are the base owner's scope; this
  lane adds no width/REX/ModR/M claim, which is honest, not a gap it hides.
- Undefined-state discipline: the "DIV keeps flags" lemma
  (`divGuard_div_flags_bleiben`) is proved from the accepted
  `md_div_erfolg` successor, which preserves the whole flag snapshot. Per
  the SDM the DIV flags are undefined, so "keeps" is one allowed
  refinement inside the model, and the lane claims only the no-FP-visible
  half (`keinGleitErsatz` at machine level). Integration must keep reading
  DIV flags as undefined (the `Ganzzahl`/`MulDiv` discipline), not as
  defined-kept values. Noted as a boundary, not a repair: the lemma states
  model preservation, nothing about silicon flag contents.
- Memory/TSO/atomicity: the connection concludes `orte = []` on both
  windows (verified against `Semantik.lean` lines 168-171: `weiter.orte =
  e.orte`, `div.orte = a.orte ++ b.orte`, all `lit` so `[]`), i.e. the rule
  moves no shared access. No TSO/GX bridge is claimed (explicit CUT).
- Pre-fault effects: `divGuard_null_halt`, `divGuard_ueberlauf_halt`,
  `divGuard_idiv_null_halt` are direct applications of the accepted halt
  theorems; speculation above the guard is refused by decided-Bool legs,
  never warned through. No `ensures` is derived anywhere.

## Premise use, witnesses, negative mutations

- Mechanical grep of the candidate for `sorry|admit|axiom|native_decide|
  unsafe` (word boundaries): zero hits (earlier substring hits were only
  English "admitted"). No `Prop`-typed premise; no `intro _`/`have _ :=`.
- The three `rfl` conjuncts of `OptDivGuard_verbindung` were checked against
  `Semantik.lean`, not taken on trust: both `.n` values reduce to
  `x.tdiv y` (`Zahl.div` computes `tdiv`; `Zahl.weiter` re-wraps); both
  footprints are `[]`; `execEnd` over `Endblock.bind` with equal footprints
  and definitionally equal bound values is definitionally equal for
  arbitrary oracle/budget/callee-resolver/continuation — that generality IS
  the claimed preservation, not a vacuity. `h0`/`h1'` are load-bearing for
  well-typedness (no well-typed `div` exists without them); `cert`/`hz`
  gate `hEq`; `hW` feeds `divGuardWort`; `eF` closes the float conjunct.
- Witness `OptDivGuard_verbindung_zeuge`: jointly instantiates every premise
  (`7/2 -> 3` by `decide`, `leave` continuation, float site `(3/4)/1`),
  on non-degenerate `refD` (`refEin_schreibt`, verified at
  `ReferenzB.lean:123`) beside the reached memory-changing F-run
  (`refB_erreicht`, `refB_schreibt`, verified at lines 987/1007: slot
  `0 -> 100`). Name matches the `ZEUGE` target with `_zeuge` suffix.
- Negative mutations are real: five `decide` probes covering each false
  cert bit, two planted zero-divisor probes (`istHalt ... = true`,
  `zugelassen ... = false`), and the `7/2=3` / `7%2=1` anti-floor probes.
- Axioms per author build evidence: everything within
  `propext, Classical.choice, Quot.sound`. No new axioms possible by
  construction (no `axiom` command in the file).

## Claim boundaries (precise, and the acceptance is bounded by them)

CUTS in the file match the proved content: no signed-division window
(`sdiv`/`srem`); no branch-hoist equation with `Stmt`/branch semantics —
the only certified "motion" is the value-preserving guarded window with the
check kept at its site; no formal level-(c) machine-work bound (open per
IR-VALIDIERUNG lane 278); no silicon correspondence, TSO/GX bridge, or
ABI/loader claim. The float conjunct is an unrelated-site
non-interference equation closed by the admitted-site premise — thin but
accurately described, not closure over float optimisation. Ownership
hygiene is clean: no friend-reserved optimiser files, no
source/checker/Spec/goal/emitter edits, no new diagnostic/gift/example/CLI
numbers, no emission-counter change.

## Reproduction

- `./lean-probe grammatik/Grammatik/X86/MulDiv.lean`: 0 error(s) in the
  COMPLETE output, exit 0 (reused foundation re-verified on base).
- Candidate build evidence (`BUILD-EVIDENCE.json`): final `./lean-bau`
  `Build completed successfully (511 jobs)`; intermediate probe errors
  during authoring were repaired before commit (placeholder inference,
  invalid projection, unused-variable warnings), which reads as genuine
  incremental development, not pasted green.
- The candidate file itself was NOT rebuilt in this clone: this review owns
  only `MUSE-REPORT-1039.md`, so the module was verified by exact-text
  inspection plus foundation reproduction. The serial merge gate rebuilds
  the exact commit anyway.

## Remarks on the task

Nothing in the task was found to be wrong. The DESIGN section 7 LICM row is
a motion rule and the lane certifies only the guarded same-site window
rather than branch hoisting; that reduction is honestly recorded as CUT, so
follow-up lowering work (branch-hoist equation, `sdiv`/`srem`, level-(c)
bound) stays open without blocking this rule's bounded acceptance.
