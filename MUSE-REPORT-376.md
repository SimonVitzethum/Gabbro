# MUSE-REPORT-376: Independent exact-candidate A4 review of 338 ControlFlow

Lane 376, 2026-10-01. Review-only lane: owns only this report.
Candidate staged privately (owned module + additive umbrella import),
verified, then fully restored before this commit. Tree is clean apart
from this report.

## Candidate

Pinned HEAD `b28f9a8a3ef6cc857991ba7f404162f01c36f5f7` (base
`f737a6f04c22dfdd9499532e0535ad119cf2e56d`, per `.tmp/review/SNAPSHOT.json`).
PATCH touches exactly three paths: new
`grammatik/Grammatik/X86/ControlFlow.lean` (500 lines), one additive
import at the end of `grammatik/Grammatik.lean`, and `MUSE-REPORT-338.md`.
No off-limits file (checker, Spec, goal, Typen, Rust, emitter, docs,
friend OptimizationRules/OptimizationWitnesses) is touched.

## What was verified

- `./lean-probe grammatik/Grammatik/X86/ControlFlow.lean` with candidate
  staged in this clone: `0 error(s)`, all 29 `#print axioms` lines are
  subsets of `[propext, Quot.sound]` (several axiom-free).
- Full `./lean-bau` with candidate staged: `exit 0; 0 error line(s)`,
  `Build completed successfully (387 jobs)` (387 here vs 386 in the
  author evidence: my tree additionally contains SpillPrivate; the
  candidate's additive import merges by union).
- `gabbro_ziel` axiom probe with candidate staged: still exactly
  `[propext, Classical.choice, Quot.sound]`.
- `grep` for `sorry|admit|axiom |native_decide|unsafe`: only the English
  word "admitted" inside a CUTS comment. No `Prop`-typed premise; final
  probe shows no unused-variable warnings.
- Every referenced canonical name resolved against this clone's accepted
  sources: `Bedingung/bedingung` (Wort.lean), `laengeOk/ripNach/dispWort/
  effAddr/regSet/schritt_jump32/schritt_jumpIf32_genommen/
  schritt_jumpIf32_nicht/schritt_call32_erfolg` (Ausfuehrung.lean),
  `read64/write64/lesbar8/schreibbar8/writeBytes/writeBytesN/
  read64_nach_write64/writeBytesN_hit/addrOff_null` (Speicher.lean).
  No invented source behaviour, no duplicated evaluator: the three step
  helpers reuse (never re-implement) the 14-form `schritt` theorems for
  the direct-target equations, and add no `Befehl` constructor, decoder
  row, register, or memory model.

## Task delivery (all target-direction items present)

- SETcc: `setCCWort/setCCByte/setLowByte/setCCAnwenden` with upper-56
  preservation (`setLowByte_hoch/tief`) and flag/memory framing. Matches
  the physical narrow-8 rule (upper bits unaffected) and MOV-like flag
  preservation.
- Register CMOVcc: `cmovAnwenden/cmovSchritt` from pre-state source under
  the pre-state flag snapshot, flags/memory framed, RIP from decoded
  `Decodiert.laenge` gated on `laengeOk` only. No emitter length anywhere.
- Faulting CMOV-memory: `cmovMemSchritt` reads FIRST through
  permission-checked `read64`, then selects; `cmovMem_feheler_bleibt`
  keeps the fault on the untaken path. This matches real hardware (the
  memory operand is fetched regardless of the condition).
- LEA: `leaAnwenden/leaSchritt` writes the pre-state effective address,
  no memory touched, flags preserved. Correct: LEA performs no access.
- Direct target: `direktZiel rip len disp = ripNach rip len + dispWort
  disp` with reuse equations `direktZiel_jump32`,
  `direktZiel_jumpIf32_genommen`, `direktZiel_call32`, plus fall-through
  `direktZiel_jumpIf32_nicht`. Hand-checked arithmetic of the refusals:
  4096+5+2=4103 mid-instruction, +4091=8192 data, +100=4201 off-image,
  +0=4101 accepted start.
- Admission: `direktZielOk` is an explicit validator/profile `Bool` with
  `direktZielOk_garantiert` (start-or-entry), documented as NOT a
  hardware fault. No alignment invented; no stop renaming; no TSO, cost,
  time, termination, source, or gate/OS-contract claim.
- Witnesses: `cmov_witness_unterscheidet` (rax=20 under zf, rax=10
  without, condition `.e`) and joint memory-changing
  `cmov_speicher_zeuge` (flag-selected word stored at 8192, read back as
  20, byte observably changed from zero); joint `_zeuge` companions for
  every main theorem. Refusals proved concretely by `decide`, with the
  positive `ziel_anfang_akzeptiert`.
- CUTS block is truthful and complete; the report claims only the bounded
  helper scope. Nothing in the owner task text was found to be wrong.

## Non-blocking notes (suggestions, not defects)

1. `setCCWort` (line 16) is defined but never used; only `setCCByte`
   feeds `setCCAnwenden`. Dead helper: remove or use.
2. `cmovMem_feheler_bleibt` carries the untaken-path premise into the
   conclusion as a restated conjunct and covers only the false-condition
   case; the general fault-refuses fact (both condition values) and a
   taken-path value-selection success theorem (the analogue of
   `cmovSchritt_genommen`/`leaSchritt_erfolg` for the memory form) are
   not stated. The safety-critical no-speculation direction is proved.
3. German identifiers (`direktZiel`, `ziel_*_verweigert`, `witDunkel`)
   match the established pilot-vocabulary convention of the X86 subtree
   (`Zustand`, `schritt`, `lesbar8`); comments and docs are English.
   Consistent, not a violation in context.

## Open (remains with follow-up work, as the candidate states)

No decoder rows or `Befehl` constructors; no silicon correspondence;
`starts`/`eintraege` are checked inputs with an OPEN decoded-start
producer; no indirect-target certificates; no source/TSO/concurrency/
cost/time claims. Full final-byte/source/hardware correspondence stays
OPEN. The candidate's import line will union-merge with SpillPrivate in
current master (mechanical).

CANDIDATE: 338 b28f9a8a3ef6cc857991ba7f404162f01c36f5f7
VERDICT: ACCEPT
