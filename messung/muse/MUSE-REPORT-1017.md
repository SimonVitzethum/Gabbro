# MUSE-REPORT-1017: Exact review of author 867 (range-check elimination rule)

CANDIDATE: 867 050d19147479d21b83e630e05a87bb9474838d1b
VERDICT: ACCEPT

The acceptance above is bounded; the scope notes below are non-blocking
and do not change it. The substantive verdict and findings are preserved
from the reviewed pinned snapshot.

Base `b040b155159f47629542b0083e2f0a8a607f2b4c` matches this clone's HEAD
(`b040b155` merge: Muse 975 direct-x86 foundation). Patch files:
`MUSE-REPORT-867.md`, `grammatik/Grammatik.lean` (one import line appended
after `ComposeImageFetch`), `grammatik/Grammatik/X86/OptRangeElim.lean`
(new, 195 lines). No other files. No diagnostic/gift/example/CLI numbers,
no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
friend-reserved optimiser files (`OptimizationRules.lean`,
`OptimizationWitnesses.lean` untouched).

## Scope (what this candidate is and is not)

DESIGN section 7 row (`DIRECT-COMPILER-DESIGN.md:516`) is one row,
"Range/bound/overflow-check elimination", split across three lanes:
867 range (this candidate, `Block.narrow`), 868 bound, 869 overflow
(`DIRECT-COMPILER.md:545-547`). The author's CUTS exclusions
(`pruefung` connection, overflow-guard elimination, level-(c) totalCost
inequality, silicon/TSO/ABI) are therefore sibling-lane or later work,
not gaps in this lane. The owner task explicitly permits the real
Syntax/Semantik fragment until the single accepted IR lands; the
candidate stays at the source `execBlock` outcome level and claims no
byte forms. Hardware checklist reduces accordingly: the rewrite removes
a pure integer test, adds/removes no store, no register/flag effect, no
shared access, no handler interaction — both sides read `e.orte`
through the same `lese`. No hardware claim is made; CUTS excludes
silicon correspondence, TSO/GX bridge and ABI/loader.

## Independent verification (pinned snapshot + this clone's base)

- Proof step checked against the real equation: `Semantik.lean:852-856`
  defines narrow as `if h : lo' ≤ v.n ∧ v.n ≤ hi' then
  (execBlock rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf else …`.
  The candidate's `simp only [execBlock]; rw [dif_pos (hRegel hz)]`
  matches this equation exactly, including the `.schrumpf` and the
  anonymous-constructor value shape. The equation is a genuine (one-step)
  semantic consequence, not a restatement of a premise: `hRegel` supplies
  the range fact, the conclusion is the outcome equality.
- `hRegel` (validator-recomputed at-site range fact, conditional on
  admission `hz`) is a consumer-side proof obligation, openly declared as
  the file's interface ("this file is its interface", CUTS). This is the
  same admitted-validator pattern as accepted sibling
  `X86/OptFoldConst.lean` (`foldZulassen` gate + refusals + probes +
  admitted connection + joint witness). Not a desired-simulation
  assumption, not guarantee weakening: without admission no `hz` exists
  and the connection cannot fire.
- All major premises used: `e/sonst/rest/σ/ρ` occur in the goal's
  `Block.narrow`/both outcome sides; `V/O/passes/R/l/Γ/Λ/Λ'` in the
  `execBlock` applications; `lo/hi` in `e`'s type; `lo'/hi'` in the
  narrow site and `hRegel`; `c` in `hz`/`hRegel`. No `intro _`,
  no `have _ :=` discards. No `Prop`-typed premise.
- Witness `OptRangeElim_verbindung_zeuge` is joint (single existential
  over ALL premises) and non-degenerate: literal `3` narrows into
  `0..10` with `Endblock.leave` else-branch and `Block.nil`
  continuation (constructor usage matches `SonstLeaveZeuge.lean:34`;
  `eval | .lit n` gives `⟨n, refl, refl⟩` per `Semantik.lean:215`, so
  `(fun _ => by decide)` discharges `0 ≤ 3 ∧ 3 ≤ 10`); program side is
  `refD` with writing leaf (`refEin_schreibt`, `ReferenzB.lean:123`);
  run side is reached `MB` (`refB_erreicht`) with real memory change
  (`refB_schreibt`, slot `0 -> 100`). All names verified present in
  this clone's base (`keinRuf` `Maschine.lean:383`, `vertragVon`
  `Syntax.lean:641`, `initB`/`MB`/`refSp0` in `ReferenzB.lean`).
- Negative mutations: four `decide` probes (admit-all pass + one per
  refused bit) plus three refusal theorems, one per gate bit
  (`extentAmOrt`, `einmalGebunden`, `keinSchreiberDazwischen`). Both
  DESIGN failure cases (entry invariant across a writing call; entry
  invariant removing a check inside the writer's own mutating loop) map
  to the one writer bit; the validator's duty to SET that bit in both
  shapes is consumer-side B+C work, already booked as such in CUTS.
  The author's decision not to duplicate an identical second theorem is
  reasonable.
- Forbidden tokens: grep over the pinned file finds no `sorry`,
  `admit` (only the English word "admitted" in a comment), `axiom`
  (only required `#print axioms` lines), `native_decide`, `unsafe`.
  Axiom report in build evidence is exactly the standard set for the two
  main theorems (`propext, Classical.choice, Quot.sound`), `propext`
  for refusals, none for gate/probes.
- No build was run in this clone: the review owns only this report
  ("no source or live controls"), the candidate file does not exist in
  this clone, and a base-only `lean-bau` would add no candidate signal.
  Evidence relied on: author's `BUILD-EVIDENCE.json` (`lean-probe`
  `0 error(s)` at each stage; `lean-bau` `exit 0`, `511 jobs`,
  `Built Grammatik.X86.OptRangeElim`) plus the equation-level and
  name-level verification above, performed by hand against this clone.

## Bounded acceptance (what ACCEPT does not cover)

1. Byte-facing preservation, fetched execution, TSO/atomicity leg: open
   by design; the equation stops at source `execBlock` outcomes.
2. `pruefung` (where-condition) removal and overflow-guard elimination:
   lanes 868/869 territory, per the lane split.
3. Formal level-(c) machine-work/totalCost inequality: open per CUTS
   (the removed test is fuel-free inside `execBlock`; the static
   `KostenG` narrow cost is a separate accounting).
4. The validator's B+C recomputation behind `hRegel` (at-site extent
   over the once-bound name incl. N571/N463/N506 shapes; duty binding
   with no intervening writer): consumer obligation, pinned as the
   file's interface, not proved here.

## Remarks (non-blocking)

- The connection's doc gloss ("step-budget accounting is unchanged")
  is true at the `execBlock` fuel/passes level (narrow consumes no
  fuel) but could name the static `KostenG` cost explicitly to avoid
  misreading; CUTS already excludes the formal cost bound, so this is
  a wording suggestion, not a repair.
- Nothing in the owner task turned out wrong. The `ZEUGE:` target
  (`OptRangeElim_verbindung` + `_zeuge`) is delivered exactly;
  no target-statement latitude issue (rule 12) arises.

## New definitions/theorems by this reviewer

None (report-only review). Candidate's items reviewed:
`RangeElimCert`, `rangeElimZulassen`,
`rangeElimVerweigert_ohneAusmass/_zweitbindung/_schreiberDazwischen`,
`probe_rangeElimZulassen_ok/_ohneAusmass/_zweitbindung/_schreiber`,
`OptRangeElim_verbindung`, `OptRangeElim_verbindung_zeuge`.

## Last build result

No `./lean-bau` run in this clone (see above). Author's pinned
evidence: `./lean-bau` `exit 0`, `0 error line(s)`,
`Build completed successfully (511 jobs)`.

## Open

Integration of candidate 867 (merge + publication checks) is the
coordinator's serial business, not this review's. Follow-up work lives
in lanes 868/869 and the consumer-side B+C validator.
