# MUSE-REPORT-304: Independent review of candidate 288 (InvariantenOpt)

Lane 304, reviewer, independent from author 288. Model: opencode-go/muse-spark-1.3-contributor.
Reviewed snapshot: `.tmp/review/author-288/` (MUSE-REPORT-288.md, OWNER-TASK.md,
PATCH.diff, BUILD-EVIDENCE.json, candidate file copy). Pinned author HEAD
3208d01243eca25b44e718580ea36789f81222d8 is not fetchable in this clone
(`git show` on it fails), so the review was conducted on the exact snapshot
files, which is the authoritative candidate record here. No delegation, no
Rust work, no source/Spec/goal changes. Own file: this report only.

## What the candidate delivers (verified against code)

New file `grammatik/Grammatik/X86/InvariantenOpt.lean` (550 lines, confirmed
by `wc -l`) + one additive umbrella import in `grammatik/Grammatik.lean`
(PATCH.diff shows exactly these two code changes plus the author report;
no other files touched, no Spec/goal edits, no numbers, no MARKE).

Content, all against real `Syntax.lean` / `Semantik.lean` constructs:
- Executable checkers `alsLitOpt`, `litLeBool`, `litEqBool`, `isWahrAll`/
  `isWahr`, executable rewrite `foldAddLit`, scope tag `InvScope`
  (ruhe/sicht/wechsel), witness program `wD`/`wV`/`wCond`/`wIdx`/`wVal`/
  `wRest`/`wSonst`/`wFull`/`wWorld0`/`wO`/`wR`.
- Correspondence theorems: `alsLitOpt_lit`, `eval_alsLit`,
  `litLeBool_sound`, `litEqBool_sound`, `isWahrAll_sound`,
  `eval_foldAddLit` (rfl), `eval_weiter_n` (rfl), `exec_pruefung_wahr`,
  `exec_ite_wahr`, `exec_pruefung_inv`, `slot_read_stabil`.
- Witness facts `wit_schreibt`, `wit_isWahr`, `wit_elim`, `wit_step`
  plus eleven `_zeuge` companions, one per syntax-quantified theorem.

## Independent checks performed

1. `./lean-probe .tmp/review/author-288/grammatik/Grammatik/X86/InvariantenOpt.lean`
   (runs `lake env lean` from `grammatik/`, so imports resolve without
   copying anything into the tree): **0 errors**. Output also shows all 8
   `#print axioms` lines, each exactly
   `[propext, Classical.choice, Quot.sound]`. Report's axiom claim CONFIRMED.
2. Forbidden tokens: `grep` for `sorry|admit|axiom |native_decide|unsafe`
   over the candidate: none. Also none of `ensures|Ensures`,
   `intro _`, `have _ :=`, `MARKE`, `N[0-9]{3}`. CUTS block + 8
   `#print axioms` lines present at file end (lines 517-548). CONFIRMED.
3. Semantics cross-check against this clone's `Semantik.lean`:
   - `execBlock` `.pruefung` arm (line 857-859) evaluates the condition in
     the post-`lese` world and branches on `wahr?`; candidate's
     `exec_pruefung_wahr`/`exec_pruefung_inv` statements reproduce that
     world exactly, so the "exact trace transfer" claim is real, not
     assumed. `Stmt.ite` (lines 722-723) likewise. CONFIRMED.
   - `eval` for `.le`/`.eq` is `decide` over `.n` projections (lines
     245-246); the `litLeBool_sound`/`litEqBool_sound` bridge via
     `eval_alsLit` + `simp only [eval, wahr?, e1, e2]` is the correct
     shape. `eval` for `.slot` (line 220) reads `slots` at the index
     value; `slot_read_stabil`'s `rw [hidx]` step is legitimate.
     `eval_foldAddLit`/`eval_weiter_n` by `rfl` are plausible
     (proof-irrelevant bound proofs; `Zahl.weiter` preserves `.n`).
     All of these typechecked in my own probe run, which is the
     decisive evidence. CONFIRMED.
4. Witnesses and joint inhabitation: `wV.schreibt () = true` by `rfl`
   (contract writes the one table); `wit_step` closes a memory-changing
   run (`slot reads 5 afterwards`) by `decide` and typechecks, so the run
   is reached with a state change, not an empty run. All eleven `_zeuge`
   theorems typecheck; `exec_pruefung_wahr_zeuge` reuses `wit_elim`,
   `exec_ite_wahr_zeuge`/`exec_pruefung_inv_zeuge` instantiate on the same
   table-writing witness (`h := rfl` valid since `wCond = .wahr`
   computes). `slot_read_stabil_zeuge` uses the same world twice with
   `rfl` stability premises, which the author report discloses honestly
   (the discharging evidence is the stated separate obligation).
   Non-degeneracy gate HOLDS.
5. Genericity/boundaries: no per-program names, no `ensures` inference,
   no assumed transformation result (truth evidence is always a premise:
   computed `isWahr _ = true` or explicit `h` plus a `cases`-consumed
   `InvScope` tag, so an undischarged scope does not typecheck). No
   source-to-bytes, concurrency, cost, Folge, fault, atomic/MMIO claims;
   CUTS lists exactly these as OPEN. Multiplication folding refused with
   a checkable technical reason (four-corner range type not definitionally
   literal); `isWahrAll` has no `nicht` arm with the correct
   soundness-vs-completeness justification. Honest scoping, no weakening.
6. Owner-task coverage: check/branch elimination at the reached state
   (exec_pruefung_wahr, exec_ite_wahr), integer strength reduction in
   miniature (foldAddLit + weiter lemma; mul openly deferred), optional
   load-redundancy rule with explicit stability premises
   (slot_read_stabil), executable syntax transformation present,
   generic correspondences present, table-writing witness present,
   obligations as computable facts/premises at the right location.
   All mandatory deliverables present; the OPEN items are the ones the
   task explicitly leaves as separate obligations.

## Findings

- Trivial inconsistency, not a defect: report says `./lean-bau` gave
  "369 jobs", BUILD-EVIDENCE tail shows "368 jobs". Both say success;
  job counts vary with incremental state. The green full build is
  evidenced by the author's log; my own file probe (0 errors, correct
  axioms) plus the strictly additive change shape (new file + one import
  line) make a green full build the expected outcome. Per review rules I
  ran no full build for prose.
- No material defect found. No counterexample to reproduce: every
  report claim I could check mechanically (line count, error count,
  axiom triples, forbidden tokens, CUTS presence, patch scope, semantics
  equations, witness computation) held.

## Verdict

CANDIDATE: 288 3208d01243eca25b44e718580ea36789f81222d8
VERDICT: ACCEPT
