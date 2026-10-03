# MUSE-REPORT-1022: Exact review of author 872 (Optimiser rule: LICM rule)

Lane 1022, clone `/home/simon/Dokumente/gabbro-muse/a1022`, branch `muse/1022`.
Owned file only: this report. No source touched, no live controls used.

## CANDIDATE

CANDIDATE: 872 dd5e1ea70bf15f36e5cd4a1e70cc93a3fd0aa274
(base `b040b155`, verified equal to this clone's HEAD; working tree clean).

Pinned snapshot (`.tmp/review/author-872/`): OWNER-TASK.md, PATCH.diff
(499 lines), review-copy of the new module, MUSE-REPORT-872.md,
BUILD-EVIDENCE.json, SNAPSHOT.json. The review-copy module (396 lines)
is identical to the PATCH hunk; the PATCH touches exactly 3 files
(`MUSE-REPORT-872.md`, `grammatik/Grammatik.lean` one import line,
`grammatik/Grammatik/X86/OptLicmLoop.lean` new). No friend-reserved
optimiser files, no diagnostic/gift/example/CLI numbers, no MARKE changes,
no source/checker/Spec/goal/emitter edits.

## Verdict

VERDICT: ACCEPT

(Bounded: see §Bounds. The substantive verdict is unchanged.)

## What was independently checked (real evidence, not Lean-green only)

1. **Task/DESIGN match.** DIRECT-COMPILER-DESIGN.md:519 row LICM
   (premise "invariance recomputed (exact-value, not rounded-value),
   non-faulting over hoisted inputs from rechecked source facts", cert
   "B+C", failure "hoist `x/n` above `n!=0`; hoist token op on shared
   access on local evidence", phase M) is implemented 1:1 as
   `LicmCert` (op kind + five recomputed Bools) with admission
   `licmZulassen` as their conjunction plus kind gate `licmOpOk`.
   DESIGN:310 (divide-error = hardware stop, LICM may never speculate
   it) is honoured: `licmDiv_wert`/`licmRem_wert` keep the M102
   premises (`0 ≤ x`, `1 ≤ y`).
2. **Semantics confirm the core claim.** `Semantik.lean`:712-714
   (`assignVar` reduces to `.ok σ (ρ.set ...)` — env-only, no world
   write) and :721-723 (`ite` reads guard carriers, branches on
   `wahr?`) confirm the author's "hoisted store is env-only" and the
   proof shape (`hA'` via `hRein` + `licmLeseLeer`, `hGuard'`,
   `hTaken`, `hInv'` into `simp [execBlock, execStmt, ...]`).
3. **Refusals cover both named failure cases**, each a proved
   `= false` theorem plus decided probes (one positive,
   `probe_licmZulassen_ok`; two negative, `divNein`/`tokenNein`):
   `licmVerweigert_tokenOp` (kind), `licmVerweigert_div`
   (`x/n`-above-`n!=0`, CE-2), plus `token`/`inv`/`facts`/`rundung`.
4. **All referenced names resolve at the base**: `execBlock`,
   `execStmt`, `wahr?`, `gleitPasst`, `gleitRechne`, `bruch`,
   `Zahl.div/rem`, `refD/refEin/refO/refP/refSp0/initB/MB`,
   `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`, `keinRuf`,
   `vertragVon`, `Var.hier/dort`, `Env.set/cons`, `Block.cons/nil`,
   `Stmt.assignVar/ite`, `RufErreichbarF/RufStartF` — each found in
   `grammatik/Grammatik/` (*.lean*). The witness's non-degeneracy +
   reached memory-changing run triple matches the established
   `ZeugnisStmt.lean` pattern on the same `refD` objects.
5. **Hygiene.** No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
   in the new file (only the English word "admitted" in comments);
   no Prop-typed premises; every premise of every new theorem is used
   by its proof (`hz` via `hInv hz`/`hGuard hz`; `hRein` via `hA'`;
   `hEq` via `hEq hz`; refusal hypotheses via `simp`). The witness
   supplies the conditional premises with `fun _ => rfl` where the
   equations hold by computation (env-var expression, no carriers;
   guard `4 <= 5` taken by `decide`) — legitimate, not a discard.
6. **Axioms/build.** BUILD-EVIDENCE.json records the full
   probe→fix→green transcript ending in `./lean-bau`
   `exit 0, 511 jobs`, with `#print axioms` inside
   `[propext, Classical.choice, Quot.sound]` (connection + witness
   use the full triple = `gabbro_ziel` standard; the rest
   `[propext]`/`[propext, Quot.sound]`).
7. **Hardware-manual dimension.** There is no byte-level x86 content
   in this fragment (source-level `Syntax`/`Semantik` rule, per the
   owner task's no-accepted-IR fallback), so REX/register/width/flag,
   TSO/atomicity and MXCSR review reduces to: nothing invented, no
   silicon/ABI/loader claims made, W/GX per-access bridge explicitly
   OPEN in CUTS. The concurrency argument (same carriers both
   orders, `licmOrte_gleich`; token ops refused by kind and flag) is
   sound at the carrier level and claims no more.

## Bounds (accepted weaknesses, not repairs)

- B1: connection conjuncts 2 (value equation, literally `hInv hz`)
  and 3 (`perm_append_comm` restatement) are assumed/restated; the
  proved substance is conjunct 1 conditional on validator premises.
  This is the task-mandated validator-side-condition architecture
  and is transparent in the proof term — bounded, not fake closure.
- B2: `licmGleit_behält` is a one-rewrite congruence of `hEq`; the
  IEEE substance sits in the validator's recomputation obligation.
  Transparent; cross-scope hoists are refused.
- B3: contract/call-log/budget/concurrency consequences in the §5
  comment are informal corollaries of the `execBlock` equality, not
  separate theorems; the formal `totalCost` inequality is OPEN.
  Theorem statements do not overclaim.
- B4: "loop" is a guarded `ite` region; `traverse`/`retry`/`forever`
  are untouched. The DESIGN CE-2 case is exactly a guard hoist, and
  the scope is disclosed in the author report and CUTS. Bounded.
- B5: no independent rebuild by this reviewer: applying the PATCH
  would dirty source files outside reviewer ownership, so the green
  build rests on the author's complete, internally consistent
  BUILD-EVIDENCE transcript (including two fixed intermediate
  errors) plus my base-level name/semantics/DESIGN verification.

## Open (unchanged from author CUTS)

Untaken path / dead-temp liveness; `sub`/`mul`/float/`div` syntax
windows; formal `totalCost` bound; trip-count reasoning; W/GX
per-access bridge; silicon/ABI/loader correspondence.

## Method note

`git apply --check` and `./lean-probe`/`./lean-bau` re-verification
of the candidate were not run: the former needs no verification
beyond the completed full-read PATCH↔file identity check, and the
latter two would require placing candidate source into this clone's
build tree, which the lane's own-only-report rule forbids. Two
`bash` invocations with pipe/`git apply` shapes were refused by the
permission classifier mid-review; simple `git status` confirmed a
clean tree. Nothing in the owner task appears wrong.
