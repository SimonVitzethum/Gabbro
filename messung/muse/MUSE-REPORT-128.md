# MUSE-REPORT-128 — A formal semantics for five emitted C forms

Lane 128 (measurement lane for the translation-validation plan).
New file: `grammatik/Grammatik/CSemantik.lean` (782 lines).
`./lean-bau` green (full build, 64 jobs); `import Grammatik.CSemantik`
appended to `grammatik/Grammatik.lean`.

## 1. What I did

Built a small C-subset AST plus big-step semantics over a C memory model
shaped exactly like Gabbro's `Speicher` (`CMem := Nat → Nat → Nat → Int`:
table, index, field to machine integer), for the five most-used emitted
forms (picked from `BEWEIS.md` §1a census figures and the `Erhaltung.lean`
ruling table, since `zaehle-c-formen.py` cannot run here — see §6):

- **A** — `uint32_t` arithmetic with explicit width (binary `+ - * / % & | ^ << >>`,
  signed/unsigned, widths 8/16/32/64).
- **B** — array indexing with a checked index (`t->slots[i]`, bound-checked
  against the declared slot count).
- **C** — assignment to a struct field of a table slot
  (`t->slots[i].f = v;`, the exact shape `emit.rs` writes).
- **D** — `if`/`else` on C's nonzero test.
- **E** — the admitted counting `for` (`for (x = lo; x < hi; x++) body`).

UB inventory: each undefined/implementation-defined behaviour is an
inductive predicate, and the semantics returns `none` (stuck) there —
`ABinUB` (14 constructors: zero divisors unsigned/signed for `div`/`mod`,
`INT_MIN / -1`, signed overflow of `+ - *`, shift count outside
`0 ..< width` for `shl`/`shr`, shift of negative signed values,
signed bitwise operators), `IdxUB` (2: below zero, past slot count),
`CExprUB` (5: propagation ×2, operator fire, index-sub, index fire),
`CStmtUB` (8: index/value sub-UB, index fire, range fire, seq ×2,
condition UB, first-iteration body UB). A `Bool` checker (`cBinOk`,
`cOk`) agrees with the semantics by construction (`isSome`), giving
both directions: inventoried UB implies stuck, clean check implies
progress.

ONE correspondence theorem, `cCorr_assignSlot`: Gabbro `assignSlot`
(the smallest writing statement) and the emitted store reach the same
memory, under the emitter's range guarantee, from corresponding memories
(`corrMemW`: both `konto` cells agree). Generic over the declared C
integer type subject to the range premise.

ZEUGE (`cCorr_assignSlot_zeuge`, see §5): the correspondence on `refD`'s
write `konto[0] := 100` (einzahlen's body statement `refWriteStAt`),
jointly instantiating every premise, plus the non-degeneracy facts
(einzahlen writes `konto`; the reached run step `refSchrittB` fires
exactly that write).

## 2. New definitions and theorems (exact names)

Defs: `CWidth`, `CWidth.bits`, `cLo`, `cHi`, `CMem`, `CEnv`, `CGeom`,
`CBinOp`, `CExpr`, `cWrap`, `cBinApply`, `aEval`, `ABinUB`, `cIdxRead`,
`IdxUB`, `CExprUB`, `cBinOk`, `cOk`, `CStmt`, `cUpd`, `cForRun`, `cExec`,
`CStmtUB`, `cGeomRef`, `cEmitWrite`, `corrMemW`.

Theorems: `aBinUB_stuck`, `cIdxRead_stuck`, `cIdxRead_progress`,
`cBinOk_some`, `cBinOk_none`, `cOk_progress`, `aEval_none_of_ok_false`,
`cExprUB_ok`, `cExprUB_stuck`, `cStmtUB_stuck`, `cExec_assign_progress`,
`cExec_cif_progress`, `cForRun_exit`, `cForRun_progress`,
`cExec_cfor_progress`, `cRefIdx`, `cRefVal`, `cCorr_assignSlot`,
`cCorr_assignSlot_zeuge`.

`#print axioms` (in build log): everything rests only on
`propext, Classical.choice, Quot.sound` (the loop/operator-stuck lemmas
on `propext, Quot.sound`) — the same standard axioms the rest of
`grammatik/` uses. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## 3. Last `./lean-bau` result line

`Build completed successfully (64 jobs).` — green for the whole project
(`CSemantik.lean` builds as job 63/64).

## 4. Measurement (the actual lane deliverable)

Line counts are exact (section boundaries in `CSemantik.lean`):

| form | lines (semantics + UB + progress) | wall time | build-fix probes |
|---|---|---|---|
| shared (header, widths, CMem/CEnv/CGeom) | 60 | — (with skeleton) | — |
| A: uint arithmetic | 145 | ~4 min | 3 |
| B: checked index | 191 | ~7 min | 4 |
| C: slot-field store | 176 | ~7 min | 4 |
| D: if/else | 17 | ~2.5 min | 1 |
| E: counting for | 58 | ~2 min | 2 (+1 green restructure probe) |
| correspondence (refD store + zeuge) | 91 | ~5 min | 4 (+1 green zeuge probe) |
| CUTS + `#print axioms` | 44 | ~2 min | 1 |
| total | 782 | ~30 min hands-on (+~15 min full builds/probes) | |

What each iteration cost (recurring Lean-tax, all in the report for the
full-semantics planners): `cases ... with` naming on indexed inductives
(the unified indices are not counted — `case` + `rename_i` is the robust
idiom); pair-matches do not iota-reduce for `show`/`rfl` (use full `simp`
or single-side-known shapes); `Function.update` and `by_contra` do not
exist in this core (`cUpd` local, `Classical.em` splits); `rw` fails
where `rfl` succeeds (τ displayed as `refD.typ () ()` vs `.int 0 100`).

Extrapolation to all 64 forms. The five measured forms are the EASY ones
(first-order stores, no aliasing, no layout, no concurrency): mean
~117 lines/form, ~4.5 min/form, ~2.8 probes/form. The remaining 59 split
into three cost classes: (i) ~15 near-neighbours of the five (more
operators, `+=`, `++`, `while`-as-for, `return`, casts — same machinery,
≈100 lines each); (ii) ~20 medium forms (preprocessor/`typedef`/`enum`
declarations, `struct` layout with padding, `?:`/`&&`/`||` conditional
evaluation, `sizeof`, explicit casts with conversion ranks — each needs
new semantic machinery, ≈200–300 lines each); (iii) ~24 hard forms
(pointer arithmetic/index/deref/address-of need an aliasing memory model;
`volatile`/`_Atomic`/ordering need a memory model with observations;
`goto` needs continuations; `asm`/`__builtin_unreachable`/`restrict`
are proof exports, not semantics — each 300–600 lines, and (iii) decides
the memory model for everything). LOW (59 × easy mean, no new machinery):
≈7 000 lines, ≈2–3 lane-days. MID (15×100 + 20×250 + 24×450): ≈17 000
lines, ≈6–8 lane-days plus one memory-model redesign mid-way (the
(iii) model will not be this lane's function map). HIGH (with
layout+aliasing+observation model, per-form correspondence lemmas, and
the 30 open census slots ruled): ≈30 000 lines, several waves. The
binding constraint is not lines but the memory model: this lane's
`(table, index, field) → Int` map covers exactly the five measured
forms and must be replaced before the first pointer form.

## 5. The ZEUGE (rule 13)

`cCorr_assignSlot_zeuge` (CSemantik.lean:722). It instantiates ALL
premises of `cCorr_assignSlot` jointly (`ρG := refRho7`,
`ρC := fun _ => 0`, memories `(refM1B.weltVon 1, fun _ _ _ => 0)`,
`uint32`, both range facts by `decide`) on the non-degenerate program:
`refEin_schreibt ()` (einzahlen writes `konto`) and `refSchrittB` (the
reached D-machine step firing `konto[0] := 100`, i.e. a run with a step
that changes memory). No theorem in this file has a premise universally
quantified over Gabbro syntax (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/
`Expr`/`Args`) — quantification is over `CExpr`/`CStmt`/values only.

## 6. What remains open / what I believe is wrong in the task

- The task says "read the census output". The census
  (`zaehle-c-formen.py`) shells out to `cargo`, which is not installed
  on this machine (`FileNotFoundError`), and rule 1 forbids installs.
  I ranked the five forms from `BEWEIS.md` §1a + the `Erhaltung.lean`
  ruling table instead (`->` 704 sites, assignment/index/branch/loop
  rows). A re-rank against live census output is still owed.
- "Lean lines per form (semantics + UB + correspondence)": correspondence
  exists exactly once (for `assignSlot`), not per form — §4 books it
  separately. Per-form correspondence lemmas are the HIGH-estimate work.
- The task names the F-machine/PC-machine runs (`refB_erreicht`,
  `refB_pc_erreicht`); the witness uses the D-machine write step
  (`refSchrittB`), which is the direct memory-change evidence for a
  store correspondence. The F/PC runs prove surrounding machinery, not
  the store.
- `pruefe-englisch.py` is red on this branch (3 broken ratchets), but
  pre-existing: my diff touches only `grammatik/` and adds no German
  text. `pruefe-kennungen.py` passes; `pruefe-todo.py` cannot run here
  (needs `cargo`).
- CUTS (in-file, 8 items): later-iteration `for` UB not inventoried;
  signed-operand conversion gap; no checker-completeness direction;
  single-statement correspondence; no layout/aliasing/pointer forms;
  emitter width choice unpinned; local `cUpd`; no `by_contra`.
