# MUSE-REPORT-180: counterexamples for handed-over obligations

Lane 180 (PLAN-ZIELSATZ.md §9). The command is `gabbro counterexample|gegenbeispiel
<file.gab> [fn]`; the report it prints is a Lean file, and every number below was
recomputed from a green `lean-probe` run, not read off the searcher.

## 0. Result

For each function of a program `gabbro lean-g` accepts, the tool searches inputs
(parameters in declared ranges, table slots in field ranges) -- exhaustive while the
space fits 2048, deterministically sampled (512, fixed seed) above -- and prints the
`lean-g` export plus a section that runs every candidate through the EXPORTED
program's Lean semantics (`rufAt` for the contract verdict, `execEnd` for the
witness) via `#eval`, with a kernel-checked `example ... := by decide` per hit
(verdict, `requires`, every `ensures` conjunct). A wrong `ensures` yields confirmed
counterexamples; a right one yields "none found", never "proved".

## 1. What was built, and where (CLI, not a script)

`crates/gabbro-check/src/gegenbeispiel.rs` (new) + `gabbro counterexample|gegenbeispiel`
in `crates/gabbro-cli/src/main.rs` + `crates/gabbro-check/tests/gegenbeispiel.rs`
(7 tests) + register lines in `fahnen.rs`/`erstnamen.rs` + visibility/`analysiere`/
`ensures_konjunkte` in `lean_g.rs`. No new diagnostic codes (the `LG` refusals are
reused unchanged), no gift or example touched, probe units live in untracked `.tmp/`.

A Python script would re-derive parameter ranges (constants inlined, aliases
resolved), field ranges and per-conjunct `ensures` terms by scraping the export text
-- a second register over the same facts, drifting at the first exporter change.
In-crate code reuses `Model`, `CheckedFn` and `tr_ensures` directly and succeeds
exactly where `lean-g` succeeds. Either spelling is equally outside the trusted
base: every searcher verdict is re-checked by the kernel.

## 2. Computability (checked, not assumed)

`execEnd`/`rufAt` (`Semantik.lean`) are computable `def`s: `rufAt` recurses on its
fuel argument, `execEnd`/`execBlock` on the block. The computable path needed no
detour -- nothing on it is `noncomputable`. The oracle the file constructs is the
trivial one, and it exists only because the export sets `Ax/Reg/Glob := Empty`
(`where`-form with full binders, as in `BlattGegenbeispiel.lean`'s `O1`; the
anonymous-constructor short form does not elaborate). Searcher and file share one
fuel (`--fuel`, 64): a deeper call chain reads `abstieg` on both sides.

The confirmations are kernel `decide` over `Bool` verdicts (`rfl`-equivalent cost:
the kernel still evaluates `rufAt`). No `native_decide`, no `bv_decide`, no axiom --
PLAN §9's `ofReduceBool` caveat does not apply here. (Hygiene note, measured: a
`#eval` over a `sorry`-poisoned definition does not just fail, it panics the Lean
compiler backend (LCNF `explicitBoxing`, unreachable-code panic on this toolchain).
One more reason the verdicts that count are kernel-checked, not merely evaluated.)

## 3. What buys the reliability

The searcher is a small surface-AST interpreter mirroring `eval`/`execStmt`/
`traverseLauf`/`rufAt` (unbounded integers, `Nat` bit operations on nonnegative
operands, shifts as `*`/`/` by powers of two, the traverse invariant checked every
round with `.logik .schleife` on failure, `old()` at frame entry). It is dumb on
purpose: a form it cannot model skips its candidate LOUDLY (counted in the summary),
never silently. Division never reaches it (`tr_binaer` refuses it, `LG003`).

The confirmation buys the reliability: every predicted hit is re-executed by the
kernel on the concrete input. A false positive fails the file LOUDLY (red, never a
wrong report); a miss stays what the tool says -- "none found", never "proved".
Misses stay auditable: every candidate carries the Lean-computed `#eval` beside the
searcher's comment, and §4 checks they agree on every candidate, not just the hits.

## 4. Probes (wrong `ensures` must hit, right ones must not)

| probe | fragment | candidates | hits | Lean check | agreement |
|---|---|---|---|---|---|
| `result > x` for `return x` | pure int | 4 exh | 4 | 0.7 s | exact: 4×(t=true, q=true, c=false) |
| `result == x` | pure int | 4 exh | 0 | 0.3 s | exact: 4×t=false |
| `if`, `result == 0` | `wenn` | 6 exh | 3 | 0.7 s | exact (9 true / 6 false decompose) |
| slot write, `== 7` | slots, index | 512 samp | 468 | 25 s | exact |
| slot read, `result == slot` | slots | 242 exh | 0 | 5.4 s | exact |
| `locks` block, `== 7` | `locks` | 512 samp | 512 | 40 s | exact (1024 true / 8 false) |
| `old(slot) <= slot`, write `b` | `old()` | 512 samp | 227 | 18 s | exact (739 true / 293 false) |
| `let y = doppel(x)` in a block | calls | 10 exh | 4 | 1.0 s | exact (14 true / 10 false) |
| `traverse`, `== 99` | `traverse` | 1331 exh | 1331 | 3 m 0 s | exact (2662 true / 8 false) |
| callee violated through a caller | derived hits | 1491 (512+512+467) | 933 | 1 m 2 s | exact (2424 true / 566 false) |

"Exact" means the full `#eval` output was counted, not windowed: every
searcher-HIT is a Lean-`true`, every searcher-clean a Lean-`false`, every `requires`
a Lean-`true` -- on all candidates including the 470 caller runs that die in the
callee's violated contract (they read `false` for their OWN `ensures`, §6). The
witness reads as designed: input, `requires = true`, `Ergebnis: 3`, `Endzustand:
3, 0`, the failing conjunct `= false` -- a human sees whether the code or the
promise is wrong.

Cost model, measured: the Rust search is milliseconds (104: 17 ms); Lean pays
~20 ms per candidate (elaborate + compiled `#eval`) plus ~50-135 ms per hit
confirmation (kernel `decide`, heavier over `traverse` bodies). Full witness
(result, end state, every conjunct) is emitted for the first 8 hits per function
(`--hits`); every further hit still gets its `t = true` + `q = true` confirmations.

## 5. Corpus (the 9 programs `lean-g` exports)

| program | candidates | confirmed | Lean check |
|---|---|---|---|
| 104-referenz (`einzahlen`+`lies`: ptr/index params, `old()`, a call) | 1024 samp | 0 | 28 s, 1024/1024 agree |
| 108, 118, 119, 15, 16, 62, 69, 73 | 0 (no function carries an `ensures`) | 0 | ~0.3 s each, green |

Eight of nine exportable programs have nothing the tool could violate: their
functions carry no `ensures` (118/119's properties are lock invariants -- the
separate family `gS`, see §6). The corpus measurement is therefore thin by
construction, and the probes of §4 carry the lane, not the corpus.

## 6. Findings (all fixed or booked)

1. **The classifier counted the wrong function.** First shape matched ANY
   `.nachbedingung`, so a caller dying in a callee's violated contract read
   `true` with no confirmation and no count. Found by counting true/false
   against the model instead of eyeballing green. Now `| .logik
   (.nachbedingung f) => f == g_<fn>` (`GFn` has `DecidableEq`).
2. **Three Lean-shape facts, each measured, not guessed:** a bare `fun`
   inside `{ … }` swallows the following comma (parenthesize); `Env` values
   go through dot-notation `.cons`/`.nil` with the `def` ascription (never
   named `D` arguments); the oracle goes through the `where`-form.
3. **Boundaries the tool inherits from the export (all stated in the file,
   none hidden):** `requires` is `.wahr` -- every input satisfies it, still
   kernel-checked; `invs := []`, so only `ensures` violations are searched;
   `ensures` sides take no arithmetic (`tr_side` refuses it -- the searcher
   never sees such a clause); an `ensures` cannot read a table taken in a
   body `locks` block (its context holds only signature locks -- a function
   that takes its guard in the body and promises over it is unexportable).
4. **A checker gotcha, not a tool bug:** a `traverse … over slots of T`
   domain reads the TABLE (`reads T`, as in 122-matrix), not `T.slots`.

## 7. Gates

- `./cargo-pruef`: exit 0, 0 failing (7 new `gegenbeispiel` tests; the
  `fahnen`/`erstnamen` registers extended for the command, the pair, and the
  five flags -- including the byte-identical `counterexample`/`gegenbeispiel`
  run).
- `./lean-probe`: green over all ten probe files and all nine corpus files
  (table above; full outputs counted in §4).
- `./lean-bau`: not run -- no tracked Lean file changed.
- Untouched, as tasked: no diagnostic codes (only reused `LG`), no gift or
  example file changed, corpus files read-only, scratch in ignored `.tmp/`.
  English throughout the code and this report.
