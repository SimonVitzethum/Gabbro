# MUSE-REPORT-174: lean-g exporter aligned with the model

Lane 174. Both verdicts of 2026-09-14 read
(`messung/URTEIL-OPUS-2026-09-14.md`, `messung/URTEIL-MUSE-2026-09-14.md`);
the work is `crates/gabbro-check/src/lean_g.rs` (`gabbro lean-g`) plus
tests in `crates/gabbro-check/tests/lean_g.rs` and a one-line comment in
`crates/gabbro-cli/src/main.rs`.

## 0. Measurement first: where the exporter sieves

Static heuristics over the 105 tracked `beispiele/*.gab` (text patterns,
comments stripped) ordered the work; `zaehle-kette.py` column (b) confirms
the result (§2).

Item-level forms with no G counterpart (stay refused, LG001): `extern fn`
30, `static` 28, `assume` 16, `device` 13, `opaque type` 10, `atomic` 10,
`entry` 6, `format` 5, `divergent fn` 5, `library` 5, `spec fn` 3, `axiom` 3,
`check` 3, `global` 2, `accumulates` 2, `const fn` 2, `arena` 2, `raw`/
`prim`/`group` 1 each.

Statement/type-level forms (of 105): `let` 41, `if` 30, calls ~35,
`locks` blocks 18, `match` 17, `return` of a call 17, `traverse` 12,
compound assignment 11, `return` of arithmetic 11, `narrow` 13,
`let…else` 13, `retry`/`forever` 7 each, `leave`/`next` 6.

27 files have no hard item blocker. Of those, hand-read to the end, the
files blocked *solely* by the widened forms are 119 (`locks`), 15
(`bool` + `own`), 16 (`bool`), 62/69 (bit ops, conversions, limit words,
tableless), 73 (sugar conversions/limits, tableless). Everything else in
the 27 dies on a form outside this lane: shared locks (10, 13), records
(21, 32, 56), `bool` + `+=`/traverse-over-pointer/invariant (19, 46),
`deadline`/`count` (71), table `ops`/invariants/op-calls (47),
`tree`/`option`/non-table traverse domains (18, 53, 55), `tagged`/`match`
(34, 120), `breaking` (53, 55), array-`const` (123),
library/translator/profile (101), `narrow` (26, 32), return-of-call (21).

## 1. What was built

Subset held sets + floors: `RufPasst.hh` is now the subset; `boden` per
function is the minimum rank its own body takes in `locks` blocks, or
`none`. `hx`/`hb` print explicitly on every call (witness/`hn`-absurd/
`hL`-absurd branches for `hx`, witness/contradiction for `hb`); `hw` is
generation-checked; anything unprovable is refused LG004 naming
`hh`/`hx`/`hb`/`hw`.

In widening order: `locks` blocks (exclusive, rank-checked `H006`;
`shared` refused), `if`/`else` (incl. `else if`; tail-`if` needs
return-free branches, mid-`if` returns through `Stmt.ret`), `traverse`
over `slots of T` (mode/`decreases`/`touches` ledgered as static
annotations; invariant translated or refused; `.wahr` where none stands),
`let` (pure values bind anywhere, ascribed with the computed type;
call-valued `let` only in blocks via `bindCall`), `let…else` with a
reason (`bindCallElse`; `gruende` is the `reason` case count; place
sources, falling-off `else` branches and valueless callees refused
LG007), `return` of expressions (arithmetic, comparisons, `&&`/`||`/`!`,
bit ops with the width off the left operand, `~` over the storage width
exactly as M1 reads it, `uN(x)` conversions as `weiter`, `T::max/min`
and sugar limits off the desugar rule itself).

Carried because the corpus demands it: `bool` fields/params/results
(`Ty.bool`), `own` as read-write, tableless units (`Tab := Empty`, never
a fresh empty inductive; empty `GLock` likewise). New codes LG006
(loops) and LG007 (reason channel); LG001–LG005 keep their meanings.
Every `weiter`/`decide` over a computed range is decided in Rust first;
literals and widenings carry ascriptions so no `by decide` runs under a
metavariable; a Lean failure is never the refusal mechanism.
`fussOrtGB` prints exactly where its mirror holds
(signature-guarded or written-by-none, over the footprint mirror);
elsewhere a comment names the flagship's `FussS`/`fussSperreB`, which has
no Rust rule. `programmImFragmentG` holds structurally and always prints.

## 2. Measured: column (b) 3 → 9, all nine check green

`python3 instrumente/zaehle-kette.py --allow-stale`: sieve totals
`(a) 0 (b) 9 (c) 14 (d) 57 (e) 0 of 105`. Column (b) reads
`[.YYY.] 104`, `[.YYY0] 108`, `[.YYY0] 118`, `[.YFY0] 119`,
`[.YFY0] 15`, `[.YFY0] 16`, `[.YFF0] 62`, `[.YYY0] 69`, `[.YYY0] 73`.
Every one of the nine fresh `lean-g` outputs re-checked with
`./lean-probe`: **0 errors** each (fragment `by decide` everywhere,
footprint `by decide` for 104/108/118/62/69/73; 119/15/16 carry the
`FussS` comment instead, as designed).

The lane target (15) is NOT reached. The sieve analysis (§0) says why:
after this lane, every remaining refusal is item-level (globals, devices,
axioms/externs, entries, assumes, formats, libraries, atomics) or a type
the model has but this lane did not wire (shared locks, records,
`option`, `tagged`, `match`, `narrow`, `breaking`, `retry`/`forever`,
`leave`/`next`, `+=`/`assignVar`, `return f()`). Ordered follow-ups by
file weight: shared-lock taking (10, 13 and the `locks shared` effects),
`match` on tagged/option (34, 120, 27 with `static`), `narrow` (26, 28,
32-shapes), `breaking` (53, 55).

## 3. Three findings from the probing loop (all fixed, all green)

Each was found by `./lean-probe` on a fresh export, fixed in the
exporter, and re-measured to 0 errors:

1. **Nested `weiter` under ambiguous targets.** Literals used to travel
   wrapped in a self-`weiter`; under an implicit-only position (a `bor`
   operand, a comparison side) its range stayed a metavariable and `by
   decide` failed with "must not contain metavariables". Literals now
   travel bare and ascribed (`((.lit n) : Expr … (.int n n))`); `fit`
   ascribes its widening with the expected type.
2. **Negative numerals after the dot.** `.int -2147483648 2147483647`
   and `(.lit -5)` misparse as field notation on the numeral. Bounds
   print parenthesized (`(.int (-2147483648) 2147483647)`); same for
   negative literals.
3. **The model's default `hx` does not close -- including the exact
   held-set case.** The fresh 104 export failed at `gHp` with the
   pre-lane emitter shape (plain `hh`, defaulted `hx`/`hb`); the green
   `Export104.lean` pin carries a stale `hh_von` print from an older
   emitter. So the fresh 104 output was already red before this lane,
   and only the pin was re-checked. `hx`/`hb` are now always printed
   explicitly (generation-checked per lock), never defaulted; the fresh
   104 output is green again.

## 4. Gates

- `./cargo-pruef`: exit 0, 0 failing tests (42 suites ok, incl. 46/46 in
  `lean_g` -- 21 new accept/refusal tests, one existing test changed:
  `refuses_let` became `accepts_let` with `refuses_top_level_let_call`
  beside it; all others re-traced and green).
- `./lean-probe` over all nine fresh exports: 0 errors each.
- `./lean-bau`: exit 0, `Build completed successfully (180 jobs)`.
- `./emission-pruef` not run: the emitter (`emit.rs`) is untouched.

## 5. Untouched, as instructed

No diagnostic codes (only `LG006`/`LG007` exporter refusals), no gift or
example file changed, `MARKE_EMIT*` untouched, corpus files read-only.
Scratch `.lean`/logs live in the ignored `.tmp/` trees. English
throughout the code and this report.
