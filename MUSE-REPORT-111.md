# MUSE-REPORT-111 — compile-time evaluation, first cut (PLAN-BITS.md §6)

Lane 111, Rust + Lean lane. Branch `muse/111`. The checker evaluates the
total, effect-free const fragment and prints Lean certificates; the Lean
side closes them entry by entry with `decide` (encoding N).

## What was built

**Surface.** `[e0, e1, ...]` parses only as a `const` initializer
(`ExprArt::ArrayLit`, `parse.rs::arraylit` + `constdecl`); the general
expression reader never reads `[`, so anywhere else it is `P011` by grammar
shape. `const T : [u32; N] = […]` is a const table computed element-wise:
each element is an ordinary `constexpr` and may call a `pure`
single-return `const fn` (64 `quad(i)` calls in the example).

**Checker** (new pass `crates/gabbro-check/src/konstanten.rs`, wired behind
`syscall`): the fragment over the checked AST is integer literals, other
consts, arithmetic/bit operators and calls of `pure` single-return
`const fn` — the exact fragment `Umgebung::konst_wert` computes (reused,
not reimplemented; W7). Codes, all owned by this one file:

- `K190` — initializer or element outside the fragment (carrier reads,
  layout queries, indirect and block-bodied calls);
- `K191` — literal length against the declared count;
- `K192` — a non-`pure` function in the const call hull (through `const fn`
  bodies, at the inner site);
- `K193` — a reference cycle through a `const` (a `const` carries no
  `decreases` by grammar shape);
- `K194` — a folded element outside the element range.

One fault keeps one refusal by construction: scalar ranges stay `M101`'s
(`m1` leaves table literals `Unbekannt`), function-only recursion stays
`K008`/`K009`/`H022`'s (this pass stays silent on it, including the `K190`
it would otherwise owe), division by zero stays `M102`'s, `~` stays the
emitter's (`C001`, gift 445), floats stay silent (the fragment is integers).
Table-embedded consts (`table T { const Q … }`) are indexed and held too —
the item walk never yields them, and the first probe showed a `[1, 300]`
passing in silence.

**Emitter** (`emit.rs`): a const table lowers to one
`static const uint32_t Q[64] __attribute__((unused)) = {0u, 1u, …};` from
the checker's own folder; anything unfoldable is `C001`. `korr_form` books
it as static storage.

**Certificate.** `konstanten::certificate(name, values, equation)` prints
the values as a `List Nat` literal plus the defining equation as a
`List.all` predicate over `zipIdx`, closed by `decide` (encoding N).

**Lean** (`grammatik/Grammatik/Konstanten.lean`, imported from
`Grammatik.lean`): `konstZert` (the predicate shape), `konstZert_nil`,
`mem_zipIdx_aux`, `mem_zipIdx_of_getElem?`, the generic lemma
**`konstZert_mem`** — a closed certificate yields every entry's defining
equation — and the witness: `squares64` (the 64-entry square table),
`squares64_zert` (`by decide`), and **`konstZert_mem_zeuge`**
instantiating all premises jointly at entry 63 (`3969 = 63 * 63`).
Axioms: `[propext, Quot.sound]` throughout; `squares64_zert` is axiom-free.

**Probes.** Gift 860 (`K190`, table read in an element), 861 (`K191`,
short literal), 862 (`K192`, impure callee), 863 (`K193`, const cycle —
falls once per member), 864 (`K194`, `300` in a `u8` table). Examples
92 (`92-const-squares.gab`, the certified 64-entry table, emits and
compiles under `cc -O2 -Wall -Wextra -Werror`) and 93
(`93-const-scalars.gab`, the scalar fragment). Rust suite
`crates/gabbro-check/tests/konstanten.rs`: 13 tests — fragment
acceptance, all five refusals with exact single-code sets, transitive
impurity, the table-body hole, the emitter string shape, a
compile-and-run readback (`wert(63, 7) = 4018`), and the
printer↔`squares64` correspondence (a drift breaks the test; the `decide`
itself breaks `./lean-bau`).

**Documents.** `SYNTAX.md` §1 (`constwert`/`arraylit`, table row) and §4
(attribute row); three register sentences (`consts.evaluable`,
`consts.table`, `consts.callhull`, attached to the M1 list — no new
`passliste` entry, like `H021`/`H022`); one differential probe
(`constdecl.[`, scores CARRIES) in `miss-grammatikdeckung.py`. Census
re-booked to measured: 76 examples, 577 poison, 583 tests, 319 diagnostics
(+5 mine), 169 EBNF rules (+2 mine), 124 sentences / 116 measured / 268
codes (the row stood at 94 while the register held 121), TODO's 304→319.

## Verification results

- `./cargo-pruef`: `== exit 0; failing tests: 0` (582 passed at the count
  run, +1 table-body test after — final tree green).
- `./lean-bau`: `Build completed successfully (54 jobs).`, 0 error lines.
- Green guardians: kennungen (319, ALL PASS), saetze (55 held),
  grammatiktafel (0/226 UNGEDECKT), wortschatz (226/226), syntax.sh
  (ALL PASS), konstrukte (0), deckung (UNCOVERED = 0), reichweite
  (0 ungelesen), miss-deckung speech + new probe CARRIES, todo README
  section (deckt sich), englisch count 7905 unchanged (my lines add zero
  German words; identifiers and comments are English throughout the new
  code).
- Red at base, untouched: emission-pruef (file-count drift; my files emit
  and compile but are not in its populations), manifest E1 (no new
  obligations), sondendeckung floor, sonden.sh date probes, klauseln
  `zucker`, todo 3× stale numbers (89/88 ×2, 179/180 — none from this
  lane: `zahlen.py` untouched, README unscanned for bold numbers, SYNTAX
  adds no bold numbers), c-formen Urkunde gap (64/30 vs measured 66/31,
  identical to lane 88), syntax.sh Warnungen (calls bare `cargo`, exit
  127 — environmental, no cargo on PATH outside `cargo-pruef`).

## What remains open (for the next const lane)

- Recursive `const fn` WITH `decreases` still exceeds the single-unfolding
  folder (`K190`, honestly named); bounded recursion needs fuel, not just
  a bound. Conversions (`u64(x)`) and block-bodied pure callees are
  `K190` for the same reason: the folder is single-expression.
- Non-recursive callees without `decreases` are accepted (the bound is
  owed where unboundedness lives, the `K008` line). See below — this is
  weaker than the strictest reading of the task.
- The certificate equation travels as a printer parameter: the checker
  guarantees the values, the human asserts the equation, Lean checks they
  match. No `gabbro const-cert` command (the task allowed "or a test").
- `korr_form` books table consts as static storage; the `Erhaltung.lean`
  ruling behind the row is still the literal one.

## Where I believe the task text needs sharpening

1. **"calls of functions declared `effects { pure }` with `decreases`"**
   reads strictly (every callee carries `decreases`), but the tree's own
   precedent is recursion-gated: `K008` demands `decreases` only of
   self-reaching functions, and `rechenwerk.rs` pins a `const fn`
   WITHOUT `decreases` evaluating in a `count`. I enforced purity
   strictly (`K192`) and `decreases` at cycles (`K193`), accepting
   non-recursive decreases-less callees. The poison "unbounded recursion"
   supports the cycle reading: a non-recursive call always terminates.
2. **Rule 13's "non-degenerate program" clause** (a written table plus a
   reached run with a memory-changing step) fits theorems over program
   syntax, not a pure `List` lemma. The companion `konstZert_mem_zeuge`
   instantiates every premise jointly (table, equation, closed
   certificate, entry 63 with `rfl` membership) at the task-named 64-entry
   table; the Rust test ties the checker's evaluated values to the same
   literal. The reference fixture (`refB`) has no entry point here by the
   task's own witness clause.
3. **"Tables of consts" via literal** writes the 64 squares out (generated,
   committed). A generator form (`= quad(i) for i in …`) would be smaller
   but is new syntax with its own fragment questions; the literal keeps
   the first cut to one production.

## Merge master-neu (reviewer request, 2026-09-12)

Merged master (lanes 86, 87, 88, 91, 100-107) with conflicts in
`Grammatik.lean` (union of all import lines), `README.md`, `TODO.md`,
`DONE.md` (union prose, every count re-measured, never picked).
No new enum variants on master (only `FnDecl.bibliothek/nutzlast`
fields), so no match arms were owed in either direction; `./cargo-pruef`
exit 0 first try (600 passed), `./lean-bau` 62 jobs green. Merged truth:
78 examples, 590 poison, 335 diagnostics, 169 EBNF rules, 228 terminals,
133 sentences (125/2/6/0) claiming 284, 55 unmapped, 1427+110 ceremony
sites, blind spots 79/169/24/13 of 285, all 78 examples emitting and
`cc -O2`-clean (both sides' 53/54 were stale). Guardians: saetze mark 55
held, todo 3 pre-existing findings, probe CARRIES on the merged binary.

## CUTS (not proved / not built)

- No theorem that the printed literal equals the evaluated table — trust
  base at the printer, held by the correspondence test.
- No block fallback for the certificate (64 entries decide in milliseconds;
  larger tables re-measure first, per the measurement).
- Scalar consts outside the fragment WITHOUT calls, and float consts,
  stay silent (zero-regression rule; the corpus has both).
- `gabbro prove` does not run the const certificate; `./lean-bau` checks
  the witness shape instead.
