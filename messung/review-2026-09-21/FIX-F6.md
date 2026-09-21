# Fix lane F6 — bounded strings (review G12 F4, F5, F6; lane 256)

*2026-09-22. Worktree `review-integration`, branch `review-0921-integration`, on top of F5
`b3e1f411`. Built and run locally (fisch unreachable); `free -g` beside every heavy run:
31 GB total, 20 GB available each time.*

Commit: `12682336` (code, gifts, Lean, docs); this report in the commit after it.

## What was fixed

### 1. MEDIUM (G12 F4): an index is proven against the length, not the max

`zeichenfolge.rs` accepted `s[k]` for any literal `k < max`, so `gift/1125` (`s[7]` on
`string max 8`) checked clean, while the Lean `bindex` refuses `k >= length` and a
`string max 8` may be empty. Now `N454` demands a **flow fact**:

- a literal `k` needs a known `lenof(s) > k` (also `k < lenof(s)`, `lenof(s) >= k+1`,
  `lenof(s) == c` with `c > k`);
- a name `i` needs a known `i < lenof(s)` and must be of an unsigned integer type (a
  signed or unannotated name proves nothing);
- facts come from an `if` condition in its branch (`&&` joins, `!`/`||` negate), from the
  negated condition after an `if` without `else` whose block always ends (`endet_immer`),
  and from `requires` at the head;
- a fact dies when either name is assigned anywhere under a statement
  (`crate::schreibziele`) or rebound, and before a loop body that assigns it;
- no fact reaches the right side of `&&` inside one expression (refuses more, never less).

Lean (`ZeichenfolgeGebunden.lean`): `bindex_max_beweist_nichts` (an empty `string max 8`
refuses index 7), `bindex_geschuetzt`, `bindex_mindestlaenge` (the accepted guard forms
give a character). `gift/1125` now expects `N454` (renamed
`1125-index-in-max-ohne-laenge.gab`); positive probe `gift/1159` (all four guard forms,
checker-silent, `C001`); `gift/1168` (the guard's fact dies with an assignment, `N454`).

### 2. MEDIUM (G12 F4): copying into a shorter max at every position

Instead of adding the four named sites to a list, the positions are closed:

- **`N465` (new) at the declaration**: a `string max N` stands only as the whole type of a
  function parameter, a function result or a `let` annotation. Everything else is refused
  through `crate::jeder_typausdruck_im_item` (exhaustive over `ItemArt` and `TypExpr`) plus
  an exhaustive `TypExpr` walk for `let`/`alloc` annotations and `sizeof`: struct and
  table fields, `const`/`static`/atomic types, arena elements, aliases, arrays, variant
  payloads, pointer targets, fn-pointer parameters, `syscall` heads. With that, every string
  value comes from a bound name, a resolved call or a `+`, so "not known as a string" means
  "not a string".
- **`N455` everywhere a value flows**: the statement walk is exhaustive over `StmtArt` (no
  `_` arm); a string flows only into a known string slot that fits it (annotated `let`,
  assignment to a string name, `return`, a string parameter -- in bodies, `requires`/
  `ensures`, loop invariants, `retry … until`, check floors and `let … else` sources). A
  string at a condition, `match` subject, index, unary/other operand, array element,
  field/global target, publish, arena slot, `const`/`static`/table/arena initializer or
  non-string parameter falls. `s += t` is held as a concat against `s`'s own max (`N453`).
- **`N465` at unresolved callees**: a string handed to a method call, library call,
  constructor or unknown name falls, and so does an ambiguous name whose candidates carry a
  string.

Lean: `bconcat_max_summe` and `bkopie_max` prove the checker's max rules sound against the
exact-length `bconcat`/new `bkopie`; `bkopie_kuerzer_scheitert` shows the refused case exists.
Gifts: `1160` struct field, `1161` `const`, `1162` `static`, `1163` table slot (all `N465`),
`1164` a `requires` copying 8 into 2, `1165` a `let … else` source copying 8 into 2 (both
`N455`). A per-site gift for `LetSonst` binding, publish, alloc etc. was not added: those
are covered by the same `wert_ohne_kette` call and pinned in `tests/zeichenfolge.rs`
where cheap.

### 3. LOW (G12 F5): the name table is scoped

The flat per-body `sammle_lets` map is gone. `Zustand` is a stack of block scopes walked in
statement order; a binding ends with its block; an unannotated `let` the pass cannot type
binds a non-string (it shadows). Match binders, traverse variables, quantifier and `count`
variables, `let … else` error names, `alloc`/`awaits`/`exchange` names are bound too.
Probe pair: `gift/1166` (a name reused as a number in a sibling block: a false `N455`
before, measured; clean now) and `gift/1167` (a sibling block's `x` holds `string max 64`
and is copied into `string max 2`: accepted before, measured; `N455` now).

### 4. LOW (G12 F6): the witness

`bounded_string_zeuge` no longer joins the reference-machine run (`refB_erreicht`/
`refB_schreibt`). It states, on non-empty distinct strings: `"hi" + "!" = "hi!"` at max 8
(length 3), index 2 reads `'!'` under `2 < blaenge`, the same index is refused on the empty
`string max 8`, `"hi!"` copies into max 8 and not into max 2. The file no longer imports
`ReferenzB`. Header and CUTS rewritten to claim no more than the value model; no theorem
says the Rust pass implements the rules. SATZKARTE §43 added (there was no entry).

### 5. Recorded, not done: NUL and the upper limit on `max`

`OFFEN.md` O24 and the TODO wave-E row: the representation (length word vs NUL-terminated
`max + 1` bytes, NUL inside data), the missing upper bound on `max` (parsed `u128`),
literals, strings in aggregates/constants -- all the lowering lane's.

## Measured

| check | result |
|---|---|
| `cargo test --no-fail-fast` | **1310 passed, 0 failed, 1 ignored, 72 collections** (baseline 1304/0/1, 71; +6 in the new `tests/zeichenfolge.rs`) |
| `instrumente/pruefe-emission.sh` | **ALL PASS** (37 pierced, 288 of 288 compile, 2 reverse probes; ASan stage 6b not run on this machine) |
| `cd grammatik && lake build` | **281 jobs, 0 errors**; `#print axioms gabbro_ziel` = `propext`, `Classical.choice`, `Quot.sound` |
| `lake env lean ZeichenfolgeGebunden.lean` | all `#print axioms` at most `propext` (`vergl_refl`: `propext`, `Classical.choice`, `Quot.sound`) |
| `pruefe-saetze.py` | pass (443 codes, 184 sentences, 0 invented) |
| `pruefe-kennungen.py` | ALL PASS |
| `pruefe-todo.py` | 16 findings (= baseline) |
| `pruefe-zahlen.py` | 37 findings (= baseline) |
| `pruefe-englisch.py` | rc 1, same ratchets as master (7965 German comment lines, 37/26 feeders) |

**Corpus diff** (old vs new binary, `gabbro check` over `beispiele/*.gab` and
`beispiele/gift/*.gab`, diagnostics by code and position): **0 changes in `beispiele/`**
(no example uses a string). In `gift/`: `1125` gains `N454` (intended), and the new gifts
`1159`-`1168` read as listed above; under the old binary `1159` drew `N454`, `1166` drew
`N455`, and `1160`-`1165`, `1167`, `1168` were silent.

## What stays open

- The rules are tied to the Lean model by gifts and pins, not by a proof; the model has no
  representation, literals, aggregates or max limit (O24). Every string program still ends
  at `C001`.
- Deliberately conservative: no fact crosses `&&` within one expression; `narrow` and loop
  conditions give no facts; a signed or unannotated index name proves nothing; `+`/copies
  compare maxes, not lengths.
- `N465` refuses strings in aggregates and constants outright -- a cut until a layout
  exists, not a model of them.
