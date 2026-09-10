# CForm work-off: census, cheapest-first order, ruling template

Source for the census: `dokumente/BEWEIS.md` lines 771-827 (Subject 2, the C census),
rulings at lines 843-911. Target side: `grammatik/Grammatik/Ziel.lean` lines 54-64
(`CForm`, 19 named shapes, explicitly not a closed list). Refusal anchor:
`crates/gabbro-check/src/emit.rs` line 2542 (`weigere` refusal helper, see section 4).
Date of census values: 2026-09-10 assessment
(`messung/ZIEL-BEWERTUNG-2026-09-10.md` lines 132-134: 64 measured forms, 30 unruled).

Denominator, as booked in the source: 102 of 485 versioned `.gab` files emit;
8001 lines of C, of which 1732 are comment. The counter is a lexer over the token
stream, not a text search, and every keyword and punctuator must map to a catalogue
entry under `UNBEKANNT`.

## 1. Census (A / B / C1 / C2 / C3)

Headline counts:

| set | meaning | count |
|---|---|---|
| A | allowed and used, the actual table | 34 |
| B | allowed and never used, dead entries | 6 |
| C | used and not allowed, the findings | 30 |
| Forms in emitted C | A plus C, the ratchet | 64 |

B, the six dead entries: `#if` out of `when`, `#else`, `#elif`, `extern`,
`_Bool`, unary `-`. Note from the source: the five `#if` in the corpus are all
`#if defined(__GNUC__)` around `__builtin_unreachable()`, written by the emitter,
so the permitted form is never emitted and the emitted form was never permitted.

C1, used and on the never list (seven):

| form | sites | note |
|---|---|---|
| pointer arithmetic | 491 | contradicts the old row 2 claim of no pointer arithmetic |
| index on a pointer | 156 | `p[i]` is `*(p+i)` by definition of C |
| `#include` | 408 | preprocessor other than `#if` |
| `typedef` | 240 | list asks for typedef-free struct and union definition |
| `#define` | 210 | preprocessor other than `#if`; enum-free constants plainly mean it |
| `enum` | 28 | list asks for enum-free constants |
| `?:` | 8 | ruled as template, see section 3 |

C2, used and on neither list, no generous reading covers them (nineteen):

| form | sites |
|---|---|
| `void` | 930 |
| `__attribute__` | 766 |
| `inline` | 440 |
| `const` | 419 |
| `*` dereference | 141 |
| `&` address-of | 111 |
| `~` | 98 |
| `break` | 51 |
| `++` / `--` | 42 |
| `sizeof` | 27 |
| `&&` / `\|\|` | 23 |
| `double` | 18 |
| `while` | 11 |
| `__typeof__` | 9 |
| `float` | 8 |
| `__builtin_unreachable` | 5 |
| `#if defined(__GNUC__)` | 5 |
| `continue` | 3 |
| `_Static_assert` | 1 |

Two of these are decisions nobody took, per the source: `float` / `double`
(the type row knows no floating point, 26 emitted sites) and `&&` / `||`
(the binary row names `&` and `|` but not the conditional pair).

C3, used, unnamed, generous reading covers them (four):

| form | sites | generous reading |
|---|---|---|
| `->` | 704 | field access |
| `bool` | 350 | `<stdbool.h>` rather than `_Bool` |
| `true` / `false` | 211 | boolean constants |
| `+=` / `\|=` / `-=` | 24 | assignment |

Under the generous reading the findings are 26 rather than 30; the file lists all
four so that the count of 30 carries both readings.

Second instrument, good news from the source: `cc` with strict conversion and
promotion warnings finds zero hits over the 101 units it compiles. Implicit
conversion, `const` discarding, and variable-length arrays hold measured. The
102nd unit does not compile and is booked as such rather than as zero warnings.

## 2. Ruling order, cheapest first

Rule: single-site generator fixes before list admissions, deletable sites before
load-bearing ones, generous-reading admissions before new semantics, and forms
with no new semantics before forms that import one. Ruling by taste is what
produced a list with 30 holes; each step below uses the template in section 3.

| step | batch | why this cheap |
|---|---|---|
| 1 | `?:` | one emission site, zero-cost fold measured, template already worked |
| 2 | `__builtin_unreachable` plus its `#if defined(__GNUC__)` | five sites, four deletable by the adjacent-return rule, one load-bearing at `-O0` only |
| 3 | C3 (four forms) | admit by name under the stated generous reading, near-zero semantic price |
| 4 | C2 small control forms (`break`, `continue`, `while`, `++` / `--`, `~`, `sizeof`, `_Static_assert`) | narrow semantics, each admits with a short price note |
| 5 | C2 qualifier and type-address forms (`void`, `const`, `*`, `&`, `float`, `double`, `&&` / `\|\|`, `inline`, `__attribute__`, `__typeof__`) | each imports real semantics; rule one by one, `&&` / `\|\|` together with `?:` as one conditional-evaluation class |
| 6 | C1 hard forms (pointer arithmetic, index on a pointer, `#include` / `#define`, `typedef`, `enum`) | generator change or list admission with full price; pointer arithmetic also rewrites the affected inventory row |

Class warning from the source, kept: deciding `?:` alone looks like a solved
class and is one door of three. `&&` and `||` evaluate conditionally exactly
like `?:` and must be ruled with it, not after it is forgotten.

Open items as booked in the source: the 19 unnamed C2 forms are to be ruled one
by one the way `?:` was, and the inventory row that claims no pointer arithmetic
is to be rewritten because the emitter writes 491 sites of it.

## 3. Ruling template, worked for `?:`

Every ruling fills all four slots. A ruling with an empty slot is a draft.

1. Emitter site. All eight `?:` sites are one line, `z = (z > v) ? z : v;`,
   out of one emission site (`MergeOp::Max` / `Min` in the emitter). Name the
   construct, the site, and the site count. A form with several sites needs one
   row per site, because the fix may differ per site.
2. Compiler fold. Three shapes of the same fold under `cc` (GCC) 16.2.1 on
   x86-64:

| flags | `?:` | `if` and `else` naive | `if` tight |
|---|---|---|---|
| `-O0` | 34 | 36 | 34 |
| `-O2` | 11 | 11 | 11, identical apart from the file line |
| `-Os` | 11 | 11 | 11, identical apart from the file line |

   Reading: `if (v > z) { z = v; }` costs nothing at any level. Measure before
   claiming; the table above is the pattern, not a citation to reuse.
3. Semantic price. `?:` is, besides `&&` / `||`, the only operator that
   evaluates conditionally, and the only one that forms its result type by the
   usual arithmetic conversions over its two arms. Listing it drags an
   implicit-conversion rule into a table the compiler just certified free of
   one. A rule that costs a semantics and buys zero instructions is the wrong
   side of the trade.
4. Verdict: admit with price, or refuse. Admit means onto the list with the
   price stated plus a row in the undefined-behavior inventory where the form
   can devalue a proof (the `__builtin_unreachable` remainder is the model:
   admitted with its proof-export price said). Refuse means out of the
   generator through the anchor in section 4, with the booked change:
   the emitter writes `if (v > z) { z = v; }` for `MergeOp::Max` / `Min`,
   then C1 loses `?:` and both marks fall by one. Either way, close the
   conditional-evaluation class together: `?:` plus `&&` plus `||`, or the
   file records which door is still open.

## 4. Refusal anchor: `weigere`, fail closed

`weigere` stands at `emit.rs:2542`. It pushes a named refusal (`C001`, `no
lowering`, with the span and the reason) plus a note: the emitter refuses by
name instead of emitting something plausible, because a generator that guesses
undoes every pass in front of it.

Fail-closed property: there is no path that returns guessed C for an
unsupported form. The array-field setter beside the anchor is the worked
example: a non-zero value where only the aggregate zero initializer is
expressible is refused by name rather than braced and hoped for. New refusals
call this helper; they do not invent a second channel.

Effect on the census: each refused form leaves the emitted set, so the C count
and the affected class count fall together, and the marks that track them fall
by the same step. Each admitted form enters the allow list with its semantic
price and, where it can devalue a proof through the rules of C, with an
inventory row beside it.
