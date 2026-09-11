# CForm ruling: `bool` type name

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C3, `boolTyp`, 350 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.boolTyp`). This is the
second of the four C3 forms, covered by the generous reading printed beside
the count (`<stdbool.h>` rather than `_Bool`). The siblings are ruled in
`messung/CFORM-REGEL-PFEIL.md`, `messung/CFORM-REGEL-BOOLLIT.md`, and
`messung/CFORM-REGEL-VERBUNDZUWEISUNG.md`.

## 1. Emitter site

`bool` in emitted C comes out of the type lowering plus the fixed skeleton
headers in `crates/gabbro-check/src/emit.rs`:

| emitter line | function | shape written |
|---|---|---|
| 676 | unit prelude | `#include <stdbool.h>`, the header that defines `bool` |
| 2699 | `c_typ` for `TypExpr::Bool` | `bool` as the C type of every Gabbro boolean |
| 2655 | object-size table | `bool` listed with size 1 beside the integer bytes |
| 3970, 3989 | unit check header and body | `bool pruefe_{unit}(void)` as the per-unit check signature |
| 4564 | bit-device guard | `"bool"` as the reader type for single-bit fields |
| 4676 | `_gueltig` helper | `bool {n}_gueltig(const {n} *v)` as the validity signature |

Every comparison node and every `Und` / `Oder` node is typed `bool` as well
(`wert_ctyp`, lines 9407-9421, per the `LOGUNDODER` ruling). The 350 sites are
the sum of these: type positions, check signatures, and validity helpers,
never an invented idiom.

Count: 350 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the type lowering plus the fixed
skeleton signatures above.

## 2. Compiler fold

Two spellings of the same negation, `cc (GCC) 16.2.1` on x86-64, instruction
counts from `objdump -d --disassemble=<fn>` per function:

```c
#include <stdbool.h>
bool neg_bool(bool b) { return !b; }
_Bool neg_bit(_Bool b) { return !b; }
```

| flags | bool form | _Bool spelling |
|---|---|---|
| -O0 | 11 | 11, same mnemonic sequence |
| -O2 | 3 | 3, same mnemonic sequence |
| -Os | 3 | 3, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is what
the header guarantees (`bool` is the macro for `_Bool`). A refusal that
rewrote `bool` into `_Bool` would buy nothing at any level because there is
nothing to buy: the compiler already sees one form.

## 3. Semantic price

Admitting `bool` pins two facts into the target language, and the note names
both because the admission is the ruling:

1. Alias of `_Bool` through `<stdbool.h>`. The header must be included in
   every unit that names the type, and the prelude line 676 discharges that
   obligation once per unit. Values are 0 or 1; any nonzero Gabbro truth
   normalizes to 1 at the boundary, and a reader of emitted C can trust that
   every `bool` object holds exactly one of the two.
2. No new conversion rule. Unlike the refused `?:`, `bool` never forms a
   common type over two arms; the `LOGUNDODER` ruling already books that the
   operator pair computes `int` 0 or 1 underneath while the emitter types the
   node `bool`. No usual-arithmetic-conversion rule is dragged in here.

UB inventory: `bool` contributes no UB class of its own. Reading an
uninitialized `bool` or overflowing a conversion into it belongs to the
operand's row, not to this form's. There is nothing here that can devalue a
proof through C's rules beyond what the `_Bool` row would already say, so no
inventory row is owed.

## 4. Verdict: admit with price

`bool` goes on the list under the generous reading of `_Bool` with the two
prices of section 3: header obligation discharged in the prelude, values 0 or
1, no conversion rule, no UB. Refusal was considered and rejected: the only
rewriting-style refusal (`bool` into `_Bool`) is definitionally the same type
(section 2 measures it identical at -O0, -O2, and -Os), and a real refusal
would rename the 350-site type of every check signature in the corpus, which
fails the trivially-safe bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two spelling shapes above.

Effect on the census on admission: C3 loses the `bool` row, and the
generously-covered class carries two open doors instead of three.
