# CForm ruling: `enum`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C1, `cEnum`, 28 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cEnum`). The allow list
asks for enum-free constants; this note is the second of three C1-remainder
rulings in this lane beside `messung/CFORM-REGEL-TYPEDEF.md` and
`messung/CFORM-REGEL-DEFINE.md`. Pointer arithmetic and `#include` stay open,
and the ruled forms of the parallel lane are not touched.

## 1. Emitter site

`enum` in emitted C comes out of two lowerings in
`crates/gabbro-check/src/emit.rs`, one per Gabbro sum shape:

| emitter line | function | shape written |
|---|---|---|
| 2315 | reason lowering | `typedef enum { ... } {r};` for the error channel of a failable body |
| 2818 | mark lowering | `typedef enum { ... } {n}_marke;` for the tag of a mark union |

Both sites close over a fixed alternative list: the reason enum names every
failure the body can report, the mark enum names every variant the union can
hold. The matching `switch` over each enum (the `match_markiert` and
`match_grund` lowerings, lines 8909 and 8971 per the `BREAK` ruling) carries
no `default` on purpose so that `-Wswitch` stays a second reader of the
closed distinction.

Count: 28 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the two lowerings above.

## 2. Compiler fold

Two spellings of the same tag read, `cc (GCC) 16.2.1` on x86-64, instruction
counts from `objdump -d --disassemble=<fn>` per function:

```c
enum E { EA = 1, EB = 2 };
int get_enum(enum E e) { return (int)e + 1; }
int get_int(int e) { return e + 1; }
```

| flags | enum form | int spelling |
|---|---|---|
| -O0 | 7 | 7, same mnemonic sequence |
| -O2 | 2 | 2, same mnemonic sequence |
| -Os | 2 | 2, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is
what the language guarantees (an unscoped enum has `int` representation
here). A refusal that replaced every enumerator with a bare `int` constant
would buy nothing at any level because there is nothing to buy, and it would
drop the closed-alternative reading the `switch` without `default` relies on.

## 3. Semantic price

Admitting `enum` pins two facts into the target language, and the note names
both because the admission is the ruling:

1. Named `int` constants over a closed alternative list. Each enumerator has
   a fixed value set at emission; the emitter types the tag as the enum and
   C reads it as `int`. The closed list is load-bearing: exhaustiveness of
   the two `switch` lowerings is checked against exactly these names, with
   `-Wswitch` as the net. Any consumer that adds a variant must extend both
   the enum and every switch over it.
2. No new conversion rule. The enumerators are `int` constants, so the only
   conversions are the existing integer ones; unlike the refused `?:`, no
   usual-arithmetic-conversion rule over two arms is dragged in.

UB inventory: `enum` contributes no UB class of its own. An out-of-range
cast into the enum type would be the caller's row, not this form's; the
emitted code never performs such a cast (every tag value is constructed by
the emitter's own writers). There is nothing here that can devalue a proof
through C's rules beyond what the `int` row already says, so no inventory
row is owed.

## 4. Verdict: admit with price

`enum` goes on the list with the two prices of section 3: closed alternative
list with fixed values, exhaustiveness obligation on the two `switch`
lowerings, no new conversion rule, no UB. Refusal was considered and
rejected: the enum-free spelling (bare `int` constants plus `#define`, the
sibling ruling) would keep the values and drop the closed list the switches
are checked against, trading a named distinction for magic numbers at zero
measured gain (section 2), which fails the trivially-safe bar for an emitter
change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two spelling shapes above.

Effect on the census on admission: C1 loses the `enum` row while pointer
arithmetic and `#include` stay open; the declaration trio of this lane
carries one open door fewer.
