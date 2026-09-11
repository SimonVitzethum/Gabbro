# CForm ruling: `~` bitwise complement

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `bitNicht`, 98 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.bitNicht`).
The unary minus beside it is refused by name (unsigned stays unsigned
under the usual conversions, so `-x` would compute what M1 does not say);
the complement stays because its emitter already pays the width price in
full. This note books that payment.

## 1. Emitter site

`~` reaches C through one lowering line in
`crates/gabbro-check/src/emit.rs`, with one named refusal beside it:

| emitter line | function | shape written |
|---|---|---|
| 10714-10726 | `ausdruck`, `BitNicht` arm | `({c})~({c})({})`: the complement with the operand width read off the declaration (`wert_ctyp`), inner cast binding the operand, outer cast cutting the promoted result back |
| 4974-4982 | `ausdruck_format`, `BitNicht` arm | named refusal: `~` inside a `where` clause of a `format`, because a field reader's width is not readable at that point and the emitted complement would be an `int` complement |

Two facts narrow the form, both read off the code:

- The width comes from the declaration or the form is refused. Where
  `wert_ctyp` yields no width, the arm calls `weigere` instead of
  defaulting (10715-10724): a `uint64_t` default would be a guess, one
  level above the known bad `_ => 8`. Zero corpus sites need the
  refused position (Rule A).
- The constant folder leaves `~` unfolded. `const H : u32 = ~G;` is a
  constant expression the evaluator declines to compute (comment at
  2985-2989), so the complement always reaches C in the double-cast
  shape above rather than as a precomputed literal. One spelling for one
  thing.

Count: 98 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), one lowering line plus the
where-clause refusal.

## 2. Compiler fold

Two shapes of the same 16-bit complement, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef unsigned int u32; typedef unsigned short u16;
u32 flip_idiom(u16 x) { return (u32)~(u32)(x); }
u32 flip_naiv(u16 x) { return (u32)(~x); }
```

The `idiom` shape is the emitter's own double cast; the `naiv` shape
complements the promoted `int` and converts once.

| flags | double-cast idiom | naive complement |
|---|---|---|
| -O0 | 7 | 7, same mnemonic sequence |
| -O2 | 3 | 3, same mnemonic sequence |

Reading: the width-binding casts cost zero instructions at every level;
the compiler sees one complement either way. The price of `~` was never
in code size. It is in the value: on a `uint16_t` operand the naive
spelling computes `0xFFFFFF0F`-class values in `int` before converting,
while the idiom computes the 16-bit complement the checker means. The
emitter comment at 10700-10709 states the trap (`-Wall -Wextra` mostly
says nothing about it) and why both casts stand. A ruling that admitted
the operator but deleted the casts would keep the keyword and change the
numbers.

## 3. Semantic price

Admitting `~` pins two facts into the target language, and the note names
both because the admission is the ruling:

1. Bitwise complement under integer promotion, tamed by the double cast.
   The inner cast binds the operand to its declared width, the outer one
   cuts the promoted result back; only the outer one is effective, the
   inner one stands so that `mirrors` and the bit-field setter keep one
   spelling (comment at 10705-10709). A proof that reasons about a
   complemented value must read the width from the declaration, because
   the complement is a different number in every width.
2. Defined on the emitted widths. All 98 sites complement unsigned
   operands of declared width, where the value is fully defined. The
   signed-`~` question does not arise in the emission, and the refusal
   beside the arm keeps width-less positions from ever creating it.

UB inventory: `~` contributes no UB class on the admitted shape. The
complement of an unsigned value is defined in every width, and the
double cast keeps every site on unsigned widths. There is nothing here
that can devalue a proof through C's rules, so no inventory row is owed.
The adjacent danger (promotion silently widening the value) is a wrong
value, not UB, and the idiom is its guard.

## 4. Verdict: admit with price

`~` goes on the list with the two prices of section 3: the width rule
(double cast as the only spelling), definedness on unsigned widths.
Refusal was considered and rejected: the operator has no desugar (a mask
`x ^ 0xFFFF` needs the width too, so it moves the price instead of
removing it), the casts cost zero at every level (section 2), and 98
sites of mask and mirror logic would need a new lowering each.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `bitNicht` row; the C
count falls by one step. The unary-minus sibling stays refused by name
at `emit.rs` 10738-10747 and is not booked here.
