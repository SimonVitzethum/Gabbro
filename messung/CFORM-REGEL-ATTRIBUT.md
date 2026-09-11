# CForm ruling: `__attribute__`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `cAttribut`, 766 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cAttribut`).
The form is a GNU extension on no list, and it is three different promises
under one spelling, so the ruling prices each one separately. The bulk is
warning-only; a minority programs the optimiser.

## 1. Emitter site

`__attribute__` reaches C through four generator families in
`crates/gabbro-check/src/emit.rs`. The list is grouped because 766 keyword
hits cannot each carry a row:

| generator lines | family | shape written |
|---|---|---|
| 1890, 2040, 7995, 6210, 2116, 2126, 8075, 10945, 11500 | `unused` on statics | `static ... __attribute__((unused))` on table stores, static cells, fixed arrays, helpers, prototypes, the watchdog pointer, the `__typeof__` alias mark, boot constants |
| 3719, 3729, 3834, 3846, 4133, 4349, 4357, 4600, 4615, 4676, 11219, 11222, 11226 | `unused` on inline accessors | `static inline __attribute__((unused))` on device register readers/writers, field readers/writers, validity functions, walk helpers |
| 3114-3119 (`leise` closure in `ops`) | `unused` where uncalled | the attribute says whether this unit calls this operation, and where it does, it must go; the comment at 3105-3112 records the measurement that made it conditional rather than habitual |
| 5434, 5436 (`wirkungsweise`) | `const` / `pure` effect attributes | `__attribute__((const))` for fully pure callees with no pointer parameters, `__attribute__((pure))` for read-only ones |
| 501 (`abschnitt_attribut`) | `section` placement | `__attribute__((section("...")))` for the two witnessed `.rodata` names, with a named refusal for any other character (494-517) |

Two facts narrow the form, both read off the code:

- The `unused` family is measured, not habitual. Until 2026-08-28 every
  generated operation carried it; since `messung/OPS-RUFFORM.md` the call
  form exists, so the attribute is emitted only where this unit does not
  call the operation. An attribute claiming a function is unused while a
  line below calls it would be a false statement about the unit.
- The effect family is an instruction to the compiler, not bookkeeping.
  The comment at 5406-5412 states the direction plainly: a wrong one lets
  the optimiser fold away calls that do something, and a new effect kind
  falling into the branch silently would be permission to delete the call.

Count: 766 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), four generator families.

## 2. Compiler fold

Two shapes of the same call pair, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef unsigned int u32;
static u32 add_plain(u32 a, u32 b) { return a + b; }
static u32 add_attr(u32 a, u32 b) __attribute__((unused));
static u32 add_attr(u32 a, u32 b) { return a + b; }
u32 run_plain(u32 a, u32 b) { return add_plain(a, b); }
u32 run_attr(u32 a, u32 b) { return add_attr(a, b); }
```

The `attr` shape is the emitter's own `unused` idiom; the `plain` shape is
the same unit without it.

| flags | plain call | unused-attribute call |
|---|---|---|
| -O0 | 12 | 12, call target differs by name only |
| -O2 | 2 | 2, same mnemonic sequence |

Reading: the `unused` spelling changes no instruction at any level; it
speaks to the warning net, not to code generation. This table covers the
bulk family only. The effect family (`pure` / `const`) is deliberately not
fold-compared: its whole point is to change optimisation, and the tree
already records what that costs when wrong (a false `pure` once deleted
calls the caller could see, per the comments in `emit.rs` at 5277-5289 and
`lib.rs` at 730). Measuring a miscompile on purpose would be a second
witness nobody needs.

## 3. Semantic price

Admitting `__attribute__` pins three things into the target language, one
per family, and the note names all three because the admission is the
ruling:

1. `unused`: a truthful statement about the unit. The function or object
   may be unreferenced; the compiler must not warn. Price: the statement
   must stay true, which the conditional emission at 3114-3119 already
   guarantees by construction.
2. `pure` / `const`: an effect promise exported to the optimiser. `const`
   says the call depends on its arguments alone and touches nothing;
   `pure` adds read-only memory access. Price: the promise must match the
   checker-computed effects, which `wirkungsweise` derives from the
   declared `WirkungArt` set with device reads excluded (5401, 5440-5449).
   A promise wider than the declaration deletes calls that do something,
   and a proof that assumed the call happened would be devalued by it.
3. `section`: a linker placement promise for the two witnessed names.
   Price: the name character set the refusal enforces, so the name
   survives the C string literal and the assembler directive unchanged.

UB inventory: `unused` and `section` contribute no UB class. The effect
pair owes no new inventory row either, but it leans on one: the promise is
only as true as the effect analysis behind it, and the per-call-site
`D012` check is what holds the two together. The proof-relevant fact this
ruling books is that `pure` / `const` are target meaning now, and a proof
about which calls happened must respect what the optimiser was told.

## 4. Verdict: admit with price

`__attribute__` goes on the list with the three prices of section 3: a
truthful unused-statement, a checked effect promise, a two-name placement
promise. Refusal was considered per family and rejected on all three:

- `unused`: deleting it re-arms `-Werror=unused-function` over hundreds of
  conditionally used helpers; the replacement is warning noise, not fewer
  instructions (section 2 measures zero at every level).
- `pure` / `const`: deleting them is safe but purely a pessimisation; the
  promises are derived, checked, and already paid for.
- `section`: deleting it unplaces the two `.rodata` witnesses; nothing is
  bought.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `__attribute__` row; the C
count falls by one step. The `__typeof__` mark in the alias line (10945)
is booked here, not in that form's own ruling: the keyword belongs to this
row, the type operator to its own.
