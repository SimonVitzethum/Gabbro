# CForm ruling: `#define` constants

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C1, `cDefine`, 210 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cDefine`). The list asks
for enum-free constants, which plainly means these macros; this note is the
third of three C1-remainder rulings in this lane beside
`messung/CFORM-REGEL-TYPEDEF.md` and `messung/CFORM-REGEL-ENUM.md`. Pointer
arithmetic and `#include` stay open, and the ruled forms of the parallel lane
are not touched.

## 1. Emitter site

`#define` in emitted C comes out of the constant lowerings in
`crates/gabbro-check/src/emit.rs`, one shape per constant kind:

| emitter line | function | shape written |
|---|---|---|
| 1721 | constant lowering | `#define {name} {w}u` for an unsigned width constant |
| 1729 | constant lowering | `#define {name} {v}` for a plain constant value |
| 1744 | constant lowering | `#define {name} {w}{suffix}` for a suffixed width constant |
| 2197 | atomiciki helper | `#define {n}_ORDER {wort}` for the memory-order word of an atomiciki |
| 2924 | table lowering | `#define {n}_NONE ({len})` for the out-of-range sentinel of a table |

Every site names a fixed value the unit reads but never writes: widths,
sentinels, order words. The suffixed shapes (1721, 1744) carry their type in
the spelling so that no implicit conversion is needed at the read.

Count: 210 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the constant lowerings above.

## 2. Compiler fold

Two spellings of the same constant read, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
#define K1 41
int get_def(void) { return K1 + 1; }
int get_lit(void) { return 41 + 1; }
```

| flags | define form | literal spelling |
|---|---|---|
| -O0 | 5 | 5, same mnemonic sequence |
| -O2 | 2 | 2, same mnemonic sequence |
| -Os | 2 | 2, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is
what the preprocessor guarantees (the macro expands before the compiler ever
runs). A refusal that inlined every constant at each read would buy nothing
at any level because there is nothing to buy, and it would drop the single
definition point the 210 reads share.

## 3. Semantic price

Admitting `#define` pins two facts into the target language, and the note
names both because the admission is the ruling:

1. Textual substitution before compilation. A function-like macro would
   evaluate its arguments at each expansion; every macro here is
   object-like, a bare value with no parameters, so the double-evaluation
   class never arises. The obligation is hygiene going forward: any future
   function-like macro must parenthesize its parameters and its body.
2. Untyped definition, typed read. The macro itself has no type; the type
   arrives from the suffix in the spelling (1721, 1744) or from the context
   of the read. The suffixed shapes discharge that explicitly, so a reader of
   emitted C can trust that a `u`-suffixed constant never undergoes a signed
   conversion at its read.

UB inventory: `#define` contributes no UB class of its own. Substitution
happens before any C semantics applies, and no emitted macro forms an
expression with a sequencing decision. There is nothing here that can devalue
a proof through C's rules, so no inventory row is owed.

## 4. Verdict: admit with price

`#define` goes on the list with the two prices of section 3: object-like
only, hygiene obligation on any future function-like macro, typed reads via
suffixes, no UB. Refusal was considered and rejected on two grounds, one of
fit and one of cost:

- Fit: the enum-free-constants row the list asks for is exactly this form;
   refusing it would leave the constants with no lawful spelling at all (the
   `ENUM` ruling covers the closed-alternative tags, not the open width and
   sentinel values).
- Cost: section 2 shows the inline-everything desugar buys nothing at any
  level while scattering 210 single definition points across their reads.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two spelling shapes above.

Effect on the census on admission: C1 loses the `#define` row while pointer
arithmetic and `#include` stay open; the declaration trio of this lane
(`typedef`, `enum`, `#define`) is fully ruled.
