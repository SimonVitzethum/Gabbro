# CForm ruling: boolean constants (`true` / `false`)

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C3, `boolLit`, 211 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.boolLit`). This is the
third of the four C3 forms, covered by the generous reading printed beside
the count ("boolean constants"). The siblings are ruled in
`messung/CFORM-REGEL-PFEIL.md`, `messung/CFORM-REGEL-BOOL.md`, and
`messung/CFORM-REGEL-VERBUNDZUWEISUNG.md`.

## 1. Emitter site

`true` and `false` in emitted C come out of the fixed skeleton tails in
`crates/gabbro-check/src/emit.rs`, never out of user expressions:

| emitter line | function | shape written |
|---|---|---|
| 6387 | result-body closer | `return true;` for the body that reports success to its caller |
| 4679-4681 | `_gueltig` helper tail | `if (!({p})) return false; ... return true;` as the validity verdict |
| 6707 | error-channel store | `{e}return false;` on the failure path that also stores the reason |

User booleans reach C through the `bool` type row (ruled in
`messung/CFORM-REGEL-BOOL.md`); the constants themselves are the skeleton's
own verdicts. The `LOGUNDODER` ruling already books the companion fact: the
emitter types every comparison and every `Und` / `Oder` node as `bool` while
C computes `int` 0 or 1 underneath.

Count: 211 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the three fixed skeleton tails
above.

## 2. Compiler fold

Two spellings of the same constant return, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
int flag_true(void) { return true; }
int flag_one(void) { return 1; }
```

| flags | true form | 1 spelling |
|---|---|---|
| -O0 | 5 | 5, same mnemonic sequence |
| -O2 | 2 | 2, same mnemonic sequence |
| -Os | 2 | 2, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is what
the header guarantees (`true` is the macro for 1). A refusal that rewrote
`true` into `1` (and `false` into `0`) would buy nothing at any level because
there is nothing to buy.

## 3. Semantic price

Admitting `true` / `false` pins one fact into the target language, and the
note states it whole because the admission is the ruling:

1. Macros for 1 and 0 through `<stdbool.h>`. The same prelude line that the
   `BOOL` ruling books (line 676) discharges the obligation for the constants
   too; no second header is needed. The type of each constant is `int` under
   the macro, converting to `bool` 1 or 0 at a `bool` boundary exactly as a
   spelled-out 1 or 0 would. No conversion rule beyond the existing
   integer-to-boolean one is dragged in.

UB inventory: `true` / `false` contribute no UB class of their own. A
constant cannot be out of bounds, cannot overflow, and cannot be unsequenced;
there is nothing here that can devalue a proof through C's rules, so no
inventory row is owed.

## 4. Verdict: admit with price

`true` / `false` go on the list under the generous reading of boolean
constants with the price of section 3: macros for 1 and 0, header obligation
already discharged by the `BOOL` ruling, no new conversion rule, no UB.
Refusal was considered and rejected: the only rewriting-style refusal (`true`
into `1`) is definitionally the same constant (section 2 measures it
identical at -O0, -O2, and -Os), and it would touch the three most fixed
skeleton tails in the tree to no effect, which fails the trivially-safe bar
for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two spelling shapes above.

Effect on the census on admission: C3 loses the `true` / `false` row, and the
generously-covered class carries one open door instead of two.
