# CForm ruling: `typedef`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C1, `cTypedef`, 240 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cTypedef`). The
allow list asks for typedef-free struct and union definition; this note is the
first of three C1-remainder rulings in this lane beside
`messung/CFORM-REGEL-ENUM.md` and `messung/CFORM-REGEL-DEFINE.md`. Pointer
arithmetic and `#include` stay open, and the ruled forms of the parallel lane
(`bedingt`, `logUndOder`, `continue`, `break`, `zeigerIndex`) are not touched.

## 1. Emitter site

`typedef` in emitted C comes out of the aggregate lowerings in
`crates/gabbro-check/src/emit.rs`, one shape per Gabbro aggregate:

| emitter line | function | shape written |
|---|---|---|
| 1699 | marker struct | `typedef struct { uint8_t nichts; } {m};` for the empty marker |
| 2728 | record lowering | `typedef struct { ... } {n};` for a record type |
| 2818-2822 | mark union | `typedef enum { ... } {n}_marke;` plus `typedef struct { {n}_marke marke; ... } {n};` |
| 2878, 2893 | table lowering | `typedef struct { ... } {t}_slot;` plus the table struct itself |
| 3628 | device struct | `typedef struct { {basisfeld}{felder} } {n};` for a device frame |
| 4304 | byte-reader struct | `typedef struct { uint8_t *bytes; uint32_t len; } {n};` for the slice view |
| 2315 | reason enum | `typedef enum { ... } {r};` for the error channel (shared with the ENUM ruling) |

Every site names a fresh aggregate the unit could not otherwise spell: C has
no anonymous-struct field access path that the `ort` lowering could reuse, so
each record, table, mark, and device frame needs its own named type.

Count: 240 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the aggregate lowerings above.

## 2. Compiler fold

Two spellings of the same two-field read, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef struct { int a; int b; } Pair;
struct P { int x; int y; };
int get_td(Pair p) { return p.a + p.b; }
int get_st(struct P p) { return p.x + p.y; }
```

| flags | typedef form | struct-tag spelling |
|---|---|---|
| -O0 | 8 | 8, same mnemonic sequence |
| -O2 | 4 | 4, same mnemonic sequence |
| -Os | 4 | 4, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is
what the language guarantees (a `typedef` names the type, it does not make
one). A refusal that expanded every alias into `struct { ... }` at each use
would buy nothing at any level because there is nothing to buy, and it would
cost readability at every one of the 240 sites.

## 3. Semantic price

Admitting `typedef` pins one fact into the target language, and the note
states it whole because the admission is the ruling:

1. A name alias, nothing more. `typedef` introduces no new type, no new
   layout, and no new conversion: two spellings of one aggregate. Layout,
   padding, and field order are fixed by the single `struct` definition the
   alias names, so the `.feld` row (padding bytes never read) applies
   unchanged. The price is namespace discipline: each alias must name a
   distinct aggregate, and the emitter discharges that by deriving every
   alias from the Gabbro type name (`{n}_marke`, `{t}_slot`, the record name
   itself), which the checker guarantees unique per unit.

UB inventory: `typedef` contributes no UB class of its own. It performs no
access, no arithmetic, and no sequencing decision; there is nothing here that
can devalue a proof through C's rules, so no inventory row is owed. This is
the cheapest of the three C1-remainder rulings in this lane: a spelling
admission with a uniqueness obligation, no semantics imported.

## 4. Verdict: admit with price

`typedef` goes on the list with the price of section 3: alias only, layout
fixed once, per-unit unique names, no UB. Refusal was considered and
rejected on two grounds, one of meaning and one of scale:

- Meaning: the typedef-free spelling the list asks for would repeat the full
  `struct { ... }` definition at every use or invent a parallel naming
  scheme; the alias is what keeps the 240 sites readable, and section 2 shows
  the expansion buys nothing at any level.
- Scale: a real refusal would restructure every aggregate lowering in the
  emitter (records, tables, marks, device frames, byte readers) against zero
  measured gain, which fails the trivially-safe bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two spelling shapes above.

Effect on the census on admission: C1 loses the `typedef` row while pointer
arithmetic and `#include` stay open; the declaration trio of this lane
(`typedef` here, `enum` and `#define` beside it) carries one open door fewer.
