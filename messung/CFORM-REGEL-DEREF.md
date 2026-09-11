# CForm ruling: `*` dereference

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `deref`, 141 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.deref`). The counter
tells three `*` apart by position: pointer declarator (`zeigertyp`),
multiplication (ignored, allowed binary), and the rest, which is this row:
a `*` that opens an expression rather than a declaration.
`grammatik/Grammatik/Ziel.lean` names no dereference shape.

## 1. Emitter site

Dereference reaches C through two generator families in
`crates/gabbro-check/src/emit.rs`. Both are device reads: Gabbro user code
has no dereference operator, so every one of the 141 sites is machine
text, not user control flow:

| generator lines | family | shape written |
|---|---|---|
| 3772 (`geraetelesung`) | register read | `(*(volatile {breite} *)({name}{pfeil}basis + {stelle}))`, documented at 3276 as `(*(volatile uint16_t *)((r)->basis + 0x102))` |
| 3899 (bit-field reader) | field read | `(((*(volatile {breite} *)(d->basis + {versatz})) >> {lo}) & {maske}u)` |

The same `*` appears on one write path (the register write left-hand side
at 6869, `(((*(volatile uint32_t *)(d->basis + 4)) >> 0) & 1u) = 1`), which
belongs to the write family of the same two lines rather than to a third
site: the address computation is identical, only the position differs.

Two facts narrow the form, both read off the code:

- The cast is the whole type of the access. `volatile {breite} *` says
  the width, the volatility, and the object kind in one place; there is
  no bare `*p` anywhere in the emission. A refusal that kept the address
  but changed the spelling would still compute the same address through
  the same provenance.
- The base is always a device base plus a declared offset (`basis +
  {stelle}`), never an arbitrary integer. The offset comes out of the
  register declaration, so the in-bounds question has a per-site answer
  in the declaration rather than in the arithmetic.

Count: 141 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), two generator families plus the
write-position twin.

## 2. Compiler fold

Two spellings of the same half-word device read, `cc (GCC) 16.2.1` on
x86-64, instruction counts from `objdump -d --disassemble=<fn>` per
function:

```c
typedef unsigned int u32; typedef unsigned short u16; typedef unsigned char u8;
u32 get_deref(volatile u8 *basis) { return (*(volatile u16 *)(basis + 4)); }
u32 get_sub(volatile u8 *basis) { return ((volatile u16 *)basis)[2]; }
```

The `deref` shape is the emitter's own idiom; the `sub` shape is the
index spelling the `zeigerIndex` ruling already measured as definitionally
identical (`p[i]` is `*(p+i)`).

| flags | dereference-cast idiom | subscript spelling |
|---|---|---|
| -O0 | 9 | 9, same mnemonic sequence |
| -O2 | 2 | 2, same mnemonic sequence |

Reading: the two spellings are the same program at every level, exactly
as the `zeigerIndex` note predicts from C11 6.5.2.1p2. A refusal that
rewrote one spelling into the other would remove characters and keep the
semantics, which is bookkeeping, not a ruling; a real refusal would
reject the device readers outright (section 4).

## 3. Semantic price

Admitting `*` pins three things into the target language, and the note
names all three because the admission is the ruling:

1. A volatile access on every site. `volatile` makes each read an
   observable act the compiler must not fold, merge, or drop; the probe
   reader test (`emit.rs` 11528: `q = (*(volatile uint16_t *)(d->basis +
   0xc)); /* ONE read */`) holds the single-read property by name.
   Consequence for readers: counting reads in emitted C counts device
   acts, and any proof about read counts must count them too.
2. An in-bounds obligation beside the 491-site pointer-arithmetic row.
   The `+` inside the cast scales by the element size under C11 6.5.6 and
   must designate within the device window the base may address. The
   bound travels with the declaration (offset against window), like the
   pointer-index twin ruled in `messung/CFORM-REGEL-ZEIGERINDEX.md`.
3. Provenance carried by the base pointer. The access aliases whatever
   object the base addresses; the alias obligation (`satz_alias`: no
   address arithmetic in the image) grows by exactly these sites,
   carried openly as the named exception list.

UB inventory: unlike `break` / `continue`, this form owes a row. A null
or dangling base, an out-of-window offset, or a misaligned volatile
access is undefined behavior through C's own rules, and a proof that
assumed the read touched its register would be devalued by it. The row
belongs beside `satz_alias` and the rewritten row 2, quoting this count
and the per-site bound of item 2 above.

## 4. Verdict: admit with price

`*` goes on the list with the three prices of section 3: volatile access
as observable act, a per-site in-bounds obligation, and a UB inventory
row for the bad-base case. Refusal was considered and rejected on two
grounds, one of meaning and one of scale, mirroring the `zeigerIndex`
ruling:

- Meaning: the only rewriting-style refusal is definitionally the same
  form (section 2 measures it identical at -O0 and -O2).
- Scale: a real refusal rejects the register readers the drivers are
  built on. That is not a one-line generator fix; it fails the
  trivially-safe bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two spelling pairs above.

Effect on the census on admission: C2 loses the `deref` row while the
pointer-arithmetic row stays open and now explicitly includes its
cast-shaped third spelling beside the plain and index-shaped halves.
