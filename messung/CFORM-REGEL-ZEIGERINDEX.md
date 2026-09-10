# CForm ruling: index on a pointer (`zeigerIndex`)

Status: ruled 2026-09-10. Verdict: admit with price. No emitter change.

Census slot: C1, `zeigerIndex`, 156 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.zeigerIndex`).
The question this ruling decides is the one the census already prints beside
the count: the allow list says `index`, and does not say whether it means
`p[i]` on a pointer too. The answer is no, with C-definition evidence in
section 3. The plain-`index` ruling (array over the declared range) does not
cover this form.

## 1. Emitter site

Every `[...]` in emitted C comes out of one generic line of
`crates/gabbro-check/src/emit.rs`, the `Index` arm of the place lowering in
`ort`:

| emitter line | function | shape written |
|---|---|---|
| 10085-10088 | `ort`, `OrtSuffix::Index` arm | `t = format!("{t}[{}]", ...)` for every index suffix, pointer or array alike |

Whether the site counts as `index auf zeiger` depends on the base type, not
on the line: a pointer-typed base (a pointer parameter, a device byte
pointer) against an array base (a table store, a fixed field). The census
lexer tells the two apart by construction: a declarator pre-pass collects
the pointer names of the unit into its `zeiger` set, and a `[...]` on such
a base is counted apart, never folded in silently
(`instrumente/zaehle-c-formen.py`, comment at 829-832). The cited example is
from the census itself: `p[1]` where `p` is `const uint8_t *p`.

Count: 156 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), one generic emission line with the
pointer case distinguished by the base type.

## 2. Compiler fold

Two spellings of the same read and the same write, `cc (GCC) 16.2.1` on
x86-64, instruction counts from `objdump -d --disassemble=<fn>` per
function:

```c
int get_sub(const int *p, int i) { return p[i]; }
int get_add(const int *p, int i) { return *(p + i); }
void set_sub(int *p, int i, int v) { p[i] = v; }
void set_add(int *p, int i, int v) { *(p + i) = v; }
```

| flags | subscript read | dereference read | subscript write | dereference write |
|---|---|---|---|---|
| -O0 | 13 | 13, same mnemonic sequence | 16 | 16, same mnemonic sequence |
| -O2 | 3 | 3, same mnemonic sequence | 3 | 3, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is
what the definition in section 3 predicts. A refusal that rewrote `p[i]`
into `*(p + i)` would buy nothing at any level because there is nothing to
buy: the compiler already sees one form. Refusal therefore cannot mean
rewriting; it could only mean refusing the 156-site programs outright
(section 4).

## 3. Semantic price, and why `index` does not cover it

The allow list (`dokumente/BEWEIS.md` Subject 2) grants `index` without
saying which. Three pieces of evidence, all of them definitions rather than
readings, say the grant reaches the array case and stops there:

1. C's own definition. C11 6.5.2.1p2: the expression `E1[E2]` is identical
   to `(*((E1) + (E2)))`. Where `E1` has pointer type, the `+` inside is
   pointer arithmetic under 6.5.6, with its scaling, its in-bounds
   requirement, and its provenance carried by the base pointer. An array
   `a[i]` over the declared range computes an element position the
   declaration already bounds; a pointer `p[i]` computes an address. The
   spelling is one bracket pair, the semantics are two different things.
2. The census books them as two catalogue entries. Plain `index []` is the
   allowed row; `index auf zeiger` is its own C1 row on the never list via
   pointer arithmetic (`p[i]` is `*(p+i)`), with the generous reading
   `Expressions: index` printed beside it so both totals stay honest. A
   form the counter deliberately counts apart cannot be ruled by citing the
   row it was kept apart from.
3. The ruling table already says so in data. `Erhaltung.lean` admits the
   named shape as `index over the declared range; pointer-index is NOT
   this (see zeigerIndex)` and carries `zeigerIndex` as its own open slot
   at 156 sites. This ruling closes that slot; it does not re-read the
   named one.

Admitting `zeigerIndex` therefore pins three things into the target
language, and the note names all three because the admission is the ruling:

1. Address computation beside the 491-site pointer-arithmetic row. The
   `+` inside `p[i]` scales by the element size and is subject to the same
   rules as the spelled-out `d->basis + 8` sites. The two rows are one
   semantics in two spellings, and the rewrite of UB inventory row 2
   (which promises no pointer arithmetic while the emission generates both
   spellings) must name both counts.
2. An in-bounds obligation on every one of the 156 sites. The index must
   designate an element of the object the base pointer may address; the
   declaration bounds the array case, while here the bound travels with
   the pointer (length parameter, table count, device window). A proof
   that reasons about which object a read touches must discharge it per
   site.
3. Provenance carried by the base pointer. `p[i]` and `q[i]` are different
   computations even at equal `i` when `p` and `q` point at different
   objects; the alias obligation (`satz_alias`: no address arithmetic in
   the image) grows by exactly these sites, carried openly as the named
   exception list rather than as a residual risk of none.

UB inventory: unlike `break` / `continue`, this form owes a row. An
out-of-bounds pointer index is undefined behavior through C's own rules,
and a proof that assumed the read touched its object would be devalued by
it. The row belongs beside `satz_alias` and the rewritten row 2, quoting
the 156 count and the per-site bound of item 2 above.

## 4. Verdict: admit with price

`zeigerIndex` goes on the list with the three prices of section 3:
address computation in the target language, a per-site in-bounds
obligation, and a UB inventory row for the out-of-bounds case. Refusal was
considered and rejected on two grounds, one of meaning and one of scale:

- Meaning: the only rewriting-style refusal, `p[i]` into `*(p + i)`, is
  definitionally the same form (section 2 measures it identical at -O0
  and -O2). It removes the spelling and keeps the semantics, which is
  bookkeeping, not a ruling.
- Scale: a real refusal would reject the programs behind 156 sites across
  the corpus, i.e. the pointer-based byte readers the drivers are built
  on. That is not a one-line generator fix; it fails the trivially-safe
  bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-10 with `cc -O0/-O2 -c` plus per-function `objdump -d`
counts on the two spelling pairs above.

Effect on the census on admission: C1 loses the `zeigerIndex` row while the
pointer-arithmetic row (491 sites) stays open and now explicitly includes
its index-shaped half; the generous-reading total and the strict total fall
by the same step.
