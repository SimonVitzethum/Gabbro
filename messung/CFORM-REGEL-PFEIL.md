# CForm ruling: field access through a pointer (`->`)

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C3, `pfeilZugriff`, 704 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.pfeilZugriff`). This is the
first of the four C3 forms, all of them covered by the generous reading printed
beside the count ("field access"). The other three are ruled in
`messung/CFORM-REGEL-BOOL.md`, `messung/CFORM-REGEL-BOOLLIT.md`, and
`messung/CFORM-REGEL-VERBUNDZUWEISUNG.md`; none of the four touches the
C1 remainder or the forms ruled by the parallel lane.

## 1. Emitter site

Every `->` in emitted C comes out of the place lowering in `ort`
(`crates/gabbro-check/src/emit.rs`), which decides per base whether the access
spells `.` or `->`:

| emitter line | function | shape written |
|---|---|---|
| 10077-10085 | `ort`, `OrtSuffix::Feld` arm | `{t}->{field}` when the base is pointer-typed, `{t}.{field}` otherwise |
| 10086 | `ort`, `OrtSuffix::Ueber` arm | `{t}->{field}` unconditionally for the overlay suffix |
| 8334, 8631 | walk skeleton setup | `{basis}->slots` for the node-table base |

The static-of-record guard just above (10060-10075) is the worked evidence
that the choice is deliberate: a static record is a value, not a pointer, and
the lowering forces `zeiger = false` so the access spells `.` (comment cites
`cc: error: invalid type argument of '->'`). Further emitted `->` sites are
the fixed skeleton readers: line 3193 (`t->slots[s].{field}`), line 4676
(`v->len` in the `_gueltig` guard), lines 4349 and 4357 (byte-reader and
setter helpers over `v->bytes`), and line 4961 (`v->len` for `Lenof`).

Count: 704 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the `ort` lowering plus the fixed
skeleton readers above.

## 2. Compiler fold

Two spellings of the same read through a pointer, `cc (GCC) 16.2.1` on
x86-64, instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
struct P { int x; int y; };
int get_arrow(struct P *p) { return p->x; }
int get_star(struct P *p) { return (*p).x; }
```

| flags | arrow form | star-dot spelling |
|---|---|---|
| -O0 | 7 | 7, same mnemonic sequence |
| -O2 | 2 | 2, same mnemonic sequence |
| -Os | 2 | 2, same mnemonic sequence |

Reading: the two spellings are the same program at every level, which is what
C's definition predicts (`p->x` means `(*p).x`). A refusal that rewrote `->`
into `(*p).` would buy nothing at any level because there is nothing to buy.
Refusal could only mean rejecting the 704-site programs outright (section 4).

## 3. Semantic price

Admitting `->` pins one fact into the target language, and the note states it
whole because the admission is the ruling:

1. Field access through a pointer-typed base. The base must point at a live
   object of the named struct type; the access reads exactly the named field.
   Padding bytes are never read (the `.feld` row already carries that term,
   and it applies unchanged here). A proof that reasons about which object a
   read touches must discharge the base-pointer bound per site, the same
   obligation the `zeigerIndex` ruling books for its 156 sites.

UB inventory: `->` contributes no UB class of its own. A null or dangling
base is undefined behavior through C's own rules, and a proof that assumed
the read touched its object would be devalued by it; that row belongs to the
pointed-to object and the base-pointer bound, not to a new row for this
form. The generous reading ("field access") covers the spelling, and the
price above covers the pointer half that the spelling adds.

## 4. Verdict: admit with price

`->` goes on the list under the generous reading of "field access" with the
price of section 3: pointer-typed base, per-site object bound, padding never
read, no new UB row. Refusal was considered and rejected on two grounds, one
of meaning and one of scale:

- Meaning: the only rewriting-style refusal, `p->x` into `(*p).x`, is
  definitionally the same form (section 2 measures it identical at -O0, -O2,
  and -Os). It removes the spelling and keeps the semantics, which is
  bookkeeping, not a ruling.
- Scale: a real refusal would reject the programs behind 704 sites, the most
  frequent C3 form in the corpus, i.e. every pointer-based field read the
  walker and the device readers are built on. That fails the trivially-safe
  bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two spelling shapes above.

Effect on the census on admission: C3 loses the `->` row, the C count falls
from 30 to 29 (26 to 25 under the strict reading that never counted C3), and
the generously-covered class carries three open doors instead of four.
