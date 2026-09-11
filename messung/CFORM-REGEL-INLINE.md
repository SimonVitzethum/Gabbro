# CForm ruling: `inline`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `cInline`, 440 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cInline`).
The keyword is a hint on no list, always paired in this tree with `static`
and usually with the `unused` attribute ruled in
`messung/CFORM-REGEL-ATTRIBUT.md`. This note rules the hint, not the pair.

## 1. Emitter site

`inline` reaches C through two generator families in
`crates/gabbro-check/src/emit.rs`, grouped because 440 keyword hits cannot
each carry a row:

| generator lines | family | shape written |
|---|---|---|
| 3719, 3729, 3834, 3846, 4133, 4349, 4357, 4600, 4615, 4676, 11219, 11222, 11226 | generated accessors | `static inline __attribute__((unused))` on device register readers/writers, field readers/writers, validity functions, walk helpers |
| 4771-4807 (`SCHREIBER_C`, `LESER_C`) | byte-order helpers | `static inline` without the attribute (`gabbro_setz_be32`, `gabbro_u8`, and siblings): internal helpers every unit may call, so no unused-statement is owed |

Two facts narrow the form, both read off the code:

- Every `inline` in the tree is `static inline`, never bare `inline`.
  Internal linkage means no external definition is owed anywhere and no
  other unit can observe whether the call was inlined. The one-definition
  question bare `inline` asks in C99 does not arise.
- The helpers without the attribute are dependencies, not ornaments: a
  unit that reads a multi-byte field needs `gabbro_be32` whether or not
  the call survives as a call. The test at `rechenwerk.rs` 3596-3599 reads
  both spellings as required content.

Count: 440 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), two generator families.

## 2. Compiler fold

Two shapes of the same doubling, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef unsigned int u32;
static u32 dbl_plain(u32 x) { return x + x; }
static inline u32 dbl_inline(u32 x) { return x + x; }
u32 run_plain(u32 x) { return dbl_plain(x); }
u32 run_inline(u32 x) { return dbl_inline(x); }
```

The `inline` shape is the emitter's own hint; the `plain` shape is what a
refusal would have to write instead.

| flags | static call | static inline call |
|---|---|---|
| -O0 | 9 | 9 |
| -O2 | 2 | 2, same mnemonic sequence |

Reading: at -O0 the hint changes nothing (the call stands in both); at
-O2 both shapes fold to the same two instructions. Refusal buys nothing at
any level: the compiler already treats a `static` single-use callee the
way the hint asks.

## 3. Semantic price

Admitting `inline` pins one fact into the target language: a non-binding
request to expand the call in place. The price is small and this note
states it whole:

1. Hint only, no meaning. An ignored `inline` is the same program; a
   honoured one is the same program with the call expanded. No evaluation
   order, no value, and no address changes either way, because every use
   is `static` with internal linkage.
2. No address-taken class. The accessors are called, never named as
   values, so no function-address comparison can distinguish the expanded
   from the unexpanded form.

UB inventory: `inline` contributes no UB class of its own. It performs no
access, no arithmetic, and no sequencing decision. There is nothing here
that can devalue a proof through C's rules, so no inventory row is owed.

## 4. Verdict: admit with price

`inline` goes on the list with the price of section 3: a hint, static
only, ignorable without meaning change. Refusal was considered and
rejected: it would strip the hint off every generated accessor to buy
zero instructions at every level (section 2), while touching the
device-reader lines whose exact spelling the register tests hold.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `inline` row; the C count
falls by one step. The `unused` half of the usual pair is ruled in
`messung/CFORM-REGEL-ATTRIBUT.md`, so the accessor spelling carries zero
open doors after this note.
