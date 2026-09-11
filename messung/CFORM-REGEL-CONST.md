# CForm ruling: `const`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `cConst`, 419 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cConst`).
Only `const` *discarding* stands on a never list; the qualifier itself is
on neither list, which is exactly the C2 shape. The second instrument
(strict conversion and promotion warnings over 101 compiled units) holds
measured, and this ruling books what that measurement covers.

## 1. Emitter site

`const` reaches C through four generator families in
`crates/gabbro-check/src/emit.rs`, grouped because 419 keyword hits cannot
each carry a row:

| generator lines | family | shape written |
|---|---|---|
| 525, 7992 (`konst` prefix), 1994-1995, 5259-5260 (`ctyp` pointer arm) | qualified types | `static const` stores, `const T *` against `T * const` by writability (`zeiger_schreibend`), `const void *` for read-only foreign parameters |
| 1890, 2040, 7995, 11500 | constant stores | `static const` table stores, cells, fixed arrays, boot constants |
| 3719, 3834, 4349, 4600, 4676, 11219-11226 | read-only handles | `const {dev} *d`, `const {n} *v` on every generated reader and validity function |
| 7353, 8532, 8550 | const locals | `const {typ} {b}`, `const uint32_t {r}` temporaries in the exchange and walk skeletons |
| 8075 | watchdog declarator | `static void (*const ...)(void)`: the const pointer itself |

Two facts narrow the form, both read off the code:

- The pointer-const placement is decided, not copied. `(false, false)`
  writes `const ` before the target, `(false, true)` after it (1994-1995),
  from the checker's own writability map. A read-only handle cannot be
  written through without a cast, and the cast would be a new form, not
  this one.
- The foreign-parameter word is `const void *` where the callee does not
  write (`namen.rs` 486-493). The conversion from the caller's pointer is
  C's own, which is why the second instrument can certify it instead of
  this note having to argue it.

Count: 419 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), five generator families.

## 2. Compiler fold

Two shapes of the same indexed read, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef unsigned int u32;
u32 rd_const(const u32 *p, u32 i) { return p[i] + 1u; }
u32 rd_plain(u32 *p, u32 i) { return p[i] + 1u; }
```

The `const` shape is the emitter's own read-only handle; the `plain`
shape is what a refusal would have to write instead.

| flags | const pointer | plain pointer |
|---|---|---|
| -O0 | 13 | 13, same mnemonic sequence |
| -O2 | 4 | 4, same mnemonic sequence |

Reading: the qualifier changes no instruction at any level; it speaks to
the type checker, not to code generation. Refusal would delete a contract
to buy nothing, and the deletion would widen every reader to a writer.

## 3. Semantic price

Admitting `const` pins two facts into the target language, and the note
names both because the admission is the ruling:

1. Read-only as a type, not as a comment. Writing through a
   `const`-qualified access path without a cast is a constraint
   violation; writing through it after casting the qualifier away is
   undefined behavior when the object itself is const. Every reader the
   emitter generates stays on the safe side by construction: readers take
   `const *` and never cast it off.
2. Discarding is the adjacent never-form and stays never. The admission
   covers the qualifier; it does not cover any cast or conversion that
   drops it. The standing measurement is the second instrument: `cc` with
   strict conversion warnings finds zero hits over the 101 units it
   compiles, so no emitted unit discards.

UB inventory: `const` itself contributes no UB class, but its boundary
does: a const-dropping access to a truly const object would devalue any
proof about that object's value. No new inventory row is owed beyond the
existing never-entry (`const` discarding), which this ruling leaves
exactly where it is. The proof-relevant fact booked here is the
direction: admission of the qualifier plus continued refusal of the
discard, held by the compiler measurement rather than by review.

## 4. Verdict: admit with price

`const` goes on the list with the two prices of section 3: read-only as a
type, discarding still never with the compiler as its guard. Refusal was
considered and rejected: it would widen 419 read-only sites into writers
to buy zero instructions at every level (section 2), and it would remove
the very contract the second instrument measures.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `const` row; the C count
falls by one step. The never-entry for `const` discarding is untouched by
this note and keeps its own count.
