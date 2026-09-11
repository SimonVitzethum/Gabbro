# CForm ruling: `void`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `voidTyp`, 930 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.voidTyp`). The type row
never names it, and the census counts the keyword lexically, so this is the
largest open C2 row by count and the cheapest to rule: there is no spelling
without it.

## 1. Emitter site

`void` reaches C through four generator families in
`crates/gabbro-check/src/emit.rs`, plus the checker-side word in
`crates/gabbro-check/src/namen.rs`. Every row below was read off the code;
the list is grouped because 930 keyword hits cannot each carry a row:

| generator lines | family | shape written |
|---|---|---|
| `emit.rs` 5082-5095 (`fnzeiger_deklarator`) | function declarators | result `None` becomes `void`, empty parameter list becomes `(void)`; the comment at 5074-5076 states why `(void)` and not `()`: an empty list means unspecified and is a different type |
| `namen.rs` 478-479, `emit.rs` 5962, 5971, 6020 | result-type lowering | missing result, `never`, ghost, or unit-less type all lower to `void` |
| `emit.rs` 1682, 2116-2117, 2231-2236, 2370, 3970, 3989, 11344, 11422, 11487 | prototypes and entries | `uint32_t gabbro_kern(void)`, `..._lies(void)`, `nimm` / `gib`, `lese_start` / `lese_ende`, `pruefe_<name>(void)`, `eintritt` / `gast` / `boot` |
| `emit.rs` 6329, 7141, 7679, 8551, 8897, 6344 | suppression casts | `(void)k;` for an unread parameter, an unread binding, an unread error name, a walk temporary, a match binder, `(void)_grund;` with the N034 finding |
| `emit.rs` 8075 | watchdog declarator | `static void (*const <marke>_wachhund)(void)` |

Two facts narrow the form, both read off the code:

- The `(void)` prototype is load-bearing correctness, not style. `int f()`
  declares unspecified arguments; `int f(void)` declares none. Under
  `-Wstrict-prototypes` the first is a warning and always a different type.
  A refusal that deleted `(void)` would change the declared type of every
  generated entry point.
- The `(void)k;` family is the silencer the warning net points at. The
  walker behind the decision (`emit.rs` 6495-6565) is measured in both
  directions: too many names and a dead parameter loses its cast, which
  `cc -Wextra -Werror` catches; too few and a live name is stilled.

Count: 930 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), five generator families.

## 2. Compiler fold

Two shapes of the same store, `cc (GCC) 16.2.1` on x86-64, instruction
counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef unsigned int u32;
void set_void(u32 *p, u32 v) { *p = v; }
u32 set_ret(u32 *p, u32 v) { *p = v; return v; }
```

The `ret` shape is what a refusal would have to write instead: a result
where the checker says there is none, so that no `void` appears.

| flags | void store | returning twin |
|---|---|---|
| -O0 | 10 | 10 |
| -O2 | 2 | 3 |

Reading: at -O0 the two shapes cost the same; at -O2 the `void` form is
shorter by one move (`mov %esi,(%rdi); ret` against the same plus
`mov %esi,%eax`). Refusal invents data flow the checker never promised and
pays a register move for it at optimisation. There is no third shape: C
has no empty result type besides `void`.

## 3. Semantic price

Admitting `void` pins two facts into the target language, and the note
names both because the admission is the ruling:

1. The empty result and the empty parameter list as declared types. A
   `void` function returns nothing and a `(void)` prototype takes nothing;
   both are part of the function's type, not comments on it. A proof that
   reasons about call compatibility must read them as types.
2. The explicit-silence idiom `(void)k;`. The cast evaluates and discards;
   it changes no value and orders nothing. Its only meaning is the one the
   warning net gives it: this name is deliberately unread here.

UB inventory: `void` contributes no UB class of its own. A `void` expression
is never read, and `(void)k;` performs no access. There is nothing here
that can devalue a proof through C's rules, so no inventory row is owed.

## 4. Verdict: admit with price

`void` goes on the list with the two prices of section 3: empty types as
types, silence casts as deliberate. Refusal was considered and rejected:
the prototype spelling has no meaning-preserving deletion (`()` is a
different type), and the result spelling has no replacement that does not
invent data flow (section 2 measures the invention at one move under -O2).

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `void` row, the largest
open one; the C count falls by one step and the strict and generous totals
fall together, since no generous reading ever covered this form.
