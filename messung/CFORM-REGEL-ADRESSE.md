# CForm ruling: `&` address-of

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `adressVon`, 111 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.adressVon`).
The counter counts a `&` that opens an expression (prefix position) as
this row; `&&` and `&` as binary operators are their own allowed or ruled
entries. Like dereference, this operator has no Gabbro source spelling:
every site is machine text the emitter builds around a declared name.

## 1. Emitter site

`&` reaches C through four generator families in
`crates/gabbro-check/src/emit.rs`, grouped because 111 prefix hits cannot
each carry a row:

| generator lines | family | shape written |
|---|---|---|
| 7185, 7197, 7349, 7367, 7458 | atomics | `atomic_store_explicit(&{ziel}, ...)`, `atomic_load_explicit(&{quelle}, ...)`, the CAS retry `&{ziel}, &{h}` triple |
| 7654-7656, 7679 | call arguments | `&{local}` for out-parameters, `&{fehlername}` for the error slot, with the `(void)e;` guard where the branch does not read it |
| 9769, 9771-9773 | device transitions | `{dev}_{name}(&{handle})` for a value handle, bare name for a pointer handle; the branch is decided by the declaration, never guessed (9777-9784) |
| 3793, 6921, 9888 | place addresses | `&{name}` for device bases, `&{ziel}` for exchange targets, `&{basis}` where a `.`-place needs the entry address |

Two facts narrow the form, both read off the code:

- No user path reaches any of the four families. Call arguments come
  from the signature's out-parameters, atomics from the exchange
  lowering, transitions from the device declaration. A Gabbro program
  cannot take an address; only the generator can, and only of names the
  declaration already types.
- The transition branch refuses rather than guesses: an argument that is
  not a handle of that device is a named refusal, not a bare call
  (9777-9784). The `&` therefore never invents provenance; it forwards
  the one the declaration states.

Count: 111 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), four generator families.

## 2. Compiler fold

Two shapes of the same counter bump, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
typedef unsigned int u32;
static u32 bump(u32 *p) { *p += 1u; return *p; }
u32 via_addr(void) { u32 x = 41u; return bump(&x); }
u32 via_val(void) { u32 x = 41u; x += 1u; return x; }
```

The `addr` shape passes the local by address as the emitter's out-parameter
family does; the `val` shape is what a refusal would have to write instead:
the callee dissolved into the caller so no address is taken.

| flags | by-address call | inlined-value twin |
|---|---|---|
| -O0 | 18 | 7 |
| -O2 | 2 | 2, same mnemonic sequence |

Reading: at -O0 the address form pays the call (address materialisation,
call, frame); at -O2 the whole call folds away and both shapes are the
constant result. Refusal would dissolve every out-parameter call and every
atomic into its caller to buy 11 instructions at -O0 and nothing above
it, while touching the exchange loop whose pass bound is the point of the
construct. The atomic family has no twin at all: `atomic_load` of no
address is not a program.

## 3. Semantic price

Admitting `&` pins two facts into the target language, and the note names
both because the admission is the ruling:

1. Address creation with provenance. `&x` names the object `x`, and the
   pointer derived from it aliases exactly that object. A proof that
   reasons about which object a callee touches must respect the alias
   the `&` created; the `restrict` parameters beside these calls promise
   the callee touches nothing else.
2. Indirection as the call protocol. Out-parameters and error slots are
   written through the passed address; the write is sequenced inside the
   callee, and the caller reads the result after return. No new proof
   obligation arises beyond the ones the signatures already carry.

UB inventory: `&` contributes no UB class of its own. Taking an address
is always defined for an object the declaration types; the UB of a bad
use (null, dangling, misaligned) belongs to the dereference row ruled in
`messung/CFORM-REGEL-DEREF.md`, not to this form's. There is nothing here
that can devalue a proof through C's rules by itself, so no inventory row
is owed. The alias fact of item 1 travels with `satz_alias`, which grows
by these sites alongside the dereference ones.

## 4. Verdict: admit with price

`&` goes on the list with the two prices of section 3: provenance-carrying
addresses, indirection as the call protocol, no user path, no UB.
Refusal was considered per family and rejected on all four: the atomic
family has no address-free spelling, the out-parameter family would pay
call overhead at -O0 to dissolve its callees, and the transition and
place families forward declaration provenance that no desugar reproduces.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the fold table of
section 2, measured 2026-09-11 with `cc -O0/-O2 -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `adressVon` row; the C
count falls by one step. The dereference twin is ruled in
`messung/CFORM-REGEL-DEREF.md`, so the address/dereference pair carries
zero open doors after this note.
