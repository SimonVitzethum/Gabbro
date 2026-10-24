# Gabbro — the language

**What the language is, what each construct promises, and what it refuses.** Four mechanisms,
two declaration rules, and a library layer of constructs derived from them — enough to write
kernels, drivers and ordinary programs.

| For | Read |
|---|---|
| the notation (EBNF, closed vocabulary, one Lean constructor per production) | [`SYNTAX.md`](SYNTAX.md) — machine-read by guardians; **this file does not repeat it** |
| a first program | [`TUTORIAL.md`](TUTORIAL.md) |
| what is proved, and the goal theorem | [`PROOF.md`](PROOF.md) |
| the checker: every pass, rule and diagnostic code | [`CHECKER.md`](CHECKER.md) |
| why the design is the way it is | [`DESIGN.md`](DESIGN.md) |
| code generation | [`LLVM-BACKEND.md`](LLVM-BACKEND.md) (current), [`C-MEMORY-MODEL.md`](C-MEMORY-MODEL.md) (the C backend, removed 2026-10-17) |
| floats, heap, hardware | [`FLOATING-POINT.md`](FLOATING-POINT.md), [`PLAN-DYNAMIC.md`](PLAN-DYNAMIC.md), [`PLAN-HARDWARE.md`](PLAN-HARDWARE.md) |

**Standing words.** *Checked* means a pass of the Rust checker refuses the opposite, by a
diagnostic code. *Modelled* means the construct has semantics in the Lean model. *Not built* is
said where a construct is only decided. Where a code is cited it exists in `crates/`; a claim
beyond that is marked. The checker is unverified; what is proved, over which statement, is
[`PROOF.md`](PROOF.md)'s subject.

---

## 0. The promise — and the non-promise

**Gabbro proves everything except logic.**

| | who | how |
|---|---|---|
| **Plumbing** — index, overflow, alias, frame, lock, race, termination, phase, leafness, publication | **the language** | type rules M1–M4 and generated schemes. **No SMT, no solver, no heuristic**: "it compiles" is a function of the source, not of solver luck |
| **Logic** — *this* function does *the right thing* (`ensures` beyond the construction) | **the programmer**, in every language | every open logic obligation is emitted into a machine-readable **obligation manifest** (§15). Nothing is silently lost |
| **Plumbing carried by logic** | mixed | falls by construction but is **booked as logic**, because its basis is a logic invariant (§8.3) |

The promise is **relative**: *memory-safe under A1…An*. The assumption set (axiom layer, §12)
stands **in the product**, not in a footnote. A checker that refuses *by name* — one code per
reason, never a timeout, never "unknown" — is the design; `gabbro paesse` lists what each pass
does and does not carry.

**What may be said:** the goal theorem is proved over the Lean model, with a witness. **What may
not:** "Gabbro is verified" — the checker inside the statement is the Lean checker, and the
bridge to the Rust checker and the emitted binary is open ([`PROOF.md`](PROOF.md)).

---

## 1. Principle

Gabbro is **C without its holes, plus two things**. Everything else is a *restriction* of C,
not an extension.

| | Mechanism | Rule |
|---|---|---|
| **M1** | **Range types.** An integer carries its value range, and every operation must stay inside it (Ada's trick) | `u32 in 0 ..< N`; overflow is a compile error, not a runtime check |
| **M2** | **Linear values, ghost ones too.** A linear value must be consumed exactly once; a ghost one exists only in the proof and is erased before code generation (no byte, no heap) | `linear type`, `linear ghost type` |
| **M3** | **Address spaces and access rights on the pointer.** A pointer carries *where* it points and *what* may be done with it; barriers follow from the space | `ptr<mmio, w> T` |
| **M4** | **No unchecked index, no unbounded loop.** Indexing needs evidence of membership; every loop names its descent measure or its bound | `traverse`, `retry`, `forever` |
| **D1** | **Opaque new types**, no implicit conversion (C's `typedef` is transparent, and that is the hole) | `opaque type Pa = u64;` |
| **D2** | **Complete layouts, no catch-all branch.** Every bit of a word is named, every enumeration exhaustive | `exhaustive`, `format`, `tagged` |

The surface decisions **E1–E6** (`SYNTAX.md`): English keywords; statement-oriented, assignment
is not an expression; nothing implicit; contracts before the body in a fixed order; every
declaration complete at exactly one place; every attribute part of the production.

**What falls away from C:** implicit conversion, `void*`, pointer arithmetic without a basis,
`goto`, catch-all branches, `union` as reinterpretation, the preprocessor, exceptions,
inheritance, GC, self-hosting. **What C keeps:** functions, pointers, structs, fixed widths,
control flow, function pointers (with a contract, §5.6), explicit conversion between compatible
types.

### 1.1 The twenty "constructs" fall out — as a library, not as syntax

If a construct is left without a derivation, a mechanism is missing. That is the test of the
reduction.

| construct | follows from | how |
|---|---|---|
| units (`Pa`, `Iova`) | D1 | opaque new type |
| counters (`Refcount`) | M1 | the type does not leave its range |
| `reason`, ground sets | D2 | exhaustive enumeration |
| `bitfield`, `format` | D2 | complete layout |
| typestate (`state`, stages of a mark) | M2 | a linear value whose type carries the state. A separate `phase` word was refused: it would lower the vocabulary by one word and give a lowering theorem about nothing (a ghost mark emits no code) |
| `lock` / `held(L)` | M2 | `linear ghost Held(L)` — an own token nobody else can mint |
| lock **order** ⇒ deadlock freedom | M2 + M1 | the rank is a range type; taking requires a strictly smaller one |
| `atomic` publication | M2 | `release` hands a ghost token over, `acquire` takes it |
| effects (`reads`/`writes`) | M2 | ghost capabilities in the signature |
| `device`, register classes | M3 + D2 | `mmio` + class per field + complete layout |
| `traverse` | M4 | notation, not a mechanism |
| `check` | M2 | a linear obligation (§13) |

### 1.2 Four design rules — now derivations, kept for their sites

Each was a paid-for mistake in a real system; each now follows from the mechanisms.

1. **Total by construction** (M4). There is no unbounded loop; "finite" is the *weakest*
   promise — a loop with a step bound terminates and can still index outside the table.
   **The counter rule:** *every counter needs a bound in the declaration **and** a check before
   the arithmetic.* A `u64` without an upper bound cannot be incremented (M1 has no bound to
   compute against); `in 0 .. LIMIT` alone is not enough, since `+ 1` reaches `LIMIT + 1` and
   `M104` falls. The check goes **before** the arithmetic — a decrement with the zero test
   *afterwards* inverts the rule.
2. **No pointers, only offsets**, each against a length in scope (M1 + M4). An offset without
   the length it holds against is not writable.
3. **Refuse, never interpret** (D2). An unknown version, a set reserved field, a crooked length:
   a *named* refusal, one code per reason. Its price stands at `by unvisited`: a mere step
   counter would cut a cycle off silently, which is interpretation — so the language forces the
   expensive version (bitmap or generation stamp).
4. **Fixed widths, spelled-out byte order** (D1 + D2). No `usize`, no host layout. What stands
   on the wire stands in the descriptor.

---

## 2. Lexis and vocabulary

Identifiers, numbers with `_`, comments (`//`, nesting `/* */`, doc `///`), floating-point literals (§3.5), strings only in
`claim`, `reason`, `assume`, `section`, `unfalsifiable`.

**The vocabulary is a closed table** (`SYNTAX.md`, the terminal and reserved-word tables are held by `cargo test`, run by `instrumente/pruefe-pruefer.py`; the retired `pruefe-wortschatz` also compared EBNF
terminals against table words, both readings). *A new word is a language change*: it needs an
entry in the table, in `kw.rs`, and in the terminal count. Everything else is an identifier, and
a word of the table is a keyword **only where the grammar expects one** — contextual words
(`tree`, `parent`, `child`, `sibling`, `string`) stay identifiers elsewhere. A second word for an
existing notion costs more than a second site for an existing word.

---

## 3. Types and ranges — M1

### 3.1 Declarations

```gabbro
module sprache::bereiche {

const NSLOTS : u32 = 64;

type SlotIdx  = u32 in 0 ..< NSLOTS;
type Refcount = u32 in 0 .. 1000;
opaque type Pa = u64;

// an underflow is not typable: the V1 fact carries `c >= 1` into the branch
impl fn runter(c : Refcount) -> Refcount
    effects { pure }
    costs   <= 4 ops
{
    if c >= 1 {
        return c - 1;
    }
    return c;
}

// what no flow rule carries needs `narrow` with a named exit
impl fn schmal(x : u32) -> SlotIdx
    effects { pure }
    costs   <= 4 ops
{
    narrow x to 0 ..< NSLOTS else { return 0; }
    return x;
}

}
```

Every integer type carries its range; `u32` without `in` is sugar for `u32 in 0 .. u32::max`.
Every operation must stay inside the range of its **result** type: if `a + b` does not fit the
target, that is a compile error (`M104`), not a runtime check. Division and remainder demand a
denominator whose range excludes zero (`M102`). The operator table with the range each operator
computes is `SYNTAX.md` §4. `opaque` forbids the arithmetic of the carrier (`D003`) and, outside
the declaring module, the conversion in both directions (`D004`).

### 3.2 The three flow rules — closed, local, predictable

`narrow` alone would become a ritual (measured in the reference kernel: 102 of 255 subtractions are
flow-sensitive, 54 of them relational), so there are exactly **three** rules. They are syntax-directed, **without
fixpoint and without solver**: the checker keeps a *fact set* per block that grows only at the
three named places and **dies on every write to a participating place**. Loops carry no facts
inward.

| | Rule | Example |
|---|---|---|
| **V1** | a checked **range condition** narrows the checked place in the branch after it | `if x >= 1 { … }` → `x : u32 in 1 .. max` |
| **V2** | a checked **relation between two places** is a branch fact; under `a >= b`, `a - b` has type `0 .. a.max − b.min`. Comparison facts over directly checked places only | `if a >= b { let d = a - b; }` |
| **V3** | a `match` on a `tagged` type narrows in the branch to the variant, payload included | exhaustive, no catch-all |

What falls under none of them needs `narrow place to range else { … }` — a statement with a named
exit, not a proof line. **The yardstick stays:** if `narrow` outgrows the remainder of the
counter-measurement (set at ≤ 24 sites; this count is a yardstick, not re-measured here), the rule set is too small, and *that* is the
refutation, not a silent growth of rules.

**Two preconditions on V1/V2**, both once held silently:

* **The place must stay the same between check and use.** A place that leads through a `device`
  register carries **no** fact: `volatile` *is* the statement "this may change between two
  reads". The way out is the ordinary form — `let i = d.ST.IDX;` (a local binding is not
  volatile), then test `i`.
* **The negation of a comparison must itself be a comparison** — a total order. Over integers
  `!(x < y)` gives `x >= y`. A partially ordered carrier (NaN) would break it (`else` would give
  *nothing*); floats are finite by type (§3.5), so the rule holds, and any partially ordered
  carrier the language ever gets must write both branches positively.

**One exception that *generates* a fact.** A loop carries nothing inward, but a counter set to a
constant before a bounded traversal, and inside the body only ever the target of `n += k` with a
positive constant `k`, is bounded by the domain: at the increment `n ≤ c + (B−1)·k`, after the
loop `n ≤ c + B·k`. Five conditions, each a refusal if missing: local scalar set from a constant;
only `n += k`; computable domain bound; **not nested** in another loop; nothing takes its address.

### 3.3 New types and sums

`opaque` forbids conversion in both directions. `tagged` is the sum type; `match` over it is
exhaustive, and a `Variant(e)` is the construction (unknown/ambiguous case `N280`, payload
mismatch `N281`–`N284`). There is **no general `option T`**: over `index into T` it is the
table's index option; over anything else the writer spells a two-case `tagged` type. The index
option is read by `match` (`Some(i)`/`None`) or tested by `x.is_some()` (`Expr.istSome`, a `bool`; over
anything but an option at a place `N593`).
`string max N` is a bounded string (one length word plus `N` bytes, no terminator).

### 3.4 Bits, widths, shifts, overflow

Decisions that shape every bit-level program. **Order of search for a new error class, binding
on every construct:** first a formulation in which the error is not expressible; then a
construction that makes the check structurally unnecessary (iteration, non-zero types,
intrinsics with a result range); then a value in the type (`index into T`); only then a runtime
check (`narrow … else`).

```gabbro
module sprache::bits {

type Refcount = u32 in 0 .. 1000;

// exact `uN` ranges wrap; a clamp is defined on every range
impl fn umlauf(a : u13, b : u13) -> u13
    effects { pure }
    costs   <= 4 ops
{
    return a +% b;
}

impl fn klemme(a : Refcount, b : Refcount) -> Refcount
    effects { pure }
    costs   <= 4 ops
{
    return a +| b;
}

}
```

* **`uN` / `iN`** (`N` = 1 … 64) is sugar: `u13` is `u16 in 0 .. 8191`, `i37` is
  `i64 in -2^36 .. 2^36 − 1`; storage is the next standard width. A packed table or format field
  of `u13` occupies exactly 13 bits. `u0`, `u65` and wider are refused (`P008`).
* **Overflow forms.** `+% -% *% <<%` exist **only on exact unsigned `uN` ranges** (`M153`
  otherwise, naming `+|`): mod 2^N is free in hardware, while on `0 .. 5` it would cost a
  division. `+|` (saturating) is defined on every shared integer range (`M154` on two ranges). An
  operation without a suffix must fit its range by construction. A literal operand takes the
  other's range when its value lies in it.
* **Shifts.** A shift whose result range does not fit the width falls at `M104`; a dynamic left
  shift is therefore usable only as `<<%` on `uN`. `>>` is the logical shift on non-negative
  operands. An arithmetic shift (`sar`) is decided as a separate explicit operation on signed
  operands, never implied by signedness — *not built*.
* **Intrinsics — the zero case lives in the argument type.** `clz`, `ctz`, `log2_floor` take an
  operand whose range excludes zero (`M157`, like a divisor) and answer `0 .. w−1`; `popcount`
  answers `0 .. w`; `rotl`/`rotr` need the exact full `uN` range and an amount in `0 .. w−1`
  (`M159`); `bswap` needs `u16`/`u32`/`u64` (`M160`); every operand is an unsigned standard
  width (`M158`). There is no convention like `clz 0 = w`: with it `31 − clz(x)` would leave the
  range the checker promised, exactly at the case the convention introduced.
* **Precedence.** `<< >> & ^ |` form ONE flat left-associative level and sit *below* the
  comparisons (`a & b == c` means `(a & b) == c`); C grades them into four levels and puts
  `& ^ |` *above* the comparisons. Where the two tables disagree and the author wrote no
  parenthesis, **`M136` refuses** (9 of 25 operator pairs and 3 comparison forms compute a
  different value; the compilers' own warning is silent at six of the nine). Gabbro's table is
  deliberately *not* aligned to C's: `&` below `==` is C's acknowledged mistake. A generated C
  backend parenthesises the tree, so the product computes what the checker proved.
* **Compile-time evaluation** is by certificate: the checker evaluates the total, effect-free
  fragment, and a Lean re-check validates a list of explicit entries, entry by entry — never a
  definitional comparison of whole tables (kernel reduction of a four-level walk is unusably
  slow), never `native_decide`.

### 3.5 Floats

`f32`/`f64` are **finite and range-carrying**: in the core a float type always carries a range
(`f64` alone is sugar for the widest finite range), so NaN and infinity are not values of any
type, and comparisons are total. A literal that is not exactly representable needs `rounded`
(`const TAU : f64 = 6.283185307179586 rounded;`) — *what is forbidden is not the inexact but the
silently inexact*. `narrow x to 0.0 .. 1.0 else { … }` and `narrow x to finite else { … }` are
the NaN path; two comparisons whose intersection is finite carry the same fact. The checker
tracks an interval plus "can be NaN / infinite"; it does **not** promise numerical accuracy.

The semantics is a concrete kernel-computable IEEE-754 model with correspondence lemmas for the
C forms ([`FLOATING-POINT.md`](FLOATING-POINT.md)). Contraction (fused multiply-add) changes results, so
the program's hardware `profile` (§12.2) pins `fp_contract off`; a profile with another value
contradicts the float rules. The legacy C backend pins `-std=c11 -ffp-contract=off` and asserts
`FLT_EVAL_METHOD == 0`. `libm` functions are **not** in the language: each would be a shipped
correctly rounded implementation in Gabbro or a named assumption.

---

## 4. Linear and ghost values — M2

```gabbro
module sprache::linear {

linear type Parked;                  // a real resource: bytes in the product
linear ghost type Zeuge;             // a token: erased before code generation
linear ghost type Phase order { roh, bereit };   // a token with stages

}
```

**Linear means linear, not affine:** a linear value is consumed exactly once. Dropping it is a
compile error; leaving a scope that holds linear values demands they be named (`leaves`). There
is no copying. Ghost values have **no lowering**. A `linear type T;` *without* a body is a token
that lowers to one byte — the ghost is erased, the token is not; an emitter that lowered both
alike would make `ghost` decorative.

**Who may produce a witness is closed**, so a hand-built token is a *type error*: `Held` only the
`locks` block, `Member` only the compiler's domain enumeration, `MayWrite` only the generated
capability resolution, `Duty` only `check`, `BootPhase` only the entry path, `Has` only the
CPUID probe, `Vis` only the success branch of an `awaits`/`exchange`. **`Vis` is the one affine
ghost value**, by decision: visibility does not expire. A token may carry an `order { … }` of
stages; `advances a -> b` goes forward only, and the mark stands at its source stage at the call
(`O001`–`O007`).

**Protocol races fall out of M2, and those are the expensive ones.**

| class | falls out of |
|---|---|
| data race | M2 + M3 (Rust does it too) |
| *visibility before completion* (a thread runnable before it has authority) | M2: the phase is a linear value (`Parked` → `admit`) |
| *lost wakeup* (one bit for four reasons) | M2: the waker consumes exactly its reason |
| *publication without payload* | M2: `release` hands a ghost token over, `acquire` takes it |
| progress / starvation | **nothing** — no mechanism addresses liveness, and that stays said |

Phases and lock tokens being linear values means they stand in every signature that touches
shared state — which is why this is in the language now and not a later retrofit.

---

## 5. Pointers, address spaces, embedded pointers — M3

### 5.1 Spaces and rights

```gabbro
module sprache::zeiger {

type Kopf  = { x : u32, y : u32, };
type Worte = { w0 : u32, w1 : u32, };

// a re-view: the answer has the root of its argument
extern fn sicht(r : ptr<normal, r> Kopf) -> ptr<normal, r> Worte effects { reads r } costs <= 4 ops;

impl fn lesen(k : ptr<normal, r> Kopf, w : ptr<normal, r> Worte) -> u32
    effects { reads k, reads w }
    costs   <= 8 ops
{
    return k.x;
}

// two views of one root, both read-only: fine
impl fn nur_lesend(k : ptr<normal, r> Kopf) -> u32
    effects { reads k }
    costs   <= 32 ops
{
    let w = sicht(k);
    return lesen(k, w);
}

}
```

`ptr<space, rights> T`: space is one of `normal mmio dma code boot port` or a declared name;
rights are `r w rw x own[@ident]`. **A pointer names a declared carrier and nothing else** —
its only producer is `&T`; there is no address of an expression and no arithmetic on a pointer.
An access `p->f`, `p[i].f` is the same access as `T.slots[i].f` with the same guards: a pointer
is not a way past a lock or an owner mark. A write needs `rw` **and** the write right of the
enclosing contract (`R002`/`R003`). The barrier follows from the **space**: an `mmio` access is
volatile and unreorderable, a store to `dma` carries the target's publication barrier, and a
carrier with generated `ops` is not placed in `dma` (`R001`).

**Aliasing is decided at calls, not by an alias analysis.**

* **Roots (`R014`).** The root of a pointer is the parameter it came from; a function that takes
  *and answers* a pointer (a re-view) answers a pointer with the root of its argument — it
  *borrows*, it does not consume. Two pointer arguments of one call must not share a root when
  one of the two parameters is writable or `own`. A pointer the pass cannot trace (a field, an
  index, an indirect call, a computed argument) is **unknown and equals every root**. Two
  read-only views are free. The stale-checksum defect — a header read through one view after a
  write through another — is exactly this shape.
* **The boundary (`R015`).** A function that assumes two of its pointer parameters distinct, and
  is `pub` or called by no body of its unit, says so: the distinctness is a *named assumption*
  about a caller outside the unit (a hint, not a refusal — refusing would tighten every export
  with a pointer pair).
* **`own`** is a *loan*, not a note: `ptr<…, own> T` is sugar for "`T` is owned and the callee
  borrows the mark for the call", and it comes back. Two `own` parameters of one carrier are
  not derivable (`R004`); one place at two writable parameters falls at `R007`.
* **`noalias`.** A writable pointer parameter of an *internal* function the checker holds the
  whole call of (not `pub`, called from a body of the unit, address never taken, effects naming
  nothing but its own pointer parameters) is emitted `noalias` — resting on `R014` and the
  named `R015` assumption. The model side is `Logik/Vertraege/Objekt*.lean`; the rule itself is
  a Rust checker rule, not yet a Lean judgment.

Lifetimes and a general borrow checker are not built on purpose; a fragment that needs one is
booked as a fifth-mechanism finding rather than smuggled in. Design record:
[`A1-OWN-PAPER.md`](A1-OWN-PAPER.md).

### 5.2 Pointer arithmetic has exactly one form

`place[expr]` with an M1-bounded index, and `offset_into` in formats. Otherwise none — an index
through a *byte* pointer is held against an extent the function's own `requires n <= lenof(p)`
(or a gate's `ensures`) names (`N571` at the index, `N463` at a call, `N464` at a gate); a
pointer with no extent cannot be indexed.

### 5.3 `embeds` — a PTE is pointer and bitfield at once

```text
format Pte endian little {
    present  : bool @0,
    writable : bool @1,
    nx       : bool @63,
    pfn      : Pa embeds [51:12] scale 4096 where aligned(it, 4096),
}
```

An `embeds` field carries a **typed value inside a bit range**, scaled: reading `pfn` delivers
`Pa` (`[51:12] << 12`), writing demands the `where` condition (`aligned` is a built-in over M1,
no solver), and the lowering is mask-and-shift computed at translation time. The multi-bit-field
class of device registers and the PTE class are **one** construct.

### 5.4 `walk` — self-describing, multi-level tables

```text
walk PageTable levels 4 {
    node : [Pte; 512],
    down : pfn when it.present && !leaf(it),
    leaf : it.present && (level == 0 || it.large),
    invariant wx_disjoint cost O(n) runs online :
        forall m in mappings of Self: !(m.writable && !m.nx);
}
```

`down` names the embedded field along which the descent goes; `levels` is a constant, so the
depth is M1-bounded and termination falls by construction. From the declaration the compiler
generates the enumeration, the traversal, the induction scheme and the mutation operations of a
`table`. The generated domain `mappings of` has `node length ^ levels` entries (68 719 476 736
for four levels of 512 — *not* `levels × length`); a run-time traversal over it therefore holds
no cost promise, and W^X is a statement about the **set**, meaningless over one path.

### 5.5 Byte pointers and regions

A byte carrier is a table whose field is `u8 in 0 .. 255`; `n` bytes from index `i` are one
number `0 .. 256ⁿ−1`, with the bound `hi(i) + n ≤ count` as the attribute. A `format` over a byte
carrier is a *view* — two views on the same bytes read the same world.

**Memory from outside comes as a region, never from a number.** A gate (§16) may answer
`-> ptr<normal, …> u8 or R` whose contract names the extent (`ensures n <= lenof(result)`); a
`let … else` that binds the answer to a name bound once and never assigned carries it, and every
index (`N571`) and every length handed on (`N463`) is held against it. **No expression turns a
number into a pointer** (`M140`), and thread start is a template, not an int-to-pointer cast. An
extent never crosses a thread (`N578`: the stack parameter of a gate is an integer), so region
bytes are thread-private memory.

*Machine G has no byte pointers yet* (`LG002`): programs using one stay `UNCERTIFIED`. The
design is a `Ty.bytes` place (a declared byte field from slot `k` on, or region `r` from byte `k`
on), a `regionen` store with an owner per region, a logic stop `Logik.ausdehnung`, and one race
leg ("every region access is made by the region's owner"); slices S1–S5 move `Spec.lean` and are
waiting for a coordinated freeze of the model's core inductives. **OFFEN O37** also names the
missing release of a region and the passing of an extent by a Gabbro body.

### 5.6 Function pointers carry their contract

`fn(…) -> T effects { … } costs <= n ops` is a type; the value is `&f` (the one `&` that takes a
name, not an expression). At an indirect call there is no name to resolve, so what is known about
the callee stands at the type (`N035` demands `effects` and `costs`). The type is STRUCTURAL
(2026-10-21): `&f` fits wherever `f` conforms to the type -- equal parameters, result and reason
channel, `f`'s writes among the type's, no lock held or taken by `f`. A call through the pointer
is checked against the type. A `requires` and an `ensures` at a pointer type are refused
(`N589`): the model's signatures carry no contract yet (TODO O43).

```gabbro
module sprache::fnptr {

type Treiber = {
    bereit : fn() -> bool
        effects { pure }
        costs   <= 4 ops,
    senden : fn(u8)
        effects { pure }
        costs   <= 4 ops,
};

impl fn hart_bereit() -> bool
    effects { pure }
    costs   <= 3 ops
{
    return true;
}

impl fn hart_senden(b : u8)
    effects { pure }
    costs   <= 3 ops
{
}

impl fn baue() -> Treiber
    effects { pure }
    costs   <= 2 ops
{
    return Treiber(bereit: &hart_bereit, senden: &hart_senden);
}

impl fn ausgeben(t : ptr<normal, r> Treiber, b : u8)
    effects { reads t }
    costs   <= 12 ops
{
    if t->bereit() {
        t->senden(b);
    }
}

}
```

| rule | code |
|---|---|
| `&x` where `x` is no function | `M127` |
| the producer promises more than its slot (arity, effects, costs) / the signature differs | `M128` / `M141`, `M142` |
| call through a place with no `fn(…)` type | `M129` |
| `locks`, `masks`, `consumes`, `publishes` at the type — they do not cross an indirect call | `N036` |
| `requires` or `ensures` at the type — a pointer type is a signature without a contract | `N589` |
| `&f` where `f` requires `Held(..)` — no lock crosses an indirect call | `N590` |
| an indirect call with another number of arguments than the type declares | `N296` |

Conformance is decided (`Deklaration.passt`, `SigPasst` in the Lean model): effects `⊆`, arity
and signature by the checker; a contract on the type would need a contravariant `requires` and a
covariant `ensures` in the model first. **The honest gap:** lock order, interrupt context, linearity and pairing do
not cross an indirect call — a program that would need that does not pass (measured need in the
reference code: zero of four indirect call sites take a lock). A `let … else` over an indirect
call is refused by the emitter by name (the type has no `or R` channel). `entry fn(…)` is a
separate type: code handed in by generated driver C, held by `N575`–`N577`.

### 5.7 User memory

Bytes on the far side of a user/kernel boundary may be rewritten between a range check and the
copy. There are exactly two sides, a *user region* is declared with base and length, and a
**validated copy** is one copy through a checked handle — the checked address is the copied
address, and the value agrees under the single-copy-atomicity premise, named and satisfiable.
Lean: `Adressraum.lean`. What stays open: a range check *inside* the run and a user partition in
the world.

---

## 6. Predicates — the line, with the eighth domain

```text
quant  = ( "forall" | "exists" ) ident "in" domain ":" pred ;
domain = slots of | chain(a, b) in | descendants of | ancestors of | queue | fields of
       | elems of | threads | mappings of
```

**Closed set of domains. Nesting at most two. `old(place)` only in `ensures`. `count n in D : p`
over ONE table only** (a cross-table count is a `group` invariant). No user-defined quantifier
domains, no recursion in `spec fn`, no handwritten lemmas. If a property falls out of the
domains, it is **not formulable** — it migrates as a named `obligation` into the manifest (§15),
not into a comment.

**A domain binds the ADDRESS of an entry** — `slots of`, `elems of`, `descendants of`, `queue`
bind an index or handle and the element is `p[i]` (from an index one gets the element, not the
other way). `mappings of` is the one exception: it quantifies over the reachable leaf entries of
a `walk`, including virtual address and level.

**The cut for declared functions in domains.** A function that takes a value and delivers an
`option` value without touching the world is a *declared step*: it may generate witnesses in a
domain (the surface today is `chain(a, b) in place` and `reaches … via`; a chain over an
arbitrary declared function is the decision's reach, not a built form). Quantifier stock begins where the same function appears in `requires`,
`invariant` or `ensures` — there, not earlier, the line between language and prover migrates.
(Precedent: the pure `update` body of `exchange`, §11.6.)

---

## 7. Functions, contracts, costs

```text
fndecl = [ "pub" ] [ "spec" | "impl" | "raw" | "divergent" | "prim" | "extern" ]
         "fn" ident "(" [ params ] ")" [ "->" typeexpr [ "or" reason ] ]
         [ "requires" predlist ] [ "ensures" predlist ] [ "maintains" identlist ]
         [ "effects" "{" efflist "}" ] [ "costs" "<=" expr "ops" ]
         [ "by" inductlist ] [ "section" string ] [ "arch" ident ]
         ( block | "=" pred ";" | ";" )
```

Contracts stand **before** the body in this fixed order, so a tool that does not sort can say
"`effects` is missing here".

**`effects` is not fail-open.** Where the body settles the hull, an omitted clause is *derived*
and checked exactly like a written one; whoever touches nothing derives `effects { pure }`. A
written clause is the enforced bound: the body must stay inside it (`E008`, `E010` for reads).
Where nothing settles — no body (`extern`, `prim`), an unresolvable edge, a callee promising
more than its deeds cover — the omission is refused with the reason (`N305`). `gabbro abgeleitet`
prints the derived clause per routine.

**`costs` counts operations, and the unit is defined: 1 op = one Gabbro primitive** (assignment,
arithmetic operation, load, store). A call counts the **declared** `costs` of the callee; a
traversal counts body × domain bound; branches count the maximum. It is a **property of the
program**, computed statically (`gabbro kosten`), not a time measurement; there are no cycles in
the language. An omitted `costs` is never refused (it is not a promise); a written bound is what
the body is held against (`K001`); calling a gate or `extern fn` with no countable promise is
`K003`/`N322`. Two sharpenings:

1. The four primitives are conclusive: `if`, `match`, `return`, `leave` cost **nothing** (the
   *condition* costs); and what is fixed at compile time (`GRENZE`, `NSLOTS * 8`) is not a load.
2. What stands after a branch that **always leaves** lies on the other path — otherwise every
   early return pays twice and the number measures a path no run takes.

`raw fn` demands `&BootPhase` (§12.2); `divergent fn` is spoken-out non-termination (idle loop,
main loop); `prim fn … -> never` is a primitive that does not return (`switch_to`, `resume`: a
stack switch is expressible in no structured language, so it is *emitted*, not written); `spec fn`
is a specification, never code.

---

## 8. Statements

### 8.1 Stock, and a function that can fail

`let` (with `else (e) { … }` as the **only** error propagation: the branch diverges or returns),
assignment (not an expression), `if`, exhaustive `match`, `narrow … else`, `locks` block,
`return`. Operator precedence is §3.4.

**A function that can fail says so: `-> T or R`.** Both questions — what does `e` hold, how does
a call report failure — are answered at the *callee's declaration*, the one place an answer can be
checked.

```gabbro
module sprache::fehler {

type Idx = u32 in 0 .. 7;

reason Fehler {
    Leer   = 1 "the source was empty"
    Kaputt = 2 "unreadable"
    exhaustive
}

extern fn hol() -> u32 or Fehler effects { pure } costs <= 1 ops;

// the consumer: `let … else`, and `e` is a value of the reason
impl fn nutze() -> u32
    effects { pure }
    costs   <= 8 ops
{
    let x = hol() else (e) {
        match e {
            Leer   => { return 0; }
            Kaputt => { return 1; }
        }
    }
    return x;
}

// the producer: `return R::F;` is the failure exit
impl fn erzeuge(f : bool) -> u32 or Fehler
    effects { pure }
    costs   <= 4 ops
{
    if f { return Fehler::Kaputt; }
    return 7;
}

}
```

Three decisions sit in the lowering `bool f(T *_wert, R *_grund)`: success is the *return value*,
not a sentinel inside the result (a sentinel would narrow the type — `option index into T`
already does that); the reason leaves through its **own out-parameter**, since `reason` values
are given by the human and there is no free "no error" word; `bool`, not `int`, because there are
exactly two exits. Rules, **in the checker, not only the emitter**:

| code | refusal |
|---|---|
| `N028` | a `let … else` over a function that declares no `or R` (the branch could never run) |
| `N029` | a call to a function that *can* fail, outside a `let … else` (the reason falls on the floor) |
| `N034` | a body of its own that declares `or R` and never returns a reason |
| `M122` | `return R::F;` in a function whose `or R` is a different `R` or none |
| `M124` | a reason compared against anything but a reason of the same declaration |
| `M123` | a `match e` over a reason that is not exhaustive |

#### 8.1.1 The producer — `return R::F;`

A reason goes through exactly two doors (`return`, and comparison within its own declaration);
the number in a `reason` line is there so a *report* can name it. A `reason` is an item kind
that carries `pub`, so a fallible function can leave its module.

### 8.2 `leave` and `next`

`leave L;` and `next L;` target a **named** loop; there is no unnamed `break`/`continue` (with
nested loops the target would be convention instead of syntax). `leave` out of `forever` is the
orderly shutdown: the `leaves` clause names the linear values that leave through the exit.

### 8.3 `breaking` — with a booking rule

`breaking I { … }` names the region in which invariant `I` **rests**. Inside it `I` is not
available as a premise: functions with `requires I` or `maintains I` are not callable. At the end
`I` must be restored — *by construction only if the block closes with a generated operation of
the structure*; otherwise the restoration is an `obligation` in the manifest. **The booking rule:**
if a plumbing obligation falls only via a logic invariant, it is booked as logic — otherwise
"falls by construction" becomes the convenient booking.

#### 8.3.1 `I` has to BE something — `D013`

`D013`: `I` must name an invariant this unit declares (of a `table`, `group`,
`walk`, or a `spec fn`: exactly the list `maintains` accepts). A `breaking` on the
wrong-but-existing invariant still passes: the rule checks that the name resolves, not that the
invariant really rests here.

---

## 9. Loops — three forms

### 9.1 Grammar and bounds

```text
traverse = "traverse" ident [ "of" expr ] "over" domain
           "by" ( "unvisited" | "consuming" ) [ "decreases" expr ] [ "touches" efflist ] block ;
retry    = "retry" [ ident ] [ "until" pred ] "bounded" expr "ops"
           [ "progress" ident ] "on_exceeded" ident [ "effects" "{" efflist "}" ] block ;
forever  = "forever" [ ident ] "per_pass" "bounded" expr "ops" "on_exceeded" ident
           "effects" "{" efflist "}" [ "progress" ident ] [ "leaves" identlist ] block ;
```

**Every loop names its bound or its measure.** `traverse` iterates a declared domain (an index
outside the set is not formulable); `retry` is the bounded wait loop — `bounded` is a *number of
ops, not a descent measure*, `progress` names **who** ends the loop (an assumption with a
falsifier — the watchdog *is* the falsifier), and `on_exceeded` is rule 3: the overrun is named,
not interpreted; `forever` is the service loop, with `per_pass bounded` over the pass's *own* ops
(which may depend on pass inputs: `64 + 12 * lenof(msg) ops`) and `on_exceeded` obligatory.

### 9.2 `by consuming` — the witness order is part of the domain

The loop variable is a `linear ghost Member(domain)` that the body **must** consume. A domain
that offers `by consuming` delivers its witnesses in the **well-founded order the structure
generates** — for `descendants of` *depth-descending* (children before parents), for `chain` the
chain order, for `mappings of` leaf-upward. The witness therefore carries "all successors in the
order are already consumed", which is exactly **leafness at the moment of consumption**;
`delete_leaf(it)` demands it as `requires`, and it comes from the order, not a runtime check.

The edge a tree domain walks is named **once, at the table** — `tree { parent elter, child
erstes_kind, sibling naechstes }` — checked once (`D006`–`D008`), and holds for every domain
that needs it. A table that declares only `parent` makes `descendants of` a named refusal. The
three edges are all named because post-order lowers *without a stack* (child down, sibling
across, parent back; a stack as deep as the tree is high would be `count` entries of kernel
stack); every edge is read **before** the body runs, since the body may destroy the node.
Booked honestly: "witness set empty ⇒ set empty" and order preservation fall due once per
construct in the generator's template — amortised, not eliminated.

### 9.3 `forever` — lock waiting time, decided

Lock waiting time does not count into `per_pass` and must nevertheless not be unbounded; the
resolution is compositional:

1. Every lock declares `held <= K ops` (§11.2); a `locks` body costing more is a compile error
   (`K002`).
2. In `forever`/`retry` only a lock **with** a `held` figure is takeable — an unbounded ticket
   spinlock is not writable in a service loop.
3. `per_pass bounded` counts the pass's own ops.
4. The **latency statement per waiting site** is derivable (higher-ranked holders hold at most
   the sum of their `held`) and emitted as a number into the product — a derived quantity,
   nobody runs parallel to the truth.
5. For locks taken shared point 1 holds with a different number, `shared held` (§11.2.1).

---

## 10. `format`, `table`, `walk`, `device`

### 10.1 `format` — wire formats

A pure function at a boundary: bytes in, structure **or named refusal** out. Fixed set: fields
with ranges, `where` conditions, `offset_into` against `lenof(Self)`, `endian`, `@version` with
**refusal instead of migration** (measured: 0 of 11 format changes in the reference code were
migrations). The reader checks the buffer length **once at entry** and everything after is a
proven access; the writer is the inverse; `read(write(x)) == x` is obligatory in the differential
test. Generates reader, writer, fixed-width layout, and one code per refusal reason. *Open:*
variable lengths, version evolution.

### 10.2 `table` — tables with invariants

```text
table Slots count 80256 {
    slot { used : bool, parent : option index into Slots, gen : u32 wrapping, }
    invariant kind_zeigt_zurueck cost O(n * kette) runs offline : forall s … ;
    ops insert, remove, relabel, delete_leaf;
}
```

A format is a function; a table is **mutated state**, and the cut decides the value of the
construct. **`ops` names the generated mutations**; per operation the generator shows *once over
the declaration* that every `online` invariant is preserved. A handwritten mutation on a table
with `ops` is a compile error (`D001`), a field `by ops` too (`D002`); a table *without* `ops` is
description with a generated checker — one line apart, so the choice is visible. Invariants
carry `cost O(…)` and `runs online | offline` — an invariant without a cost figure is not an
audit under a core lock but an outage. Wrapping is spoken (`wrapping`): a wraparound nobody
spoke out is a mistake, one that carries the word is a design.

*The free list* (reuse without fragmentation) is a **pattern**: typed compartments do not
fragment, so a head plus a `naechst` chain gives reuse of whole slots with no size classes
(`beispiele/27`, `58`). It gives **no** use-after-free protection — that half is the arena's
`free` (§17), whose index dies statically.

#### 10.2.1 `breaking` is not a write right

A hand mutation inside a `breaking` block on a table with `ops` is `D001` exactly as outside it,
and `D002` on a field `by ops` — both bolts hold. What `breaking` changes is the *measurement*:
the carrier drops out of the count "K holds" (all mutations generated), because a region in which
a statement rests is exactly the region the argument "the generator shows it once" does not
cover. If `breaking` were a permission for `by ops`, `by ops` would be a suggestion with a back
door.

### 10.3 `device`

`class r|w|rw|w1c|rc` per **field** (a mixed register carries both kinds), `bank … at expr stride
… count …` (M1-bounded), `mirrors … from …`, and `transition` over the **whole written word**
including `keeping` — a read-modify-write on a `w` register stays unformulable. `transition …
publishes { place }` is device publication (§11.3). A device register read twice is two reads
(§3.2); a **`port` device** (x86 `in`/`out`, console, PCI config) is a sixth address space
lowering to `in`/`out` instead of volatile loads, declarable only under `arch x86_64`; a `bank`
inside one is refused (no clause bounds its base inside sixteen bits).

---

## 11. Concurrency

**Race freedom is a shape.** Every access to a carrier derives its guard (`Held(L)`,
owner mark, or atomic), every `locks` derives its rank, every publication its pairing — and
`Wettlauf.lean` proves over *any interleaving* of such traces that two accesses of different
threads to one carrier are ordered by happens-before, **or the carrier is `atomic`**, whose order
is the memory model, a named hardware assumption. There is no third case.

### 11.1 `atomic`

`atomic A : T [publishes { … }] [acquire|release|seq|relaxed] [observed by assumption] ;`. The
ordering words are **derived and checked** from the pairing (§11.5), not chosen: `publishes`
forces at least `release`, `awaits` at least `acquire`; `relaxed` is writable only payload-free.
`observed by a` says the other side stands in silicon, with the falsifiable assumption `a`.

### 11.2 `lock` — rank and hold time

```gabbro
module sprache::nebenlaeufig {

const NSLOTS : u32 = 64;
type Rechte = u32 in 0 .. 15;

table Kappenraum count NSLOTS {
    slot {
        belegt : bool,
        rechte : Rechte,
    }
}

// `rank`: a lock may only be taken under strictly smaller ranks;
// `held`: the hold time, in ops, that every `locks` body is held against
lock KAPPEN protects { belegt, rechte } rank 0
    held <= 3 ops
    shared held <= 4 ops;

impl fn lesen(k : ptr<normal, r> Kappenraum, i : index into Kappenraum) -> Rechte
    effects { reads k.slots, locks shared KAPPEN }
    costs   <= 4 ops
{
    locks shared KAPPEN {
        if k.slots[i].belegt {
            return k.slots[i].rechte;
        }
    }
    return 0;
}

impl fn setzen(k : ptr<normal, rw> Kappenraum, i : index into Kappenraum, r : Rechte)
    effects { writes k.slots, locks KAPPEN }
    costs   <= 3 ops
{
    locks KAPPEN {
        k.slots[i].rechte = r;
    }
}

}
```

Taking requires a **strictly smaller rank** than every lock held (`H006`, through calls `H012`,
non-constant rank `H014`); `protects` bites — every access to a protected place stands under its
lock (`H007`), a never-taken lock shows (`H008`). `held` is a **latency** statement checked per
`locks` body (`K002`), and it must be a constant: `held <= 40 * n ops` is `K010`, because latency
lives at the *largest* assignment and a symbol does not have one (a symbolic `held` is a lock
held for an unbounded time). `masks irqs` at a lock names the state it establishes; an entry that
reaches such a carrier must declare `nested masked` (`H101`). Same-core interrupt deadlock is
`H102`. A lock may carry a pure `invariant p` over its protected places, re-established at
release (`N275`–`N277`).

#### 11.2.1 `locks shared`

The hottest lock of a real kernel is a reader-writer lock and the hot path is the shared side
(33 reader takings against 44 writer takings in the reference scheduler). **Holding shared means
reading the protected places, not writing them** — the same comparison as `E006`.

| code | refusal |
|---|---|
| `H001` | write to a protected place under shared taking (**the load-bearing rule**) |
| `H002` | taken shared without `shared held <= … ops` |
| `H003` | upgrade: taking exclusively while the same lock is held shared (a deadlock on a spinlock) |
| `H004` | `shared held` declared, but nowhere taken shared |
| `E007` | declared **shared**, taken **exclusively** — the dangerous direction: declaring exclusive covers shared (more is safe); the other way the caller computes with concurrency that does not exist |
| `H005` | a shared block calls a function with `requires Held(…)` — **interim and deliberately too strict**: a loud overstatement is cheaper than a silent exception; a shared witness will cover exactly `requires Held-shared` |

`shared held` is not `held` under another name: the computed quantity is the **writer waiting
time under reader pressure** (`K004`). `rcu D protects { T } reclaims p` with `observes D { … }`
is a lock *without rank* whose witness reads require (`H009`); a write also needs a real lock
(`H010`), `reclaims` stands under the writer's lock and outside `observes` (`H011`/`H012`).

### 11.3 `publish` — the publication stands at the store

`A = e publishes { p, q };` — **every store to an `atomic` and every store into a `dma` space** is
a `publishstmt` (a bare one is refused, `N270`); the payload is named where it arises, with the
indices visible there (`FP_OWNER[core] = tid publishes { FP_STATES[tid] };`). A *statement* as
payload is reified as `ghost static`. Payload-free accesses write `publishes nothing` — a word,
not an empty list. The class is called **payload-free**, not "counter": a one-shot latch carries no
payload either. Device publication (a virtio `avail` ring) stands at the `transition` of the
device. The declaration may name a superset the compiler checks every store against.

### 11.4 `accumulates` — without the forbidden loop

`accumulates A : T merge ( max | min | add | or | and ) per cpu N;` — **one cell per core**
(`relaxed`), merged on reading over the `N`-bounded loop. No CAS, no unbounded loop: the
contradiction "the compiler emits what the language forbids" is resolved, and the lowering is
faster than the one it replaces. The merge set is closed (commutative monoids).

### 11.5 Ordering is paired, not declared — `awaits`

`let x = A awaits { p, q };` is the counterpart of `publishes`: it puts reception at the load.

1. **Pairing obligation** (`V001`–`V004`): every `awaits` on an atomic needs a `publishes` store
   on **the same** atomic with **the same** places (name equality after index substitution); an
   orphan half is a compile error.
2. **Visibility is a branch fact**: only the branch that confirms the loaded value makes the
   expected places readable; reading foreign-published places without it is refused.
3. **Order follows from the pairing, not the other way round.** `seq` stays for algorithms that
   need a *global* order — and exactly those fall outside the pairing: their correctness is
   **logic** and stands as an `obligation`.

Beyond the three rules that check a pairing someone wrote: `V009` finds a **missing** pairing —
an atomic that carries no payload anywhere whose value gates a branch behind which a foreign
shared place is read; `V010`: a release of core 0 publishes the writes of core 0, not those of
core 5, so a payload whose writer lies outside the publisher's call hull orders nothing;
`V011`: an `awaits` read stays clean only until the place is revalidated. The *meaning* of
release/acquire is the memory model — an axiom (§12.5). The pairing covers message passing
(producer→consumer, ownership transfer, flags with payload); lowering is exactly the C11 atomics
that stand there today, extra cost 0 — the gain is that a missing `acquire` is no longer
writable.

### 11.6 Read-modify-write — the third form

`fetch_add`, compare-exchange, ticket taking are both halves in one instruction:

```text
let my  = NEXT_TICKET exchange update(t) { t + 1 } publishes nothing;
let won = FP_OWNER[core] exchange my_tid when old == NOBODY returns old
          publishes { FP_STATES[my_tid] } awaits { FP_STATES[old] };
```

Rules: the `update` body is **pure** and M1-typed (an overflow in the RMW is a compile error);
`publishes` forces at least release, `awaits` at least acquire, both acq_rel — derived; the
visibility from `awaits` arises only in the **success** branch; the pairing holds over load,
store and `exchange` together. Lowering: `atomic_fetch_*` where the body matches a closed
pattern table (`t+1`, `t-1`, `t|m`, `t&m`), else a **bounded** CAS loop with its bound written
at the construct in the same words a `retry` carries (`bounded NKERNE * 4 ops on_exceeded …`).
Without the clauses the refusal stands — an unbounded CAS loop is exactly what the language
forbids. **`Vis` is passable:** the success branch produces `linear ghost Vis(P)` per expected
place, so one function may check the flag and another read the payload (§4).

### 11.7 Threads and `concurrent`

`concurrent { f, g(1, true) }` declares the bodies that run concurrently, each with the
arguments it is started with (one value per parameter -- a literal in range, `true`/`false`, `None`,
`&T` for a pointer into `T` -- `N591`/`N592`); the checker holds them against
each other over the transitive hulls — shared writes fall (`W001`), undeclared overlapping roots
fall (`W002`), an incomplete hull refuses (`W003`). `start` creates real threads in the
generated runtime. Per-form atomicity (which emitted forms are single accesses) is measured per
backend and ruled in `SYNTAX.md` §11. *Not covered by the goal theorem:* per-core writes beyond
the payload rule, same-core interrupt preemption beyond `H102`, DMA (a checked space with no leg
in the theorem).

---

## 12. Hardware, boot and axioms

*What kernel logic demands beyond M1–M4:* deliberate non-termination (`divergent fn`, §7);
**interruptibility** — an effect (`masks irqs`), because a handler is not a call and can run
between any two statements; **privileged instructions** (`mov cr3`, `wbinvd`, `invlpg`, `tlbi`)
— an **axiom layer**, per instruction one declared effect on the machine model, where trust
collects and is irreducible; **code as data** — `code` space is reachable only through a checking
gate; alignment and layout — part of the type. The axiom layer is the largest unproven surface of
the language, and it is **countable**: a ratchet over *names*.

### 12.1 `assume` / `falsifier` — hardware assumptions

```text
assume vtd_te_wirkt arch x86_64
    "GCMD.TE arms the translation; DMA without a context entry is reported as a fault."
    falsifier probe_vtd_te;
```

No formalism covers "the VT-d unit honours `TE=1`" — but the assumption can be **named** and made
**testable**. **A guardian checks the existence of a reason, never its truth.** Three classes,
and the third must never look like the first:

| class | means |
|---|---|
| **falsified** | the probe ran and held — a *sample*, not a proof (a passed probe checks *this* machine, *this* configuration, *this* moment; CPU errata are exactly assumptions that almost always hold) |
| **not falsifiable** | no probe possible, *with a reason* |
| **not run** | open — it must never look like the first class, in the source or in the product |

`arch` names the machine and is optional (a timer ticks everywhere; a statement about caches or
barriers is about *one* architecture); `A005` refuses an `arch` no declaration names, `A006` a
sealed one — `x86_64` and `aarch64` are open. A named assumption must carry **one** statement per
falsifier: a conjunction ("coherent *and* ordered") discharged by one green probe leaves its second
half unchecked. The falsifier is code like any other and needs its own speech test: can it fail
at all?

**The assumption set is IN THE PRODUCT**, as a set of *names* with their class — not a number
(a ratchet over a number bites against growth, not against exchange):

```text
proved under:  vtd_te_wirkt (falsified)
               x2apic_zweischritt (not falsifiable: no x2APIC under qemu64)
               smmu_stall_model (NOT RUN)
```

(`gabbro annahmen`.) A library requires entries of the program's single `profile { … }` by
reference (`N215`–`N219`), so linking adds no premise.

### 12.2 Boot code with proof that it never runs again

The demand is not "as little `unsafe` as possible" but **"`unsafe`, but demonstrably expired"** —
strictly stronger than affine systems can say, because the token is **linear** (cannot be copied
or restored).

```text
linear ghost type BootPhase order { roh, mmu, geraete };
raw fn phys_write(p : Pa, w : u64) requires &BootPhase;
fn boot_end(t : BootPhase, root : ptr<normal, rw> PageTable)
    ensures !exists m in mappings of root : m.frame >= BOOT_LOW && m.frame < BOOT_HIGH
    retires t from boot falsifier probe_boot_gone
    effects { consumes t, writes root };
```

| layer | rule | covers | trust | built |
|---|---|---|---|---|
| **S1 types** | every `raw fn` demands `&BootPhase`; it arises once in the boot `entry`, `boot_end` consumes it; afterwards no call types | every static chain | checker (M2) | `O008` (clause demanded), `O001`–`O007` (phase order) |
| **S2 references** | `raw fn` lies in `section ".boot"`; **taking the address of a `raw fn` is not writable** | dynamic reachability via pointers | checker (M3/D2) | `O009` for the half that bites (`&f` refused); the section placement is **not** enforced |
| **S3 hardware** | `boot_end` consumes the token **and** retires the address space, one event: `retires t from boot falsifier <probe>`; the probe at a `.boot` address must fault | jumps S1/S2 do not see | axiom layer + falsifier | `O010`–`O012` for the formulable half; "no mapping ⟹ unreachable" is booked as an assumption with the probe it names |

A theorem "no call after `boot_end` types" alone would be a request (a kill switch gets set and
never taken back); one whose code is *unmapped* is an assurance. **Outside the language:** the
trampoline before the first Gabbro line and the linker script (section bounds) are named
assumptions. A `boot` declaration lists `step`s and a `dispatch`; the checker chains the steps
by their `advances` clauses (`O007`, checked where declared, not where run — a step without
`advances` is skipped). **Designed, not built:** an architecture's mode ladder as a *token flow*
(`write_cr0(PG)` would require the tokens of `PAE`, `LME` and `CR3`, so breaking the order is a
missing token), precomputed boot page tables as a `walk`-checked constant, and descriptor tables
as `format` in the `normal` space with mandatory right `w` (the CPU writes the accessed bit into
the GDT, so a placement in a read-only section is the trap).

### 12.3 `entry` — syscalls and interrupts from one declaration

```text
entry syscall arch x86_64 {
    regs in  { nr: rax, a0: rdi, a1: rsi, a2: rdx, a3: r10 }
    regs out { ret: rax }
    preserves { rbx, rbp, r12, r13, r14, r15, rsp_user }
    clobbers  { rcx, r11 }
    stack KernelStack per cpu
    nested never
    dispatch kernel::syscall::dispatch;
}
```

**Checked:** register and binding names are unique, and a register is not in both `preserves`
and `clobbers` (`N017`); the `dispatch` target resolves (`N018`); the execution context an entry
opens is held by the lock passes (`H013`, `H101`/`H102`). `dispatch` points at an ordinary Gabbro
function with a bounded, exhaustive `match`, so M1–M4 hold from the first Gabbro line. `Has(F)`
witnesses (CPUID as the only generator, affine) make an instruction on a feature the machine may
lack a compile error: `N016` demands the witness at the call site; the generating probe itself
is **not built**. `entrust` is a room whose *content* Gabbro does not know, with a falsifiable
contract at entry (`N004`/`N005`, `N006`).

**Designed, not checked:** register sets *complete* (every architecture register in exactly one
of `regs in/out`, `preserves`, `clobbers` — D2 on registers); the `clobbers` set derived from the
mechanism (`vector 0x80 via softint` lays a full trap frame, `syscall` clobbers `rcx`/`r11`);
`stack … per cpu`, `ist n` (NMI/double fault: only lock-free code) and `nested
never|masked|bounded n` as nesting depth made M1 material; two typed exits for a dispatch ending
in `switch_to`/`resume` with a linear saved `Context`; a `regs out` register carrying a `tagged`
result only through a declared encoding with non-overlapping ranges; FP state as an opaque save
area saved eagerly in `switch_to` (the lazy variant is a known leak). **What does not fall,
honestly:** entry has no downstream prover — the emission comes from one site, probes sit in the
acceptance series; the LLVM backend lowers `entry` (x86_64 IDT stubs, aarch64 vector table) and refuses `boot`/`entrust` by name.

### 12.4 Not built, named

The detailed x86_64 assumption catalogue (25 entries measured against a reference kernel's
`arch/x86_64` branch: MSR/CR/IDT/TLB instructions, TSO mapping, linker disjointness, VT-d
activation) is in git history; **x86-64 hardware-model work has stopped** and the target is
AArch64 on a Sail Arm model ([`PLAN-HARDWARE.md`](PLAN-HARDWARE.md), [`ARM-PLAN.md`](../ARM-PLAN.md)).
The principle it taught stands: the forbidden transition is a *missing token*, an instruction
without a line or a line without an instruction is an error, and the catalogue grows only with
hardware surface.

### 12.5 The memory model is an axiom

`publishes`/`awaits`/`exchange` promise visibility **under the assumption** that the target's
mapping carries release/acquire. That is a named, per-architecture `assume c11_release_acquire
arch …` with a litmus falsifier (message passing, store buffering, load buffering) run in the
check harness — the machine lives in the `arch` clause, not in a name suffix.

---

## 13. `check` — the linear checking obligation

`claim`, `measures` (the list **is** the report line), `gates`, `can_fail`, `floor`,
`counterprobe … expects`. The checker produces a `linear ghost Duty(check)`; whoever does not
consume it does not compile — a `check` that stands in no gate list is a mistake (`N020`), and it
falls out of M2 rather than a special rule. The speech test is a second obligation that only a
*failed* run consumes; the lower bound is M1 (a measured quantity `in 1 ..` cannot report zero);
"the measured path writes the quantity itself" is an M3 write right. `check` bodies compile only
under `when TESTBUILD`: a gated item produces **no line of output** in the shipping build
(`gabbro llvm --testbuild` or a build directory with `-Dbuildtype=testbuild` opens the gate); `G001` (ungated code calls a gated function), `G002`
(any other `when` condition), `G003` (`TESTBUILD` declared as a name). `offline` invariants are
*not* gated — a different clause with a different reader.

---

## 14. Code generation

**Syntax-directed, not optimising.** Every construct has exactly one lowering; the untrusted
compiler checks first, and what the checker refused never reaches the emitter. An unlowered form
is refused **by name**, not guessed (`Y101`–`Y106` for LLVM; the removed C emitter's `C001` is gone).

* **LLVM backend — current.** `gabbro llvm [--target=x86_64|aarch64]` lowers checked Gabbro
  directly to LLVM IR; `opt`, `llc`, `ld.lld` produce a static binary with **no C, no libc, no
  linked runtime** — locks, threads and arenas are generated IR over raw kernel gates.
  [`LLVM-BACKEND.md`](LLVM-BACKEND.md).
* **C11 emitter — removed 2026-10-17** (tag `archiv/c-emitter-2026-10-17`).
  [`C-MEMORY-MODEL.md`](C-MEMORY-MODEL.md).
* **Native machine code with translation validation** is the long-term path and needs a Lean
  model of the CPU first ([`PLAN-TRANSLATION-VALIDATION.md`](PLAN-TRANSLATION-VALIDATION.md)).

**What is proved is not checked at run time.** Ranges, indices, leafness, phases, tokens —
all M1/M2 material is **absent** from the output, not switched off. Runtime checks exist at
exactly two places: a `format` entry (one length check per buffer) and `narrow` (one branch).
Ghosts, `progress`, `costs`, contracts, `check` in the shipping build: zero bytes. Every
construct has an extra cost of zero against correct handwriting; `accumulates` is *negative*
against the CAS version. Output is deterministic: same source, same bytes.

**`extern fn` is the edge.** A foreign body whose contract is an `assume` per declaration,
counted into the axiom layer — the edge is visible and ratchetable instead of silent. It takes
no function pointer (`N574`) and a buffer parameter needs its length clause (`N506`).

**The generator also emits the ANNOTATIONS** — contracts the downstream prover reads. A
generator that accidentally emits *weakened* contracts delivers a green proof over a weaker
statement. So every construct brings its emission **and the mutation showing the emission
gates**: code weakened → the proof falls; contract weakened → only a mutation probe catches it;
both weakened consistently → only a differential test.

---

## 15. The obligation manifest — logic is not lost

Per translation unit the compiler emits a manifest of three classes: **open logic obligations**
(for the programmer or an external tool), **the assumption set** (names with class), and
**closed amortised items with a site**. "Memory-safe under A1…An, functionally open at O1…Ok" is
a sentence *in the product*. The ratchet runs over names; exchange is visible. `gabbro
obligations`, `gabbro annahmen`, [`GABBROV.md`](GABBROV.md) (the logic obligations as Lean).

---

## 16. System calls — every OS call is the program's own

**There is no standard library, no libc and no runtime in a Gabbro binary, and no operating system
is known to the language, the checker, the Lean model or the compilers.** A system or kernel call
is a *generic call whose contract the program or its binding library declares in Gabbro*; the
instruction (`syscall`, `svc`, `int`) comes from the declaration, the number and registers from
the program. Only hardware behaviour is a named assumption. Networking protocols (HTTP, TLS) are
neither built in nor forbidden: they are ordinary Gabbro modules over gates (the standard
library's scope is [`PLAN-STDLIB.md`](PLAN-STDLIB.md)). Handwritten C or assembly stays only where
Gabbro cannot express the thing (a thread entry before any stack exists), each piece booked with
its reason.

A foreign body (`extern fn`) throws away what a system-call site knows — an ABI, a structured
error channel, OS state, a counterpart, a class of assumption — so the user side has its own
construct:

```gabbro
module sprache::systemruf {

reason IoError {
    BadFd       = 9  "the file descriptor is not open"
    Interrupted = 4  "the call was interrupted before anything was written"
    WouldBlock  = 11 "the descriptor is non-blocking and the write would block"
    exhaustive
}

assume linux_write_contract
    "Write keeps its contract on this machine."
    falsifier sonde_write;

// the gate: ABI, register map, total errno decoding, contract, named assumption
syscall write(fd : u64, buf : u64, len : u64) -> u64 or IoError
    abi linux arch x86_64 number 1
    regs in  { rdi = fd, rsi = buf, rdx = len }
    regs out { rax }
    clobbers { rcx, r11 }
    errors   { EBADF => BadFd, EINTR => Interrupted, EAGAIN => WouldBlock }
    requires len <= 1024
    ensures  result <= len
    effects  { pure }
    costs    <= 8 ops
    assume   linux_write_contract falsifier sonde_write;

impl fn schreibe(fd : u64, buf : u64, len : u64) -> u64
    effects { pure }
    costs   <= 32 ops
{
    let n = write(fd, buf, len) else (e) {
        match e {
            BadFd       => { return 0; }
            Interrupted => { return 0; }
            WouldBlock  => { return 0; }
        }
    }
    return n;
}

}
```

**What the checker holds** (`SYNTAX.md` §12.1):

* **register map** (as for `entry`): in-registers pairwise distinct (`N063`), no out register
  clobbered (`N064`), every parameter bound exactly once (`N065`), registers are real (`N066`);
* **error map**: total over the errnos the contract admits, targets are cases of the declared
  `or R` channel (`N067`); an errno *outside* the table is the named hardware outcome "the kernel
  answered outside its contract". The decoding is generated;
* **machine**: `A006`; **assumption** with a falsifier (`N004`/`N005`); **costs**: a call counts the
  declared figure plus the dispatch step, never zero (`N322`, `K003`);
* **buffers**: a pointer parameter the kernel moves *bytes* through points at `u8`/`i8` and is
  bounded by `requires x <= lenof(p)` (`N464`, held at every call by `N463`; `N506` for
  `extern fn`; a kernel that finds the end of its data by a terminator owes a named caller
  obligation, `N507`);
* **a region answer** (`-> ptr<normal, …> u8 or R`, §5.5): the word zero is `hardware`; without the
  `or R` channel the C emitter refuses (`C186`);
* **`stack r` + `child { … }`** — the checked clone handoff: the `stack` clause names the handed
  stack register (`N446`, `N447`), every stack-gate call hands to a `child` region (`N572`), the
  region never returns into the caller's frame (`N448`), never falls through (`N449`), is one per
  call (`N450`), is a thread of its own (no locks around it `N456`; every carrier it touches that
  anyone writes is guarded, atomic or per-core `N457`); the spill-read rule keeps it off unhanded
  caller slots (`N451`/`N452`), the stack parameter is a number (`N578`). The checker's reading
  *assumes the lowering enters the child by jump at the region*; a lowering that lifts `C185`
  keeps that or re-checks the gap.

**Targets — a gate's kernel is a binding, not its text.** `syscall V;` declares a variable; a gate
written `via V` carries only the contract; each `target T abi A arch X { V = number … regs … errors
… assume … }` binds the variable for one kernel ABI (`N562`–`N567`), and `target T;` (or
`--target T`) selects. One program can therefore carry a hosted Linux binding and a bare-metal
one with its own, destroyed-nothing kernel entry, under *its own* assumption — never silently the
Linux one. `kernel <path>` (the call paired with a Gabbro kernel's dispatch entry, so the
assumption becomes a theorem) is **not built** (`N068`).

**Not covered:** signals, `fork`/`vfork`, `mmap` of executable memory change control flow or the
address space under the caller — they stay foreign bodies until a separate design exists; a
JIT's generated code runs in the same domain with the same authority and is not analysed.

---

## 17. Arenas — a heap that is never unbounded

A heap is allowed, but **every region has an upper and a lower bound** — a pool form (fixed
element, per-element release) already exists as `table T count N` with generated
`insert`/`remove`, and the arena is the monotone general form: release as a whole (`reset`) or by
slot (`free`), no fragmentation, allocation fails only beyond the upper bound.

```gabbro
module sprache::halde {

// a bounded arena: reservation 0, hard bound 4, never unbounded
pub arena Vorrat capacity 0 .. 4 of u64;

pub fn main() -> u64 effects { reads Vorrat, writes Vorrat } costs <= 128 ops {
    let a = alloc Vorrat (7) else { return 1; };
    let b = alloc Vorrat (35) else { return 2; };
    free Vorrat[a];
    let c = alloc Vorrat (100) else { return 3; };
    return Vorrat[c] +% Vorrat[b];
}

}
```

* **`arena A capacity lo .. hi [max M] of T [pb P blw B];`** reserves `lo`, bounds at `hi`
  (`N210`: `0 <= lo <= hi <= M`, constants). `alloc` binds an index of the *current generation*;
  its `else` runs when the arena is full and is owed exactly when the static allocation count
  since the last reset may exceed the reservation (`N212`). `A[i]` reads; the slot is never
  written outside `alloc` (`N214`) — **an arena slot is write-once**.
* **`reset A;`** starts a fresh generation; every index bound before is stale (`N211`), also
  across calls, through parameters and through globals the program resets.
* **`max M`** reserves address for `M` slots while storage starts committed up to `hi`; **`grow A
  by n else { … };`** commits `n` more below the ceiling or runs the `else` (`N426` refuses an
  uncountable amount and any request that may reach past the ceiling — whole-run, every path,
  every loop pass, every root).
* **`pb P blw B`** is the *pressure-sampled* unbounded form: no `max`, the ceiling is the counter
  room; the generator reserves address once and commits per chunk, asking the program's own probe
  `P` for free bytes first — below `B` the `else` runs (`N584`/`N585`: probe of the wrong shape or a
  run-time threshold are refused). The probe is itself a Gabbro function; the sampling is one per
  chunk, zero on the fast path.
* **`free A[i];`** gives one slot back; the name **dies statically** — a later read or second
  `free` is `N586` (copies die with it, joins take the union, a parameter index is borrowed, a
  computed place names no death to carry). No `else`: freeing a live slot cannot fail. At run time
  the slot carries a link word (intrusive LIFO; elements under 8 bytes carry an external link),
  so the next `alloc` reuses it without commit.
* Unbounded without a ceiling remains refused **by default**; an explicit opt-in is planned, not
  required. Page return (`reset X at i count n;` on a zero-initialised static array, `N569`)
  and aligned statics (`aligned N`, `N570`) let a program give memory back to the system through
  *its own* binding.

Lean: the generation is a type index (a stale index does not typecheck); `alloc` succeeds exactly
below the bound, the first `lo` allocations after a reset never fail, indices are contiguous;
`FreiZustand` adds the free list with proved reuse and no double free. The G exporter refuses
the newer statements by name (`LG005`) — *open*: `free` across function boundaries, aliases
outside the tracked discipline, the full export. See [`PLAN-DYNAMIC.md`](PLAN-DYNAMIC.md).

---

## 18. What deliberately does not exist

`while`, `for` (as a loop), `goto`, `switch`, preprocessor, implicit conversion, `void*`,
catch-all branch, exceptions, inheritance, reflection, GC, assignment as an expression, forward
declaration, self-hosting (the checker stays Rust: a project that rebuilds its checker has
none), user-defined quantifier domains, recursion in `spec fn`, handwritten lemmas, unnamed
`break`/`continue`, lock hold time unnamed in service loops, unbounded CAS loops as a lowering
detail, migration in format versions, cycles as a time unit, `option T` over arbitrary `T`, a
variable-length array tail, `libm`, a hidden OS.

---

## 19. The checker — pass order

The checker is Rust with `forbid(unsafe_code)` and **no proof-tool dependency**; it reads the
unified grammar (handwritten parser, no generator) and runs a **fixed pass order**. *The
specification is the pass list*: a new pass is a change to this document, booked at this line or
not at all. `gabbro paesse` prints each pass with the sentence it owes.

| # | pass | content | § |
|---|---|---|---|
| 1 | Namen | every declaration complete at one place; module boundary; closed export hull | 1 |
| 2 | D1/D2 | opacity, complete layouts, exhaustive enumerations | 3 |
| 3 | M1 + V1–V3 | ranges, flow rules, `narrow` | 3.2 |
| 4 | M3 | spaces, rights, register classes, alias roots | 5 |
| 5 | M2 | linear/ghost, exactly once per path | 4 |
| 6 | M4 | the loop forms, `leave`/`next` | 9 |
| 7 | Paarung | `publishes`/`awaits`/`exchange` over the united set | 11.5 |
| 8 | effects | writes, `locks`, reads held against the written list | 7 |
| 9 | costs | bodies, `locks` against `held`, calls over declared costs | 7, 9.3 |
| 10 | Gruppe | lock footprint, move, connecting statement (`U001`–`U007`) | 11 |
| 11 | Phasen | stages of a mark, branches (`O001`–`O007`) | 4 |
| 12 | Sperren | rank order, shared/exclusive, contexts, RCU | 11.2 |

Every pass has a speech test in both directions (poison falls, clean passes) **plus a mutation
probe on its emission**. Three of the twelve are fully built, nine *carried* — what a pass can say
it says, and where the rest lies stands beside it with an address (axiom layer, template, or
decision). Where each pass stops is [`CHECKER.md`](CHECKER.md)'s subject. The checker never
verifies itself; the goal theorem names what it does and does not say ([`PROOF.md`](PROOF.md)).

---

## 20. Induction and step promises

* **Induction is named, not guessed.** `by induction over <domain>` names the scheme the
  compiler generated from the declaration (as a proof assistant derives one from a datatype): no
  lemma, no recursive `spec fn`, no heuristic; a named scheme that does not discharge an
  obligation says *which* and *where*. The declaration must name the invariant carrying
  well-foundedness (`invariant acyclic …`), as a **precondition**. Three levels were weighed:
  generated schemes (A — keeps the language), recursive `spec fn` with `decreases` (B — adds
  termination obligations to the specification language), handwritten lemmas (C — that is
  Verus/Dafny). Only A is in.
* **A promise the code MUST make may only be a statement about ONE step.** An enforced promise is
  either checked or an axiom, and a global one that is checked needs induction (circular) or
  becomes one axiom per operation (the axiom layer would grow). The way out is locality: a step
  promise over *one generated operation* is checked by the generator against its own emission.
  The form `op delete_leaf shrinks descendants by 1 maintains cdt_wellformed;` is **not built**
  (no `op`/`shrinks`/`grows`/`keeps` words); the rule it states is the design.
* **The ceiling.** Level A reaches *safety hull + declared invariants + inductive properties over
  declared structures*. It does not reach undeclared structures (machine state), anything that
  quantifies over runs (liveness), or functional correctness whose argument is not a descent
  (an IPC fast path is about values). Named promises buy *certainty of arrival*, not height.

**The method behind every construct:** not "is that possible?" but **"what must minimally stand
there, and can it be lowered?"** — both are conditions, and a clause that cannot be lowered is no
answer. A report that names a hole without the minimal clause is incomplete.

---

## Appendix — where the old citations went

Code comments and tables cite this file by section; the numbers of the specification part were
kept. Older spellings resolve as:

| cited as | now |
|---|---|
| §M1 … §3 "core" | §1, §3 |
| Part II §1 / "part II §1" (pairing) | §11.5 |
| Part II §2 (entry) | §12.3 |
| Part II §3, "§12" boot theorem, "§S2" | §12.2 (S1, S2, S3 rows) |
| Part III §1 (RMW), "part III E5" | §11.6 |
| Part III §6 (checker plan, pass list) | §19 |
| Part IV (`port`, `Has`, catalogue, `boot`) | §10.3, §12.2–§12.4 |
| Part V (induction), Part VI (step promises) | §20 |
| "§9: `rank`, `held`, `protects`" (lock discipline) | §11.2 |
| `LANGUAGE.md` § *the sixth address space* | §10.3 |
