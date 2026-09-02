# The emitter under the sweep — 5 889 cases, and the promise broke 342 times

**Measured 2026-09-02 on `ki-pc-fisch-101` with `instrumente/fuzze-erzeuger.py`, over the
tree at `41782b0`.** Both build profiles, `cc (Ubuntu 13.3.0-6ubuntu2~24.04.1)`, `LC_ALL=C`,
10,2 s wall / 85 s CPU at 14 threads.

`fuzze-grenzen.py` holds the CHECKER to *accept, or refuse by name*, and its closing note
names what it cannot do:

> **`gabbro emit` is not part of the property.** A sweep holding the emitter to *"lowers, or
> refuses by name"* is the obvious next instrument and does not exist.

It exists now. This document is what it found on its first full run.

---

## 1. The property, and it has three answers

For an input the checker **accepts** (`gabbro pruefe`, exit 0), `gabbro emit` must either

* **lower it** — exit 0, C on stdout, and that C compiles under
  `cc -std=c11 -O0 -Wall -Wextra -Werror -c`; or
* **refuse by name** — `C001`, with a note saying what it cannot lower.

`C001` is the emitter's own sentence for this: *the emitter refuses by name instead of
emitting something plausible — a generator that guesses undoes every pass in front of it.*
Nothing measured whether it keeps it.

---

## 2. The denominators, and there are seven of them

| | |
|---:|---|
| **5 889** | cases generated, over **64** declaration forms |
| **3 517** | accepted by the checker — **the population of this property** |
| 2 372 | refused by the checker; the emitter never sees them |
| **3 046** | lowered by the emitter |
| **471** | refused BY NAME at the emitter |
| **2 773** of 3 046 | compile under the gate — **273 do not** |
| **1 382** | could be **oracled**: the swept value is findable in the C at all |
| 1 664 | lowered, compiled, and only shape-checked — no oracle exists for them |

**21 of 64 forms carry the swept NUMBER into their C**, and **3 of 64 carry the swept NAME.**
The rest are ghost declarations, compile-time clauses and bare types whose C never held the
value at any rung; they are out of **both** the numerator and the denominator, because a
denominator that counts what could never have been measured is `W25`.

*The oracle calibrates itself and is not asserted.* A form counts as oracle-able only where
some accepted rung demonstrably put its own value into a C the baseline's C does not carry.

### What the four shapes cost

| shape | | count |
|---|---|---:|
| 1 | a third answer — panic, timeout, unnamed exit, `C001` with no note | **0** |
| 2 | the C does not compile | **273** |
| 3 | the number did not survive (oracle) | **69** |
| 4 | debug and release disagree — answer or C bytes | **0** |
| | **shapes 1–4 together** | **342** |

Beside the property, three further nets, each reported apart:

| net | | count |
|---|---|---:|
| 5 | not ISO C (`-Wpedantic`) | 23 |
| 6 | an identifier past C11 5.2.4.1 significance | 58 |
| 7 | degenerate constant arithmetic (`* 0`) | 3 |

---

## 3. Eleven complaints, six defects

A count of CASES is not a count of DEFECTS. `cc`'s own message, normalised, groups the 273:

| cases | the compiler's complaint | forms |
|---:|---|---:|
| 98 | `implicit declaration of function 'Pte_rest'` | 2 |
| 65 | `no return statement in function returning non-void` | 1 |
| 54 | `integer constant is so large that it is unsigned` | 9 |
| 30 | `integer constant is too large for its type` | 6 |
| 12 | `comparison is always true due to limited range of data type` | 1 |
| 4 | `size of array 'X' exceeds maximum object size 'X'` | 2 |
| 4 | `comparison is always false due to limited range of data type` | 1 |
| 3 | `missing name` *(assembler)* | 1 |
| 1 | `junk at end of line` *(assembler)* | 1 |
| 1 | `missing terminating " character` | 1 |
| 1 | `null character(s) preserved in literal` | 1 |

### D1 — a `walk` descends through a `reserved` field · `beispiele/gift/641`

`emit.rs` writes one accessor per `format` field and **none** for a `reserved` one — that is
what the word is for. The descent function of a `walk` lowers `down : <field> when …` into a
call on exactly that accessor. Nothing joins the two facts.

```
gabbro pruefe   3 items, 0 errors, 0 hints
gabbro emit     exit 0, no C001
cc              implicit declaration of function `Pte_rest`; did you mean `Pte_praesent`?
```

**And the place it was found is the finding.** The two `walk` templates of
`instrumente/fuzze-grenzen.py` carry this exact shape at their own **known-good baseline**.
That sweep validates a baseline against the CHECKER and never against the emitter, so 130 of
its cases had been lowering to C that does not compile since 2026-09-02 — under a green run.
*A baseline is only good against the question it was asked.*

### D2 — a `forever` loop is the whole body of a function that answers · `gift/642`

The loop never leaves, so Gabbro needs no `return` after it, and the checker is right to say
so. The emitter writes `for (;;) { … }` and stops. GCC's `-Wreturn-type` is syntactic at the
front end — measured on plain C beside the generated file, `static uint64_t g(void) { for
(;;) { x = 1; } }` draws the same error with no Gabbro anywhere near it.

**65 of 65 accepted rungs fail, at every bound from `1` to `2^127`.** The swept slot has
nothing to do with it, and that is the class a form-wise sweep is good at showing: *one answer
at every rung means the finding sits in the FORM.*

The corpus never showed it, and the reason is measurable: `pruefe-emission.sh` reports 117 of
117 units compiling, and not one of them puts a `forever` in a function that answers. *A gate
over a corpus measures the corpus.*

### D3 — an integer literal with no `u` on it · `gift/643`

The emitter suffixes in many places — `#define K 7u`, `i * 8u`, `& 1099511627775u` — and in
the ordinary expression path it does not. A bare decimal constant in C takes the first of
`int`, `long`, `long long` that holds it; `2^64 − 1` fits none.

**54 cases over NINE forms** — `return`, `if`, `let`, `static … =`, an assignment, a
`bank at`, a `reason` code, an array length, a `walk` node count. *One missing character,
nine slots.* Which makes it the one to be careful with: `-Wconversion` and
`-Wsign-conversion` read the same literals (`zaehle-c-formen.py` runs both over 102 units), so
a suffix added without measuring the whole corpus trades this error for a different one.

### D4 — a literal wider than every C integer type · `gift/644`

`embeds … scale 2^64` lowers to `* 18446744073709551616u`. **This is the `konst_zahl` family
with the cast repaired and the question still open**: on 2026-09-02 `konst_zahl` went from
`Some(*n as i128)` to `i128::try_from(*n).ok()`, which stopped `2^128 − 1` coming out as `-1`.
`2^64` fits `i128` perfectly well, so it is handed over and written. *A repair at the reader
is not a repair at the writer.*

### D5 — an array length past C's maximum object size · `gift/645`

`[u64; 2^63 − 1]` is an honest `u64` and no C object can have it. `gift/602` is the
neighbour: that one carries the length the emitter READ WRONG, this one a length it reads
exactly right and writes into a declaration that cannot exist.

### D6 — a `section` name copied into C with nothing escaped · `gift/646`

Four shapes past the checker: an empty name and a blank one reach the **assembler**
(*missing name*); Gabbro's own doubling form for an embedded quote lands as *junk at end of
line*; a trailing backslash closes the C string (*missing terminating " character*); a NUL
draws *null character(s) preserved in literal*.

> **Two of the four are found by the compiler and two only by the assembler.** That asymmetry
> is a finding one level up: `tests/beispiele.rs` compiles a `-- erwartet: cc` probe with
> `-fsyntax-only` and never assembles it, so half of this defect is invisible to the poison
> harness. `fuzze-erzeuger.py` compiles with `-c` for exactly this reason.

---

## 4. The oracle — 69 cases, and it is the class it was built for

| form | cases | |
|---|---:|---|
| `entry-vector` | 23 | the interrupt vector |
| `entry-ist` | 23 | the stack-table index |
| `entry-nested-bounded` | 23 | the nesting bound |

Every one is a value above what the emitter can write, at an `entry` clause that emits the
unit anyway. `messung/AUDIT-2026-09-02.md` §7.7 item 3 books it: the diagnostic says *"vector:
not a constant in this unit"*, and it **is** a constant — one the emitter cannot represent.

**This is the `konst_zahl` shape found mechanically for the first time.** The original was
found by reading C by hand; the oracle here is a compile-time constant compared against the
integer tokens of the emitted C, and it needed no knowledge of `entry` at all.

---

## 5. What the two zero-answer shapes mean

**Shape 1 is 0 over 3 517 accepted cases.** The emitter never panicked, never timed out,
never left with an unnamed non-zero exit, and every one of its 471 refusals carried a note
saying what it could not lower. *The `C001` contract's own wording holds everywhere it fires.*

**Shape 4 is 0.** Debug and release gave the same answer for every case, and where both
lowered, the C was **byte-identical**. The two profiles differ in Rust's overflow checks, and
the emitter's arithmetic never reached one.

---

## 6. The self-check — the four cases that were waiting

The audit of 2026-09-02 left five findings open (§7.7). Four of them were the self-check for
this instrument, and the honest answer is not the same for all four.

| | what the audit said | what the sweep says |
|---|---|---|
| `table count 0` | *"refused at emit"* | **WRONG, and this is a correction.** It lowers to `T_slot slots[0]`. Found by net 5: *ISO C forbids zero-size array*. GCC takes it as an extension and says nothing under the plain gate. |
| `[u64; 0]` | *"refused at emit"* | **right** — `C001`, *"`static` array of length zero — C has no such object"*. The property is kept; the sweep sees it as `REFUSE C001`. |
| `embeds … scale 0` | *"lowers, and the frame number is multiplied by zero"* | **found**, by net 7, 3 rungs (`0`, `0x0`, `0b0`) writing the same `* 0u`. |
| 65 536-character identifier | *"accepted and written into C"* | **found**, by net 6: 58 cases over 6 slots, up to 65 536 characters. |
| `aligned(p, 0)` / `aligned(p, 3)` | *"an alignment of zero lowers to a modulo by zero"* | **the sweep was BLIND, and then was made to see.** See below. |

### The blind spot, named

`fuzze-grenzen.py`'s `aligned-n` template puts its swept value in a **`spec fn`**, which is
ghost: its whole emitted C is the twelve-line preamble, with no declaration in it. Measured —
`wc -l basis-aligned-n.c` is 12, against 14 for the smallest form that emits anything at all.
**So the shared template could not say one word about how `aligned` lowers, and never could.**

That is not a fault of the other sweep — its property is about acceptance, and a ghost
function is accepted exactly as loudly as any other. It is the cost of reusing one table
across two questions.

The cure is a form this sweep **owns**: `aligned-im-rumpf` puts the same call in an `impl fn`
body, where the emitter looks. Result over 111 rungs:

```
aligned-im-rumpf    111 cases   94 accepted   0 lowered   94 refused C001
```

**The emitter refuses `aligned(p, 0)` and `aligned(p, 3)` by name, so the property holds** —
and it holds for the reason the audit already gave: `C001` says *"`aligned` outside a `format`
predicate"*, which is the right answer for the wrong reason and would disappear the day
`aligned` lowers there. **The modulo by zero does not exist today**; it is a hypothesis about
a lowering that has not been written.

The shared form is **added to and not moved**: `fuzze-grenzen.py` publishes *63 forms /
5 778 cases*, and a form added there for this question would silently restate that mark as
something else.

---

## 7. The booking, and why it is a ratchet and not an excuse

`GEBUCHT` in `fuzze-erzeuger.py` carries **27 keys** — one per (shape, form) — each with its
measured count and where it is recorded. Every one is printed at every run. The verdict counts
only what is **not** booked, so the tool is green over the tree as it stands and red on:

* a **new** (shape, form) pair,
* a booked count that has **risen**,
* a booked finding that has **vanished** — *a stale booking hides the next one at the same
  place.*

The first run's bookings were written from a guess and the tool answered `7 risen, 5 gone`.
They were then replaced by the measurement. **The numbers in this document are the second
kind.**

---

## 8. What was not measured, and why

* **The C is compiled, not RUN.** `pruefe-emission.sh` runs seven units under UBSan and ASan
  and compares results; this sweep holds 64 forms to compilation. A generated expression that
  compiles and computes the wrong thing passes here unless the oracle sees the number.
* **1 664 of 3 046 lowered cases have no oracle.** They are held to shapes 1, 2 and 4 only.
  That is the honest half of the coverage, and it is the larger half.
* **The checker's own answer is taken as given.** A rung both profiles accept wrongly is
  invisible to this property by construction — the same limit `fuzze-grenzen.py` names for
  itself, one storey down. The rule that catches THAT is the poison corpus.
* **One slot at a time.** `stride` and `count` at their boundaries *together* is a different
  sweep.
* **`-Wconversion`, `-fanalyzer`, `clang -Weverything`.** `zaehle-c-formen.py` owns those over
  the corpus; running them over 3 046 generated units is a further instrument and not this
  one.
