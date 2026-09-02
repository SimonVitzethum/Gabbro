# The six emitter defects of 2026-09-02 — repaired one by one

**Opened 2026-09-03 on the tree at `a053d3a`.** `instrumente/fuzze-erzeuger.py` found six
places where `gabbro pruefe` says `0 errors`, `gabbro emit` exits `0`, and `cc` refuses the
result (`messung/ERZEUGERSWEEP.md`). Each of the six arrived as a probe under
`beispiele/gift/` headed `-- erwartet: cc` — *Gabbro accepts, a foreign tool refuses* — and
none of them was repaired on the day it was found.

This document is the repair log. **It is written as the work happens and not after it**, so
that a number measured is a number the tree keeps.

---

## 0. The baseline, measured before anything moved

`cc (GCC) 15.2.1`, `cc -std=c11 -Wall -Wextra -Werror -fsyntax-only` over the emitted C,
binary built on `ki-pc-fisch-101` out of `gabbro-dd` at `a053d3a`.

| | probe | `pruefe` | `emit` | `cc` |
|---|---|---|---|---|
| **D1** | `641-a-descent-over-a-field-with-no-reader` | `3 items, 0 errors, 0 hints` | `0` | *implicit declaration of function `Pte_rest`* |
| **D2** | `642-a-forever-loop-in-a-function-that-answers` | `5 items, 0 errors, 0 hints` | `0` | *no return statement in function returning non-void* |
| **D3** | `643-an-unsuffixed-literal-past-the-signed-end` | `2 items, 0 errors, 0 hints` | `0` | *integer constant is so large that it is unsigned* |
| **D4** | `644-a-scale-wider-than-any-c-integer` | `2 items, 0 errors, 0 hints` | `0` | *integer constant is too large for its type* |
| **D5** | `645-an-array-longer-than-c-can-object-to` | `2 items, 0 errors, 0 hints` | `0` | *size of array `A` exceeds maximum object size* |
| **D6** | `646-a-section-name-that-closes-the-c-string` | `2 items, 0 errors, 0 hints` | `0` | *missing terminating `"` character* |

All six reproduce. The marks standing beside them at `a053d3a`:

| mark | file | value |
|---|---|---|
| `MARKE_UMGEKEHRT` | `instrumente/pruefe-emission.sh` | 10 |
| `MARKE_EMIT_G` | `instrumente/pruefe-emission.sh` | 8 |
| `MARKE_TABELLE` / `MARKE_UNERLAUBT` | `instrumente/zaehle-c-formen.py` | 67 / 32 |
| vocabulary | `instrumente/zaehle-wortschatz.py` | 221 / 208 / 333 |
| German comment lines | `instrumente/pruefe-englisch.py` | 7883 / 1069 |

`zaehle-c-formen.py` carries a **named exit** at 67/32: it falls back to 66/31 the day D1 is
fixed, because the 67th form — `implizite umwandlung` — is D1's shadow. C assumes `int` for
an undeclared callee and `int → uint64_t` is the conversion `-Wsign-conversion` reports.
*That is the check on the D1 repair, and it is an independent one.*

---

## 1. D1 — a descent over a field with no reader

**The decision: refuse by name.** Two answers were on the table, and the probe's own header
named both: grow a reader for `reserved` fields, or refuse a `down`/`leaf` over a field that
has none.

**The second landed, because the first contradicts the word.** `reserved` is the one way a
`format` says *these bits exist and nobody reads them*, and `emit.rs` already refuses
`in a .. b` at a `reserved` field for exactly that reason — *"a reserved field has no reader,
so there is no place at which the bound could be established"*. A repair that made `reserved`
readable would have had to undo that rule as well, and would have made the declaration word
mean nothing.

`Namen` now carries `formatfelder`: per `format`, the fields that get a reader, built by the
same `!reserviert` condition `format_` lowers by — *one rule, read twice, not a second
opinion about the emitter's own output.* `walk_` looks the descent field up instead of
spelling its C name, and `ausdruck_eintrag` does the same for every `it.<field>` in
`down … when` and `leaf`. A **misspelt** field lands in the same refusal, and it had been
reaching `cc` the same way.

| stage | before | after |
|---|---|---|
| `pruefe` | `3 items, 0 errors, 0 hints` | unchanged — the checker still says nothing |
| `emit` | exit `0`, writes `if (!knoten_zu(Pte_rest(it), &k)) return false;` | exit `1`, `C001` at `down : rest` |
| `cc` | *implicit declaration of function `Pte_rest`* | never reached — no C is written |

The refusal, literally:

    error: [C001] …:38:12: no lowering: `down : rest` over `format Pte`, which hands out no
    reader for `rest` -- a `reserved` field is declared and deliberately has none, and a
    field that is not declared has nothing to read; either way this would call `Pte_rest`,
    which no accessor of this unit defines

**Probe state:** `beispiele/gift/641` re-headed `-- erwartet: cc` → `-- erwartet: C001`, and
its header rewritten to say which of the two answers landed and why.

### The mark fell by itself, which is the whole check

`instrumente/zaehle-c-formen.py --uebersetzer`, run on `ki-pc-fisch-101` before and after,
with **no line of that file touched**:

```
before   MARKE_TABELLE  Marke 67  gemessen 67   MARKE_UNERLAUBT  Marke 32  gemessen 32
after    MARKE_TABELLE  Marke 67  gemessen 66   MARKE_UNERLAUBT  Marke 32  gemessen 31
```

The 67th form was `implizite umwandlung`, D1's shadow: C assumes `int` for an undeclared
callee and `int → uint64_t` is the conversion. After the repair the run reports **zero hits
over all nine measuring switches** where the day before `-Wsign-conversion` reported one.
Marks pulled to **66 / 31**, with the reason at the mark.

*That the confirmation came from a census over emitted C — an instrument that knows nothing
about `walk` — is what makes it worth something. Had the mark stayed at 67, the repair would
have been a different repair than the one it claimed to be.*

### What it cost the corpus: nothing

Ten `.gab` files in the tree carry a `walk`. The four that emitted before (`beispiele/07`,
`messung/grammatik/blocklauf`, `messung/proben/probe-neun-domaenen`,
`messung/proben/probe-stellungen`) all still emit. Measured by running `gabbro emit` over
**all 612 versioned `.gab`** and diffing the exit codes.

---

## 2. D2 — a `forever` loop in a function that answers

**The decision: refuse by name, with the word the language already has.**

`__builtin_unreachable();` after the loop was the candidate the finding itself named, and it
lowers a declaration that is not true. **`-> u64` says this function hands back a `u64`, and
nothing in it ever does.** `never` is in the vocabulary, `M2` reads it, and `prototyp_kern`
has lowered it to `_Noreturn void` since `exit()` got one.

**Checked before it was promised in a message**, which the brief asked for: the same program
with `-> never` and `diverges` in its effects was written out and run end to end —
`5 items, 0 errors, 0 hints`, `gabbro emit` exit `0`, `cc -std=c11 -Wall -Wextra -Werror`
silent, and the C reads `static _Noreturn void g(void)`. *So the refusal points at a form the
author can actually write.*

### The rule is GCC's own, deliberately

The probe's header already established that `-Wreturn-type`'s first form is **syntactic**:
*no return statement in function returning non-void* fires when the body holds no `return`
anywhere. Measured beside the generated file:

```c
static unsigned long g(void){ for(;;){ return 1; } }   /* cc: silent  */
static unsigned long h(void){ for(;;){ } }             /* cc: refuses */
```

So the emitter now asks exactly that question — `rumpf_antwortet`, a walk over the body for
any `Return` statement — and refuses where the answer is no and the C return type is neither
`void` nor `_Noreturn void`. **A `forever` with a `return` inside it is untouched, and should
be: that function answers.** A `forever` with a `leave` and a `return` after it likewise —
written out and compiled to confirm.

### The defect is WIDER than the loop that carries it

Measured the same day, and it is a finding this lane adds rather than inherits:

```gabbro
impl fn g() -> u64 effects { reads erledigt, writes erledigt } { erledigt = 1; }
```

No loop anywhere. `gabbro pruefe`: `3 items, 0 errors, 0 hints`. `gabbro emit`: exit `0`.
`cc`: *no return statement in function returning non-void*. **The same three answers as D2,
without a `forever` in sight.** One rule covers both, because it is one rule — and because it
is GCC's rule, it cannot be over- or under-tight relative to the gate it has to clear.

| stage | before | after |
|---|---|---|
| `pruefe` | `5 items, 0 errors, 0 hints` | unchanged |
| `emit` | exit `0`, writes `for (;;) { … }` and closes the function | exit `1`, `C001` at `g` |
| `cc` | *no return statement in function returning non-void* | never reached |

The refusal, literally:

    error: [C001] …:40:9: no lowering: a body that holds no `return` at all under a
    declaration that promises a result -- nothing in it ever answers, and the `forever` loop
    that ends it is exactly that case. A function that is MEANT never to answer says so in
    its own declaration: `-> never` lowers to `_Noreturn void`, and the callers already
    read it

**Probe state:** `beispiele/gift/642` re-headed `-- erwartet: cc` → `-- erwartet: C001`.

**Cost to the corpus: one file.** `gabbro emit` over all 612 versioned `.gab` before and
after the rule: the exit code changes for `beispiele/gift/642` and for nothing else.

### A debt mark went to zero, and not the way its own note expected

`pruefe-emission.sh` carried `MARKE_UMG_NUR_CC=1` — *reverse probes that bite under `cc`
alone* — booked for **this exact probe**: `clang` stayed silent on `642`, because clang sees
the `for (;;)` never falls out. The note offered two repairs, both at the probe. **Neither was
taken.** `642` stopped being a reverse probe at all, so no compiler is asked about it any
more, and the disagreement between the families is settled at its source. Mark pulled to
**0**, with the reasoning at the mark.

> *The family that was silent was silent for a reason, and the emitter had the same reason
> available — it knew the loop never leaves. It wrote the declaration anyway.*

---

## Marks after D1 and D2

| mark | file | was | is | why |
|---|---|---|---|---|
| `MARKE_UMGEKEHRT` | `pruefe-emission.sh` | 10 | **8** | `641`, `642` are no longer reverse probes |
| `MARKE_EMIT_G` | `pruefe-emission.sh` | 8 | **6** | both now fall at the emitter, before it writes |
| `MARKE_UMG_NUR_CC` | `pruefe-emission.sh` | 1 | **0** | the one entry was `642` |
| `MARKE_TABELLE` | `zaehle-c-formen.py` | 67 | **66** | `implizite umwandlung` was D1's shadow |
| `MARKE_UNERLAUBT` | `zaehle-c-formen.py` | 32 | **31** | same one form |
| vocabulary | `zaehle-wortschatz.py` | 221/208/333 | **unchanged** | neither repair wanted a word |
| German comment lines | `pruefe-englisch.py` | 7883/1069 | **unchanged** | *see below* |

> **The language ratchet caught me once and it was right.** A first draft of the note at
> `MARKE_TABELLE` quoted the counter's own German output inside an English comment, and
> `1069` went to `1070`. The quotation was replaced by the number it was quoting. *A guardian
> that only ever holds has not been tested; this one moved.*

**`cargo test --offline --no-fail-fast`: 399 passed, 0 failed** (unchanged from `a053d3a`).
**`pruefe-emission.sh`: `ALL PASS` — 120 of 120 emitting files compile, 8 reverse probes.**

---
