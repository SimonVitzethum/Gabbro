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

## 3. D3 — an unsuffixed literal past the signed end

**The decision: a lowering. The suffix belongs there.**

A bare decimal constant in C takes the first of `int`, `long`, `long long` that holds it.
Past `2^63 - 1` none of them does, so GCC gives it `unsigned long` and says so. The value is
legal Gabbro — `u64` reaches exactly that far — and legal C **with the suffix**. Nothing is
being withheld and nothing has to be decided: there is a correct spelling, and the emitter
was not writing it.

### What the emitter already got right, checked first

The brief asked what happens at `i64::MAX`, since some literals must already be right.
Measured: **the emitter suffixes at five kinds of site and not in the ordinary expression
path** — `#define K 7u`, `i * 8u`, `& 1099511627775u`, `{n}_EBENEN {ebenen}u`, and `* {k}u`
at a `scale`. Those are all places where the emitter writes the `u` itself into a format
string. `ExprArt::Zahl(n) => n.to_string()` is the door that carries the user's own number,
and it had none.

### The boundary is where C needs it, and that is the whole care

The probe named the risk itself: `-Wconversion` and `-Wsign-conversion` read the same
literals, and `zaehle-c-formen.py` runs both over the whole corpus — *a suffix added without
measuring trades this error for a different one.*

So `czahl` writes the `u` **only above `2^63 - 1`**:

| range | spelling | why |
|---|---|---|
| `n <= 2^63 - 1` | `n` | C's own rule already gives it a signed type that holds it; **unchanged, byte for byte** |
| `2^63 <= n <= 2^64 - 1` | `n` + `u` | no signed type holds it; the `u` picks the first unsigned one that does |
| `n > 2^64 - 1` | *refused* | `unsigned long long` is at least 64 bits and C promises no more — there is no spelling |

**Measured rather than argued:** the emitted C of all 612 versioned `.gab` was dumped before
and after and compared file by file. Four files differ — this one and the three probes of
D4, D5, D6 — plus one extra diagnostic (below). *Below the boundary nothing moved.*

| stage | before | after |
|---|---|---|
| `pruefe` | `2 items, 0 errors, 0 hints` | unchanged |
| `emit` | `return 18446744073709551615;` | `return 18446744073709551615u;` |
| `cc` | *integer constant is so large that it is unsigned* | accepted, also under `-Wconversion -Wsign-conversion` |

**Probe state: it stopped being poison.** The program was always correct Gabbro; the *C* was
wrong. So `beispiele/gift/643` moved to
`messung/proben/probe-literal-past-the-signed-end.gab`, where `pruefe-emission.sh` stage 9
compiles it under `-Werror` at every run. **A file that stops being poison does not stop
being a probe.**

### A seventh site the same door fenced

`beispiele/gift/601-an-index-too-wide-to-have-a-type.gab` (a `-- erwartet: M139` probe) now
draws an additional `C001` at `T.slots[170141183460469231731687303715884105728]` — a `2^127`
index the emitter had been writing into C. It falls at the checker first, so nothing changes
for the corpus; it is named here because it is the one other place the dump moved.

---

## 4. D4 — a scale wider than any C integer

**The decision: refuse by name.** C has no such number, and this is `C001`'s sentence
exactly.

`konst_zahl` was changed on 2026-09-02 from `Some(*n as i128)` to `i128::try_from(*n).ok()`,
which stopped the emitter writing `-1` for `2^128 - 1`. It did not stop it writing `2^64`:
that value fits `i128` perfectly well. **A repair at the reader is not a repair at the
writer**, and the fence now stands at `u64::try_from`, where the multiplier becomes C text.

| stage | before | after |
|---|---|---|
| `pruefe` | `2 items, 0 errors, 0 hints` | unchanged |
| `emit` | exit `0`, `… & 1099511627775u) * 18446744073709551616u)` | exit `1`, `C001` at the field |
| `cc` | *integer constant is too large for its type* | never reached |

    error: [C001] …:28:5: no lowering: `scale` past `2^64 - 1` -- the reader multiplies the
    raw bits by this number and the multiplier goes into the C as a literal. No C integer
    type holds it, so there is no reader to write

**Probe state:** `beispiele/gift/644` re-headed `-- erwartet: cc` → `-- erwartet: C001`.

> `scale` needs its own fence because its number never passes through `czahl`'s door: it
> comes out of `konst_zahl` as an `i128` and is formatted straight into the reader.

---

## 5. D5 — an array longer than C can object to

**The decision: refuse by name, and the number in the refusal is C's own.**

What the refusal has to get right is **which** limit. It is not the element count: C requires
the difference of two pointers into one object to be representable as a `ptrdiff_t`, so the
bound is on **bytes**. `9223372036854775807` is `PTRDIFF_MAX` — and it is the number GCC
prints in its own message, read off that message rather than assumed.

The emitter multiplies the declared length by the width of the element type. An element whose
width it cannot name counts as **one byte**, the smallest any C object has, so the rule
under-refuses rather than over-refuses where it cannot see. *That is the safe direction: what
it lets through, `cc` still catches.*

| stage | before | after |
|---|---|---|
| `pruefe` | `2 items, 0 errors, 0 hints` | unchanged |
| `emit` | `static uint64_t A[9223372036854775807] … = {0};` | exit `1`, `C001` at `A` |
| `cc` | *size of array `A` exceeds maximum object size 9223372036854775807* | never reached |

    error: [C001] …:21:12: no lowering: `static` array of 9223372036854775807 x 8 bytes --
    C's largest object spans `PTRDIFF_MAX` = 9223372036854775807 bytes, because the
    difference of two pointers into one object has to be representable. There is no C
    declaration for this

**Probe state:** `beispiele/gift/645` re-headed `-- erwartet: cc` → `-- erwartet: C001`.

### A neighbour found here and NOT closed, and it is worse than what was closed

    static mut A : [u64; 100000000] = 7;

A hundred million — well inside `PTRDIFF_MAX`, so D5's rule does not fire. **`gabbro emit`
never returns.** A non-zero initialiser is written out element by element, deliberately
(`= {5}` in C means *first five, rest zero*, which is not what Gabbro's `= 5` means), and the
emitter builds that text one element at a time. Measured 2026-09-03: killed at 25 s, exit
`124`, output file empty.

**That is the emitter's third answer — neither a lowering nor a refusal — and
`messung/ERZEUGERSWEEP.md` counts zero of those** (*"a third answer — panic, timeout, unnamed
exit, `C001` with no note: 0"*). The sweep never reached it because its `array-laenge` ladder
sweeps the length over a ZERO initialiser, which short-circuits to `{0}`.

**Left open on purpose.** Fencing it needs a bound on how much C text the emitter may write,
and no such number is derivable from C — the standard's own translation limit (65535 bytes in
one object) sits far below what this corpus's tables need. *Inventing one is the guess `C001`
exists to prevent*, so it is booked here for the owner instead.

---

## 6. D6 — a section name that closes the C string

**The decision: refuse by name. Escaping was the smaller change and it is the wrong one.**

Doubling the backslash makes the C legal and hands the **assembler** a section whose name
ends in one. GCC writes that name into a `.section` directive *unquoted*, so the failure
simply moves from `cc` to `as`. The probe's own header already measured why that matters: of
this slot's four shapes, **two are caught by the compiler and two only by the assembler**,
and `tests/beispiele.rs` stops at `-fsyntax-only`. *Escaping moves the failure one tool
further out — to the tool fewer instruments look at.*

So a `section` name is held to what a section name can be: at least one character, each a
letter, a digit, or one of `. _ - $`. That is the set the linker's own sections live in
(`.text`, `.data.rel.ro`, `.init_array.65535`) and the set the corpus uses — **two `section`
declarations in 612 files, both `.rodata`**, and both still emit byte-identically.

All four shapes now fall, each naming the character it stopped at:

| written | refusal says |
|---|---|
| a name ending in a backslash | a backslash is not a name character |
| an empty name | it is empty |
| a blank name | a space is not a name character |
| the doubling form | a space — **and that is a finding of its own** |
| a name holding a NUL | `\0` is not a name character |

**The doubling form is not an embedded quote at all.** `parse.rs::erwarte_text` joins
adjacent string literals **with a space**, so two literals side by side make one name with a
space in it. The probe's header had recorded the assembler's answer (*junk at end of line*)
without the cause; the refusal names it now.

| stage | before | after |
|---|---|---|
| `pruefe` | `2 items, 0 errors, 0 hints` | unchanged |
| `emit` | the attribute copied the text through unchanged | exit `1`, `C001` at the name |
| `cc` | *missing terminating quote character* | never reached |

**Probe state:** `beispiele/gift/646` re-headed `-- erwartet: cc` → `-- erwartet: C001`.

> **A written claim this refutes.** The note beside `emit.rs::kommentartext` had ruled this
> channel closed, in so many words: a Gabbro string cannot contain a quote, so nothing can
> escape out of a `section` attribute. *It was open by one character nobody had thought of.*
> A closed channel is a claim about every character, and it had been checked against one.

---

## Marks after all six

| mark | file | at `a053d3a` | now | why |
|---|---|---|---|---|
| `MARKE_UMGEKEHRT` | `pruefe-emission.sh` | 10 | **4** | all six left the reverse-probe set |
| `MARKE_EMIT_G` | `pruefe-emission.sh` | 8 | **2** | five refuse at the emitter, one moved out |
| `MARKE_EMIT_M` | `pruefe-emission.sh` | 53 | **54** | D3's probe arrived in `messung/proben/` |
| `MARKE_UMG_NUR_CC` | `pruefe-emission.sh` | 1 | **0** | its one entry was D2's probe |
| `MARKE_TABELLE` | `zaehle-c-formen.py` | 67 | **66** | D1's shadow form is gone |
| `MARKE_UNERLAUBT` | `zaehle-c-formen.py` | 32 | **31** | the same one form |
| `MARKE` | `pruefe-zitate.py` | 342 | **343** | D6's note cites `L006`, issued in `lex.rs` |
| vocabulary | `zaehle-wortschatz.py` | 221/208/333 | **unchanged** | no repair wanted a word |
| German comment lines | `pruefe-englisch.py` | 7883/1069 | **unchanged** | |
| poison corpus | `README.md`, `DONE.md` | 432 | **431** | D3's probe is no longer poison |

**`cargo test --offline --no-fail-fast`: 399 passed, 0 failed.**
**`pruefe-emission.sh`: `ALL PASS` — 121 of 121 emitting files compile, 4 reverse probes, and
121 of 121 are accepted by `clang` as well.**

### The acceptance run, both ends, and it is the same three

`./instrumente/abnahme.py` was run on `ki-pc-fisch-101` twice: once over this tree, and once
over a clean checkout of `a053d3a` built beside it. **Both report `ABNAHME ROT: 3 von 49`,
and it is the same three guardians with the same lines:**

    pruefe-grammatiktafel.py   red by owner decision (`state`)
    zaehle-gifttreffer.py      the covered-probe cap
    zaehle-karten.py           45 direct card lookups against a mark of 40 / 36

*The comparison is the point.* A lane that only ran the acceptance over its own tree could
say `three red` and would not know whether it had made any of them so.

### And the two that are not the owner's known one

`zaehle-karten.py` reads the public `HashMap` fields of `umgebung.rs` and looks for direct
`.get(` / `.contains_key(` on them. Its listing carries **zero entries from `emit.rs`**, its
numbers are identical with and without this lane's changes, and identical again in the clean
`a053d3a` checkout: 45 / 40 in all three.

`zaehle-gifttreffer.py` names eight covered probes — `155`, `188`, `300`, `411`, `56`, `63`,
`87`, `92`. None is this lane's, none expects `C001`, and the tool runs `emit` only for
`C001` probes, so for these eight it never reaches the emitter at all; its own printed chains
carry checker codes only. `git diff a053d3a -- beispiele/gift/` touches exactly `641`-`646`.

`zaehle-gifttreffer.py` reports its covered-probe cap at 8 where 7 is booked. **Measured, not
assumed:** it reports 8 at the D1/D2 commit as well, and the eight files it names — `155`,
`188`, `300`, `411`, `56`, `63`, `87`, `92` — are none of this lane's, expect no `C001`, and
are therefore files for which the tool never runs the emitter at all (it runs `emit` only for
`C001` probes, and its own printed chains for all eight carry checker codes only).
`git diff a053d3a -- beispiele/gift/` touches exactly `641`–`646`. *The mark was already
broken at `a053d3a`.*

---

## What this lane could not close

1. **The non-terminating emitter at a large non-zero array initialiser** (§5). Reproduced and
   measured; left open because fencing it means inventing a number C does not give. It is the
   emitter's THIRD answer, which the sweep of 2026-09-02 counted at zero.
2. **Two guardians that were already red at `a053d3a`** -- `zaehle-gifttreffer.py`'s
   covered-probe cap and `zaehle-karten.py`'s lookup ratchet. Both were measured at both
   ends and neither was moved by this lane; neither was repaired by it either.
3. **Three of D6's four shapes fall at the emitter and only one carries a probe.** The poison
   corpus has `646` for the backslash; the empty name, the blank name and the NUL are measured
   in this document and in the refusal's own text, not in a file that runs every day.
