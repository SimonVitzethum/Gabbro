# The emitter residue of 2026-09-03 — what the sweep still finds after `D1`–`D12`

**Opened 2026-09-03 on the tree at `393d866`.** `messung/ERZEUGERDEFEKTE.md` is the repair log
for the six defects of the day before; `messung/ERZEUGERSWEEP.md` is the first full run of
`instrumente/fuzze-erzeuger.py`. This document is the next step of the same line: **run both
sweeps again on today's tree, say which numbers moved and why each moved, and work what is
left.**

It is written as the work happens, so that a number measured is a number the tree keeps.

---

## 1. Both sweeps, today, with their denominators

Run on `ki-pc-fisch-101` out of `gabbro-d7` at `393d866`, `cc (GCC) 15.2.1`, debug and
release built from the same tree.

### `fuzze-grenzen.py` — the CHECKER: accept, or refuse by name

| | 2026-09-02 | today |
|---|---:|---:|
| cases over 63 forms | 5 778 | **5 778** |
| panics — a third answer | 0 | **0** |
| debug/release disagree | 0 | **0** |
| unexpected exit or timeout | 0 | **0** |
| forms with one answer for every rung | 0 of 63 | **0 of 63** |

**Unmoved, and that is the honest reading**: this sweep never runs `emit` and never runs
`cc`, so not one of the six repairs could show up in it. What did move is inside a note it
prints about itself, and that note is now stale — §3 below.

### `fuzze-erzeuger.py` — the EMITTER: lower, or refuse by name

| | 2026-09-02 | today | |
|---|---:|---:|---|
| cases generated over 64 forms | 5 889 | **5 889** | |
| accepted by the checker — the population | 3 517 | **3 514** | −3 |
| refused by the checker | 2 372 | **2 380** | +8, and all 2 380 also run under net 8's deadline |
| lowered by the emitter | 3 039 | **2 813** | −226 |
| refused BY NAME at the emitter | 478 | **701** | +223 |
| of the lowered, compile under the gate | 2 766 of 3 039 | **2 791 of 2 813** | 22 do not, was 273 |
| could be ORACLED | 1 375 | **1 229** | |
| lowered, compiled, shape-checked only | 1 664 | **1 584** | |
| forms whose C carries the swept NUMBER | 21 of 64 | **19 of 64** | |
| forms whose C carries the swept NAME | 3 of 64 | **3 of 64** | |

| shape | | 2026-09-02 | today |
|---|---|---:|---:|
| 1 | a third answer — panic, timeout, unnamed exit, `C001` with no note | 0 | **0** |
| 2 | the C does not compile | 273 | **22** |
| 3 | the number did not survive (oracle) | 69 | **69** |
| 4 | debug and release disagree | 0 | **0** |
| | **shapes 1–4 together** | 342 | **91** |

| net | | 2026-09-02 | today |
|---|---|---:|---:|
| 5 | not ISO C (`-Wpedantic`) | 16 | **15** |
| 6 | an identifier past C11 5.2.4.1 significance | 58 | **58** |
| 7 | degenerate constant arithmetic (`* 0`) | 3 | **3** |
| 8 | a run that does not halt | *(net 8 did not exist)* | **0** |

**Unbooked findings: 0. Stale bookings: 11.** The verdict line reads
`3423 of 3514 accepted cases kept the emitter's promise`.

---

## 2. Which findings went, and why each went

The tool answers this itself, and that is the whole reason it books rather than lists.
**Eleven of its 25 bookings came back `BOOKED AND GONE`**, one came back shrunk, and the rest
stood. Read per booking:

| booking | booked | found | why it went |
|---|---:|---:|---|
| `NICHT-UEBERSETZBAR walk-knoten` | 65 | **0** | `D1` — the descent looks its field up in `Namen::formatfelder` and refuses a `reserved` one by name |
| `NICHT-UEBERSETZBAR walk-levels` | 65 | **0** | `D1`, the same rule at the other slot |
| `NICHT-UEBERSETZBAR forever-schranke` | 65 | **0** | `D2` — `rumpf_antwortet` refuses a body with no `return` under a declaration that promises a result |
| `NICHT-UEBERSETZBAR ausdruck` | 6 | **0** | `D3` — `czahl` writes the `u` above `2^63 − 1` |
| `NICHT-UEBERSETZBAR if-bedingung` | 10 | **0** | `D3`, and `D4`'s refusal at the top rungs |
| `NICHT-UEBERSETZBAR let-wert` | 6 | **0** | `D3` |
| `NICHT-UEBERSETZBAR zuweisung` | 6 | **0** | `D3` |
| `NICHT-UEBERSETZBAR bank-at` | 6 | **0** | `D3`, inside the bank accessor |
| `NICHT-UEBERSETZBAR embeds-scale` | 4 | **0** | `D4` — `u64::try_from` at the multiplier |
| `NICHT-UEBERSETZBAR array-laenge` | 12 | **0** | `D5` — the `PTRDIFF_MAX` fence, plus `D3`/`D4` at the top rungs |
| `NICHT-UEBERSETZBAR text-abschnitt` | 6 | **0** | `D6` — a `section` name is held to `[A-Za-z0-9._$-]+` |
| `NOT-ISO text-abschnitt` | 3 | **2** | `D6` again: one of the three was the trailing backslash, which no longer reaches `cc` at all. The two that stand are `-Woverlength-strings`, a different complaint about the same slot |

**Nothing on that list fell for a reason nobody wrote down.** Each row names the rule that
took it, and each rule is in `messung/ERZEUGERDEFEKTE.md` with its own before/after.

### And two bookings did NOT go, under a heading that says they did

`messung/ERZEUGERDEFEKTE.md` §3 reports `D3` as repaired and names its reach: *"**54 cases
over NINE forms** — `return`, `if`, `let`, `static … =`, an assignment, a `bank at`, a
`reason` code, an array length, a `walk` node count. *One missing character, nine slots.*"*

Seven of those nine slots are at zero today. **Two are not**, and the sweep says so at every
run:

    [==] NICHT-UEBERSETZBAR reason-code             16 of  16
    [==] NICHT-UEBERSETZBAR static-wert              6 of   6

They are `D13` and `D14` below. *The booking was honest — it printed `[==]`, not `GONE` —
and the prose one directory over was not.* A repair reported by the slot it was found at,
rather than by the slots its own count enumerates, leaves exactly this residue.

---

## 3. `D13` — a `reason` value C cannot put in an enumerator

**The decision: refuse by name, and the boundary is C's own constraint.**

A `reason` lowers to `typedef enum { … } R;` — *«C3a»: a `reason` is a named set of numbers,
and the numbers STAND THERE.* C11 6.7.2.2p2 is a **constraint** on what may stand there: an
enumeration constant *shall be an integer constant expression that has a value representable
as an `int`.* The emitter wrote whatever the source named.

### Three complaints, one cause, and the books had them under two headings

| the value | what `cc` says | where it was booked |
|---|---|---|
| `2147483648` | *ISO C restricts enumerator values to range of `int`* (only under `-Wpedantic`) | net 5, `D9`, 13 cases |
| `18446744073709551615` | *integer constant is so large that it is unsigned* | shape 2, `D3`, 6 cases |
| `2^127` | *integer constant is too large for its type* | shape 2, `D4`, 10 cases |

**They are one defect.** Everything past `INT_MAX` is ill-formed, and which of the three
complaints `cc` prints depends only on how far past. *A finding filed under the gate that
happened to see it is filed under the wrong heading* — the split made a constraint violation
look like a style note standing beside a compile error.

**A suffix was the smaller change and it is the wrong one.** `A = 18446744073709551615u`
silences `-Werror` and leaves the constraint violation where it stood; the failure moves to
`-Wpedantic`, a gate `tests/beispiele.rs` does not run. *That is `D6`'s argument one file
over: a repair that moves the complaint to a quieter tool is not a repair.*

| stage | before | after |
|---|---|---|
| `pruefe` | `2 items, 0 errors, 0 hints` | unchanged — the checker still says nothing |
| `emit` | exit `0`, writes `R_A = 2147483648, /* one */` | exit `1`, `C001` at the case |
| `cc` | *ISO C restricts enumerator values to range of `int`* (`-Wpedantic`) | never reached — no C is written |

The refusal, literally:

    error: [C001] …:3:5: no lowering: a `reason` case whose value is 2147483648 -- a `reason`
    lowers to a C `enum`, and C11 6.7.2.2 requires every enumerator to be representable as an
    `int`. The largest one is 2147483647, and there is no wider enumerator to write

> **`int` is taken as 32 bits, and that is an assumption, so it stands at the constant.** C
> promises only 16, so on a narrower target the fence UNDER-refuses — the safe direction, and
> the one `cbreite` already takes: what slips through, `cc` still catches. The number in the
> refusal is GCC's own, read off its message rather than assumed.

**Probe:** `beispiele/gift/666-a-reason-value-past-the-c-enumerator.gab`, and the value in it
is `INT_MAX + 1` deliberately — *the largest value draws `-Werror` from the plain gate, and a
probe that falls at the loudest reader does not measure the quiet one.*

**Cost to the corpus: nothing.** Every `reason` case in the tree is a small number: the widest
is `9`, in `messung/fragmente/F02.gab`.

## 4. `D14` — a `static` initialiser with no `u` on it

**The decision: a lowering, and it is `D3`'s, at the eighth of the nine sinks `D3` named.**

`czahl` grew the suffix in the **expression** path — `ExprArt::Zahl(n)`, the door a user's
number travels through in a `return` or a `let`. A `static` initialiser does not travel it:
the value arrives as an `i128` out of `konst_zahl` or out of `namen.konstwert`, and was
written with `to_string()`.

**The `#define` a `const` lowers to had carried a suffix since it was built**, two branches up
in the same function. *Two spellings for one thing, and the weaker one decided here* — `W7`,
the shape `konst_wert` had before it.

| stage | before | after |
|---|---|---|
| `pruefe` | `2 items, 0 errors, 0 hints` | unchanged |
| `emit` | `static uint64_t x … = 18446744073709551615;` | `… = 18446744073709551615u;` |
| `cc` | *integer constant is so large that it is unsigned* | accepted under `-Wall -Wextra -Werror` |

**The boundary is `czahl`'s and not the `#define`'s.** That branch suffixes every non-negative
value; `czahl` suffixes only past `2^63 − 1`, for the reason its own note gives —
`-Wconversion` and `-Wsign-conversion` read these same literals, so a suffix added where C
does not need one trades this error for a different one. A negative value keeps its plain
spelling: `-5u` is not a smaller spelling of `-5` but another number.

**Past `2^64 − 1` the sink now refuses through `czahl_oder_absage`** — where it used to say
*"`static` with a non-constant initialiser"* about a number that is as constant as a number
gets. That is the same wrong-reason diagnostic `konst_zahl`'s own note complains about, one
sink further in.

**Probe:** `messung/proben/probe-static-past-the-signed-end.gab` — not poison, because the
program was always correct Gabbro. `pruefe-emission.sh` stage 9 compiles it under `-Werror`
at every run, and `MARKE_EMIT_M` went `54 → 55` for it.

### The cost to the corpus, measured and not argued

`gabbro emit` was run over **all 613 versioned `.gab`** with the tree at `393d866` and again
with both repairs in, and the two dumps compared byte for byte:

    diff -rq /tmp/d7-korpus-vorher /tmp/d7-korpus-nachher   ->  (no output)
    diff  vorher/CODES.txt nachher/CODES.txt                 ->  (no output)

**Not one byte of emitted C moved, and not one exit code.** No corpus `static` stands past
`2^63 − 1` and no corpus `reason` case stands past `9`.

---

## 5. The sweep after the two repairs

Same tool, same machine, same denominators.

| | at `393d866` | after `D13`+`D14` |
|---|---:|---:|
| accepted by the checker | 3 514 | 3 514 |
| lowered by the emitter | 2 813 | **2 784** |
| refused BY NAME | 701 | **730** |
| of the lowered, compile under the gate | 2 791 of 2 813 | **2 784 of 2 784** |
| **shape 2 — the C does not compile** | 22 | **0** |
| **net 5 — not ISO C** | 15 | **2** |
| shape 1 / shape 4 / net 8 | 0 / 0 / 0 | 0 / 0 / 0 |
| shape 3 — the oracle | 69 | **69** |

**Shape 2 is empty.** Every one of the 2 784 units the emitter lowers compiles under
`cc -std=c11 -O0 -Wall -Wextra -Werror -c`, and 2 782 of them also under `-Wpedantic` — the
two that do not are `-Woverlength-strings` on a 4 096-character section name, a different
complaint about the same slot.

### The bookings, and a finding about the ratchet itself

`fuzze-erzeuger.py` returns 1 on a booking whose finding has **vanished** — *a stale booking
hides the next one at the same place.* At `393d866` it reported **11 stale bookings** and
therefore returned 1: `D1`–`D6` landed and their lines stayed. **The tool was red at `master`
with nothing wrong in the tree**, and a real finding at any of those eleven places would have
arrived in the same paragraph as eleven that were not findings.

All fourteen are out now — the eleven of `D1`–`D6` and the three this lane closed — and each
removal is measured: the run before each deletion printed `booked N, found 0` for exactly the
line deleted.

---

## 6. The oracle question, answered

The mandate this lane answers puts it exactly: *shape 3 was found 69 times, all of them the
`konst_zahl` class at three `entry` slots — that class is repaired. Is the oracle finding
anything else, and if not, is that because there is nothing or because the oracle is narrow?*

### First, the premise. `D7` is NOT repaired

**Shape 3 stands at 69 today, and it is the same three `entry` slots.** The tool books it
under `D7` and prints `[==]` — unchanged — at every run since 2026-09-02. What was repaired on
that day was `konst_zahl`'s lossy `as i128`, which stopped `u128::MAX` coming out as `-1`; the
`try_from` that replaced it returns `None`, and the emitter then writes

    /* entry e -- arch x86_64
     * vector: not a constant in this unit

for `entry e vector 340282366920938463463374607431768211455`. **It IS a constant**, and the
unit emits, and `cc` is content. *A repair at the reader stopped the wrong number; it did not
stop the missing one.*

### Second, what the oracle IS, and what it therefore cannot ask

The oracle is one sentence: **the integer the source names must appear literally somewhere in
the emitted C.** It runs only where a form's C demonstrably carried some rung's value, and
that self-calibration is what keeps a `costs` clause out of the denominator.

It is therefore silent wherever the number reaches the artefact **transformed** — a bit range
becomes a mask, an offset becomes an address, a stride becomes a multiplier — and at
`393d866` that silence covered **1 584 of 2 784** lowered cases: the larger half.

**Widening it per form is not cheap and would not be trustworthy.** It would mean writing
down what each form's C ought to look like — a second emitter beside the emitter, `W7` — and
a second emitter is the one thing that cannot be relied on to disagree with the first.

### Third, the widening that IS cheap, and it was built

There is one question about a transformed value that needs no knowledge of the transform:

> **Two source programs that name different numbers must not produce one artefact.**

A transform may be anything; it may not be constant. Where it is, the emitter threw the value
away. `kollisionen()` in `fuzze-erzeuger.py` is that question, about 30 lines, with a SHA-256
of each lowered unit as the only new measurement. It calibrates itself the same way — a form
whose C never varies has one fingerprint over every rung and is out of both numbers — and it
groups by the NUMBER and never by the text, so `16`, `0x10` and `0b10000` agreeing is silence.
Four speech probes, both directions.

**It found `D7` from a standing start**, knowing nothing about `entry` or `konst_zahl`, and it
found **one case per form MORE than the literal oracle**: the negative rungs, where 3a cannot
speak because *"the literal does not appear"* is also true of an honest lowering.

### Fourth, and this is the finding: the widening did NOT widen the denominator

    reached by 3b and NOT by 3a: (none)
    reached by 3a and NOT by 3b: name-const name-fn name-tabelle

At `393d866` **3b's population was a strict subset of 3a's** — 1 140 of 1 200 — and the union
was still 1 200. The 1 584 unoracled cases stayed 1 584. *A form whose C varies with the
number is a form whose C carries the number, and on that tree every such form carried it
literally.* **The oracle was not narrow. The TEMPLATES were.**

### Fifth: where the unoracled half actually lives, and it is now printed

`fuzze-erzeuger.py` now names them — **27 forms, 1 495 lowered cases whose emitted C is
byte-identical over every rung.** Two causes, and only one of them is repairable:

| | |
|---|---|
| **compile-time slots** | `costs`, `lock … held`, `invariant cost`, a range type, a bare `spec fn`. There is nothing in ANY C to check, and no instrument over emitted text ever will. |
| **a declaration NOTHING USES** | `device D(basis : Pa) at mmio { reg X : u64 @0x8 class rw }` lowers to `typedef struct { volatile uint8_t *basis; } D;` **and nothing else** — 44 distinct offsets, one artefact. The emitter writes an accessor for a register that is READ, and the shared template reads none. |

*That is `ERZEUGERSWEEP.md` §6's finding about `aligned-n`, and it was never only about
`aligned`.* The shared table is written for the CHECKER, where a bare declaration asks the
whole question; for the EMITTER a declaration is a promise and the USE is the artefact.

### Sixth: two templates with a reader, and four defects in the first run

`fuzze-erzeuger.py` owns two more forms as of today — `reg-versatz-leser` and
`reg-bit-hi-leser`, the same slots the shared table declares without reading. They cost
222 cases and 40 lines. **The first run found four defects, in a slot the sweep had been
calling clean since 2026-09-02:**

| | | cases |
|---|---|---:|
| `D15` | the field mask is computed in `u32`, and `u32::MAX − 0 + 1` **panics** | 13 |
| `D16` | the register offset goes into the C with no `u` and no fence — **the ninth sink of `D3`** | 7 |
| `D17` | a register whose offset is not foldable is **dropped from the map**, and the access falls through to `d->X` | 3 |
| `D18` | two negative offsets share one artefact — found by 3b, invisible to 3a | 1 |

**And `reg-bit-hi-leser` is the first form 3b reaches that 3a does not**, exactly as
predicted: `@[3:0]` becomes `& 15u` and `@[15:0]` becomes `& 65535u`, so the swept number is
nowhere in the text and only the comparison between two cases can see it.

### The answer, in one line each

* **Is shape 3 empty?** No. It is 69, it is `D7`, and `D7` is open.
* **Is anything else there?** Yes — the collision oracle adds 3 cases at `entry` that 3a
  cannot see, and the two new templates added 24 more at a slot nobody had emitted.
* **Was the oracle narrow?** *Not in the way it looked.* Over the 64 shared forms the second
  oracle reached no case the first did not. **The narrowness was in the templates**, and the
  measurement that says so is the 27-form list the tool now prints.
* **What would it cost to widen further?** The list is the work order: about 40 lines per
  form, and the first two returned four defects. The compile-time half of the list is not
  work — no instrument over emitted C can reach it, and the one that can is
  `fuzze-grenzen.py`, one storey down.

---

## 7. `D15`–`D18` — the four the two new templates found

All four sit at one construct: **a `device` register that something READS.** The shared
template declares one and reads none, so none of the four had ever been emitted.

### `D15` — the field mask is computed in `u32`

**The decision: widen the arithmetic. There is nothing to decide.** `Geraet::felder` stores
`(hi, lo, width)` as `u32`, so `hi - lo + 1` was a `u32` add — and `u32::MAX - 0 + 1` is not a
number. The debug build panics; the shipped build wraps and writes a mask that is wrong.

| stage | before | after |
|---|---|---|
| `pruefe` | refuses (`N007` — a bit past the width) | unchanged |
| `emit` | **panic**: *attempt to add with overflow*, `emit.rs:9403` | the refusal, and no panic |
| `cc` | never reached either way | |

**The input is one the CHECKER refuses, and the panic happened anyway** — `command_emit` runs
the whole back end before it reads the verdict, and the range refusal sits at the declaration
while this expression is reached from a function body. *That is net 8's whole reason for
existing, and this is the first defect it has caught.* Net 8 went `0 → 13 → 0`.

> The bit position `4294967295` is itself a truncation — `*b as u32` in `Namen`, the
> `konst_zahl` cast one construct over. **Two lossy conversions in a row, and the second one
> is the one that panicked.**

### `D16` — the register offset, the NINTH sink of `D3`

**The decision: a lowering plus a refusal, and both are `D3`/`D4`'s.** The offset becomes C
text in `geraetelesung` through a bare `{versatz}`.

| stage | before | after |
|---|---|---|
| `pruefe` | `4 items, 0 errors, 0 hints` | unchanged |
| `emit` | `return (*(volatile uint64_t *)(d->basis + 9223372036854775808));` | `… + 9223372036854775808u));` |
| `cc` | *integer constant is so large that it is unsigned* | accepted |

`messung/proben/probe-literal-past-the-signed-end.gab` names nine sinks. **This is not among
them, and it could not have been**: nothing in the corpus or in either sweep had ever emitted
a register accessor at a boundary offset.

### `D17` — a register the emitter cannot READ vanishes, and the access falls through

**The decision: refuse by name at the declaration.** This is the worst of the four.

    device D(basis : Pa) at mmio { reg X : u64 @_1 class rw }
    impl fn g(d : ptr<mmio, rw> D) -> u64 … { return d.X; }

| stage | before | after |
|---|---|---|
| `pruefe` | `4 items, 0 errors, 0 hints` | unchanged |
| `emit` | exit `0`, writes `return d->X;` | exit `1`, `C001` at the `reg` |
| `cc` | *`D` has no member named `X`* | never reached |

`Namen`'s builder records a register only `if let Some(v) = umg.konst_wert(...)`. An offset it
cannot fold **drops the whole entry**; `ort` then finds no register of that name and falls
through to the generic suffix walk, which writes a plain struct member. *A filter that turns a
KNOWN fact into a MISSING one* — word for word the class `ERZEUGERSWEEP.md` §9 named for
`table count 0`, one construct over. **A rule with no value does not refuse; it says nothing.**

> The comment beside the WIDTH filter in the same loop already promised this shape of answer —
> *"`geraet` refuses it by name a few hundred lines further down"*. The offset was the half of
> that sentence nobody had written.

The refusal, literally:

    error: [C001] …:3:36: no lowering: a `reg` whose `@` offset is not a constant this unit
    can fold -- the offset is the whole of the access (`basis + offset`), and without it there
    is no accessor to write. The access would fall through to a plain struct member that no
    declaration ever made

### `D18` — two negative offsets, one artefact

Found by the collision oracle and invisible to the literal one. Closed by `D16`'s fence: a
negative offset has no reading at all, since the base is the device and there is nothing below
it.

### The cost to the corpus of all four: two diagnostics, no C

`gabbro emit` over all 613 versioned `.gab`, `393d866` against this tree, byte for byte:

* **no emitted C changed and no exit code changed**;
* `beispiele/gift/411` — this lane's own rename;
* `beispiele/gift/600-registerlage-jenseits-der-zeigerbreite.gab` gains a `C001` **beside**
  its `N051`, which still falls first. The probe stays green and stays `begleitet`.

> **The overlap with `N051` is deliberate and it is not `W7`.** `N051` is the checker's rule
> about an offset past `u64::MAX`; this is the emitter's about an offset it cannot write.
> **`gabbro emit` runs the back end BEFORE it reads the verdict**, so the emitter reaching this
> code on an `N051` input is not hypothetical — it is what `D15` panicked in.

---

## 8. Both sweeps, closing numbers

| `fuzze-erzeuger.py` | 2026-09-02 | at `393d866` | this tree |
|---|---:|---:|---:|
| forms | 64 | 64 | **66** |
| cases generated | 5 889 | 5 889 | **6 111** |
| accepted — the population | 3 517 | 3 514 | **3 584** |
| lowered | 3 039 | 2 813 | **2 816** |
| refused BY NAME | 478 | 701 | **768** |
| of the lowered, compile | 2 766 of 3 039 | 2 791 of 2 813 | **2 816 of 2 816** |
| 1 a third answer | 0 | 0 | **0** |
| 2 the C does not compile | 273 | 22 | **0** |
| 3a the literal oracle | 69 | 69 | **69** |
| 3b the collision oracle | *(did not exist)* | *(did not exist)* | **72** |
| 4 debug/release disagree | 0 | 0 | **0** |
| 5 not ISO C | 16 | 15 | **2** |
| 6 identifier past C11 | 58 | 58 | **58** |
| 7 degenerate arithmetic | 3 | 3 | **3** |
| 8 the emitter did not halt | *(did not exist)* | 0 | **0** |
| reached by an oracle | 1 375 | 1 200 | **1 249** |
| shape-checked only | 1 664 | 1 584 | **1 567** |
| verdict | — | **exit 1**, 11 stale bookings | **exit 0** |

`fuzze-grenzen.py` is unmoved at **5 778 of 5 778 over 63 forms**, 0 panics, 0 disagreements —
and it cannot move, because it runs neither `emit` nor `cc`.

**Everything left in shape 3 is `D7`**, at the three `entry` slots, and it is the one thing
this lane found and did not close.

---

## 9. The named residue, each verified before it was worked

### 9.1 `zaehle-gifttreffer.py` at 9/8 — repaired, and the mark did not move

**Verified real:** the tool reported `DECKE verdeckt: 9 statt 8` at `393d866`, and probe `411`
sat over the mark exposed. The previous lane wrote down why it had left it: *"Raising to 9
would swallow it. A mark lifted past somebody else's finding does not record a repair; it
deletes a report."*

**What `411` needed, measured:**

    error: [N046] beispiele/gift/411:17:11: `recv` does not match the declaration C already has
      = this declaration becomes `uint64_t(uint64_t)`; C declares `ssize_t(int, void *, size_t, int)`
    error: [M134] beispiele/gift/411:24:14: `.op` reads a field on something that has none

`411` is about `M134` — a field access on a scalar. It calls its callee `recv`, cut from
`messung/fragmente/F05.gab`, where the IPC primitive is called that for reasons of its own.
**`N046` landed on 2026-09-01 and reads `recv` as POSIX's**, so from that day the probe had a
second subject, standing ahead of its first.

*It is the same shape as `662` and it is not the same cause.* `662` cannot be written any
other way — the emitter defect it holds needs a shape the checker refuses, so `M140` and
`C001` are untangleable and the pair belongs in `GIFT-GEGEN-ZUSAGE.md` §10. **`411`'s pair is
untangleable only because of a NAME**, and a name is free.

**The repair: the callee is `empfange`, a word C does not carry.** The finding is not deleted
— it stands in the probe's own header, which is where a probe records what once fell over it.

| | at `393d866` | now |
|---|---:|---:|
| `sauber` | 363 | **368** |
| `begleitet` | 59 | **59** |
| `verdeckt` | **9** (mark 8, red) | **8** (mark 8, green) |
| probes | 432 | **436** |

`MARKE_VERDECKT` is **untouched at 8**, and nobody's report was deleted.

> **A second finding, and it is not this lane's to move.** `MARKE_SAUBER` stands at 271
> against a measurement of 368, and `MARKE_PROBEN` at 333 against 436. Both were last set on
> 2026-08-31, when the corpus was 333 probes. *The tool's own note says what that costs*:
> *"A floor that lags behind the corpus is slack, not safety: at 262 it would have taken nine
> probes losing their subject before anybody heard a word."* **At 271 it would take
> ninety-seven.** Left standing deliberately — a floor is somebody's decision and the mandate
> named these numbers as ratchets, so the measurement is booked here rather than acted on.

### 9.2 Three of `D6`'s four shapes had no daily probe — they have one now

**Verified real**, all four re-run on this tree: an empty name, a blank name, the doubling
form and a NUL all fall at `C001`, and only the backslash carried a file.

| | probe |
|---|---|
| a name ending in a backslash | `beispiele/gift/646` *(stood already)* |
| an empty name | **`beispiele/gift/663-a-section-name-that-is-empty.gab`** |
| a blank name | **`beispiele/gift/664-a-section-name-that-is-a-space.gab`** |
| the doubling form | **`beispiele/gift/665-two-string-literals-join-with-a-space.gab`** |
| a name holding a NUL | *no file, deliberately* |

**The NUL is measured and deliberately has no probe.** It falls with the same refusal naming
the same character class, and a NUL byte in a versioned source file is a hazard for every text
tool in the tree for no measurement anyone does not already have.

*Why these three and not the backslash:* the backslash is the one shape a COMPILER sees. The
other three reach the **assembler**, and `tests/beispiele.rs` compiles a poison probe with
`-fsyntax-only` and never assembles one — so half of `D6` was invisible to the gate this
corpus actually runs. **Prose is not a probe**; `messung/ERZEUGERDEFEKTE.md` §6 measured all
four on the day and none of them ran again.

### 9.3 The 54 `-Wcast-align` sites — costed, and the cure PROVED on one unit

**Verified real, and the number is 100 and not 54.** Measured on this tree over all 125
emitted units:

    cc -std=c11 -O0 -Wall -Wextra -Wcast-align=strict
    125 units compiled, 15 carry -Wcast-align, 100 hits total

`messung/BERICHT-UEBERSETZERFAMILIE.md` §3.4 has the same 100 over the same 15 units, from
both compiler families, with identical per-unit counts.

**And the class has exactly ONE cause.** Grouping the 100 by the C form that draws them:

    50  (*(volatile uint32_t *)      26  (*(volatile uint64_t *)      16  (*(volatile uint16_t *)
    26  (volatile uint64_t *)         6  (volatile uint32_t *)         6  (volatile uint16_t *)

Every one is a cast from the handle's `volatile uint8_t *basis` up to a wider volatile
pointer — a register access, a bank access, or a transition mirror. **Nothing else in the
whole emitted corpus draws it.**

#### The cure, and it is three sites in the emitter

| | |
|---|---|
| the preamble | `typedef uint8_t gabbro_wort __attribute__((aligned(8)));` |
| the handle | `volatile uint8_t *basis;` → `volatile gabbro_wort *basis;` |
| the constructor | `(volatile uint8_t *)(uintptr_t)` → `(volatile gabbro_wort *)(uintptr_t)` |

*Applied BY HAND to one emitted unit and compiled, so this is a measurement and not a design:*

    beispiele/02-geraet.gab, emitted C
      before   cc -Wcast-align=strict   21 hits
      after    cc -Wcast-align=strict    0 hits
      after    cc -Wall -Wextra -Werror              exit 0
      after    cc -Wall -Wextra -Werror -Wpedantic   exit 0

**The class goes to zero and the tree's own gate does not move.** Arithmetic is unaffected:
the typedef's `sizeof` is still 1, so `basis + 8` still advances eight bytes.

#### What it costs, and why this lane did not do it

* **The alignment is a CLAIM and it needs its ground written beside it.** `aligned(8)` says
  every device base is 8-aligned. `N047`–`N049` prove the offsets; the BASE comes from the
  device constructor and is the caller's number. *A `__attribute__` that states more than the
  checker proves is a guess in an attribute*, and the honest form of this repair carries the
  proof reference in the emitted comment.
* **It changes the handle's C type**, which is in 15 units' public surface, in the 25
  hand-comparison units of `pruefe-emission.sh` stage 1–8, and in whatever `manifest::sammle`
  writes into the header.
* **The reward is real but it is not a defect.** `BERICHT-UEBERSETZERFAMILIE.md` §5 already
  decided against adding `-Wcast-align` to the gate, in writing: *"Adding it books 15
  permanent exemptions to catch nothing."* The repair turns those 15 exemptions into zero and
  lets the switch join the gate — **which is the actual prize, and it is a gate decision and
  not an emitter one.**

*So: costed, proved on one unit, and handed over with its blast radius named.*

---

## 10. What this lane could not close

1. **`D7` — an `entry` number the emitter cannot represent, and it emits the unit anyway.**
   69 cases by the literal oracle, 72 by the collision oracle, at `entry … vector`, `stack …
   ist` and `nested bounded`. The C reads *"vector: not a constant in this unit"* about a
   value that is a constant. **It was reported repaired and it is not**; the `konst_zahl`
   repair of 2026-09-02 stopped the wrong number and not the missing one. The booking says
   where the answer belongs — *a named refusal at check time, in the `N051` family* — and
   that is a checker decision, not an emitter one.
2. **The `-Wcast-align` repair** (§9.3): costed, proved on one unit, not applied. Its prize is
   a gate decision.
3. **`MARKE_SAUBER` at 271 against 368 and `MARKE_PROBEN` at 333 against 436** (§9.1): a
   floor with ninety-seven probes of slack, measured and left standing.
4. **Twenty-five more forms whose lowered C does not move** (§6, fifth). The two this lane
   added returned four defects between them; the tool prints the rest as a work list, and the
   compile-time half of it is not work at all.

---

## 11. The runs, at the end

Everything on `ki-pc-fisch-101` out of `gabbro-d7`.

    cargo test --offline --no-fail-fast     400 passed, 0 failed
    instrumente/pruefe-emission.sh          ALL PASS -- 25 run through, 122 of 122 compile,
                                            4 reverse probes, clang agrees on all 122
    instrumente/fuzze-erzeuger.py           exit 0 -- 6111 cases, 66 forms, 0 unbooked,
                                            0 stale bookings
    instrumente/fuzze-grenzen.py            exit 0 -- 5778 of 5778, 0 panics
    instrumente/zaehle-gifttreffer.py       ALL PASS -- 368 of 436 hit alone
    instrumente/mutiere-pruefer.py --anker  ALL PASS -- 383 of 383 anchors hold
    instrumente/zaehle-karten.py            45 / 40 -- unmoved from `393d866`
    instrumente/pruefe-englisch.py          ALL PASS -- 7883 / 1069, both unmoved
    instrumente/zaehle-wortschatz.py        exit 0 -- 221 / 208 / 333, all unmoved
    instrumente/pruefe-todo.py              ALL PASS
    instrumente/pruefe-zahlen.py            exit 0 -- 83 of 83 entries recomputed

**Three guardians moved and each one has its reason at the mark:**

| | | why |
|---|---|---|
| `MARKE_EMIT_M` | 54 → **55** | `messung/proben/probe-static-past-the-signed-end.gab` |
| poison corpus | 432 → **436** | four probes: `663`–`666` |
| `pruefe-widerruf.py` files | 188 → **189** | this document; measured by removing it and putting it back |

And two numbers in `TODO.md` were recomputed rather than carried: **3182 → 3191** line
continuations (the refusal texts of `D13`, `D16` and `D17`), and the `register-ohne-volatile`
mutation anchor, which hung on the very line `D16` rewrote. *The missing anchor WAS the
report* — `--anker` said `382 von 383` and named it.

### The acceptance run, both ends

`./instrumente/abnahme.py` was run on `ki-pc-fisch-101` over this tree and, before anything
moved, over `393d866` in the same directory.

    at 393d866   ABNAHME ROT: 3 von 50
                 pruefe-grammatiktafel.py   red by owner decision (`state`)
                 zaehle-gifttreffer.py      the covered-probe cap, 9 against 8
                 zaehle-karten.py           45 direct card lookups against a mark of 40 / 36

    this tree    ABNAHME ROT: 2 von 50
                 pruefe-grammatiktafel.py   unchanged -- owner decision
                 zaehle-karten.py           45 / 40, IDENTICAL to `393d866`

**One guardian repaired, none broken, and the two that stand are the two that stood.**
`zaehle-karten.py` is the one to say out loud: `D16`/`D17` added a direct `.geraete.get(` and
the count went 45 → 46. *It is back at 45 because the lookup was hoisted*, not because the
counter was appeased — `geraet` asked `u.geraete` twice in one function and now asks once,
which is the sentence `ort` already carries over its own three: *asking it three times in one
block is three chances to ask it differently.*

> **And a finding about that counter, since the hoist is what showed it.** `zaehle-karten.py`
> matches `\.<map>\s*\.\s*get\(` **per LINE**, so the multi-line spelling `u\n.geraete\n.get(`
> — which is what `rustfmt` produces for a long chain, and what stood in `geraet` already —
> escapes it entirely. *Its 45 is a lower bound and reads like a count.* Not moved by this
> lane; booked here.

---

## 12. The merge, and the collision the mandate predicted happened

**`master` moved from `393d866` to `3b17d9a` while this lane ran, and the two lanes moved the
SAME number by one, for DIFFERENT files.**

    this lane   188 -> 189   `messung/ERZEUGERREST.md`      -- measured, file out and back
    master      188 -> 189   `messung/GABBROV-AUDIT.md`     -- measured, file out and back

Each side was correct alone. **The merged tree has 190.** Resolved by re-measuring in the
merged tree — `pruefe-widerruf.py` says `190 Dateien` — and not by picking a side and not by
adding.

> **What is different about this one is only luck.** `TODO.md`'s own entry records three
> earlier instances *"und `git` sah keinen Konflikt"*: two lanes writing the same digit in
> different places merge silently, both green, and the result is wrong. This time both lanes
> wrote into the same line, so git reported a text conflict and the number could not be
> missed. *That is a property of where the prose happened to sit, not of the guard* — and the
> three that came before show what it looks like when the prose sits elsewhere.

**Everything else was re-measured in the merged tree rather than carried across:**

    cargo test --offline --no-fail-fast   400 passed, 0 failed
    instrumente/fuzze-erzeuger.py         exit 0 -- 0 unbooked, 0 stale bookings
    instrumente/zaehle-gifttreffer.py     ALL PASS -- 368 of 436, 8 covered against a mark of 8
    instrumente/pruefe-zahlen.py          exit 0 -- 83 of 83 entries recomputed
    instrumente/pruefe-todo.py            ALL PASS

`master`'s changes touch `messung/gabbrov/`, `programmlogik/gabbrov/`, `dokumente/PLAN-HARDWARE.md`
and `TODO.md`; **nothing under `crates/`, `instrumente/` or `beispiele/`**, so no repair, no
probe and no booking of this lane had a second author.
