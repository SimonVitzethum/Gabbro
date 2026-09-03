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
