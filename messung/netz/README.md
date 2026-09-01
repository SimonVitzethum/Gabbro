# The network stack — stage 4, and the template comes from outside

**Subject: Ethernet → ARP → IPv4 → UDP, an echo service.** Written against **RFC 791**,
**RFC 826**, **RFC 768** and **RFC 1071** — and checked against **published test vectors**,
not against packets of our own.

<!-- The block below is a QUOTED RUN of `zaehle-netz.py`, in the tool's own language.
     It is EVIDENCE, not prose: a translated transcript is no longer a transcript, and
     `pruefe-zahlen.py` reads the last line of it. Do not "fix" it into English -- it moves
     when the tool's output moves, and not before. -->

```
$ ./instrumente/zaehle-netz.py
ok   ohne   Gabbro b861  Gegenrechnung b861   IPv4-Kopf, Feld genullt (RFC 791)
ok   mit    Gabbro 0000  Gegenrechnung 0000   derselbe Kopf MIT der Summe — muss 0 sein
ok   summe  Gabbro ddf2  Gegenrechnung ddf2   RFC 1071, Abschnitt 3: die Summe
3 von 3 Proben grün
```

## Why the vectors have to come from outside

**Rule A: no new construct without a program that needed it.** *Rule B, and rule A does not
hold without it:* a stack that the same author writes against his own test packets measures,
once again, **how well Gabbro fits Gabbro**.

Hence a threefold separation:

| | |
|---|---|
| **the template** | the RFCs — nobody picked them for Gabbro |
| **the vectors** | the classic IPv4 header and RFC 1071 §3; they were there beforehand |
| **the counter-calculation** | a **second implementation**, in Python, deliberately written differently (there every step folds; in Gabbro only the end folds, twice) |

> *A comparison against one's own figure is no comparison* (W7). Were both sides from the same
> pen, the same error in reasoning would pass twice.

**The third probe carries the most:** the sum over a header that already holds the checksum
must be **0**. That is the property the whole receive path rests on — and the only one of the
three that a wrong folding does not survive.

## The yield: four holes that 45 examples did not show

**1. `!` had no lowering — and the entire clean corpus has zero occurrences.**

```
if !kopf_gueltig(k, w) { return 0; }     -- the most ordinary line of a receive path
gabbro pruefe → 0 errors · gabbro emit → C001 "expression form"
```

*The corpus is written **per construct** — one file for `table`, one for `device`. A `!` is not
a construct; it is what one does when one writes a program.* Built, with a counter-probe in
[`beispiele/46-verneinung.gab`](../../beispiele/46-verneinung.gab). **Unary minus was
expressly *not* built along with it**
([`gift/219`](../../beispiele/gift/219-unaeres-minus.gab)): in C, `-x` on an unsigned operand
stays unsigned, while M1 says `i32 in -4294967295 .. 0` — and no program needed it.

**2. The error channel `-> T or R` lowered WRONGLY, and in two ways at once.**

```
f(0)  →  the call reports FAILURE, although 0 is a valid value
f(7)  →  the call reports success, and *_wert stays UNTOUCHED
```

The generator wrote `return <value>;` into a function whose C signature returns `bool` — and
put `__attribute__((const))` on it into the bargain, whereupon GCC dropped the store.
**`gabbro pruefe`: 0 errors, 0 hints. `gabbro emit`: return code 0. `cc` without `-Werror`:
compiles.**

> *The whole corpus carries `or R` exclusively on `extern fn`* — that is, on bodies this
> generator never sees. **The first body of our own with an error channel was this stack.**

**3. A `reason` value has no producer — and now it says so in the emitted C.** `*_grund` stays
unwritten because `primary` knows no production for it. Without a line, compilation fails
under `-Werror=unused-parameter`; the generator writes it **with the finding in it** rather
than passing over it in silence.

**4. "Read the same bytes as big-endian 16-bit words" is not writable.** A `format` explains
the byte order *for its fields*; a field type `[u16; 10]` in a `format` is refused twice — the
field type itself, and the access to it (*"a reader yields a VALUE, and a value has no place
in the bytes"*, and that is right).

> **The consequence stands in the test rig:** assembling the words out of the bytes happens in
> C, not in Gabbro. *Gabbro computes the checksum; the view onto the same bytes comes from
> outside* — and with that, precisely the step a language would need to manage for network
> code lies outside the language.

### And the edge stands settled BEFORE anything is built *(2026-08-21)*

**The byte view must not open an alias question. One view writing, all others reading, and the
switch is an EVENT** — that is the shape of `state`/`transition`, applied to views instead of
to states. The long form stands in
[`dokumente/SYNTAX.md`](../../dokumente/SYNTAX.md) §3; here stands why this folder is the
occasion.

**This file already contains the case.** `echo_beantworten` takes two pointers:

```gabbro
impl fn echo_beantworten(e : ptr<normal, r>  EthKopf,
                         k : ptr<normal, rw> IpKopf,      -- writing
                         w : ptr<normal, r>  Kopfworte,   -- THE SAME bytes, reading
                         meine_ip : u32) -> u32 or Verwurf
    effects { reads e, reads w, writes k }
```

`w` is `kopfworte_von(k)` — the same twenty bytes, once as fields and once as ten 16-bit words.
The body checks the checksum over `w`, and afterwards it writes `k.ttl = 64`. **From that line
on, the answer read through `w` is stale**; RFC 791 demands the checksum recomputed, and
`effects` claims both accesses are declared.

Measured on 2026-08-21 with a hand probe of the same shape: **0 errors, 0 hints.** `gabbro
pruefe` is equally silent for `zwei(r, r)` on two `ptr<normal, rw>` parameters. Only the
syntactically identical site on two `own` parameters falls (`R004`), and its own note says the
rest: *"two DIFFERENT names pointing at the same object stay indistinguishable (M3's open
alias question)."*

> **The rights half is already right here** — `w` reads, `k` writes. **What is missing is the
> event half:** nothing invalidates `w` at the write site, nothing forbids its use afterwards.
> *A byte view that takes over only the rights half inherits this hole and gives it a construct
> to hide behind* — and then the item buys its completeness with a silent alias exception.

## What does NOT stand here

No TCP, no fragmentation, no variable header length (`ihl > 5` is checked and not handled), no
timer, no retransmission. **The stack is measured against three vectors, not against a
network** — what it can do stands above; what Gabbro could not do meanwhile stands beside it,
and that is the real yield.
