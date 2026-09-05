# A word is a keyword only where the grammar expects one

**2026-09-05.** «K3» produced **0 of 8** and `P002` fired in six of the eight excerpts, every
time on an identifier the Linux kernel itself wrote. This document holds the measurement that
followed, the decision it forced, the price of the three alternatives, and what the corpus did
when the decision was built.

> **The order matters and is checkable.** The collision was measured against foreign code
> *before* a line of `crates/` moved; the corpus-wide sweep was taken *before and after* the
> same build. Both are reproduced below with the command beside every number.

---

## 1. The collision, measured against code nobody wrote for Gabbro

### 1.1 The method, stated before the run

A word counts as a collision at a site only where a programmer **bound** that name — a local,
a parameter, a struct field, a function, an object-like macro. A mere *use* is not counted:
`p->next` is the same binding as the `struct` field, counted once at the declaration. That is
deliberately the narrower question, and it is the one `P002` answers.

Three foreign bodies of code, **585 files**, none of them written for or by this project:

| corpus | files | why it is here |
|---|---:|---|
| `linux/lib/*.c` | **212** | the region «K3» drew from — `K3-AUSWAHL.md` §3 |
| `linux/kernel/*.c` + `linux/mm/*.c` | **234** | the region «K2» counted over; already surveyed, so the figures are comparable |
| `../caprock-messbasis` (`.rs`) | **139** | a second language, and this project's own measurement base |

```bash
# the tool: /tmp/.../kollision.py -- the extractor is stated in its docstring
python3 kollision.py crates/gabbro-syntax/src/kw.rs kollision.json
python3 bericht.py  kollision.json
```

*The C extractor takes `#define NAME`, declaration statements ending in `;`, and parameter
lists before `{` or `;`; the Rust extractor takes `let`, `fn`, `const`/`static`, item heads
and `name : Type` at a field or parameter boundary. Both drop comments and string literals
first, and both exclude their host language's own keywords — **which is why a C keyword scores
zero, and soundly: a word C reserves is a word no C programmer bound.***

**Calibration, so the extractor is checked and not believed:** all eight words «K3» found by
hand (`node`, `old`, `next`, `progress`, `release`, `stack`, `index`, and `to`, which never
reached the transcription) come out non-zero.

### 1.2 Direction one — how many of the 221 are plausible identifiers?

> ## **105 of 221.**

| | |
|---|---:|
| words that bind **somewhere** in the 585 files | **105** |
| words that bind **nowhere** | **116** |
| of those 116: also a keyword of C or Rust | 17 |
| of those 116: genuinely absent | **99** |

**And the collision mass is extremely concentrated.** 5564 declarator sites over 105 words:

```
word        lib        kernel+mm    caprock      total   (sites / files)
node        226/27      235/47        1/1          462
count       158/42      223/70       16/10         397
entry       160/13      210/47       27/9          397
cpu          30/15      330/46       15/5          375
order        55/8       308/44        0/0          363
index       140/24      102/24       33/12         275
next         44/23      166/52       36/16         246
type         61/8       182/42        0/0          243
ptr          84/22       97/22       18/6          199
parent       68/15       89/30       21/7          178      (already contextual)
```

| the top | share of all 5564 colliding sites |
|---|---:|
| 5 words | 34.3 % |
| 10 words | 55.2 % |
| 20 words | 76.2 % |
| 30 words | 87.3 % |

### 1.3 The rate per FUNCTION, which is what «K3»'s 6-of-8 is a sample of

The same extractor run over the population «K3» drew from — the function finder is the
selection program of `K3-AUSWAHL.md` §4, verbatim, so the denominator is that document's own:

```bash
python3 perfunktion.py crates/gabbro-syntax/src/kw.rs \
        /home/simon/Dokumente/SEL4Lake/_linux-mess/linux/lib
```

| population | functions | bind at least one reserved word |
|---|---:|---|
| every function in `lib/*.c` | 3324 | **1035 — 31.1 %** |
| the 8..60-line window «K3» drew from | 1709 | **646 — 37.8 %** |

**«K3»'s 6 of 8 was a high draw of a real rate**, not a freak: 37.8 % per function, and the
eight are eight draws. Of the 646, 433 carry one colliding word, 159 two, 44 three, and ten
carry four to six.

### 1.4 Direction two — which words are NEVER anyone's name?

**99 of 221, and they are Gabbro's own vocabulary.** Not a scattering: the contract words
(`requires` `ensures` `maintains` `refines` `effects` `costs` `decreases` `breaking`
`exhaustive`), the effect words (`reads` `writes` `consumes` `publishes` `diverges` `pure`),
the loop words (`traverse` `over` `unvisited` `consuming` `forever` `until` `bounded`
`per_pass` `on_exceeded` `leave` `leaves`), the assumption layer (`assume` `axiom`
`falsifier` `unfalsifiable` `counterprobe` `expects` `claim` `measures` `gates` `can_fail`),
the quantifiers and the width words (`u16` … `i64`, `f32`, `f64`, `forall`, `exists`,
`lenof`, `sizeof`, `rounded`, `finite`).

> **This is the shape that decides the design.** The words a systems programmer collides with
> and the words Gabbro invented are **almost disjoint sets**. The collision is not a property
> of having a large vocabulary; it is a property of the *library* half of it — `node`,
> `count`, `entry`, `index`, `stack`, `state`, `table`, `slot`, `walk`, `lock` — which is
> exactly the half that names things a program also names.

---

## 2. How many `P002` sites in «K3» are the collision, re-derived

```bash
for f in messung/k3-fragmente/K0*.gab; do
  ./target/debug/gabbro pruefe "$f" | grep -E '^error: \[P002\]'; done
```

**14 sites over the eight frozen files**, and they are three different things:

| | sites | |
|---|---:|---|
| an identifier the kernel wrote | **12** | `node`×2 (K01) · `old`, `next`×2 (K02) · `progress` (K03) · `release` (K05) · `stack`×3 (K06) · `index`×2 (K08) |
| a **cascade** of one of those | **1** | K01:159 `else` — the `if` at :156 died on `node`, the reader resynchronised past the closing brace, and the `else` of a perfectly good `if/else` was read where a name was expected |
| the author's own abbreviation | **1** | K02:71 `None`, shortened out of `ODEBUG_STATE_NONE` |

**13 of 14 are the collision, directly or as its wake.** `K3-BEFUND.md` §3 counted seven
distinct words; the fourteenth site and the cascade are new here because this re-derivation
counted sites and not words.

---

## 3. The design, and why the other three lose

### 3.1 What was built

> **A word of the closed vocabulary is a keyword only at a position where the grammar expects
> one. At every position where the grammar writes `ident`, every word of the table is a name.**

**The parser was already written keyword-first**, and that is the finding that made this
cheap. At every decision point the keyword arms are tried before the identifier path, so
admitting a word at an identifier position *cannot steal an existing production* — it can only
turn a refusal into a parse. The change is therefore a **conservative extension**: no program
that parsed before parses differently. Three places needed real work, because at those three
a keyword production and a name genuinely compete:

1. **the head of a `stmt`.** Thirteen forms open with a word (`let if match traverse retry
   forever breaking narrow observes locks leave next return`), and a place may stand there
   too. One token decides — `parse.rs::ist_ortfortsetzung`: a word followed by
   `=` `+=` `-=` `&=` `|=` `.` `->` `[` `::` is a **place**, because no keyword statement may
   continue that way. `(` is deliberately excluded: `if (x) { … }`, `match (x) { … }` and
   `return (a);` are written that way. *The whole residue of the rule is the bare CALL form
   through a function named like a statement head — `beispiele/gift/683`.*
2. **`old` and `result`.** Both name something only a promise has, so they are words inside a
   contract clause and names everywhere else — `parse.rs::im_vertrag`, set at seven sites
   (`requires`/`ensures` of a `fn` and of an `fn` pointer, a `spec fn` body, a loop
   `invariant`, a `table` `invariant`, the `when` of an `exchange`, an `axiom`'s
   precondition, a `check`'s `floor`).
3. **a named type and a named address space.** The keyword arms already stand above the name
   arm, so the name arm was simply widened from `Art::Ident` to `Art::Ident | Art::Wort(_)`.
   Without that, `type count = u32;` would have been accepted at the declaration and `x :
   count` refused at the use — *a name that can be declared and not used is the worse of the
   two holes.*

**What is left reserved is 17 of 221**, on two measured grounds, and every one of the
seventeen has **zero** declarator sites in the 585 foreign files:

| | words | why |
|---|---|---|
| **10** | `sizeof` `lenof` `aligned` `forall` `exists` `true` `false` `Self` `Some` `None` | each heads a primary expression or a predicate atom unconditionally, so a variable of that name could be bound and never read back |
| **7** | `const` `static` `extern` `if` `else` `return` `bool` | each breaks the **emitted C** as an ordinary local — measured, §5 |

**The two lists meet the zero for the same underlying reason:** nine of the seventeen are C's
own keywords and two are Rust's, so no C or Rust file *can* contain one as a name.

```
                       colliding words   still reserved   declarator sites freed
before  2026-09-05          105               105                    0
after                       105                 1              5562 of 5564  (99.96 %)
```

The one is **`aligned`**, at two sites in one Caprock file.

And the per-function rate, re-run against the changed column: **0 of 3324** functions in
`lib/*.c` bind a reserved word, down from 1035; **0 of 1709** in the «K3» window, down from
646.

### 3.2 An escape — a way to spell an identifier like a keyword

**It loses on the goal itself.** The owner's sentence is *a user must not have to rename their
variables*; an escape replaces renaming with quoting, which is the same work wearing a
different hat, plus a thing to learn. It also costs a new lexical form — `` `node` `` or
`r#node` — and a new lexical form **is** a language change under E1, so it is not the small
option it looks like. And it does not fix the diagnostic: the user still meets a refusal
first, and the refusal still stops the body parsing until they act on it.

*The one thing it has going for it is that it is total.* It would have covered all 105 words
including the seventeen. Against that, the seventeen have zero measured sites.

### 3.3 Shrinking the vocabulary

**It cannot reach.** The ratchet may fall freely, and this was the direction that costs
nothing — so it was checked first and it does not answer the question. The ten heaviest
colliding words are `node` `count` `entry` `cpu` `order` `index` `next` `type` `ptr`
`parent`, and every one of them is load-bearing: `walk … { node : … }`, `table … count N`,
`entrydecl`, `per cpu`, the `order` of a boot mark, `option index into T`, `next <label>`,
`typedecl`, `ptr<space, rights> T`, the tree edge. Dropping enough of the 105 to move the
rate would gut the language.

**And the deeper objection is the shape, not the count.** A vocabulary trimmed word by word as
each collision is reported is a **blacklist of names somebody has already been bitten by** —
the exact class `instrumente/korpus.py`'s own head rejects for directory names: *"a blacklist
of PLACES stops being able to run out of names."* `parent`, `child`, `sibling`, `tree`,
`observed` and `occupied` were each prised out of the reserved set by a separate measurement
on a separate day, and after all six «K3» still hit seven more.

*Nothing fell. The ratchet stands at **221 / 208 / 333**, unmoved.*

### 3.4 Renaming, with the compiler naming the replacement — the status quo

This was the decision of 2026-08-15 (`M-woerter`), and its own docstring stated the choice it
was making:

> *"Of the three ways out — contextual words, a position rule, renaming — only the last
> carries the promise further: a softening for seven sites is a softening without measured
> need."*

**The measured need arrived.** Seven sites in a corpus this project wrote itself became 105
words over 585 foreign files, and «K3» showed the refusal masking every later diagnostic in
six of eight excerpts. The renaming table is deleted in this lane; the note it printed —
*"instead: `knoten`"* under a `P002` on the kernel's own `node` — **was** the plumbing.

---

## 4. The corpus-wide sweep, before and after

Every tracked `.gab` was run through the unchanged checker and the changed one and the two
runs diffed by file. The population is `git ls-files '*.gab'` — the authorship test
`instrumente/korpus.py` uses, so an untracked scratch file cannot move the denominator.

```bash
python3 sweep.py <tree> vorher.json  gabliste.txt     # 663 files, at b393c21
python3 sweep.py <tree> nachher.json gabliste2.txt    # 667 files, after
python3 diff.py vorher.json nachher.json
```

```
vorher=663 nachher=667 gemeinsam=663
NEU: 4   WEG: 0   GEAENDERT: 8
```

**655 of the 663 pre-existing files do not move at all.** The eight that do:

| file | before | after | what happened |
|---|---|---|---|
| six «K3» fragments | 14 × `P002` | 1 × `P002` | §6 |
| `beispiele/gift/11-wortschatz.gab` | `P002` on `let slot = 1;` | `P002` on `let Some = 1;` | **an expected code that had to move**, below |
| `beispiele/gift/220-old-in-einem-rumpf.gab` | `C001`, and `pruefe` said **0 errors** | `K003` + `E009` at the CHECKER | **an expected code that had to move**, below |

**Zero clean examples changed verdict. Zero other poison probes changed verdict.**

### 4.1 `gift/11-wortschatz.gab` — the probe whose rule was repealed

It asserted `P002` on `let slot = 1;`. That is the rule this lane removes, so the probe cannot
stand as it was: it now asserts `P002` on `let Some = 1;`, one of the seventeen, and its head
says which rule it guards and which one fell. `beispiele/70-kernel-namen.gab` holds the other
half — `slot`, and the eight «K3» words, and the nine heaviest colliding words, all clean.

### 4.2 `gift/220-old-in-einem-rumpf.gab` — a gap the change closed by accident

This probe documented a **known hole**, in its own words: *"`old(place)` belongs in an
`ensures` and no pass holds the line … `gabbro pruefe` reports 0 errors and 0 hints, and only
the generator falls. The difference is that with `!` the language was right and the generator
was missing; here the generator is right and the CHECKER is missing."*

Since `old` is now a word only inside a contract, `old(...)` in a body is a call to a name
nobody declared, and `K003`/`E009` say so **three passes before the emitter**. The expected
code moves from `C001` to `K003` and the probe gets stronger. *The hole it booked is closed —
as a side effect of a change that was after something else.*

---

## 5. Three holes the change opened, and all three are closed here

A change this wide takes exemptions with it that were sound only because of what it removed.
All three were found by probing, not by reading.

1. **`M119` exempted the name `result`.** Sound while `result` could never be a place. After
   the change, `return result;` in a body with nothing declared gave **`0 errors`** and the
   emitter wrote `return result;` into the C. `beispiele/gift/684` holds the line; the
   exemption is deleted (`m1.rs::name_aufloesen`).
2. **`M119` exempted the width words** through `breite_wort` — `u8 … i64`, `bool`, `f32`,
   `f64`. Same shape: `return u32;` with `u32` undeclared gave `0 errors` and emitted
   `return u32;`. The qualified case (`u64::max`) is already covered by the `::` test one line
   up, so the helper is deleted outright.
3. **Seven words break the emitted C as a local.** `cnamen.rs` leaves `const else extern if
   return sizeof static` out of its `C11_WORT` table *on the grounds that this vocabulary
   refuses them*, and `bool`/`true`/`false` are likewise absent from its header table. Making
   them names would have made those two statements false at once. **They are the seven (plus
   `sizeof`, `true`, `false`, already reserved on the other ground) that stay `res`** — so
   `cnamen.rs` needs no change and its sentences stay true.

The measurement behind (3), one file per candidate through
`cc -std=c11 -O0 -Wall -Wextra -Werror` with the four headers every generated unit includes:

```c
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <math.h>
uint32_t f(void) { uint32_t <name> = 1; return <name>; }
```

| of the 221 vocabulary words | 7 break — `const static extern if else return bool` |
|---|---|

> ### And the same command found a hole that is OLDER than this change and is NOT closed
>
> `N041` asks `cnamen.rs` about **item names only**. A local is never asked, and
> `let int = 1;` emits `uint32_t int = 1;` with `gabbro pruefe` reporting `0 errors`.
> Measured with the same command over `cnamen.rs`'s own three tables:
>
> | table | names | break as a local |
> |---|---:|---:|
> | `C11_WORT` | 37 | **37** |
> | `HEADER` | 366 | **77** (every one an object-like macro) |
> | `EINGEBAUT` | 155 | **0** — shadowing a function compiles |
>
> **114 names, and none of them is a word of the vocabulary**, so this lane neither created
> the hole nor enlarged it. It is booked in `TODO.md`.

---

## 6. What the change did to «K3»

The third reading has its own dated file: [`K3-DRITTE-LESUNG-2026-09-05.md`](K3-DRITTE-LESUNG-2026-09-05.md).
`K3-BEFUND.md` stays untouched — **0 of 8 remains the honest first reading.**

---

## 7. What is guarded, so the gain cannot be undone quietly

| | |
|---|---|
| `crates/gabbro-syntax/tests/wortschatz.rs` | binds every one of the 221 as a **parameter** and as a **local**, assigns it, reads it back, and requires clean **exactly** for the 204. The `res` column can no longer be a comment beside the truth |
| the same file | pins the reserved **list**, in order, so a re-reservation names itself |
| `instrumente/zaehle-wortschatz.py` | a **third mark**, `MARKE_RESERVIERT = 17`, a ratchet downwards. The other two marks cannot see this size: a later lane could re-reserve word by word and leave 221 / 208 standing |
| `beispiele/70-kernel-namen.gab` | the eight «K3» words and the nine heaviest colliding words, as parameters, locals, fields, a type name, an assignment target and a loop label |
| `beispiele/gift/682, 683, 684` | one probe per part of the residue: a C keyword, the statement-head call form, `result` outside a contract |

---

## 8. What this does NOT settle

* **A named type, a named address space, a loop mark and an `fn`-pointer parameter** are four
  positions where the parser tests `Art::Ident` literally. Two were widened (type, space); the
  loop mark of `retry`/`forever` was **not**, because a mark and the clause words that may
  follow it (`bounded`, `until`, `per_pass`, `progress`, `on_exceeded`, `effects`,
  `invariant`, `leaves`, `decreases`) would then need a second word-set to tell them apart.
  Zero measured demand for a loop label named `count`; when there is one, that is the shape.
* **Inside a contract clause**, `old`, `result`, `forall` and `exists` are still words. A
  quantifier variable named `old` in an `ensures` is unwritable. Zero measured demand.
* **A bare call at a statement head** through a function named like one of the thirteen
  (`next(x);`). `beispiele/gift/683` holds it.
* **The diagnostic for a misplaced clause word got worse**, and that is the real price. Before,
  `effects { pure }` written inside a body met `P002` — *"`effects` is a word of the
  vocabulary"*. Now it meets `P017` — *"assignment or call expected, `{` found"*. Neither
  message is good; the second is less specific. *No corpus file measures this, and the honest
  statement is that it is untested rather than fine.*
