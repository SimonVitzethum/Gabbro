# Completing the grammar for "a person proves only their own logic" — 2026-09-08

**Base:** `master` at `ec71432`, binary `target/debug/gabbro` of 15:33. Every measurement
below was **re-run today**; none is carried over from
[`OFFEN-PRUEFER-UND-GRAMMATIK-2026-09-07.md`](OFFEN-PRUEFER-UND-GRAMMATIK-2026-09-07.md),
though four rows confirm it.

**Corpus** wherever the word appears: `git ls-files 'beispiele/*.gab' | grep -v '/gift/'` — **70 files**.

---

## 0. What "complete" is going to mean, so that it can be checked

`Claude outputs/PLAN.md` states the goal as a sentence about the *person*: everything that is
not their own logic is carried, named as an assumption, or refused with a tag. That sentence
has a **grammar-side precondition nobody has written down**, and this file writes it:

> **A language surface is complete for "only own logic" when, for every form the grammar
> admits:**
> 1. **it means something** — the checker either objects to the form or the form has an
>    effect on what the checker concludes and on what the emitter writes;
> 2. **the proof channel answers for it** — the obligation it creates is carried, assumed by
>    name, or refused with a tag;
> 3. **it cannot silently disappear** — no edit that leaves the checker green may remove an
>    obligation without saying so.

Point 2 is the one `PLAN.md` has been working on for twenty-five runs, and it stands at
**11 refused forms, all tagged**. Points 1 and 3 have never been measured as a class.

> **The grammar is complete at the level of WORDS and open at the level of MEANING.**
> `zaehle-wortschatz.py` counts 221 terminals, 17 reserved and 204 contextual;
> `pruefe-grammatiktafel.py` reports `UNGEDECKT = 0`; every EBNF terminal is implemented and
> every parser-decided word is in the EBNF. **And a form can pass all of that and mean
> nothing.** Four do, measured below.

---

## 1. Forms that MEAN NOTHING — point 1, four measured today

### 1.1 The quantifier domain is decoration — and this is the worst of the four

```bash
sed 's/in slots of Topologie/in threads/' beispiele/18-vorfahren.gab > /tmp/dom-c.gab
./target/debug/gabbro pruefe beispiele/18-vorfahren.gab   # 5 items, 0 errors, 0 hints
./target/debug/gabbro pruefe /tmp/dom-c.gab              # 5 items, 0 errors, 0 hints
./target/debug/gabbro emit  … | md5sum                   # 4220717dff74105e8d12af740e7c7d3c -- BOTH
```

The invariant reads `forall g in slots of Topologie : Topologie.slots[g].bereich <= 255`.
Rewritten to `forall g in threads : …` it **quantifies over threads and indexes slots**, and
the checker says nothing, and the C is byte-identical.

**Why it belongs at the head of this list.** `PLAN.md` §5.2 books nine refused forms under
`quantified-*`, and a refusal is an honest answer. This is not a refusal: it is the *other*
nine domains, the ones that are NOT refused, having no effect either. A person writing an
invariant over the wrong domain is told nothing by the checker and nothing by the proof
channel — the channel translates the body, and the domain that was supposed to bound the
binder never reaches it.

### 1.2 A fractional bound on an integer type — **CLOSED, `M146`**

```bash
printf 'module p::r {\ntype T = u32 in 0.5 .. 1.5;\n}\n' > /tmp/float.gab
./target/debug/gabbro pruefe /tmp/float.gab   # 2 items, 0 errors, 0 hints
```

`Shape.intIn lo hi` is the model's carrier for exactly this declaration (`PLAN.md` §3.1). A
range whose ends are not integers produces a shape whose meaning nobody has stated.

> **Closed 2026-09-08 as `M146`, and the sweep is §5.1 — nineteen positions, not one.**

### 1.3 `divergent … -> never` that returns — **CLOSED, `S009`**

```bash
printf 'module p::d {\ndivergent fn q() -> never\n effects { pure }\n{\n return;\n}\n}\n' > /tmp/never.gab
./target/debug/gabbro pruefe /tmp/never.gab   # 2 items, 0 errors, 1 hints
```

The hint is not about the `return`. `PLAN.md` writes `False` into the `_post` of a `-> never`
routine — so a body that returns makes the unit's duty *unprovable*, and the person is handed
a goal that is false because of a form the checker admitted.

> **Closed 2026-09-08 as `S009`** (§5.2). And this row wrote two findings as one: the
> `cc -Werror` refusal of `__attribute__((const))` on a `void` function is a SECOND
> finding with a different subject and a different fix, and §5.3 measures it apart.

### 1.4 An obligation vanishes on a rename — point 3, and it is silent

```bash
./target/debug/gabbro pflichten beispiele/01-tabelle.gab            # == 15 obligations
sed 's/maintains baum_wohlgeformt/maintains baum_bleibt_baum/' …    # rename the maintains
./target/debug/gabbro pflichten /tmp/mt.gab                         # == 14 obligations
./target/debug/gabbro pruefe  /tmp/mt.gab                           # 18 items, 0 errors, 0 hints
```

`pflichten.rs` matches a `maintains` against an invariant by **name text**. A typo in a
`maintains` removes an obligation and reports nothing; the same statement is then booked as
owed *and* as unowned. This is point 3 of §0, and the only measured instance of it so far.

---

## 2. The named grammar lines that are still missing

Not defects — decisions already taken whose surface was never written. Each is booked with
the source that names it.

| | what is missing | cost, as its own source states it | source |
|---|---|---|---|
| 2.1 | **`by consuming` names no point in time** | *"would need **a grammar line**"* | `gabbro schablonen --gate`, premise `consuming.leermenge` |
| 2.2 | a **single-path descent** over `mappings of` (the cost promise `levels × node length` has no name) | *"kostet ein Terminal"* | `TODO.md` Stufe 3 |
| 2.3 | ~~**`threads` as a quantifier domain**~~ **— designed, measured, NOT built** | *"a language change, not a model change"* → **the change would be a synonym** | `PLAN.md` §9.1, **§15** |
| 2.4 | ~~**the traversal binder has no TYPE** in `slots of`, `descendants of`, `ancestors of`, `elems of`~~ — **CLOSED 2026-09-08**: the first three fell 2026-09-07, the fourth in §5.4 | *"eine Änderung und nicht vier"* | `TODO.md` Stufe 3 |
| 2.5 | **`group ops` / `by ops`** | heading reads *"the design, BEFORE the first grammar line"* | `TODO.md` Stufe 5 |

**2.4 was the one that cost the person proof work, and it is closed** (§5.4) — the first three
domains on 2026-09-07, `elems of` on 2026-09-08. **Its payoff in the corpus was ZERO**, and that
is measured, not assumed: five files write `traverse … over elems of` and none of them is under
`beispiele/`. *A gap can be real, be closed, and move no number — and saying so is the whole
difference between a census and a scoreboard.*

### 2.3 is closed as a QUESTION and not as a grammar line (2026-09-08, `PLAN.md` §15)

The design was written down before the first grammar line, as this file's own §4 order and
`TODO.md` Stufe 5 require — and **it measured its way out of being built.**

* **`kontexte.rs` knows only `entry`.** Seven contexts in the whole corpus, in five files
  (`gabbro kontexte` over the 117 files it accepts). A context is a static entry point; a
  thread is a runtime object. *The census §8.1 refutation stands, and is narrower than it
  reads.*
* **The obvious surface is a synonym.** `slots of Faden` emits `.forallSlots "t" 128 …`, and
  `Body.lean` declares the constructor as `forallSlots (v) (count : Int) (body)` — **a
  quantifier domain in this model IS an integer.** A `threads over T`, or a mark at the table,
  has nowhere to put anything but `T`'s `count`: the same term, the same proposition,
  byte-identical C. **That is this file's §1 in a new place**, and buying six register duties
  with it would be buying them with the same silence.
* **The surface that would mean something needs a semantics Gabbro has not got:** `threads` as
  the LIVE slots, which takes a liveness predicate at the declaration and a second model
  constructor. *A decision only the owner can take, and it was not invented.*

**What was built is the checker half.** `D024` refuses the last form of `threads` that the
checker admitted and that stated nothing — the binder as a plain number
(`forall t in threads : t < N`, measured **0 errors, 0 hints** against `6c835eb`, and
`pflichten --lean` `total 0`). It falls in **zero of the 686 `.gab` files** that were clean
before. **The refusal in `PLAN.md` §9.1 stays, with a measured ground instead of an asserted
one.**

---

## 3. What is measured and NOT in this file's scope

* **`gabbro pflichten --isabelle` over the corpus: `total 84  goals 1  refused 83`** (re-run
  today). The Isabelle channel is not the Lean channel of `PLAN.md`, and its 83 refusals are
  a different census with different classes. Named here so the two `84`/`173` figures are not
  read as one number.
* **`gabbro schablonen --gate`: 6 premises of PROVED templates have no pass** — a proof
  nothing establishes. Ratchet tooth 3. Two of the six are 2.1 above; the rest are Stufe 5.
* **The 11 refused forms of the Lean channel** — they are point 2 of §0 and they are answered.
  A refusal with a tag is a complete answer, not a gap.

---

## 4. The order, and why it is this one

1. **§1.1** — nine domains that decorate. It is the only one of the four whose blast radius is
   the whole invariant language, and the only one where the checker's silence and the proof
   channel's silence are the *same* silence.
2. **§1.4** — an obligation that disappears on a typo. Cheap to close, and it is the sole
   measured instance of point 3; a class with one instance and no guard is a class that grows.
3. **§1.2, §1.3** — two admitted forms with no meaning. Small, and each is one objection.
4. **§2.4** — the binder without a type: the only missing grammar line that the corpus already
   pays for.
5. **§2.1, §2.2, §2.3, §2.5** — grammar lines for decisions already taken, in the order their
   stages give them.

**What this file does not claim.** That the list is closed. Every entry here was found by
deriving the grammar from `parse.rs` and probing forms, not from the corpus — and the census
of 2026-09-07 says why that matters: *"Trap 80 does not only make a corpus flattering, it
makes it BLIND in a specific direction — toward every shape nobody thought to write."* A form
nobody has probed is not a form that means something.

---

## 5. Run 27 — §1.2, §1.3 and the leftover half of §2.4, closed (2026-09-08, later the same day)

**Base:** `master` at `6c835eb` (four merges past `ec71432`), merged into the working branch
before the first measurement was taken. Local, `free -g` beside every number — *31 GB total,
12–17 GB available, 20 cores; `ki-pc-fisch-101` unreachable through the jump host all day, so
the memory was measured and not assumed.*

Two codes, one emitter fix, one binder that stopped being untyped. **Nothing in this section
is carried over from §1–§4: every row was re-run against the merged tree.**

### 5.1 `M146` — the ends of a range are integers, at NINETEEN positions

§1.2 wrote the finding at ONE position and said nothing about the rest. The sweep wrote one
probe per position; every position was silent.

```bash
# each row is one file: `type T = <ty>`, or the same range at that position
./target/debug/gabbro pruefe <probe>.gab
```

| # | position | before | after |
|---|---|---|---|
| 1 | type alias `type T = u32 in 0.5 .. 1.5;` | 0 errors | **2** `M146` |
| 2 | record field | 0 | **2** |
| 3 | slot field | 0 | **2** |
| 4 | `const` | 0 | **2** |
| 5 | `static` | 0 | **2** |
| 6 | `atomic` | 0 | **2** |
| 7 | parameter | 0 | **2** |
| 8 | answer (`-> u32 in …`) | 0 | **2** |
| 9 | local (`let x : …`) | 0 | **2** |
| 10 | array element | 0 | **2** |
| 11 | pointer target | 0 | **2** |
| 12 | variant payload | 0 | **2** |
| 13 | function pointer, parameter **and** result | 0 | **4** |
| 14 | `accumulates` | 0 | **2** |
| 15 | `axiom` parameter | 0 | **2** |
| 16 | `axiom` answer | 0 | **2** |
| 17 | `format` field | 0 | **2** |
| 18 | `narrow` on an INTEGER place | 0 | **2** |
| 19 | table constant | 0 | **2** |
| — | **`f64 in 0.5 .. 1.5`** — the control | 0 | **0** |

**Nineteen of nineteen, and two per row because a range has two ends.** *A measurement that
stops at the first position that already objects answers "does one object", and the question
was "which".*

**What the silence cost, in one differential.** Three files, `type T = <ty>` and a body
`return 9;`:

```bash
u32                  ->  3 items, 0 errors    (9 fits u32)
u32 in 0 .. 1        ->  3 items, 1 errors    (9 leaves the range)
u32 in 0.5 .. 1.5    ->  3 items, 0 errors    <- the written bound bought NOTHING
```

`umgebung::intbereich` evaluates each end with `auswerten`; a float literal gives `None`; and
the arm for an end that does not stand fast is `IntBereich::voll`. **The bound is not rounded,
it is DROPPED** — the range does not get narrower, so the declaration lowers to the full width
of the word and `shape_of_typ` hands the model `Shape.intIn 0 4294967295`.

> **And the corpus found the over-reach that the design did not.** The first build read the
> range without its place and refused `beispiele/26-gleitkomma.gab`:42 —
> `narrow x to 0.0 .. 1.0` at an `f64` parameter, in the file that exists to show
> `narrow … else` as the NaN path. *W10 in the expensive direction: a refusal with the sign
> that rejects a correct program.* `narrowstmt` hangs a range on a PLACE and not on a type,
> so the rule now resolves the place and says nothing where it is not an integer. **This is
> the only file in the tree either new code touched, and it was the rule's fault, not the
> file's.**

Reservation, and it is the whole of it: **a float LITERAL, not "an end that does not
evaluate"**. `u32 in 0 .. N` with an unresolvable `N` is silently widened in exactly the same
way and is **not** refused — that is a second finding with a second measurement, and refusing
it here would need an environment this rule does not have.

### 5.2 `S009` — a `-> never` routine that comes back

Five bodies under `divergent fn q() -> never effects { diverges }`:

| body | before | after |
|---|---|---|
| `{ return; }` | 0 errors, 0 hints | **1** `S009` |
| `{ return 1; }` — and `never` has no value | 0, 0 | **1** |
| `{ }` — falls off its end | 0, 0 | **1** |
| `{ if b { return; } forever … }` | 0, 0 | **1** |
| `{ forever … }` — the one that is correct | 0, 0 | **0** |

**Why it is worse than a wrong answer.** `PLAN.md` §3.1 writes `False` into the `_post` of a
`-> never` routine. A body that returns therefore hands the person a goal that is *false
because of a form the checker admitted* — not hard, not open: unprovable, and unprovable for a
reason no line of their program states. **That is the exact opposite of the sentence at the
head of `PLAN.md`.**

`S006` two entries above asks the same question of a WATCHDOG — *"`on_exceeded x` names a
function that returns"* — and answers it from the callee's DECLARATION. **This is the half
that was missing: a declaration nobody holds against its body is a promise, not a fact.**

### 5.3 The `pure`-on-`void` half, measured APART — an EMITTER defect, not this one

§1.3 named `cc -Werror` on two counts and did not separate them. They are two findings:

```bash
./target/debug/gabbro emit <probe>.gab > p.c
cc -std=c11 -Wall -Wextra -Werror -c p.c -o /dev/null
```

| # | source | emitted C | `cc -Werror` | after |
|---|---|---|---|---|
| A | `-> never`, body **returns**, `effects { pure }` | `_Noreturn void q(void) __attribute__((const))` + `return;` | *'noreturn' function does return* **and** *'const' attribute on a function returning 'void'* | `S009` refuses the source |
| B | `-> never`, body does **not** return, `effects { pure }` | same attribute, no `return` | *'const' attribute on a function returning 'void'* | **emitter fixed** |
| B′ | `-> never`, body does not return, `effects { reads G }` | `__attribute__((pure))` on `void` | *'pure' attribute on a function returning 'void'* | **emitter fixed** |
| — | control: plain `fn q() effects { pure }`, no result clause | `static void q(void)` — **no attribute** | silent | unchanged |

**Row B is the proof that they are two findings**: it fires with no `return` anywhere, so it
is not a symptom of §1.3's `return`. The cause is one line of `emit.rs::wirkungsattribut` —
*"a function with no result has nothing to summarise"* — reading `f.ergebnis.is_none()`, the
WRITTEN result. `-> never` is a written result that lowers to `_Noreturn void`. **A guard that
asked the source a question about the C.** The control row is that same line working as
intended, which is why the fix is a condition and not a deletion.

### 5.4 §2.4's fourth domain — the `elems of` binder carries its array's bound

2026-09-07 gave the binder `index into T` for the three domains whose counter is a slot index
(`Sicht::binder_tabelle`). `elems of` stayed `Typ::Unbekannt`, **and `Unbekannt` is not
silence but an acquittal**: `M103` asks the index for its type first and says nothing when
there is none.

```bash
# type R = { buf : [u32; 8], n : u32, };
# traverse i over elems of r.buf by unvisited touches writes r.buf { … }
r.buf[i]              ->  0 errors      before AND after   (the loop that is right)
r.buf[i + 1000000]    ->  0 errors  ->  1 errors [M103]    (measured both ways)
```

The before-column is measured and not remembered: the arm was switched off, the checker
rebuilt, the probe re-run, and the source restored **byte-identically** (`diff` against a copy
taken before).

The length was never computed a second time. `Sicht::domaenenschranke` has read
`Typ::Feld { laenge }` for this domain since 2026-08-19 — **for the COST pass** — and nobody
ever turned it into a type. *One declaration, one reader, as at `indextyp`.*

> **And the folder's own prose said the binder was an element.** `binder_tabelle`'s doc reads
> *"`queue` and `elems of` bind an ELEMENT, not an index — a different type entirely"*. **Three
> channels say otherwise, and they are the ones that run:** `domaene::Binderart` books it as
> `Feldindex`, `emit.rs` writes `for (uint64_t i = 0; i < sizeof(f)/sizeof(f[0]); i++)`, and
> `lean.rs::domain_of` calls it *"the index domain of the array's pseudo-table … the binder is
> the index, as every use in the corpus reads it"*. *A comment that contradicts the emitter is
> the `W16` shape in prose: it reads like a decision and it is a stale one.*

**What it did to the corpus `sorry` count: NOTHING, and that is the measurement.**

```bash
git ls-files '*.gab' | xargs grep -l "over elems of"      # 5 files, NONE under beispiele/
```

`messung/fragmente/F06.gab`, `messung/k3-fragmente/K08-test-func.gab`,
`messung/netz/udp-echo.gab`, `messung/proben/probe-elems.gab`,
`messung/proben/probe-ipc-fastpath-durchgestochen.gab` — and all five give **byte-identical
verdicts before and after**. §2.4 was booked as *"the one item of §2 that the proof channel
already pays for"*; that is true of `slots of`, which was closed yesterday and does carry
corpus sites. **For `elems of` the corpus has no site, so the payoff is zero and could not have
been anything else.** *A number that has to be zero is worth measuring exactly once, so that
nobody measures it again hoping.*

### 5.5 The corpus, and the one file either code touched

```bash
git ls-files '*.gab' | while read f; do ./target/debug/gabbro pruefe "$f"; done
```

**686 files, and `M146`/`S009` fall in ZERO of them.** No program was leaning on either
silence. The one file that did fall — `beispiele/26-gleitkomma.gab` — fell against the FIRST
build of `M146` and is unchanged: *the objection was fixed, not the program.*

### 5.6 The Lean half, and why it did not move

Neither code is a proof-channel refusal: a file carrying `M146` or `S009` never reaches
`lean.rs`, because the checker errors out first. No `LeanReason` variant was added, no tag
changed, no form moved between verdicts.

```bash
python3 instrumente/pruefe-deckung.py     # exit 0 -- 42 reasons, 45 forms, 32 carried,
                                          # 32 discharge lemmas, UNCOVERED = 0
cd programmlogik && ~/.elan/bin/lake build   # green, Coverage.lean with no `sorry`
```

```text
'Gabbro.Coverage.the_sentence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Coverage.carried_discharges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Coverage.classify_total' depends on axioms: [propext]
```

### 5.7 Measured — before and after, with `free -g` beside them

| | before (merged base `6c835eb`) | after |
|---|---|---|
| `free -g` available / cores | 16 GB / 20 | 12 GB / 20 |
| `cargo test --no-fail-fast` | 31 collections, **426** passed, 0 failed | 31, **429** passed, 0 failed |
| Lean modules · errors · `sorry` | 192 · 0 · **25** | 192 · 0 · **25** |
| Lean seconds (P=4, sum over files) | 409 | **536** (12 GB available, not 17) |
| `.gab` files in the tree | 686 | 686 (+2 poison, counted after) |
| `pruefe-zahlen.py` findings | **5** | **4** |
| `pruefe-todo.py` | RED (1 finding) | **GREEN** |
| `pruefe-englisch.py` | RED | RED, unchanged (7879 German comment lines in the checker, 1069 in the instruments — both as before) |
| `pruefe-kennungen/-gruende/-vergabe/-saetze/-syntax/-grammatiktafel/-sondendeckung/-deckung/-klauseln` | green | **green** |
| mutation anchors sitting | 380 of 397 booked | **381 of 398** |

**The `pruefe-zahlen.py` baseline was measured twice and the first reading was wrong.** The
first run gave ELEVEN findings, five of them of the shape *"H … steht als 1, der Lauf sagt
10"*; a second, taken on a stashed-clean tree with the binary rebuilt from it, gives **five**,
and the run is deterministic across repeats. *A guardian whose entries invoke the built
compiler measures the tree AND the binary, and a baseline taken beside a build measures a
mixture — the class `CLAUDE.md` books under "zwei Werkzeuge in einem Baum".* **The five-finding
reading is the one this table uses**, and the four counters that moved were RE-MEASURED and
not added to:

| counter | booked | re-measured | why it moved |
|---|---:|---:|---|
| `messung/PASSREGISTER.md` sentences in the register | 98 | **100** | two new `Satz` entries |
| `TODO.md` refusal codes | 282 | **284** | `M146`, `S009` |
| `README.md` diagnostics | 280 | **284** | the same two — the front page was two behind before this run |
| `TODO.md` sentences over the passes | 98 | **100** | the same two |
| `TODO.md` refusal texts with no legible ground | 103 | **105** | `pruefe-gruende.py`'s candidate list, not a verdict |
| `TODO.md` line continuations | 3426 | **3499** | this run's own text |
| `TODO.md` / `README.md` mutation anchors | 397 of 397 | **381 of 398** | `binder-ohne-typ` had to MOVE WITH the code, and `elems-binder-ohne-schranke` came beside it; *the seventeen that grip nothing are all in `lean.rs` and stood so before this run* |
| `DONE.md` / `README.md` poison probes | 459 | **461** | probes 690 and 691 |

> **`pruefe-klauseln.py` said `rueckgabe` had RISEN before anyone thought of it.** The result
> type of an `axiom` was booked TOT — *"ungelesen"* — and `M146` reads it, because it is one of
> the nineteen positions. *The entry is deleted, which is what a ratchet that clamps in both
> directions is for.* The line stood there because `jeder_typausdruck_im_item` does not visit
> an `axiom` at all; that walk feeds `bindung.rs` and `namen.rs`, so **widening it is a change
> to THEIR population and was not made here** — `M146` walks the three item kinds it misses
> itself, and says so at the site.
