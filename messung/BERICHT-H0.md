# `H = 0` — the four fragments without a Durchstich

**Running report. Written while the work runs, committed with every finding** — eight lanes
died mid-run this week and every one lost its report, not its code.

`H` counts fragments **without a Durchstich**: without the path *emit → compile → RUN →
compare against a hand-written expected value*. Six go it (`F2 F4 F6 F7 F8 F10`), four do
not. The order follows the cost the owner booked in `dokumente/PLAN-HARDWARE.md` §49 `B6`:
**F09 → F01 → F05 → F03**, with a mandatory stop after `F05`.

**And the tool's own caveat stands, because it is right:** *the ten fragments are chosen for
their DIFFICULTY; `H = 0` over them stays trap 80 as long as no corpus stands beside them
that nobody looked at while building.* `H = 0` improves the tree. It is not a statement about
the language.

---

## The baseline, measured

At `3b17d9a`, with the binary built on `ki-pc-fisch-101` (`gabbro-h0`) and fetched back:

| fragment | `pruefe` | `emit` | codes |
|---|---|---|---|
| F01 | 3 errors | refuses | `M140` ×2, `N029` |
| F02 | 0 | ok | — |
| F03 | 27 errors | refuses | `N040` ×9, `M140` ×8, `N035` ×5, `M124` ×3, `M101`, `H011`, `E009` |
| F04 | 0 | ok | — |
| F05 | 4 errors | refuses | `N046` ×2, `M134`, `N041` |
| F06 | 0 | ok | — |
| F07 | 0 | ok | — |
| F08 | 0 | ok | — |
| F09 | 1 error | refuses | `K001` |
| F10 | 0 | ok | — |

Machine: local `free -g` reported 31 GB total, 14 GB available, 20 cores; every `cargo`
step ran on `ki-pc-fisch-101` in `gabbro-h0` per `CLAUDE.md`.

---

## F09 — the MMU page tables

### What the plan's row said, and what the run says

`§49 B6` lists for F09: *1 error — `K001`* and, from the emitter, *`device … at normal`*.
**The emitter says three things, not one.** `gabbro emit messung/fragmente/F09.gab` at
`3b17d9a`:

1. `[C001] :61:1` — `device … at normal`
2. `[C001] :70:1` — `walk … levels` that is not a number
3. `[C001] :81:5` — `mappings of`, no lowering

That is the first finding of this lane, and it is a finding about the **plan**, not about the
tree: F09's row understates the fragment by two refusals, and one of the two is of the same
family as F03's «B10».

### What was wrong, and who was at fault

**Three defects, and they are of three different kinds.** That matters more than the count:
one is the emitter's, one is the fragment's construct choice, one is a promise the language
decided against two weeks ago.

#### 1. `walk … levels EBENEN` — **the EMITTER was wrong**, and it is the third site of one named class

`const EBENEN : u32 = 4; walk Seitenabstieg levels EBENEN { node : [Pte; EINTRAEGE], … }`
drew

    no lowering: `walk … levels` that is not a number -- the descent's step count IS the
    declaration's one statement about the run, and it cannot be guessed

over a declaration that says `4`. **The refusal's own reason did not apply.** Nothing is
guessed: `umgebung.rs` folds every `const` of the unit before the emitter starts, and
`Namen::konstwert` carries the answer. The field's own doc comment already said what went
wrong, in the present tense, about this exact shape:

> *Je `const` sein ausgerechneter Wert -- **von `umgebung.rs` und nicht hier**. … der
> Erzeuger hatte daneben seinen eigenen, schwaecheren Auswerter (`konst_zahl`) und weigerte
> sich. Zwei Register ueber derselben Sache, und das schwaechere hat entschieden* (W7).

Two callers had already been repaired the same way — the `static` array length
(`emit.rs:7380`) and `feldlaenge_von` (`emit.rs:8615`). **`walk_` was the third, for both
`levels` and the `node` length**, and each of the three carried its own copy of the same
four-line `.or_else`. The repair is one shared reader, `konst_oder_name`, and the three
call sites now go through it — *one search path, not three registers* (W7).

- fix: `crates/gabbro-check/src/emit.rs` — `fn konst_oder_name`, called from `walk_`,
  `static_feld` and `feldlaenge_von`
- counter-direction: `beispiele/gift/667-walk-levels-is-an-expression.gab`, `-- erwartet: C001`.
  `levels EBENEN + 1` is one step past the constant table and still refuses **by name**; the
  checker stays silent at `4 items, 0 errors, 0 hints`. *The fence stands at the bare name,
  and the probe is the fence-post — the day `umgebung.rs` folds use-site expressions, this
  probe goes red and asks to be withdrawn.*

#### 2. `device … at normal` — **the FRAGMENT was wrong**, and the emitter said so

The excerpt puts the nine PTE feature bits into

    device Seitentabelle(basis : Pa) at normal { reg EINTRAG : u64 @0x0 class rw fields { … } }

and the emitter answers *"an access into the ordinary space is not a device access, and what
a `device` block would mean there is not decided"*. **That refusal is right.** A page-table
entry lies in ordinary memory; `format` is the construct that names the bits of an ordinary
word, and the same file already carried a `format Pte` **for the same word**. Two registers
over one thing, and the weaker one had no lowering at all.

A second refusal stood behind the same line and was never reached: `down : roh when
EINTRAG.PS == 0` names a device register, while `walk` reads its predicates as `it.<field>`
of the node `format` (`leser_oder_absage`, the rule `beispiele/gift/641` was built for).
**That form could never have lowered**, not even with the device in `mmio` space.

Repair: the nine bits move into `format Pte`, `A`/`D` stay `reserved` because the excerpt's
own comment says the hardware writes them and a `reserved` field gets no writer, and
`down`/`leaf` read `it.PS`.

#### 3. `costs <= 4096 ops` over `traverse … over mappings of` — **the FRAGMENT was wrong, and the language had already said so**

The checker reported `[K001] promises <= 4096 ops, the body costs 137438953472` — seven
orders of magnitude. `SPRACHE.md` §5.4 settles it in as many words:

> *"a RUN-TIME traversal over `mappings of` can therefore hold no cost promise. That is
> true, and the other reading would have been a promise nobody keeps."*

**The repair does not write the bigger number down.** It puts each of the two statements
where it belongs: the statement about the SET becomes a `walk` invariant over
`mappings of Self` — the position the eighth domain was built for, and the only one in which
it lowers (as a named `W` obligation, not a run-time computation) — and the statement about
ONE entry becomes `rechte_pruefen`, with a bound the cost pass computes and the line copies
(`costs <= 5 ops`; the first draft said 4 and the pass said 5).

### What is NOT repaired, and it is «B10»-shaped

**`traverse … over mappings of` still has no lowering.** It needs a generated recursive
descent *and* a named resolver from frame to readable node. The `walk` lowering takes that
resolver as a C parameter, `bool (*knoten_zu)(uint64_t, const T_knoten **)`, precisely
because no clause names it — `walk_`'s own doc says *"Sie steht als Parameter da und nicht
als angenommener fremder Rumpf"*. **In Gabbro there is no place to write it down.** That is a
construct question and it belongs to the owner, not to this corpus.

### The Durchstich

`lauf "fragment9"` in `instrumente/pruefe-emission.sh`.

| | |
|---|---|
| **expected** | `1 2236416 0 1 0 0` |
| `1` | the descent finds the leaf: root[7] descends, child[9] is a leaf |
| `2236416` | `Pte_roh` of the leaf — `0x222 * 4096`, the `embeds … scale` arithmetic |
| `0` | `rechte_pruefen` at a leaf with `RW` and without `NX`: W^X violated |
| `1` | the same at the neighbouring leaf with `NX`: W^X held |
| `0` | the resolver does not know root[8]'s frame: no descent |
| `0` | index 512 at a node length of 512: the bound holds |
| **poison** | `s/return (bool)(Pte_PS(it));/return (bool)(!Pte_PS(it));/` — it inverts `leaf`. Root[7] (`PS == 0`) then IS the leaf, the descent stops at level 0, and `Pte_roh` yields `1118208` instead of `2236416`. Measured: `1 1118208 1 1 1 0` |
| **certificate** | `0 assumptions …, 1 templates (0 of them UNPROVED), 5 direct forms, 0 foreign bodies …` |

**The poison is the load-bearing part**, and here it carries a specific claim: without it the
expected `2236416` would only prove the program is not constant. With it, the number is shown
to come **out of the descent** and not out of the first entry.

**And the resolver stands in the hand-written driver**, which is the honest place for it:
`walk` says THAT a descent happens; no clause says how a physical frame becomes a readable
node. That is the same gap that keeps `mappings of` from lowering, seen from the other side.

### The guard's frozen-excerpt check had to change, and that is said out loud

F02, F04, F06 and F07 assert with `verlorene_zeilen` that **no** line of the frozen excerpt
is missing from the working copy — *adding allowed, dropping not*. F09 cannot pass that: the
repair removes the `device` block, the two predicate lines and the `traverse`. So the F09
block asserts the **sharper** thing instead: *every missing line must be one of the booked
ones.* The booked list stands in the guard, one line each, and an unbooked missing line falls
exactly as it does for the others. A speech test (removing `const EINTRAEGE: u32 = 512;`)
proves the comparison can still go red.

> *A shell detail worth keeping:* the first version used `grep -Fxq "$z"`, and every second
> booked line starts with `--` (Gabbro's comment marker), which `grep` read as an option.
> **A guard that trips over its own subject matter reports every line as unbooked.** `--`
> before the pattern is the fix.

### H before and after

    before   6 von 10 sind DURCHGESTOCHEN -- F02, F04, F06, F07, F08, F10          H = 4
    after    7 von 10 sind DURCHGESTOCHEN -- F02, F04, F06, F07, F08, F09, F10     H = 3

Read with `./instrumente/zaehle-fragmente.py --je-datei` on `ki-pc-fisch-101`, which runs
`pruefe-emission.sh --absenkung` and takes a verdict per fragment rather than a line of
shell. `cargo test --offline --no-fail-fast`: **400 passed, 0 failed**, unchanged.
`zaehle-wortschatz.py`: **221 / 208 / 333**, unchanged — the repair added no word.

**Fifteen numbers in the tree moved with it**, and `pruefe-zahlen.py` named every one:
`H` in four documents, the fragment corpus counts, the `walk` declaration count (`gift/667`),
the traversal-body count (F9 lost its `traverse`), the ceremony sites, the exit sites of
`pruefe-emission.sh`, the line-continuation count, the file count of the revocation guard,
and the poison-probe count in `README.md` and `DONE.md`. *Every one re-measured from the
command, none carried forward.*

---

## F01 — the capability space

### All three refusals were right, and the excerpt contradicts itself

`gabbro emit messung/fragmente/F01.gab` printed **no `C001` at all** at `3b17d9a` — the
emitter had nothing against this file, which is more than the plan's row says. What stood
between F01 and its C were three checker errors, and each one is the fragment's.

#### 1 + 2. Two `M140` — a record handed to a parameter that declares a number

    :307:50  argument `d` requires `…::DmaObj`,   the value has `…::DmaRef`
    :308:52  argument `r` requires `…::ReplyObj`, the value has `…::ReplyRef`

**Both sides stand in the FROZEN excerpt, forty lines apart, and disagree.** At its head:

    tagged type ObjectKind = { Memory(Region), … Reply(ReplyRef), … Dma(DmaRef), … };

and at its foot, *nachgetragen 2026-08-15* — an amendment, not the 2026-08-14 core:

    extern fn free_region(a : ptr<normal, rw> Allok, m : MemObj) …;
    extern fn push_dma(rf : ptr<normal, rw> Finalized, d : DmaObj) …;
    extern fn push_reply(rf : ptr<normal, rw> Finalized, r : ReplyObj) …;

`Allok`, `MemObj`, `DmaObj` and `ReplyObj` are **declared nowhere in the excerpt**. The
completion invented all four as `opaque type … = u64`, because an unexplained handle cannot
plausibly be anything else. *The completion is not what is wrong; the amended line is.*

**And the finding is bigger than the two errors, because `M140` sees only two of three.**
The same confusion sits at `Memory(m) => { free_region(a, m); }` — `m : Region` at a
parameter declared `MemObj` — and **the rule is silent there**, because both are scalar names
over `u64` and `gestalt` looks through a scalar alias by construction. The rule says that
boundary out loud (*"taking a scalar alias nominally would be a language change, not a hole
being closed"*), so this is a booked blind spot and not a bug. It is still worth writing
down: *the visible half of a defect was two thirds of it.*

Repair: three words in the frozen lines (`Region`, `DmaRef`, `ReplyRef`, plus
`PhysAllocator` for `Allok`), which makes the excerpt agree **with itself** rather than
adding anything to it. The four invented handles are retracted with it — *four dead handles
beside the four real ones are exactly the confusion that produced the defect.*

#### 3. `N029` — an unpaid bill

`delete_leaf` declares `or Fehler` and its body can `return Fehler::Buchfuehrung;`. Its one
caller, inside `traverse … by consuming`, called it as a bare statement and dropped the
reason on the floor. The repair is the form the language has and only that form:

    let ok = delete_leaf(c, o, a, rf, victim) else (e) { return e; }

plus `or Fehler` on `revoke` — an ADDED line, no excerpt line touched. The cost bound then
rises from `16452480` to **`16612992`**: the cost pass computes it, the line copies it.

> **F01's own header refused this in advance**, and correctly: it costs frozen lines. What
> changed is not the arithmetic but the decision — the owner booked `H = 0`, and F09 had
> already set the shape for paying it: *every changed or missing line is booked, one by one,
> with its reason.* Five lines, five reasons, in the file's head and in the guard.

### And behind the paid bill lay TWO emitter holes nobody could see

Both were then measured on a **five-item file with no fragment in it**
(`messung/proben/probe-fehlerkanal-ohne-ergebnis.gab`), which `gabbro pruefe` accepts with
`0 errors, 0 hints`:

1. **The call had no lowering.** `let … else` pushed `&<binding>` for every callee that does
   not return a *ghost*, then asked `wert_ctyp` for the type of a result the declaration does
   not have, and refused: *"`let … else` whose call has no resolvable type"*. **The
   declaration side had always known better** — an `or R` function is `bool` in C and gets a
   `*_wert` parameter only when it has a result. *The two halves of one lowering disagreed
   about the same signature.* The answer stood two fields up in `Signatur` and needed no new
   rule: *"Does it return a ghost? Then `let x = f(…)` loses its binding, **not its call**."*
   A missing result is the same case.

2. **The success return was never written.** A Gabbro function without a result carries no
   closing `return`; C's `void` return is implicit. An `or R` function is `bool`, and there
   the same body **ran off the end of a non-void function** — the caller reads an
   indeterminate value out of `if (!f(...))` and branches on it. `cc -Wall -Wextra -Werror`
   compiled it at `-O0` **and** at `-O2`: `-Wreturn-type` does not reach a `static` function
   nothing has called yet.

**Why nobody had seen either:** the corpus carried `or R` *exclusively at `extern fn`* —
foreign bodies this emitter never sees — until `messung/netz/udp-echo.gab`, and that one
returns a value on every path, so the explicit `return <x>;` arm wrote the `return true;` for
it. A function with an error channel and no result had no lowering to fall out of, because
hole 1 refused every call to it one door earlier. ***A defect behind a refusal is invisible
for exactly as long as the refusal stands.***

> **And hole 2 has no reader at `cc` at all.** Its only witness is a RUN — which is the
> sharpest argument for the metric this whole lane serves: `H` counts Durchstiche and not
> compilations, and this is what the difference buys.

The probe for it is a **clean** file and not a poison, deliberately. Both refusals *were* the
bug; the counter-direction that remains (`let … else` over a callee with no `or <reason>`)
belongs to `N028`, and the checker says it before the emitter is reached — a poison on it
would land in the ten already booked as *verdeckt* and raise a mark that is meant to fall.
Stage 9 of `pruefe-emission.sh` is the reader instead: it emits the probe and hands its C to
`cc -Werror` at every run, and `MARKE_EMIT_M` falls if the refusal comes back.

### The Durchstich

`lauf "fragment1"`. Four slots, one tree, `revoke` from the root:

    0 (root) -> 1 -> 3        post-order: 3, 1, 2
             -> 2

| | |
|---|---|
| **expected** | `1 1 0 0 0 1 0 0 1 1 0 65536 4096 0 1` |
| `1` | `revoke` reports success |
| `1` | slot 0 is STILL used — the root is walked *through*, never visited |
| `0 0 0` | slots 1, 2, 3 are released |
| `1` | object 12 stood at 2 and stands at 1: no finaliser |
| `0 0` | objects 10 and 11 stood at 1 and are released |
| `1 1 0` | `push_dma` once, `push_reply` once, `free_region` **not** — object 12 never reached zero |
| `65536 4096` | the fields of the `DmaRef` that travelled through the `match`. **This is the number the `M140` repair hangs on**: with `DmaObj` there was a `u64` here and the record would not have arrived |
| `0 1` | the second call fails and `Fehler::Buchfuehrung` (= 1) arrives — the reason crosses two levels |
| **poison** | `s/o->slots\[obj\].refcount >= 1/o->slots[obj].refcount >= 0/` — it opens the bookkeeping bound downwards. Measured: `… 1 0` |
| **certificate** | `0 assumptions …, 4 templates (1 of them UNPROVED), 13 direct forms, 5 foreign bodies …` |

**The poison is surgical, and that is the point.** The first call is unchanged by it — all
three refcounts are above zero — so only the second differs. It therefore hits exactly the
chain this fragment rebuilt: `narrow … else` → error channel → `let … else` → propagation to
the caller. *Without it the fifteen numbers would only prove the program is not constant;
with it, the last two prove the reason travelled.*

### What is NOT repaired, and it was found by a solver rather than by a pass

`cdt_wohlgeformt` quantifies over `slots of c` — **the whole table, not the used slots** — so
one free slot falsifies it, and `release_slot` leaves exactly one behind. Sharper still:
`unlink`'s `ensures c.slots[s].parent == None` contradicts its own
`maintains cdt_wohlgeformt` **four lines away in one signature**. A blind second encoding
confirmed both and measured the obvious repair: a `used` guard makes the invariant
satisfiable and **leaves `L05` refuted**, because `unlink` requires `used` and does not clear
it. Booked as `dokumente/OFFEN.md` O4.

> **No Gabbro pass sees any of it, and the Durchstich does not either.** A Durchstich measures
> what the C computes, not what the promise claims. *The two sentences stand side by side so
> that nobody reads the first as the second.*

### H before and after

    before   7 von 10 sind DURCHGESTOCHEN                                       H = 3
    after    8 von 10 sind DURCHGESTOCHEN -- F01 F02 F04 F06 F07 F08 F09 F10    H = 2

`cargo test --offline --no-fail-fast`: **400 passed, 0 failed**. `pruefe-emission.sh`:
**ALL PASS — 27 durchgestochen, 124 von 124 uebersetzen**. `zaehle-wortschatz.py`:
**221 / 208 / 333**, unchanged. `zaehle-gifttreffer.py`: back at its master value of **9**
*verdeckt* — a first draft of the probe as a poison would have made it 10, and that mark is
meant to fall.

---

## F05 — the virtio-blk service

### Three of the excerpt's names belong to C, and none of them is visible at `cc`

| name | what C says | what the excerpt means |
|---|---|---|
| `exit` | `void(int)` | *this function never returns* — and all eight call sites pass no argument |
| `signal` | `__sighandler_t(int, __sighandler_t)` | a capability notification. **C's type has no Gabbro form at all**, so no signature could rescue it |
| `recv` | `ssize_t(int, void *, size_t, int)` | an seL4-style receive at an endpoint |

**All three refusals are right, and the decisive half is why the checker has to hold them:**

> The generated unit includes no POSIX header, so `cc` never sees C's declaration and has
> nothing to complain about. **The refusal that should come from the foreign compiler cannot
> come from it at all** — and the linker then finds the real symbol behind whatever this unit
> declared.

That is a *silent* wrong binding, not a compile error. Repair: rename, which is exactly what
`N046`'s own note asks for — *"rename it, and reach the C function through one that CAN be
written"*. `exit` → `dienst_abbruch`, `signal` → `benachrichtige`, `recv` → `empfange`.
Twelve frozen lines move, each booked in the guard.

`M134` (`m.op` on a `u64`) falls out of the same repair: `recv` had been *completed* as
`-> u64`, and the excerpt reads a field on it. `empfange` now returns a record `Nachricht`
carrying **one** field, because the excerpt reads one and otherwise only passes `m` on.

### The header claimed the completion was finished, and it was five names short

`decode_op`, `request_flush`, `serve_rw`, `serve_scan`, `bump_served` — all called by the
frozen service body, all declared nowhere in the tree. **The emitter said so at exactly one
of the five**, at `match decode_op(m.op)`, because a `match` needs the scrutinee's type. *The
other four the body called into nothing, and no pass said a word*; `E009` only reports that
`run`'s effect hull is therefore a LOWER bound.

> **Four checker errors were never this file's whole error surface.** That is worth keeping
> as a sentence about the metric and not only about the file: an undeclared callee is caught
> by the emitter, and only where the emitter happens to need its type.

### The checker finding, and it outranks the Durchstich

`N046` compares an `extern fn`'s lowered signature against the measured table, and
`absenkung_der_signatur` read `f.ergebnis` and `f.parameter` — **never `f.fehler`**. An
`or R` changes the C signature: the function becomes `bool`, the result leaves through
`*_wert`, the reason through `*_grund`.

Measured through the **unchanged** checker on a four-item file with no fragment in it:

    extern fn abs(a : i32) -> i32 or R effects { pure } costs <= 1 ops;

    gabbro pruefe  ->  4 items, 0 errors, 0 hints
    gabbro emit    ->  exit 0, and the unit carries
                       int32_t abs(int32_t a);        /* ONE parameter */
                       if (!abs(x, &w, &e)) { … }     /* THREE arguments */

`int32_t(int32_t)` is exactly the row the table holds for `abs`, **so `N046` passed** — and
the unit it passed carries a prototype called with the wrong arity. `cc` catches that one,
which is precisely what the rule exists to prevent: its own doc says *"at a name C already
owns the answer has to be exact, so an undecided comparison refuses"*. **Here it was not
undecided; it was wrong.**

The repair builds the spelling rather than refusing, because it can: the result pointer is
the same `ctyp_primitiv`, and a `reason` lowers to a C enum under its own name. `recv`'s note
now reads `bool(uint64_t,uint64_t *,Aufbau *)` against `ssize_t(int, void *, size_t, int)` —
true, where before it named a lowering nobody writes. *And it refuses the whole family, which
is the right answer and not a side effect: an error channel rewrites the ABI, so no C library
function is reachable through one.*

### The Durchstich

`lauf "fragment5"`. The driver pushes six messages — `Info Read Write Flush Scan Stop` — and
every foreign body appends a letter to a trace, so the expected value is a **fingerprint of
the whole dispatch** rather than a tally:

    q  request_flush    p  reply4    1/2  serve_rw with `m.op`    B  bump_served    S  serve_scan

| | |
|---|---|
| **expected** | `qp12qBpSp 1 0 3 2 2 1 1 4711 31 512 77 0` |
| `qp12qBpSp` | Info(q,p) · Read(1) · Write(2) · Flush(q,B,p) · Scan(S) · Stop(p) |
| `1 0` | `benachrichtige` exactly once, with `0` — no setup step failed |
| `3 2 2 1 1` | reply4, request_flush, serve_rw, serve_scan, bump_served |
| `4711` | the capacity `serve_rw` sees — carried over from the `Info` pass |
| `31` | the pool `bump_served` receives: `pool_new(map_window(DMA))` |
| `512 77 0` | the last argument of the three replies. **`77` is `bump_served`'s return value arriving inside `reply4`** |
| **poison** | `s/reply4(EP, Status_Ok, 0, 0, bump_served(pool));/reply4(EP, Status_Ok, 0, 0, 0);/` — the C still compiles and the loop still runs to `Stop`; only the value flow is gone. Measured: `qp12qpSp 1 0 3 2 2 1 0 4711 0 512 0 0` |
| **certificate** | `1 assumptions (0 NOT FALSIFIABLE, 1 UNCOVERED), 1 templates (0 UNPROVED), 10 direct forms, 15 foreign bodies …` |

**`1` and `2` are `m.op`** — the number the `M134` repair hangs on. With `recv` completed as
`-> u64` a one-field record could not have travelled at all.

### H before and after

    before   8 von 10 sind DURCHGESTOCHEN                                          H = 2
    after    9 von 10 -- F01 F02 F04 F05 F06 F07 F08 F09 F10                       H = 1

`cargo test --offline --no-fail-fast`: **400 passed, 0 failed**. `pruefe-emission.sh`:
**ALL PASS — 28 durchgestochen, 125 von 125 uebersetzen**. `zaehle-wortschatz.py`:
**221 / 208 / 333**, unchanged across all three fragments.

---

# The stop after F05

**Instructed, and it is where the question stands.** Only `F03` is left, and its 27 errors
over seven codes are not the reason to stop — *«B10» is*: `traverse` yields no value and
knows no `break`, so `by consuming` over a `queue` drains the whole queue, which is a
different program. Nine `N040` on top of that means nine names stand nowhere.

**What this lane can say about the price, having now paid three of the four:**

* Each of `F09`, `F01` and `F05` cost roughly what the plan booked, and in each one the
  *repair* was the smaller half. The larger half was finding out **which side was wrong** —
  and in all three cases it was the fragment, never the refusal.
* **Every one of the three carried at least one checker or emitter defect behind the
  fragment's own error**, and none of those would have been found by looking at the checker:
  `walk … levels` over a `const` name, `let … else` over a result-less `or R` plus its
  missing success return, and `N046` reading a signature without its error channel. *A
  fragment that Gabbro refuses is a place where two things are wrong at once, and the second
  one is only reachable after the first is fixed.*
* `F03` is different in kind. The three above needed **no new word**; the vocabulary ratchet
  did not move once. «B10» is a construct question, and the owner's own booking says two
  thirds of the 30–60 h sit there.

**And the tool's caveat stands, unchanged and unpaid:**

> *The ten fragments are chosen for their DIFFICULTY; `H = 0` over them stays trap 80 as long
> as no corpus stands beside them that nobody looked at while building.*

`H = 1` improves the tree. It is not a statement about the language — and nothing in these
three days made it one.
