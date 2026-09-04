# `K100` asked as TWO questions — the syntax, then the checker

**2026-09-04.** Base `master` at `3b38955` (*"`L` becomes a GATE and reads 3"*), worktree
`agent-ad3406b4824591548`, server directory `gabbro-frage`. **Nothing under `crates/` was
touched**, and the frozen half of «K3» was read and not edited:

```bash
git diff --stat 3b38955 HEAD -- crates/ messung/k3-fragmente/ messung/K3-AUSWAHL.md   # empty
```

**The mandate is the owner's reframing:** `K100` — *100 % plumbing coverage* — is first a
question to the SYNTAX (*can it be said at all?*) and only then a question to the CHECKER
(*for what CAN be said, who discharges it?*). The four gates of `dokumente/PLAN.md` are
proxies for the second question, and
[`K100-VERDICT-2026-09-04.md`](K100-VERDICT-2026-09-04.md) §5 shows they do not add up to
the headline. This document asks the two halves directly.

---

## 0. The denominator, and it is the frozen file's own

**37 walls = 36 marked in the eight bodies + 1 the measurement found unmarked.**

```bash
for f in messung/k3-fragmente/K0*.gab; do
  echo "$f $(grep -o '\[WALL [0-9]*\]' $f | sort -u | wc -l)"; done
# K01 5 · K02 7 · K03 2 · K04 4 · K05 6 · K06 6 · K07 2 · K08 4   =  36
```

The 37th is `K08`'s undeclared `test_case_array`, named in
[`K3-BEFUND.md`](K3-BEFUND.md) §5 under *"The unmarked wall the measurement found"*.

> **This is not the same cut as `K3-BEFUND.md` §5's table.** That table has sixteen rows and
> groups by *what is missing*; its per-row figures are sometimes fragments and sometimes
> sites, and they sum to 35, not 37. **The 37 is a count of SITES**, and the sort below is
> per site, because that is the only reading under which the number the report leads with is
> the number being sorted. *Two enumerations of one thing are two registers (W7) — so this
> one names which of them it is.*

---

## 1. The three registers, and the tests, stated before the sort

| | register | the test |
|---|---|---|
| **1** | **deliberately refused** | the refusal is by name or by construction, **and** a decision naming the construct stands in the tree — `SYNTAX.md` §*"What deliberately does not exist"*, a `(* G… *)`/`(* H… *)` grammar comment, a paragraph of `SPRACHE.md`/`PLAN-HARDWARE.md`/`BEWEIS.md`, a «B…» booking, or a dated `messung/` entry — **and it predates the cut** `61a1b35` (2026-09-04 19:56:06) |
| **2** | **inexpressible and undecided** | no form exists, and the search above finds no decision. *The negative is a measurement: every search term and every file is named in §3* |
| **3** | **simply unwritten** | a Gabbro program expressing the construct **checks clean today**, shown by a minimal probe run against this binary — or a near form exists and the fragment reached past it |

**Register 3's test is the only one that can be RUN, so it is applied first.** A site that
passes it never reaches the decision question at all. That ordering is not a convenience: a
wall that a probe dissolves was never a fact about the language, and asking whether somebody
decided it would be asking about the wrong thing.

*A decision found only in a `crates/` comment is counted, and marked as such — a reason with
a date in the code is a decision; a diagnostic firing with no reason anywhere is not.*

---

## 2. The count: **25 refused · 6 undecided · 6 unwritten**, over 37

| | | site | class | register | the decision, or its absence |
|---|---|---|---|---|---|
| K01 | W1 | `m->private` is a `void *` | `void *` | **1** | `SYNTAX.md`:1710 · `SPRACHE.md`:72 |
| K01 | W2 | lock taken here, released in `allocinfo_stop` | asymmetric lock | **1** | `SYNTAX.md`:1508 *"A `locks` block releases at the end"* · `MESSUNGEN.md`:843 prices it |
| K01 | W3 | return type `static void *` | `void *` | **1** | as W1. *The failure channel is NOT the blocker — see §4* |
| K01 | W4 | `(struct allocinfo_private *)m->private` | `void *` | **1** | as W1 |
| K01 | W5 | `&priv->iter` | `&` on a data place | **1** | `PLAN-HARDWARE.md`:2509/2514 (**H2b**, *"eine Sprachentscheidung"*) · `MESSUNGEN.md`:1620 (2026-08-14) |
| K02 | W1 | anonymous `union` over the same bytes | `union` reinterpretation | **1** | `SYNTAX.md`:1710 · `BEWEIS.md`:932 |
| K02 | W2 | `&src->objects` | `&` on a data place | **1** | as K01 W5 |
| K02 | W3 | `hlist_entry(…, typeof(*obj), node)` | `container_of`/`offsetof`/`typeof` | **2** | **none — §3** |
| K02 | W4 | `last->next = NULL;` | null pointer | **1** | `BEWEIS.md`:931, corrected :940 (2026-09-02) |
| K02 | W5 | `if (next)` | null pointer | **1** | as W4 |
| K02 | W6 | `next->pprev = &src->objects.first;` | `&` on a data place | **1** | as K01 W5 |
| K02 | W7 | `WRITE_ONCE(src->cnt, …)` | `atomic` on a field | **1** | `messung/RACE.md`:75, :93–133 (2026-08-24) — *"eine Entscheidung mit einer Zahl"* |
| K03 | W1 | three callees taking `void *to` | `void *` **in a parameter** | **3** | **writable today — §4** |
| K03 | W2 | `to += progress;` | pointer arithmetic w/o basis | **1** | `SPRACHE.md`:853–855 · `SYNTAX.md`:1711 |
| K04 | W1 | `#define LC_FREE (~0U)` | `~` on a literal (`M137`) | **3** | **`u32::max` checks clean — §4** |
| K04 | W2 | `test_and_set_bit(__LC_PARANOIA, &lc->flags)` | `atomic` on a field | **1** | as K02 W7 |
| K04 | W3 | `hlist_del_init(&e->collision);` | `&` on a data place | **1** | as K01 W5 |
| K04 | W4 | `list_move(&e->list, &lc->free);` | `&` on a data place | **1** | as K01 W5 |
| K05 | W1 | `unsigned long percpu_count_ptr;` | ptr↔int cast | **2** | **none — §3** |
| K05 | W2 | `__alignof__(unsigned long)` | alignment of a TYPE | **2** | **none — §3** |
| K05 | W3 | `(unsigned long) __alloc_percpu_gfp(…)` | ptr→int cast | **2** | **none — §3** |
| K05 | W4 | `free_percpu((void __percpu *) …)` | int→ptr cast | **2** | **none — §3, and the tree decided the OPPOSITE for a literal** |
| K05 | W5 | `atomic_long_set(&data->count, …)` | `atomic` on a field + `&` | **1** | as K02 W7 |
| K05 | W6 | `data->confirm_switch = NULL;` | absent function value | **1** | `BEWEIS.md`:931; refused by name (`M140`, *"a number does not answer for a function pointer"*) |
| K06 | W1 | `union handle_parts` | `union` reinterpretation | **1** | as K02 W1 |
| K06 | W2 | `static void **stack_pools;` | `void *` in a **static** | **1** | `SYNTAX.md`:1710 — the parameter carve-out does not reach a static |
| K06 | W3 | `static bool depot_init_pool(void **prealloc);` | `void **` **in a parameter** | **3** | **writable today — §4** |
| K06 | W4 | return type `struct stack_record *`, `NULL` on 3 of 5 paths | failure-returning pointer | **3** | **`-> ptr<…> T or R` + `let … else` checks clean — §4** |
| K06 | W5 | `stack = current_pool + pool_offset;` | pointer arithmetic w/o basis | **1** | as K03 W2 |
| K06 | W6 | `INIT_LIST_HEAD(&stack->hash_list);` | `&` on a data place | **1** | as K01 W5 |
| K07 | W1 | `misc_deregister(&test_fw_misc_device);` | `&` on a data place | **1** | as K01 W5 |
| K07 | W2 | `pr_warn("removed interface\n");` | variadic call **+ string argument** | **1** | variadic: `beispiele/gift/511` + `namen.rs`:445 (2026-09-02). **The string half is undecided — §3** |
| K08 | W1 | `static int test_func(void *private)` | `void *` **in a parameter** | **3** | **writable today — §4** |
| K08 | W2 | `int random_array[ARRAY_SIZE(…)];` | uninitialised **local** array | **3** | **`let a : [u32; 3] = 0;` checks clean — §4** |
| K08 | W3 | `synchronize_srcu(&prepare_for_test_srcu);` | `&` on a data place | **1** | as K01 W5 |
| K08 | W4 | `continue` in a `traverse` | no label on `traverse` | **1** | `SYNTAX.md`:1054 · `beispiele/41-handschlag.gab`:9–13 *"und das ist Absicht"* · `messung/BERICHT-SUCHE.md`:179–201, **demand 0** (2026-09-03) |
| K08 | — | `static struct test_case_desc test_case_array[] = { … }` | **array literal** | **2** | **none — §3. «B7» decides RECORDS only** |

```
register 1  deliberately refused, decision found     25 of 37   68 %
register 2  inexpressible and UNDECIDED               6 of 37   16 %
register 3  simply unwritten -- a form exists today   6 of 37   16 %
```

**Twenty-five of thirty-seven walls are the language keeping a promise it wrote down.** That
is the number that matters most and it is the least surprising one: `K3-BEFUND.md` §8 said
so in prose (*"several of them … are things the language refuses on purpose"*), and this is
that sentence with a denominator behind it. **What was not known is the other twelve.**

---

## 3. Register 2 — the refusals nobody decided. **This is the finding.**

Six sites over four constructs. Each *presents* as design — the checker refuses, the wall
note says so calmly, and a reader would file it under "Gabbro on purpose". **Nothing in the
tree decides any of them.**

### 3.1 `container_of` / `offsetof` / `typeof` — K02 W3

**And `K3-BEFUND.md`:379–380 says the opposite by name:**

> *"several of them — intrusive lists, `void *`, `container_of` — are things the language
> refuses on purpose, with reasons written down long before this corpus existed."*

`void *` has its reasons. `container_of` has none.

```bash
grep -rniE 'container_of|offsetof|__typeof__|\btypeof\b' dokumente/ messung/ README.md TODO.md DONE.md crates/
```

Four kinds of hit, and not one is a decision: `BEWEIS.md`:815 counts `__typeof__` **in the
emitted C** (9 sites, class C2 — a finding *against* the emission list); `messung/grenze/schale.c`
uses `offsetof` in a measurement harness; `cnamen.rs`:97 carries `_Alignof` in a C-keyword
blacklist; and the wall notes in `messung/k3-fragmente/` are the artefact under audit.
**`container_of` appears nowhere in `dokumente/`.**

*The construct is the whole of the kernel's intrusive-list idiom.* Its absence may well be
right — but it is a gap, not a design, until somebody writes the sentence.

### 3.2 The pointer↔integer cast, in either direction — K05 W1, W3, W4

Three sites, one construct. There **is** a decision against a general `cast` — `SYNTAX.md`:589
`(* G9: kein `cast` *)`, grounded at :656–659 — but its ground is *grammar ambiguity*:

> *"`cast` war eine echte Teilmenge von `call` und aus der Grammatik nie eindeutig
> ableitbar. Die Produktion entfaellt: ein `call`, dessen `path` einen Typ nennt, IST die
> Umwandlung."*

**That decides that conversions are spelled as calls. It says nothing about pointers against
integers.** `H2b` (`PLAN-HARDWARE.md`:2514, `MESSUNGEN.md`:9969) is a statement about
*forming* a pointer to a global, and rests on the missing address operator, not on a type
rule. `BEWEIS.md`:928 refuses casts **between pointer types**, which is a third thing.

**And on the one occasion the tree did decide, it decided the other way.** `emit.rs`:1999–2023
(2026-09-02):

> *"converting an INTEGER to a pointer is **implementation-defined** (6.3.2.3p5) rather than
> undefined, and that is exactly what a place naming a fixed address on bare metal needs.
> Address 0 there is a vector slot and not a mistake; **what was wrong is the spelling, not
> the intent.**"*

`m1.rs`:4692–4699 carries the same rule for the source language: a literal `0` at a pointer
type **is** the null pointer and **stands in the clean corpus** (`beispiele/38`). So an
integer *literal* becomes a pointer by decision, and an integer *variable* does not — by
nothing. `K05`'s wall note asserts the ground itself (*"das ist deliberate: `opaque type Pa =
u64` exists because an address that is a NUMBER is a different thing from a pointer"*), and
that sentence is **nowhere in the tree**; every `opaque type Pa = u64` found is an address
held *as* a number, which is its converse.

```bash
grep -rn 'uintptr\|opaque type\|blanke Zahl\|bare number\|address is not a number' dokumente/ messung/ crates/
```

### 3.3 An alignment-yielding builtin — K05 W2

The builtin set is closed by grammar (`SYNTAX.md`:660–661) and the vocabulary is closed by
rule (:108–111, *"Everything else is an identifier. A new word is a language change and needs
an entry here"*). **The closure is decided; this particular absence is not.** `aligned(e, c)`
is documented as a *predicate* over M1 (`SPRACHE.md`:879) and nowhere as *"and therefore we
do not give you the value"*.

Measured rather than assumed — `alignof` is not even a refusal, it is an ordinary undeclared
call:

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/q5-alignof.gab
error: [M119] :3:68: `Wort` is declared nowhere
error: [K003] :3:60: `f` promises costs, but `alignof` is not declared here
```

```bash
grep -rniE 'alignof|_Alignof|align_of|Ausrichtung' dokumente/ messung/ README.md TODO.md DONE.md crates/
```

### 3.4 The array literal — K08, the unmarked wall

**«B7» decides the braced literal for RECORDS and does not reach arrays.** The decision text
(`SYNTAX.md`:637–652 and :1716–1719, dated 2026-08-17) is about `P { a: 1, b: true }`,
`Verbundliteral`, field labels `M106`/`M107`, `P037`, `beweise/Verbund_Konstruktor.thy`.
:1714 names *"**the** braced compound literal"*, singular. **Nothing about `[ … ]`.**

And the array half was in the original finding and was never closed —
`dokumente/FRAGMENTE.md`:1267:

> | **B7** | 785 | :200 | **No struct and no array literal in `expr`.** A function therefore
> cannot produce a `structty`; tuple return and `reply(EP, [ … ])` fall with it | F4, F5, F6 |

All three of `PFLICHTEN.md`'s «B7» discharges (:239, :264, :293) close it **by replacing the
array with a record** — *"Four arguments become one record"*. The record half was built; the
array half was sidestepped and stayed booked. Confirmed absent in the code, not merely in the
documents: `primary` (`SYNTAX.md`:588) has no array alternative and
`crates/gabbro-syntax/src/ast.rs`'s `enum ExprArt` has no array-value variant.

*The consequence is exactly K08's:* there is no static table with per-element values.
A `table` declares slots and never their contents.

### 3.5 The rider — a string as a call argument (K07 W2)

The site is **register 1** because `pr_warn` is variadic and *that* is decided, with a
count, in `beispiele/gift/511-extern-auf-variadisch.gab` and `namen.rs`:439–446 (2026-09-02):
*"In C11, being variadic and finding your end in the data are the same fact."*

**But the second half of the wall is not decided.** `string` occurs in exactly five grammar
positions — `section` (:302), `assume`/`axiom` (:794, :1539), `asm` (:806), `reason` (:1284),
`check`/`claim` (:1608) — and in neither `primary` (:588) nor `arg` (:653). *No text anywhere
argues that placement.* A non-variadic callee taking a string literal is just as unwritable,
and nothing in the tree says so on purpose.

### 3.6 The list, as asked

**Sites in register 1 that turned out to have no decision behind them — and therefore are
not register 1:**

| construct | sites | what it blocks |
|---|---|---|
| `container_of` / `offsetof` / `typeof` | 1 (K02 W3) | every intrusive container in the kernel |
| pointer↔integer cast, either direction | 3 (K05 W1, W3, W4) | tagged pointers, flag bits in an address |
| an alignment-yielding builtin | 1 (K05 W2) | any allocator that computes an alignment |
| the array literal | 1 (K08, unmarked) | every static dispatch table |
| *rider:* a string as a call argument | (inside K07 W2) | every `printk`-shaped call, variadic or not |

---

## 4. Register 3 — six walls a probe dissolves, and every probe is here

Each was run against the binary built from `3b38955` on `ki-pc-fisch-101`.

### 4.1 `void *` in a PARAMETER is writable, and the decision is two days older than the cut

`PLAN-HARDWARE.md`:2476–2481, committed `6c62184`, **2026-09-02 01:53** — the cut `61a1b35`
is 2026-09-04 19:56:

> **`void *` ist in einem PARAMETER schreibbar, im ERGEBNIS nicht** — und die Asymmetrie ist
> die Regel, nicht die Bequemlichkeit. Herein erzeugt Gabbro Genauigkeit, nach der C nicht
> gefragt hat; hinaus müsste es welche ERFINDEN.

`namen.rs`:448–452 carries it in the checker: *"A `void *` that comes IN runs the other way
and IS allowed: there Gabbro supplies precision C did not ask for, and the conversion is C's
own."* The table grew 138 → **149 bindable rows** on that one decision.

K03's three callees and K08's kthread entry point are exactly that shape, and they check
clean:

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/r2-voidstar-parameter.gab
/tmp/frageproben/r2-voidstar-parameter.gab: 5 items, 0 errors, 0 hints
```

```gabbro
extern fn raw_copy_from_user(ziel : ptr<normal, rw> u8, quelle : ptr<normal, r> u8, n : u64) -> u64
    effects { writes ziel, reads quelle } costs <= 64 ops;
pub fn test_func(priv_arg : ptr<normal, rw> u8) -> i32
    effects { reads priv_arg } costs <= 8 ops { return 0; }
```

**And `void **` too** — K06 W3's `depot_init_pool(void **prealloc)`:

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/r3-ptr-ptr.gab
… 4 items, 1 errors, 0 hints        # the one error is N038 on a missing `pub`, mine
```

*So three of the eight `void *` sites are not `void *` walls at all.* K01 W1/W3/W4 and
K06 W2 stay — a field, a result and a static are the direction the decision refuses.

### 4.2 A pointer-returning function that may fail — K06 W4

The wall note looked for `option` and stopped: *"Gabbro has no null pointer and `option` only
over a table index, which a `stack_record *` is not."* **The form is `-> T or R`, and
`K3-BEFUND.md` §6 credits it one fragment over** (K05's `kzalloc`/`if (!data)` row, «C3a»):

```gabbro
extern fn hole() -> ptr<normal, rw> Satz or Fehl effects { pure } costs <= 8 ops;
pub fn f() -> u32 effects { pure } costs <= 32 ops {
    let d = hole() else (e) { return 0; }
    return d->wert;
}
```

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/q8-ptr-or-reason.gab
/tmp/frageproben/q8-ptr-or-reason.gab: 5 items, 0 errors, 0 hints
```

**K01 W3 is NOT this case** and stays in register 1: `allocinfo_start` returns a `void *`,
so the element type is the blocker and the failure channel never gets a turn.

### 4.3 A local array — K08 W2

The wall note is right about the literal and wrong about the conclusion: `letstmt` demands an
initialiser, there is no array literal — **and a scalar initialiser is accepted.**

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/q6-lokales-feld.gab      # let a : [u32; 3] = 0;
/tmp/frageproben/q6-lokales-feld.gab: 2 items, 0 errors, 0 hints
```

`random_array` is filled by `shuffle_array` on the next line, so an initialiser it never
reads is not a change to what the program does. **The static `test_case_array`, whose
elements each carry a distinct value, is a different wall and stays in register 2** (§3.4).

### 4.4 `~0U` — K04 W1

`M137`'s own message names the cure, and the cure checks clean:

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/p1-tilde-cure.gab        # const LC_FREE : u32 = u32::max;
/tmp/frageproben/p1-tilde-cure.gab: 3 items, 0 errors, 0 hints
```

The frozen file counts it deliberately (*"writing `0xFFFF_FFFF` instead would … hide the
question"*), and that was the right call for a transcription measurement. **Under the
question this document asks — *can it be said?* — the answer is yes.**

---

## 5. Three things the frozen report gets wrong about itself, and one it could not have known

1. **`container_of` is not refused on purpose** (`K3-BEFUND.md`:379–380). §3.1.
2. **«B7» does not cover arrays** — quoting it as the array literal's decision would be a
   false finding. §3.4.
3. **Six of the 37 walls are not walls today.** §4. Four of the six turn on decisions or
   forms that were already in the tree when the fragments were written — the `void *`
   parameter rule (2026-09-02), `-> T or R` (§6 of the report itself credits it), the scalar
   array initialiser, and `M137`'s named cure.

**And an EIGHTH vocabulary collision, found by accident while writing §4.1:** `to` is a word
of the vocabulary (`kw.rs`:98), and it is the parameter name of `copy_from_user_iter`'s
`void *to` — kernel-verbatim, in the fragment `K3-BEFUND.md` §3 measures. The report lists
seven (`node`, `old`, `next`, `progress`, `release`, `stack`, `index`); the fragment must
have renamed this one before the run.

```
$ ./target/debug/gabbro pruefe /tmp/frageproben/r1-voidstar-parameter.gab
error: [P002] :6:30: `to` is a word of the vocabulary, not an identifier
```

*The rate §3 reports is a lower bound, and this is the first datum after it.* The
vocabulary is **221 words** (`./instrumente/zaehle-wortschatz.py`: 212 reserved, 9
contextual).

---

# Half two — the CHECKER: for what CAN be said, who discharges it?

The audit named what would make the conjunction entail the headline
(`K100-VERDICT-2026-09-04.md` §5, point (a)):

> **a coded ratio — obligations discharged over obligations named, both read from the same
> mechanically-derived source, not a hand-typed document column.**

## 6. What exists mechanically, measured before anything is proposed

### 6.1 `gabbro pflichten` — a real, git-backed obligation register

`crates/gabbro-check/src/pflichten.rs::sammle` walks the AST and produces **eight kinds** of
obligation: `E` maintains · `N` ensures · `F` foreign ensures · `V` precondition at a CALL
SITE · `R` refines · `D` device promise · `S` loop invariant · `W` walk/table/group invariant.

Over every tracked, non-poison `.gab` in the tree:

```bash
git ls-files '*.gab' | grep -v '/gift/' > /tmp/frage-korpus.txt        # 210 files
while read f; do ./target/debug/gabbro pflichten "$f"; done < /tmp/frage-korpus.txt
```

```
files with a register:      150
files REFUSED (errors):      60
obligations total:          168
   D 38 · N 35 · V 33 · W 30 · E 13 · F 12 · S 6 · R 1
```

**168 obligations over 150 units, mechanically derived, denominator from `git ls-files`.**
This is the strongest thing in the tree of the shape the audit asked for.

*And the 60 refusals are not a hole in the denominator:* every one is a file written to draw
a refusal — `messung/proben` 11, `fnptr-proben` 10, **`k3-fragmente` 8**, `tor-proben` 7,
`stille-proben` 6, `einheit-proben` 6, `race-proben` 5, `abi-proben` 5,
`programmlogik/beispiel` 1, `messung/fragmente` 1 (**F03**). *A register that refuses a file
with errors is right to; a register whose refusals were accidental would be a different
number.*

### 6.2 And it names only the OPEN half — **by design, in its own header line**

```
-- What a HUMAN still owes here. Counted, not discharged.
```

`pflichten.rs`:1093, and the module docstring says the same at :15: *"Dieses Modul loest
keine Pflicht ein. Es ZAEHLT sie."* **Taken as the denominator, the numerator is 0 by
construction.**

### 6.3 The one discharge the register KNOWS, and throws away

`pflichten.rs`:975–980 — a `table` invariant is skipped when the table carries `ops`:

> *"else the generated mutations preserve it under the machine-checked template
> `table.ops.erhaltung` (`beweise/Table_Ops_Erhaltung.thy`), **and a discharged duty is not
> open**."*

```rust
ItemArt::Tabelle(t) => {
    if !t.ops.is_empty() {
        continue;                        // <- the numerator, at the one place it is computed
    }
```

**That `continue` is the whole finding of half two in one line.** The register computes a
discharge, recognises it, states its proof by name — and drops it, because its output has no
column for it. Everything else the checker discharges is not even computed: **a pass that
succeeds emits nothing.**

### 6.4 Four coded ratios DO exist — and the verdict's blanket sentence is wrong

`K100-VERDICT-2026-09-04.md` §5 point 1 reads *"**No code computes a percentage anywhere.**"*
**That is false, and one of the four prints on every single `gabbro pruefe` run:**

| where | what it divides | over the tracked corpus |
|---|---|---|
| `crates/gabbro-check/src/m1.rs`:51 `deckung()`, printed at `main.rs`:1229 and :1420 | expressions M1 gave a type / expressions M1 saw | **3253 / 3508 = 92.73 %** |
| `crates/gabbro-check/src/kosten.rs`:166 `Zaehlung`, printed by `gabbro kosten` | bodies whose cost was computed / bodies with `costs` | **463 / 490 = 94.49 %** |
| `crates/gabbro-cli/src/fragmente.rs`:65 | units with no errors / units — *"that is gate P2, and it demands 100 %"* | per run |
| `crates/gabbro-cli/src/main.rs`:1684, :1706 | «A4» effect-hull shares | per run |

```
$ ./target/debug/gabbro pruefe messung/fragmente/F01.gab
messung/fragmente/F01.gab: 41 items, 0 errors, 0 hints
  M1 saw 71 expressions, 11 of them without a type (85 % coverage)
```

**The verdict's conclusion survives its wrong sentence, and gets sharper.** The correct
statement is narrower and harder: *no code computes a ratio of obligations discharged over
obligations named.* What the four do compute are ratios over **expressions**, **bodies**,
**units** and **effect hulls** — and two of them (M1, `kosten`) are **exactly the discharged/
named shape, per program, from one source**. So the shape is not hypothetical. **It is built
for 2 of 12 passes and for no obligation kind.**

### 6.5 The join between the mechanical register and the hand column: **3 of 239**

`dokumente/PFLICHTEN.md`'s `239 = 173 K + 66 L` is a hand-typed third column, and
`zaehle-pflichten.py --spalten` counts it without judging it — the tool says so itself:

```
  verankert  229 = 163 K +  66 L
  Absenkung   10 =  10 K +   0 L
  insgesamt  239 = 173 K +  66 L
```
> *"die Klasse `K`/`L` ist ein URTEIL, das ein Mensch in die dritte Spalte geschrieben hat --
> dieses Werkzeug zaehlt sie, es faellt sie nicht."*

**Exactly one machine-checked join exists between that document and any source in the tree**,
and it is not the obligation register: `zaehle-pflichten.py --gabbrov` scans
`messung/fragmente/F*.gab` for `progress <name>` with a regex and matches the name as a
substring against the fourth column of an `L` row.

```
  `L` rows in `PFLICHTEN.md`                     66
  of these discharged by the assumption layer     3
  GabbroV obligation population                  63
```

**3 of 239 rows, by text, over one clause kind.** The remaining 236 have no mechanical
counterpart at all — not even a wrong one.

### 6.6 And the two registers do not measure the same objects

Over the nine of ten fragments that check clean:

| | hand `K` | hand `L` | `gabbro pflichten` | the mechanical kinds |
|---|---:|---:|---:|---|
| F1 | 42 | 17 | **17** | 3 E · 6 N · 7 V · 1 W |
| F2 | 19 | 5 | **10** | 10 D |
| F3 | 13 | 13 | *refused — 18 errors* | — |
| F4 | 24 | 7 | **5** | 5 D |
| F5 | 8 | 10 | **0** | — |
| F6 | 21 | 5 | **1** | 1 N |
| F7 | 8 | 1 | **0** | — |
| F8 | 12 | 2 | **1** | 1 V |
| F9 | 7 | 4 | **3** | 3 W |
| F10 | 9 | 2 | **2** | 1 F · 1 S |
| **nine measurable** | **150** | **53** | **39** | |

**39 against 53 on the same nine fragments** — and the disagreement is not a rounding error,
it is a different subject. F2's mechanical ten are all `D`, device-register promises; its
hand column claims five `L`. **F5 carries ten hand `L` rows and zero mechanical
obligations — and it is right to**, because F5 contains no `ensures`, no `maintains`, no
`refines` and no `invariant` at all:

```bash
grep -c 'ensures\|maintains\|refines\|invariant\|requires' messung/fragmente/F05.gab   # 0
```

*Ten obligations a human read out of the text, and not one clause for a walk to find.* *The `.gab` files carry MORE material than the `FRAGMENTE.md` blocks the hand
column was written against, so if anything 39 understates.* The register names two of its own
undercounts in its docstrings (`pflichten.rs`:407–417: generated `ops` heads are invisible to
the `V` walk, *"a number drifting parallel to the truth"*; and the `maintains` lookup is
per-unit).

### 6.7 What the checker side proves about itself: **0**

```
$ ./target/debug/gabbro paesse | tail -6
--   SENTENCES: 96 over 12 passes -- 89 measured, 2 ARGUED, 5 CONJECTURED, 0 proved.
--   They claim 231 diagnostic codes between them.
--   0 of 96 have been to Isabelle. That is the number PL.2 is about.

$ python3 instrumente/pruefe-saetze.py | tail -1
== Arbeitsmenge: 278 Kennungen, 96 Saetze, 51 ohne Satz, 0 erfunden, 1 Werkzeuglauf, 4 Proben ==

$ ./target/debug/gabbro schablonen | grep 'templates'
-- 21 templates, 11 of them unproved, 10 machine-checked.
```

These **are** coded ratios from single mechanical sources — 51 of 278 codes carry no
sentence, 10 of 21 templates are machine-checked, 0 of 96 sentences are proved. They measure
the checker's self-documentation and the generator's trust surface. **They do not measure
what a program owes.**

*The two code figures are counted differently and are not in conflict:* `pruefe-saetze.py`
counts DISTINCT codes with a sentence (278 − 51), `gabbro paesse` counts CLAIMS (231), and a
code claimed by two sentences is one code and two claims.

## 7. Verdict on half two: **not derivable today** — and here is the price

**Not derivable**, and the reasons are three, in increasing cost.

| | what is missing | cost |
|---|---|---|
| **(i)** | **`Pflicht` has no discharge state.** The one discharge the walk computes is `continue`d away (§6.3) | one field on `Pflicht`, `continue` → `push`, one column in `zeige`. **Small — and it buys exactly ONE discharge class** |
| **(ii)** | **The K obligations have no enumerator at all.** `PFLICHTEN.md`'s 173 K rows are discharged by `M101`/`M103`/`M104`, `H001`–`H006`, `K001`, `exhaustive`, `tagged type`, `wrapping` — and **none of these emits a record when it succeeds.** Silence is the discharge | twelve passes must count what they proved, not only what they refused. **The shape is proven — `m1::Zaehlung` and `kosten::Zaehlung` already do it (§6.4) — so this is 10 more of a thing that exists twice, not a new idea.** It is a lane, not a patch |
| **(iii)** | **No join.** The document's rows are anchored at `FRAGMENTE.md:NNN` from revision `708beed`; the register's at `<file>:<line>` in `messung/fragmente/*.gab`. Different files, different revision. The only join is 3 `progress` names by substring (§6.5) | either the document's rows get machine anchors into the `.gab` corpus, or the hand column is retired in favour of the walk. **This is a decision about which register is the register, and W7 says there may not be two** |

**(i) and (ii) together would make the ratio real; (iii) decides what its denominator names.**
Until (ii) exists, any ratio built on (i) alone would read `1/168` — technically coded,
and a worse sentence than the honest "not derivable", because it would look like a
measurement of coverage and would be a measurement of one template.

> *A measured "not derivable today, and here is why" is a complete result.* This is that
> result, and it is the second time this week the tree has learned that a number without a
> mechanical source is a sentence.

---

## 8. Which half is the binding constraint? **The syntax, and it is not close.**

«K3» is **0 of 8**, and it fails *before* the checker is reached:

* **6 of 8 do not parse** without a reader refusal (`P002`, on kernel-verbatim identifiers).
* **0 of 8 could be transcribed at all** — every one carries at least two walls.
* **`gabbro emit` wrote zero bytes for all eight.** The plumbing was never asked to cover
  anything, because nothing got as far as having plumbing.

**And this document's own sort says the same thing from the other side.** Of 37 walls,
**25 are the language keeping a written promise** — `void *`, `&x`, `NULL`, `union`,
`atomic` on a field, pointer arithmetic, the asymmetric lock, the unlabelled `traverse`.
Those are not gaps to be closed; they are the design. **Which means the distance between
Gabbro and this code is not a to-do list, it is a disagreement about what a systems language
is** — and no amount of plumbing coverage moves it.

So, plainly:

> **`K100`'s name points at the wrong thing.** *100 % plumbing coverage* is a claim about the
> second half — for what can be said, the language discharges everything but the logic — and
> the second half is not where Gabbro stands against a kernel. **The syntax is the wall.**
> On the eight fragments the plumbing question never came up once.

Three qualifications, because a verdict this large needs its edges:

1. **This is portability, not fitness.** `K3-BEFUND.md` §8 says it and it is right: every
   wall in §2 is a statement about *transcribing existing C*. A kernel written *for* Gabbro
   meets 25 of these 37 walls not at all.
2. **The second half is not thereby sound.** §7 says it is not even measurable today. *That
   the binding constraint is elsewhere is not a licence to stop measuring here* — it is why
   the six undecided refusals of §3 matter: a language that means to refuse should know that
   it does.
3. **And 6 of 37 dissolved under a probe.** The syntax is a wall, and it is a **16 % smaller
   wall** than the frozen measurement recorded — which is the difference between measuring a
   language and measuring a transcription of it.

---

## 9. Runs behind this document

All on `ki-pc-fisch-101:gabbro-frage`, binary built from `3b38955`.

| what | command | result |
|---|---|---|
| wall denominator | `for f in messung/k3-fragmente/K0*.gab; do grep -o '\[WALL [0-9]*\]' $f \| sort -u \| wc -l; done` | 5 7 2 4 6 6 2 4 = **36**, +1 unmarked = **37** |
| `void *` parameter | `gabbro pruefe /tmp/frageproben/r2-voidstar-parameter.gab` | **5 items, 0 errors** |
| `void **` parameter | `gabbro pruefe /tmp/frageproben/r3-ptr-ptr.gab` | 4 items, 1 error (`N038`, mine) |
| pointer-or-reason return | `gabbro pruefe /tmp/frageproben/q8-ptr-or-reason.gab` | **5 items, 0 errors** |
| local array | `gabbro pruefe /tmp/frageproben/q6-lokales-feld.gab` | **2 items, 0 errors** |
| `u32::max` for `~0U` | `gabbro pruefe /tmp/frageproben/p1-tilde-cure.gab` | **3 items, 0 errors** |
| `alignof` is not a word | `gabbro pruefe /tmp/frageproben/q5-alignof.gab` | `M119` + `K003` — an undeclared CALL |
| null at a function slot | `gabbro pruefe /tmp/frageproben/r4-null-fnptr.gab` | `M140` *"a number does not answer for a function pointer"* |
| `next` inside a `traverse` | `gabbro pruefe /tmp/frageproben/q4-next-in-traverse.gab` | 0 errors — but it retargets the ENCLOSING loop; not `continue` |
| eighth vocabulary collision | `gabbro pruefe /tmp/frageproben/r1-voidstar-parameter.gab` | `P002` on `to` (`kw.rs`:98) |
| obligation register, corpus | `while read f; do gabbro pflichten "$f"; done < /tmp/frage-korpus.txt` | **168** over 150 of 210, 60 refused |
| obligation register, ten | `for f in messung/fragmente/F*.gab; do gabbro pflichten "$f"; done` | 17 10 — 5 0 1 0 1 3 2 = **39** |
| hand column | `python3 instrumente/zaehle-pflichten.py --spalten` | `239 = 173 K + 66 L` |
| the only join | `python3 instrumente/zaehle-pflichten.py --gabbrov` | `66 L`, **3** rebooked, population 63 |
| M1 coverage, corpus | `gabbro pruefe` over `/tmp/frage-korpus.txt`, summed | **3253 / 3508 = 92.73 %** |
| cost coverage, corpus | `gabbro kosten` over `/tmp/frage-korpus.txt`, summed | **463 / 490 = 94.49 %** |
| pass sentences | `gabbro paesse` | 96 sentences, 231 codes claimed, **0 proved** |
| codes | `python3 instrumente/pruefe-saetze.py` | 278 codes, 96 sentences, 51 without |
| templates | `gabbro schablonen` | 21 templates, 11 unproved, **10 machine-checked** |
| vocabulary | `python3 instrumente/zaehle-wortschatz.py` | **221** words (212 reserved, 9 contextual) |

**Not run for this document:** the mutation catalogue, `pruefe-emission.sh`, `isabelle build`.
Nothing above rests on them.

---

## 10. The probes, in full — and why they are NOT files in the tree

**Eight probes, and every one stands here verbatim instead of under `messung/proben/`.**
A tracked `.gab` under `messung/` is corpus: `zaehle-wortschatz.py`'s denominator is
*"`beispiele/*.gab` + `messung/**/*.gab`, ohne `gift/`"* — **205 files today** — and eight
more would move the vocabulary carrier counts, the `220 benutzt / 1 nur reserviert` split,
and every other figure taken over that population. *A measurement that moves eleven
denominators in order to record itself is paying more than it is worth.* The text below is
the whole of each probe; anyone can put it in `/tmp` and get the line quoted in §9.

```gabbro
-- p1  §4.4  `~0U` -> the cure `M137` itself names.            3 items, 0 errors
module p {
const LC_FREE : u32 = u32::max;
pub fn f() -> u32 effects { pure } costs <= 4 ops { return LC_FREE; }
}
```

```gabbro
-- q5  §3.3  `alignof` is not a word: an ordinary undeclared CALL.  M119 + K003
module p {
type Wort = u64 in 0 .. 255;
pub fn f() -> u64 effects { pure } costs <= 4 ops { return alignof(Wort); }
}
```

```gabbro
-- q6  §4.3  a LOCAL array with a scalar initialiser.          2 items, 0 errors
module p {
pub fn f() -> u64 effects { pure } costs <= 8 ops {
    let a : [u32; 3] = 0;
    return lenof(a);
}
}
```

```gabbro
-- q8  §4.2  a pointer-returning callee that may fail.         5 items, 0 errors
module p {
reason Fehl { KeinPool = 1 "kein freier Pool" }
type Satz = { wert : u32 in 0 .. 9, };
extern fn hole() -> ptr<normal, rw> Satz or Fehl effects { pure } costs <= 8 ops;
pub fn f() -> u32 effects { pure } costs <= 32 ops {
    let d = hole() else (e) { return 0; }
    return d->wert;
}
}
```

```gabbro
-- r1/r2  §4.1 and §5  `void *` in a PARAMETER.  r1 = the same with `to` for `ziel`,
--                     which draws P002: the EIGHTH vocabulary collision.
--                     As written here: 5 items, 0 errors.
module p {
extern fn raw_copy_from_user(ziel : ptr<normal, rw> u8, quelle : ptr<normal, r> u8, n : u64) -> u64
    effects { writes ziel, reads quelle } costs <= 64 ops;
extern fn instrument_copy_from_user_before(ziel : ptr<normal, rw> u8, quelle : ptr<normal, r> u8, n : u64)
    effects { reads ziel, reads quelle } costs <= 8 ops;
extern fn instrument_copy_from_user_after(ziel : ptr<normal, rw> u8, quelle : ptr<normal, r> u8,
                                          n : u64, rest : u64)
    effects { reads ziel, reads quelle } costs <= 8 ops;
pub fn test_func(priv_arg : ptr<normal, rw> u8) -> i32
    effects { reads priv_arg } costs <= 8 ops
{
    return 0;
}
}
```

```gabbro
-- r3  §4.1  `void **` in a parameter.   4 items, 1 error -- N038 on the missing `pub`, mine
module p {
type Satz = { wert : u32 in 0 .. 9, };
extern fn depot_init_pool(vorrat : ptr<normal, rw> ptr<normal, rw> Satz) -> bool
    effects { reads vorrat } costs <= 32 ops;
pub fn f(v : ptr<normal, rw> ptr<normal, rw> Satz) -> bool
    effects { reads v } costs <= 64 ops
{
    return depot_init_pool(v);
}
}
```

```gabbro
-- r4  §2 K05 W6  a number at a FUNCTION slot.   M140, and the message is the finding
module p {
extern fn schalter(a : u32) effects { pure } costs <= 4 ops;
type Daten = { bestaetige : fn(u32), };
pub fn f(d : ptr<normal, rw> Daten) effects { writes d } costs <= 8 ops {
    d->bestaetige = 0;
}
}
-- error: [N035] `fn(#1)` declares no `effects` and no `costs`
-- error: [M140] the assignment requires `fn(u32)`, the value has `u8 in 0 .. 0`
--                -- a number does not answer for a function pointer
```

```gabbro
-- q4  §9  `next` inside a `traverse` -- it resolves, and it retargets the ENCLOSING loop.
--         4 items, 0 errors.  NOT `continue`: the array walk is left, not advanced.
module p {
pub static mut T : [u32; 3] = 0;
extern fn zu_lang() -> never effects { diverges } costs <= 1 ops;
impl fn f() effects { reads T, writes T } {
    forever runde
        per_pass bounded 64 ops
        on_exceeded zu_lang
        effects { reads T, writes T }
    {
        traverse i over elems of T by unvisited {
            if i == 1 { next runde; }
        }
        leave runde;
    }
}
}
```
