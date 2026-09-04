# «K3» — the measurement, and it is **0 of 8**

**2026-09-04.** Eight fragments cut from Linux 7.2.0-rc7 by the rule in
[`K3-AUSWAHL.md`](K3-AUSWAHL.md), frozen in commit `61a1b35` **before a single one of them
had been run**, and measured here in the commit after it.

```bash
git log --format='%h %ci %s' 61a1b35 -1     # the cut
git log --format='%h %ci %s' HEAD -1        # this measurement
```

*Whoever wants to check the freeze does not read this sentence; he reads those two lines.*
And the frozen half is **byte-identical to what was committed before the measurement** —
nothing in it was tidied up afterwards, not even a sentence:

```bash
git diff --stat 61a1b35 HEAD -- messung/K3-AUSWAHL.md messung/k3-fragmente/   # empty
git diff --stat 61a1b35 HEAD -- crates/                                        # empty
```

> **The full candidate list is 1709 rows and is reproducible rather than transcribed.** The
> selection program stands verbatim in [`K3-AUSWAHL.md`](K3-AUSWAHL.md) §4; run over the same
> tree at the same commit it prints every candidate with its index, so the stride can be
> checked without trusting either document. *A list of 1709 names copied by hand into an
> `.md` would be a second register over one thing (W7); a program that regenerates it is not.*

---

## 1. The headline, over a denominator nobody chose after seeing the answers

| | **«K3»** (8, unseen) | `messung/fragmente/` (10, ours) |
|---|---|---|
| **transcribable with no wall** | **0 of 8** | not counted there |
| **parse with no reader refusal** | **2 of 8** | not counted there |
| **check with 0 errors** | **0 of 8** | **9 of 10** |
| **lower — `gabbro emit` writes C** | **0 of 8** | **9 of 10** |
| **run — emitted, compiled, EXECUTED, compared** | **0 of 8** | **9 of 10** |

The right-hand column is `zaehle-fragmente.py`'s own run on this branch's `master`
(`cfe411b`), quoted rather than restated:

```
$ ./instrumente/zaehle-fragmente.py
== Der vervollstaendigte Fragmentkorpus: 10 Dateien ==
  9 von 10 pruefen sauber
  9 von 10 senken ab
  9 von 10 sind DURCHGESTOCHEN -- F01, F02, F04, F05, F06, F07, F08, F09, F10
```

**9 of 10 against 0 of 8.** The two columns share the completion rule — excerpt plus exactly
the declarations it calls and does not name, said in every file's head — and they differ in
the one thing this exercise is about: the ten are *reproductions*, written **in Gabbro** by
this project's author out of `FRAGMENTE.md` (*"dieser Korpus ist NACHGEBILDET"*, its
`README.md`), and the eight are *transcriptions* of C that was written for a C compiler by
somebody who has never heard of Gabbro. **A reproduction cannot contain a construct its
author could not write.** That is the whole difference between 9 and 0, and it is the
difference trap 80 predicts.

> **And the same tool prints the honest lower bound beside it**, which is the figure over the
> ten BEFORE their declarations were added: *"5 von 10 sauber, 3 von 10 senkten ab -- und
> JEDES der sieben offenen trug mindestens einen korpusseitigen Riegel."* Even against that
> weaker comparator, «K3» is 0.

> **This is a good outcome for the exercise and a bad one for the claim.** Nothing was fixed
> to improve it, nothing under `crates/` moved after the measurement, and no fragment was
> swapped after it was seen.

### And the honest counterfactual, which is the strongest reading available

Two of the failures are **mine**, not Gabbro's: `effects` and `costs` clauses that the C does
not have and the language demands, which I wrote wrong. Repairing exactly those, and renaming
the identifiers the reader refuses (§3), gives:

```bash
ssh ki-pc-fisch-101 'cd gabbro-k3 && for f in /tmp/k3c/K0*.gab; do \
  ./target/debug/gabbro pruefe "$f"; done'
```

| | after both repairs |
|---|---|
| check with 0 errors | **1 of 8** — `K07` alone |
| lower | **1 of 8** — 1126 bytes of C |
| compile `cc -Wall -Wextra -Werror -O2` | **1 of 8** — exit 0 |

**And `K07` at 1 of 8 is still not `test_firmware_exit`:** two of its seven statements have
no Gabbro form and are absent, so what compiles never unregisters the misc device and never
prints the line. *The best case over an unseen corpus is one function out of eight, with two
of its statements deleted.*

---

## 2. Per fragment — the runs, verbatim

```bash
ssh ki-pc-fisch-101 'cd gabbro-k3 && export PATH=$HOME/.cargo/bin:$PATH && cargo build \
  && for f in messung/k3-fragmente/K0*.gab; do ./target/debug/gabbro pruefe "$f"; done'
ssh ki-pc-fisch-101 'cd gabbro-k3 && for f in messung/k3-fragmente/K0*.gab; do \
  ./target/debug/gabbro emit "$f" > /tmp/$(basename $f .gab).c; done'
```

| fragment | source | parse | check | lower | compile | walls |
|---|---|---|---|---|---|---|
| **K01** `allocinfo_start` | `alloc_tag.c:61-76` | **3 × `P002`** | 4 err, 1 hint | 0 B | — | 5 |
| **K02** `pool_pop_batch` | `debugobjects.c:198-222` | **4 × `P002`** | 5 err | 0 B | — | 7 |
| **K03** `copy_from_user_iter` | `iov_iter.c:44-71` | **1 × `P002`** | 1 err | 0 B | — | 2 |
| **K04** `lc_del` | `lru_cache.c:299-309` | clean | 1 err (`M137`) | 0 B | — | 4 |
| **K05** `percpu_ref_init` | `percpu-refcount.c:63-105` | **1 × `P002`** | 1 err | 0 B | — | 6 |
| **K06** `depot_pop_free_pool` | `stackdepot.c:361-393` | **3 × `P002`** | 7 err | 0 B | — | 6 |
| **K07** `test_firmware_exit` | `test_firmware.c:1555-1566` | clean | 1 err (`E010`, **mine**) | 0 B | — | 2 |
| **K08** `test_func` | `test_vmalloc.c:536-594` | **2 × `P002`** | 4 err | 0 B | — | 4 + 1 unmarked |

**37 walls over 8 fragments** — places where a C statement or declaration has no Gabbro form
and nothing was put in its place. Every fragment has at least two. The column counts the
markers in each file's BODY: `5 + 7 + 2 + 4 + 6 + 6 + 2 + 4 = 36`, plus the one the
measurement found and the file failed to mark (below).

```bash
for f in messung/k3-fragmente/K0*.gab; do
  echo "$f $(grep -o '\[WALL [0-9]*\]' $f | sort -u | wc -l)"; done
```

> *Two of my own bookkeeping slips, since they are in the frozen files and cannot be
> corrected there:* `K05`'s head tallies **`WALL 5`** and its body marks six (the tagged
> `percpu_count_ptr` field is described in the head's prose and left out of its count), and
> `K08` carries the unmarked wall below. **The bodies are the record; the heads' tallies are
> a summary and two of the eight are off by one.**

`gabbro emit` wrote **zero bytes** for all eight, so the compile column has nothing to run;
it is `0 of 8` because there was nothing to hand to `cc`, not because `cc` refused.

**Whose failure each error is, since that is the question a bare 0 does not answer:**

| | attributable to | fragments |
|---|---|---|
| a **wall** — no Gabbro form for the statement | Gabbro, structurally | all 8 |
| `P002` on a kernel-verbatim identifier | Gabbro, at the reader (§3) | K01 K02 K03 K05 K06 K08 |
| `R008` on a named space, the refused `u64(x)` | Gabbro, and they are **defects** (§4) | **neither shows in the frozen run** — both stand BEHIND a `P002`, in K03 and K08, and both are reproduced by a minimal probe in §4 |
| `M104`/`M101` on ordinary arithmetic | Gabbro, by design (§7) | K05 K06 K08 |
| `M119`, `M129`, `K003` | **consequences** of a wall three lines up | K02 K06 K08 |
| `E005`/`E008`/`E010`, `S006`, `P033`, `M137` on `~0` | **mine**, in clauses Gabbro demands and C has not — except `M137`, which is a correct refusal with a named cure | K01 K03 K04 K05 K07 K08 |

---

## 3. The finding nobody could have predicted: **the vocabulary collides with the kernel**

**`P002` — *"`node` is a word of the vocabulary, not an identifier"* — fires in six of the
eight fragments, on identifiers the kernel itself wrote.**

| fragment | the C identifier | where it is in C | what Gabbro uses the word for |
|---|---|---|---|
| K01 | **`node`** | `loff_t node = *pos;` (:64) | `walk … { node : [Pte; 512] }` |
| K02 | **`old`** | `hlist_move_list(struct hlist_head *old, …)` | `old(place)` in `ensures` |
| K02 | **`next`** | `struct hlist_node *last, *next;` (:200) | `next <label>` |
| K03 | **`progress`** | `size_t progress` (:45) | `progress <assumption>` at a loop |
| K05 | **`release`** | `percpu_ref_func_t *release` (:63) | the atomic ordering `release` |
| K06 | **`stack`** | `struct stack_record *stack;` (:364) | `entry … stack <ident>` |
| K08 | **`index`** | `int index, i, j, ret;` (:540) | `option index into T` |

Seven distinct words, **all seven verbatim from the kernel source**. (An eighth `P002` in
K02, on `None`, is on a name *I* shortened out of `ODEBUG_STATE_NONE` — it does not count.)

> **This is what an unseen corpus is for.** The ten fragments in `messung/fragmente/` never
> showed it, and could not have: their identifiers are German (`plaetze`, `wartet`,
> `hochlauf`), and a German identifier cannot collide with an English keyword table. **The
> corpus and the vocabulary were written by the same hand, so the vocabulary was never
> tested against a naming convention it did not choose.**
>
> The refusal is not wrong — the vocabulary is closed by decision (E1), and the message even
> offers a substitute. What is new is its **rate**: 221 keywords against C's naming habits
> give a collision in **6 of 8** ordinary functions, and the tree carried no estimate of that
> number at all.

**And it hides what is behind it.** Renaming exactly those seven, on throwaway copies:

```bash
ssh ki-pc-fisch-101 'cd gabbro-k3 && for f in /tmp/k3b/K0*.gab; do \
  ./target/debug/gabbro pruefe "$f"; done'
```

```
K01  4 errors -> 6       K03  1 error  -> 4       K05  1 error -> 3
K08  4 errors -> 16
```

*A reader refusal stops the body from parsing, and a body that never parsed declares no
names* — the checker says so itself, in its own summary line. **The one-error verdict on K03
and K05 is not a near miss; it is a measurement that stopped at the first token.** Same
family as the entry in `CLAUDE.md`: *a measurement that stops at the first hit measures the
wrong question.*

---

## 4. Two defects, found by foreign code, and NOT repaired

**Rule 3 of this lane: after the measurement nothing under `crates/` moves.** Both stand
here, reproduced by a minimal probe, and both are left alone.

### 4.1 `u64(x)` is refused, although the grammar says it is the conversion

```
$ cat /tmp/k3p/p1.gab
module p { pub fn f(a : u32) -> u64 effects { pure } costs <= 4 ops { return u64(a); } }

$ ./target/debug/gabbro pruefe /tmp/k3p/p1.gab
error: [P002] /tmp/k3p/p1.gab:1:78: `u64` is a word of the vocabulary, not an identifier
```

`SYNTAX.md`:588 marks `primary` with *"G9: kein `cast`"*, and :656-659 gives the reason:
*"`cast` war eine echte Teilmenge von `call` und aus der Grammatik nie eindeutig ableitbar.
Die Produktion entfaellt: ein `call`, dessen `path` einen Typ nennt, IST die Umwandlung."*
**The reader refuses that form at the token.** `pathseg` was widened to admit `u8 … u64` so that `u64::max` parses, and
the call head was not.

**So Gabbro today has no integer conversion of any kind.** No corpus file needed one —
`grep -n 'u64(\|u32(\|i32(\|u8(' beispiele/*.gab messung/fragmente/*.gab` finds **zero
sites** — which is exactly why a form that is documented and unreachable could stand.
`test_func` needs two, on lines 579 and 580, and they are the most ordinary lines in it.

### 4.2 A user-defined address space is unequal to itself

```
$ cat /tmp/k3p/p2.gab
module p {
extern fn g(p : ptr<user, r> u8) -> bool effects { pure } costs <= 4 ops;
pub fn f(q : ptr<user, r> u8) -> bool effects { pure } costs <= 8 ops { return g(q); }
}

$ ./target/debug/gabbro pruefe /tmp/k3p/p2.gab
error: [R008] /tmp/k3p/p2.gab:3:8: `f` passes `q` in space `user` to a parameter of `g`
       declared `user`
```

**The two spaces in the message are the same word.** The same file with `normal` instead of
`user` gives `0 errors, 0 hints`.

The cause is in the AST and is three lines wide: `Raum::Benannt(Ident)`
(`crates/gabbro-syntax/src/ast.rs`:311), and `Ident` derives `PartialEq` over
`{ text, span }` (:12-16). `R008` compares `if ist != soll` (`m3.rs`:288), so two occurrences
of one space name at two declaration sites are never equal. **The six built-in spaces are
fieldless variants and compare fine; every named one is broken.** `saetze.rs`:1383 says
`R013` inherits `R008`'s shape, so the same comparison is likely to sit there too.

> **What it costs is exactly the one thing K03 could do well.** `space = … | ident`
> (`SYNTAX.md` §3) lets `ptr<user, r> u8` say precisely what the kernel's `__user`
> annotation says — in the type, where the checker reads it, instead of in an annotation that
> needs `sparse` to see. That is the single best fit between Gabbro and any of the eight
> excerpts, **and it does not work.**

---

## 5. Where Gabbro could not say something — every place, quoted

Thirty-seven walls. Grouped by what is missing, with the count of fragments each blocks.

| missing | fragments | quoted from the excerpts |
|---|---|---|
| **`void *`** and the conversions into and out of it | K01, K02, K03, K05, K06 (**5**) | `priv = (struct allocinfo_private *)m->private;` · `size_t copy_from_user_iter(void __user *iter_from, …, void *to, void *priv2)` · `static void **stack_pools` · `void *current_pool;` · `union { void *object; struct hlist_node *batch_last; };` |
| **the address of a data place** — `&x` is a function value and nothing else (`M127`) | K01, K02, K04, K06, K07, K08 (**6**) | `codetag_next_ct(&priv->iter);` · `hlist_move_list(&src->objects, head);` · `next->pprev = &src->objects.first;` · `hlist_del_init(&e->collision);` · `list_move(&e->list, &lc->free);` · `atomic_long_set(&data->count, start_count);` · `INIT_LIST_HEAD(&stack->hash_list);` · `misc_deregister(&test_fw_misc_device);` · `synchronize_srcu(&prepare_for_test_srcu);` |
| **`NULL`**, and the test for it | K01, K02, K05, K06 (**4**) | `return priv->iter.ct ? priv : NULL;` · `last->next = NULL;` · `if (next)` · `data->confirm_switch = NULL;` · three `return NULL;` in `depot_pop_free_pool` |
| **`atomic` on a FIELD** — `atomicdecl` is an item, one per program | K02, K04, K05 (**3**) | `WRITE_ONCE(src->cnt, src->cnt - ODEBUG_BATCH_SIZE);` · `BUG_ON(test_and_set_bit(__LC_PARANOIA, &lc->flags));` + `clear_bit_unlock(…)` · `atomic_long_set(&data->count, start_count);` |
| **`union` as reinterpretation** | K02, K06 (**2**) | `union { void *object; struct hlist_node *batch_last; };` · `union handle_parts { depot_stack_handle_t handle; struct { u32 pool_index_plus_1 : …; }; };` |
| **`container_of` / `offsetof` / `typeof`** | K02 (**1**) | `obj = hlist_entry(head->first, typeof(*obj), node);` |
| **pointer arithmetic without a basis** | K03, K06 (**2**) | `to += progress;` · `stack = current_pool + pool_offset;` |
| **an asymmetric lock** — `locks L { … }` is a block | K01 (**1**) | `codetag_lock_module_list(alloc_tag_cttype);` on :67, released in another function. *The checker found this one by itself:* `hint: [H008] … CODETAG_MODULES protects [...] but is taken nowhere` |
| **a pointer-to-integer cast in either direction** | K05 (**2 sites**) | `ref->percpu_count_ptr = (unsigned long) __alloc_percpu_gfp(…);` · `free_percpu((void __percpu *)ref->percpu_count_ptr);` |
| **`__alignof__`** — `sizeof`, `lenof` and `aligned(e,c)` exist, no `alignof` | K05 (**1**) | `size_t align = max_t(size_t, 1 << __PERCPU_REF_FLAG_BITS, __alignof__(unsigned long));` |
| **a bit position in an ordinary `type` record** | K05 (**1**) | `bool force_atomic:1;` — `error: [C001] … a type record carries no bit position and no offset_into -- those are statements about a layout, and a format makes them` |
| **a string as a call argument**, and any variadic call | K07 (**1**) | `pr_warn("removed interface\n");` — *the most ordinary statement in the kernel* |
| **`continue` in a `traverse`** — `next` needs a label, `traverse` has no position for one | K08 (**1**) | `if (!((run_test_mask & (1 << index)) >> index)) continue;` |
| **an array literal**, hence no local array and no static table | K08 (**2**) | `int random_array[ARRAY_SIZE(test_case_array)];` · `static struct test_case_desc test_case_array[] = { … };` |
| **the return type of a function that may fail with a pointer** | K01, K06 (**2**) | `static void *allocinfo_start(…)` · `static struct stack_record *depot_pop_free_pool(…)` |
| **`~0U`** — `M137` refuses `~` over a literal | K04 (**1**) | `#define LC_FREE (~0U)` — and the message names the cure, `u32::max`. *A correct refusal, counted because the C form has no spelling* |

### The unmarked wall the measurement found

**K08 does not declare `test_case_array` at all, and its head does not say so.** The reason
is a wall — there is no array literal, so `static test_case_array : [TestCaseDesc; 13] = …`
has no right-hand side; `beispiele/64` initialises an array with a single scalar and
`beispiele/49` builds its dispatch record inside a function body. I failed to mark it, and
`K003` found it:

```
error: [K003] …:222:5: `test_func` promises costs, but the domain `elems of` of the
       traversal has no bound from a declaration
```

*Worth its own note:* an **undeclared** name under `elems of` produced a **cost** complaint,
not a name complaint. `M119` fires on the same name three lines lower, at an ordinary index.

### The one substitution, declared

K08's array walk runs over `test_case_array` where the C walks the shuffled `random_array`.
`random_array` is a wall (no array literal), so the walk had no subject; the file says in
bold that this is **a change to what the program does, not a rendering of it**. It is the
only place in the eight where something was put where a wall stands. Under the strict
reading K08 loses 25 further lines and the figures above do not move.

---

## 6. What went WELL, and it is not nothing

Counted with the same care as the walls, because a corpus that only accuses measures as
badly as one that only confirms.

| the C | Gabbro's own form | fragment |
|---|---|---|
| `mutex_lock(&m); … mutex_unlock(&m);` | `locks TEST_FW { … }` — released on every path by construction | K07, and **it lowers and compiles** |
| `__must_hold(&pool_lock)` / `lockdep_assert_held(&pool_lock)` | `requires Held(POOL_LOCK)` — one clause where C has a `sparse` annotation *and* a runtime check | K06 |
| `static size_t pool_offset __guarded_by(&pool_lock)` | `lock POOL_LOCK protects { pool_offset }`, and `H007` reads it | K06 |
| `data = kzalloc(…); if (!data) { … }` | `-> T or R` + `let x = f() else (e) { … }` — the same statement, «C3a» | K05 |
| `BUG_ON(!lc)` · `BUG_ON(!lc->nr_elements)` · `BUG_ON(i >= lc->nr_elements)` | a pointer with no null value · `u32 in 1 .. LC_MAX_ACTIVE` · the index rule | K04 |
| `BUG_ON(e->refcnt)` | `requires e->refcnt == 0` — the same move «K2»'s F5 made | K04 |
| `ARRAY_SIZE(x)` | `lenof(x)` — **not exercised in K08** (its array is a wall); verified separately: `static mut T : [u32; 13]` with `return lenof(T);` gives `4 items, 0 errors, 0 hints` | K08 |
| `while (!kthread_should_stop()) msleep(10);` | `forever … { if … { leave w; } … }` | K08 |
| `void __user *` | `ptr<user, r> u8` — **would be the best fit of all eight, and §4.2 says why it is not** | K03 |

**What was exercised and what was probed, apart.** Every row above except `lenof` stands in
one of the eight and was measured there: `locks TEST_FW { … }` in K07 (which lowers and
compiles), `requires Held(POOL_LOCK)` and `lock … protects` in K06 (no `H008`, so the lock is
taken), `let … else (e)` in K05 (the only complaint on it is `P033`, my stray semicolon after
the block), the four `BUG_ON` renderings in K04 (which draws no error but `M137`), and
`forever … leave` in K08 (whose only complaint is `S006`, my `on_exceeded`). *A row that
was not exercised is marked as one.*

**Four of the six `BUG_ON`s in `lc_del` are exactly the class «K2» said Gabbro replaces**,
and this is the first time that claim met a foreign `BUG_ON` nobody picked for it. It holds.
The fifth is not an assertion at all — it takes a bit lock — and that is §5's third row.

---

## 7. What M1 costs on foreign arithmetic, measured

**Eight sites** over three fragments, and none of them is exotic:

```
K06  `pool_offset + size > DEPOT_POOL_SIZE`        u64 + u64  leaves the width   [frozen run]
K06  `pools_num - 1`                               i32 - 1    leaves the width   [frozen run]
K06  `pool_offset += size`                         u64 += u64 leaves the range   [frozen run]
K05  `start_count += 1`                            u64 += 1   leaves the range   [behind P002]
K08  `t->data[index].test_passed  += 1`            i32 += 1   leaves the range   [behind P002]
K08  `t->data[index].test_xfailed += 1`            i32 += 1   leaves the range   [behind P002]
K08  `t->data[index].test_failed  += 1`            i32 += 1   leaves the range   [behind P002]
K08  `j += 1`                                      u32 += 1   leaves the range   [behind P002]
```

*Three of the eight show in the frozen run; the other five stand behind a `P002` and appear
in the renamed copies of §3. They are marked, not merged.*

```
$ cat /tmp/k3p/p3.gab
module p { pub fn f(a : u32) -> u32 effects { pure } costs <= 4 ops
         { let mut b = a; b += 1; return b; } }
$ ./target/debug/gabbro pruefe /tmp/k3p/p3.gab
error: [M104] `b` += leaves the range: `u32` against `u8 in 1 .. 1`
error: [M101] the assignment requires `u32`, the value has `u32 in 1 .. 4294967296`
```

**An ordinary counter increment on a plain `u32` is a compile error.** That is M1 working
exactly as designed and stated — *"the overflow is a compile error, not a runtime check"* —
and the price was never measured against code that did not carry range types from birth.
**Five of the eight sites are `x += 1` on a field or a local.** Every one of them would need a
range on the DECLARATION, and in `test_case_data` those declarations are the kernel's.

*This is the plumbing claim's strongest and most expensive form in one place:* Gabbro is
right that C's silent wrap is a bug surface, and the cost of saying so is a range annotation
on every counter in the tree.

---

## 8. What this does and does not settle

**It settles trap 80 for K100's second gate, in the direction nobody wanted.** There is now a
corpus assembled by a rule stated before the cut, frozen in a commit before any measurement,
over code from an author line this project has never touched — and Gabbro handles **0 of 8**
of it, against **9 of 10** of the corpus we chose. The ten were measuring our selection, and
the distance is now bounded below by that gap.

**It does not settle how Gabbro would do on a kernel written for it.** Every wall in §5 is a
statement about *transcribing existing C*, and several of them — intrusive lists, `void *`,
`container_of` — are things the language refuses on purpose, with reasons written down long
before this corpus existed. *A corpus of foreign C measures portability, not fitness*, and the two are
not the same question. What it does establish is that the first one has an answer now, and
that the answer is not the second one's.

**Three things in it are repairs and not refusals**, and they are the ones worth acting on
first, in some later lane and not this one:

1. `u64(x)` — a documented form the reader cannot read (§4.1);
2. `R008` on a named space — a `PartialEq` over a span (§4.2);
3. `P002`'s rate against C naming — not a bug, and a number the tree did not have.

**Nothing under `crates/` was touched after the measurement**, and that is checkable:

```bash
git diff --stat 61a1b35 HEAD -- crates/     # empty
```
