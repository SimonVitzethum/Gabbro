# «K3», a THIRD reading — 2026-09-05, after the vocabulary stopped colliding

**The first reading is [`K3-BEFUND.md`](K3-BEFUND.md), and it stands. It is 0 of 8, and it
remains the honest one.** The second is
[`K3-ZWEITE-LESUNG-2026-09-04.md`](K3-ZWEITE-LESUNG-2026-09-04.md), taken after two repairs
that the first reading found and could not move the number, *because the fragments that would
show them were gated by a third defect the first reading had also named and left alone.*

**That third defect is what this lane removed.** `K3-BEFUND.md` §3:

> *"`P002` — `node` is a word of the vocabulary, not an identifier — fires in six of the eight
> fragments, on identifiers the kernel itself wrote. … **And it hides what is behind it.** A
> reader refusal stops the body from parsing, and a body that never parsed declares no names."*

The eight files are byte-identical to the commit that froze them. The measurement, the
decision and the price of the alternatives are in
[`WORTSTELLUNG.md`](WORTSTELLUNG.md); this document is only the reading.

```bash
git diff --stat 61a1b35 HEAD -- messung/K3-AUSWAHL.md messung/k3-fragmente/   # empty
for f in messung/k3-fragmente/K0*.gab; do ./target/debug/gabbro pruefe "$f"; done
for f in messung/k3-fragmente/K0*.gab; do ./target/debug/gabbro emit  "$f" | wc -c; done
```

---

## 1. The headline

| | first reading | third reading |
|---|---|---|
| transcribable with no wall | **0 of 8** | **0 of 8** |
| **parse with no reader refusal** | **2 of 8** | **7 of 8** |
| check with 0 errors | **0 of 8** | **0 of 8** |
| lower — `gabbro emit` writes C | **0 of 8** | **0 of 8** |
| run | **0 of 8** | **0 of 8** |

> ## **The number is still 0 of 8, and that is the honest headline.**

The one fragment that still meets a reader refusal is **K02**, and the word is `None` — a name
the transcriber shortened out of `ODEBUG_STATE_NONE`, not one the kernel wrote. `None` is one
of the seventeen words that stay reserved. *The collision with the kernel's naming is gone;
the collision with the transcriber's own abbreviation is not, and it never was the finding.*

`gabbro emit` writes **zero bytes for all eight**, so the compile and run columns still have
nothing to hand to `cc`. Every fragment still carries at least two **walls** — places where a
C statement has no Gabbro form and nothing was put in its place — and a wall is not something a
reader change can touch.

---

## 2. What the eight now say, against what they said

```
                             items   errors  hints        P002
K01 allocinfo_start        15 -> 15   4 -> 6  1 -> 1      3 -> 0
K02 pool_pop_batch          8 ->  9   5 -> 2  0 -> 0      4 -> 1
K03 copy_from_user_iter     6 ->  7   1 -> 2  0 -> 0      1 -> 0
K04 lc_del                 13 -> 13   1 -> 1  0 -> 0      0 -> 0
K05 percpu_ref_init        16 -> 17   1 -> 3  0 -> 0      1 -> 0
K06 depot_pop_free_pool    10 -> 10   7 -> 7  0 -> 0      3 -> 0
K07 test_firmware_exit     12 -> 12   1 -> 1  0 -> 0      0 -> 0
K08 test_func              31 -> 31   4 ->13  0 -> 1      2 -> 0
                          ---------  -------  ------      ------
                          111 -> 114 24 ->35  1 -> 2     14 -> 1
```

**Three more declarations parse, fourteen `P002` became one, and the error count rose from 24
to 35.** That last figure is the point of this reading: *the collision was not costing
diagnostics, it was hiding them.*

Every diagnostic, first reading against third:

```
  E005     0 ->   7     a write that appears in no effect
  E008     0 ->   1     a declared effect narrower than a callee's
  E009     0 ->   1     call effects undecidable (hint)
  E010     2 ->   2     a read that appears in no `reads`
  H008     1 ->   1     a lock that protects and is taken nowhere (hint)
  K003     1 ->   1     a cost promise over an unbounded traversal
  M101     1 ->   6     the assignment requires the declared type
  M104     3 ->   8     arithmetic leaves the range or the width
  M119     1 ->   3     a name declared nowhere
  M129     0 ->   1     a call through something that is not a function pointer
  M137     1 ->   1     `~` over a literal
  P002    14 ->   1     a word of the vocabulary in a name position
  P033     0 ->   1     a `;` too many after a block
  R002     0 ->   1     a write through a pointer that carries no `w`
  S006     1 ->   2     `on_exceeded` names a function that returns
                       ------
                 25 ->  37
```

---

## 3. What became visible, and it is worse than what the collision was hiding

### 3.1 Twenty-five diagnostics appeared where thirteen `P002` vanished

The net `+12` is the wrong figure to read, because two things happened at once. The gross
movement:

| appeared | | class |
|---:|---|---|
| **10** | `M104` +5, `M101` +5 | M1 on ordinary arithmetic — §3.2 |
| **9** | `E005` +7, `E008` +1, `E009` +1 | the effect clause — below |
| **3** | `M119` +2, `M129` +1 | a wall, named at its site instead of in prose — §3.3 |
| **2** | `P033` +1, `S006` +1 | the transcriber's own — a stray `;`, an `on_exceeded` that returns |
| **1** | `R002` +1 | a true statement about the excerpt — §3.4 |
| **−13** | `P002` 14 → 1 | the mask |

**The effect family is the largest new class, and six of its nine are wall consequences —
which is the honest reading and not the alarming one.** Of the seven `E005`:

```
K01  priv->print_header = true;               E005   `priv` is unbound  -- WALL 4 (void *)
K01  priv->iter = codetag_get_ct_iter(...);   E005   `priv` is unbound  -- WALL 4
K01  priv->iter = priv->reported_iter;        E005   `priv` is unbound  -- WALL 4
K06  stack->handle.pool_index_plus_1 = ...    E005   `stack` is unbound -- WALL 5
K06  stack->handle.offset            = ...    E005   `stack` is unbound -- WALL 5
K06  stack->handle.extra             = ...    E005   `stack` is unbound -- WALL 5
K03  iter_from = mask_user_address(iter_from) E005   a BOUND parameter  -- a real miss
```

Six of them write through a name a wall left unbound; they are the same wall the fragment
header already described, now with a site and a code. **One is a genuine effect-clause miss**
— `copy_from_user_iter` declares `reads iter_from` and line 53 assigns to it — and `R002`
stands beside it saying the same thing about the pointer's rights.

`K3-AUSWAHL.md` §5 marked the class in advance and could not size it: *"`effects` and `costs`
are added at every function, because the language refuses a function without them. The C has
no such clause, so this is not transcription — it is what Gabbro demands of anything that is
to be a function at all."* Sized now, on eight functions nobody chose: **one miss and one
hull complaint (`E008`, K01) that the author wrote wrong, plus two `E010` the first reading
already had.** *That is a real price and a modest one — and it is now a measurement instead of
an unexamined charge to "mine".*

### 3.2 M1's eight arithmetic sites: `K3-BEFUND.md` §7 predicted all eight, and all eight are here

That section listed eight sites and marked five of them *"behind `P002`"*, visible only on
renamed throwaway copies. **All five are now in the frozen run**, and the count matches
exactly: `M104` 3 → 8.

```
K06  pool_offset + size > DEPOT_POOL_SIZE   u64 + u64    [frozen in the FIRST reading]
K06  pools_num - 1                          i32 - 1      [frozen in the FIRST reading]
K06  pool_offset += size                    u64 += u64   [frozen in the FIRST reading]
K05  start_count += 1                       u64 += 1     [was behind P002 -- now frozen]
K08  t->data[index].test_passed  += 1       i32 += 1     [was behind P002 -- now frozen]
K08  t->data[index].test_xfailed += 1       i32 += 1     [was behind P002 -- now frozen]
K08  t->data[index].test_failed  += 1       i32 += 1     [was behind P002 -- now frozen]
K08  j += 1                                 u32 += 1     [was behind P002 -- now frozen]
```

*A prediction made from renamed copies and confirmed on the frozen files is the strongest form
this exercise has produced.* Five of the eight are `x += 1` on a field or a local, and every
one would need a range on the DECLARATION — in `test_case_data` those declarations are the
kernel's.

### 3.3 Three walls got a diagnostic instead of a prose note

`M119` 1 → 3, `M129` 0 → 1. All four are **consequences of a wall**, and that is worth saying
because it is the first time the checker names them rather than the fragment's own header:

| | |
|---|---|
| `K01:160 priv is declared nowhere` | WALL 4 — `priv = (struct allocinfo_private *)m->private;` has no Gabbro form, so `priv` is unbound, and the file's header said so in prose. The checker says it now |
| `K02:132 obj is declared nowhere` | the `hlist_entry(..., typeof(*obj), node)` wall, same shape |
| `K08:259 test_case_array is declared nowhere` | the unmarked wall the FIRST reading found by `K003` alone — now also named where it is used |
| `K08:253 test_case_array[…].test_func is not a function pointer` | the array-literal wall reaching the call site |

### 3.4 One finding that is about the C and not about Gabbro

**`K03: R002 — `iter_from` is written, but the pointer carries no `w`.`** The transcription
declares `iter_from : ptr<user, r> u8`, faithfully to `const void __user *from`; and line 65
of `iov_iter.c` is `to += progress;`, which the transcription rendered onto `iter_from`. The
transcription's own header booked this as `OPEN 1 — assignment to a parameter (line 53), the
grammar permits it and no pass held it`.

*A pass holds it now* — not because anything moved in `m3.rs`, but because the body parses.
`R002` and the `E005` beside it are the two halves of one true statement about the excerpt.

### 3.5 K02 is the one that got better, and by more than half

**5 errors → 2.** With `old` and `next` readable, `pool_pop_batch` has exactly two complaints
left: the transcriber's `None`, and `obj` behind the `typeof` wall. That is the closest any of
the eight has come to a clean check — and it is still not one, and it still lowers to nothing,
because `union { void *object; struct hlist_node *batch_last; }` has no Gabbro form.

---

## 4. What this settles and what it does not

**It settles that the collision was a mask and not a cost.** 14 `P002` became 1, 24 errors
became 35, and the twenty-five diagnostics that appeared are all true statements about the
eight excerpts — ten on arithmetic Gabbro refuses by design, nine in the effect family (six of
them a wall named at its site), three more walls named at their sites, two the transcriber's
own, one about the excerpt itself. *The first reading's 0 of 8 was correct, and its
per-fragment error counts were an undercount, in the direction the mask predicted.*

**It does not move the headline, and nothing in this lane was ever going to.** `emit` writes
zero bytes for all eight because all eight carry walls, and a wall is `void *`, the address of
a data place, `NULL`, `container_of`, a `union` as reinterpretation, an array literal, a
string as a call argument. Those are `K3-BEFUND.md` §5's thirty-seven, they are structural, and
several of them are things Gabbro refuses on purpose with reasons written down long before this
corpus existed.

**What a fourth reading would need in order to move it** is not another reader change. On the
evidence of §3 the ranking is now measurable rather than guessed, and it is:

1. **the walls — thirty-seven of them, and they are the whole of the 0.** Six of the seven new
   `E005`, both new `M119` and the `M129` are a wall showing through, and the emit column is
   zero for all eight because of them. `void *` blocks five fragments, the address of a data
   place six.
2. **a range on every counter** — five of the eight `M104` sites are `x += 1`, and the
   declarations that would have to carry the range are the kernel's.
3. **the effect clause, and it is smaller than it looked** — one genuine miss and one hull
   complaint over eight functions.

*The order of those three is the yield of this reading. On 2026-09-04 the corpus could not put
them in any order at all, because eleven of the twenty-five diagnostics that decide it were
behind a word.*
