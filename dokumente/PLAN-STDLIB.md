# The standard library, native in Gabbro — the plan

*Simon's decision, 2026-09-16: **everything a standard library does, except networking, files,
graphics and windows, is to be written in Gabbro itself.** Not as `extern` declarations with a
named assumption, not as C behind a border — as Gabbro modules the checker checks and the goal
theorem covers.*

The decision came out of a measurement, not a wish: a Linux firewall was written in Gabbro
(`/home/ubuntu/brandmauer`, 7494 lines in eight modules), and it ran — a netlink socket opened,
memory mapped, the worker parked in `recvfrom`, every system call issued from Gabbro. What it
kept hitting was not the language's semantics but its **empty shelf**: no memory copy, no ring
buffer, no queue, no timer wheel, no strings, no hash, no sort.

---

## 0. Scope — what is in and what is out

**In**, because a systems program needs it on every page:

| layer | what |
|---|---|
| **L1 primitives** | copy / set / compare over table slices; endianness; bit operations (count, scan, mask); saturating and wrapping helpers; min / max / clamp; integer `log2`, `sqrt`, division helpers |
| **L2 containers** | ring buffer (SPSC and MPSC), stack, bitset, fixed hash map and set, sorted array with binary search, index-linked list, **timer wheel** |
| **L3 algorithms** | sort (insertion, heap) over a fixed table; binary search; hashing (FNV, sip-like); CRC and Internet checksum |
| **L4 text** | byte strings over tables: length, compare, find, split; number formatting (decimal, hex) and parsing, both without allocation |
| **L5 time and concurrency** | monotonic clock; durations; sleep; the ticket lock; futex wait/wake; sequence lock; epoch-style reclamation |
| **L6 randomness** | a counter-based PRNG, and entropy from the kernel through a system call |

**Out, by Simon's line:** networking, files, graphics, windows. Those are I/O against a
world with its own rules; they stay system calls at the program's own border, declared where
they are used.

*Note what "out" does NOT mean: the firewall's netlink work stays in the firewall. The library
gives it the ring buffer and the checksum, not the socket.*

---

## 1. The blocker, and it comes first: composition across units

**Measured 2026-09-16, in the firewall:** a module that wants to read another module's table is
refused — `[M119] Kopf is declared nowhere` — and the honest workaround is an `extern fn` mirror
with a C-identical prototype **plus a named assumption per crossing**. `use` parses and reaches
nothing (it is one of the grammar census's uncovered forms). `pub` is dropped by the exporter as
a unit-boundary rule the model has no boundary for.

So today a "library" would be: modules whose functions the consumer re-declares by hand, and
whose guarantees enter the consumer as assumptions. **That is the opposite of what a standard
library is for.** Nothing below is worth building until this is answered:

1. **What does a unit see of another unit?** Public functions with their contracts, certainly.
   Tables — read-only? at all? The firewall wanted the decoded header; the honest answer may be
   "never a table, only functions", and then the library's shape follows from it.
2. **Who checks the crossing?** Today: nobody, and an assumption stands in. It must be the
   checker, over both units, or the linking theorem, over both certificates.
3. **What does the goal theorem say about two units?** `Spec.lean`'s NOT CLAIMED list names
   linking of separately compiled units. The linking theorem (PLAN-ZIELSATZ §10) is the same
   item seen from the proof side, and these two must be planned as one.

**Until this lands, every library module is a single-unit island**, and the plan below is
written so that each layer is useful as an island and better once the islands are bridged.

---

## 2. The generic question, and it is the second blocker

A ring buffer holds *something*. Gabbro's tables are concrete: `count` is fixed and the slot
record is written out. There is no type parameter, so a ring of `u32` and a ring of a 4-field
record are two modules today — and the counter lane already measured what that costs when it
had to write 256 scalars instead of one array: **5136 lines instead of 287, and 1797 ops instead
of 11.**

Three routes, and this is decided by measurement before anything is built:

* **(a) per-type instantiation by hand** — honest, and it multiplies the library by the number
  of element types. Measure: how many types does a kernel actually need?
* **(b) a generator** — a small tool that writes the module from a description. The checker
  still checks the result, so nothing is weakened; the cost is a second artefact in the tree and
  a guardian that the generated file is what the generator writes (the precedent exists:
  `pruefe-genlean.py`).
* **(c) a type parameter in the language** — the largest change, and it touches the model:
  `Ty` is deliberately non-recursive, and a parametrised table is a new shape in every pass and
  in `Akzeptiert`. **The product-former lane refused exactly this kind of change on measurement
  (`OFFEN.md` O15), and the same rule applies here: it must pay for itself in programs.**

---

## 3. What every library item owes

This is a standard library for a language whose point is that a user proves only their own
logic. So each item carries more than code:

1. **A contract** — `requires`/`ensures` that say what it does, not how.
2. **A proof obligation discharged once**, not per user: the item's own `ensures` proved against
   the model, so the caller inherits it. *That is the whole economic argument of the language,
   and the library is where it is either true or empty.*
3. **A cost bound** the checker holds it to, because a kernel's scheduler needs it.
4. **A poison probe and a positive probe**, like every rule in this tree.
5. **The named absence**, where an item cannot carry what a C library would: no allocation, no
   unbounded recursion, no growth.

---

## 4. Order

1. **Composition** (§1) — otherwise the library cannot be used.
2. **The generic question** (§2) — otherwise the library is written N times.
3. **L1 primitives**, because everything else stands on them, and because they are where the
   bound checks live.
4. **L5 concurrency** next, not last: the runtime (TODO §0) needs the lock and the futex, and
   the runtime is the top priority.
5. **L2 containers**, starting with the ring buffer and the timer wheel — the two things the
   firewall and any driver need first.
6. **L3, L4, L6** after that, in the order programs ask for them.

---

## 5. Where it lives

`bibliothek/` in this tree, one module per file, with its probes beside it, and a guardian that
every module checks, emits and compiles — the same bar the corpus carries. **It is not a
separate project**: a standard library that is not measured by the same instruments is a
promise, not a library.
