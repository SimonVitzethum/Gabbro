# For Caprock, not for Gabbro

> **Findings that arose in this folder and whose subject is Caprock.**
> Taken out of [`../TODO.md`](../TODO.md) on 2026-08-16: *a task list that runs two projects
> sorts for neither.* **Not deleted — they are findings, just not ours.**
>
> Measurement base throughout: `SEL4Lake/SEL4Lake` @ `arch/x86_64`, commit `a1bf707`.

---

## N1 — the two lock orders contradict each other · **resolved, proposal stands**

`kernel/src/system.rs:11–13` states `… → SCHEDS[*] (R2) → Heap.inner (R3) → MEM (R4,
innermost)` and adds **"`MEM` never holds another lock"**. Line `:724` states
`CAPS < {EPS[i], NTFNS[i], MEM} < SCHEDS[*] < FP_STATES` — there `MEM` has something **below**
it.

**Measured (2026-08-15):**

| Question | Answer |
|---|---:|
| `MEM` holders that take another lock | **0** of 54 |
| holders of outer locks that take `MEM` afterwards | **2** — both `CAPS` (`space.rs` path, `system.rs:2495`, `:2509`) |
| nestings of `MEM`/`SCHEDS`, in either direction | **0** |

> **`MEM` is a leaf. The header describes the code; `:724` is wrong.**

**Proposal** (not carried out — Caprock was not modified):

```
// Lock order (outer->inner): CAPS < {EPS[i], NTFNS[i]} < SCHEDS[*] < FP_STATES < MEM.
// MEM is a leaf (R4) and never holds another lock -- measured: 0 of 54 acquisition sites.
```

## N2 — which atomics take part in the order?

`system.rs:725` lists `FP_OWNER` as an **atomic tender** of the lock order: the reschedule path
holds `SCHEDS[core]` "+ atomic `FP_OWNER`", and the atomic is **explicitly part of the deadlock
argument**.

**Open:** the full ordering count needs a column *"order participant"*. Which atomics those are
decides whether they belong in the pairing or in the lock order — and `FP_OWNER` today appears
in **neither** of the two documented orders, although the argument relies on it. **A third
version of the same thing, this time incomplete.**

## K1–K3 — extend the ordering protocol by the removals

These are **removals, not refutations**:

* **K1** — under a lock the atomic falls away; part of the 2 231 sites disappears.
* **K2** — the inside of a construct counts towards the template surface instead of the sample.
* **K3** — `accumulates` with a record is **strictly better than the original** at
  `caprock-sync:572-592`.

## Eager FP per architecture or global

Corrected: **on x86 it is eager** (`system.rs:1215`, with exactly the CVE justification),
**lazy is the aarch64 path**. So the decree hits the other architecture, where the argument
does not apply in the same form.

> **Blocked, and not for reasons of time:** the only aarch64 tree in the folder is **not a
> second kernel** but an older snapshot of the same lineage (`git log --follow`: `R099`, a
> rename with 99 % similarity). See [`MESSUNGEN.md`](MESSUNGEN.md), *Die aarch64-Lücke*.

## Two plumbing obligations that remain open

One refutation of the criterion each, at their own site:

1. `self.queues[p]` after `31 - leading_zeros()` (`caprock-sched/src/lib.rs:1996`) — needs the
   **data-structure invariant** to discharge the index obligation. Pure plumbing, and today not
   solvable by construction.
2. **Every refinement lemma**, should the lowering not be flat enough.

## Progress / starvation (D8)

Falls under **none** of the mechanisms M1–M4. Open whether it stays that way or whether it
would need a sixth — *but that is a question for Caprock's scheduler guarantees, not for
Gabbro's type system.*

---

## What is NOT here

The `2 231 publishes` sites and the base rate stay in Gabbro's lists: they measure **against**
Caprock, but they answer a question **about Gabbro** — does the construct carry the load, and
is the trap frequent enough to justify a language. *The difference is whose decision hangs on
it in the end.*
