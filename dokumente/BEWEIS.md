# Gabbro — the proof architecture

**What is proved, what it speaks about, who discharges it, and where it is lowered to.**
Drawn together on 2026-08-14 from six separate files — text unchanged.

---


---

# The criterion — logic only

## The criterion: **prove logic, nothing else**

**2026-08-13.** Up to here the goal was a **number** (0,5 : 1). It is a proxy, and proxies are a
paid-for trap in this project. The actual criterion is a **kind**, not a quantity:

> **Whoever proves a Gabbro program proves the LOGIC of their program — and nothing else.**
> Everything else falls out by construction.

**Even 2 : 1 would be good if the counted lines are logic.** And 0,5 : 1 would be a failure if
hand-written range checks sit inside it. **The number thereby turns from the goal into the
diagnosis.**

---

### The dividing line, and it has to be sharp

> **An obligation is PLUMBING if its statement mentions only the MACHINE.
> It is LOGIC if it mentions the SUBJECT.**

| **Plumbing — must fall by construction** | **Logic — you write it, in every language** |
|---|---|
| an index lies in range | "the tree stays a tree" |
| no over-/underflow | "the refcount is the number of references" |
| no alias, no borrow violation | "the message arrived at the right thread" |
| frame condition: what is **not** touched | "after `revoke`, `s` has no descendants" |
| the lock is held, the order is right | "an exhausted thread does not run" |
| no data race | "the colouring separates the tenants" |
| the loop ends because the set is finite | the loop ends because **the algorithm** makes progress |
| the refinement source ↔ C | — |
| the well-formedness of a data structure after a **generated** mutation | the **formulation** of the invariant |

**The borderline case is termination**, and the rule decides it: "ends because it runs over a
finite set" names only the machine — **plumbing**. "Ends because the scheduler makes progress"
names the subject — **logic**, and it belongs written down.

---

### The first DISPUTED case, and it is not termination *(2026-08-21)*

Termination is the borderline case the rule **decides**. Here is one it does not, and it is a
real site in foreign code, not a construction: **`caprock`, the reclaim of a dying thread's
kernel stack.** *(`../caprock-messbasis`, branch `arch/x86_64`, read-only —
`crates/caprock-sched/src/lib.rs`:183-197 and :1973-1983.)*

```rust
// `record_zombie` legt die Stack-Region des Sterbenden in den Zombie-Ring; von dort gibt SIE JEDER
// Kern per `reap_core` an den Allokator zurueck [...]. Beim Selbst-Ende (`exit_current`) ist das
// aber genau die Region, auf der der Kernel in diesem Moment noch rechnet: der Trap-Handler laeuft
// auf SP_EL1, und das ist bei einem EL1-Thread SEIN Stack. Zwischen `record_zombie` und dem
// `mov sp, x0` des Vektor-Epilogs darf ein fremder Kern die Region also holen [...]
```

**The obligation is:** *when the region enters the zombie ring, no core is still executing on
it.*

**Apply the rule literally, and it says PLUMBING.** The sentence mentions cores, a stack, a
memory region, a moment — the machine, and nothing else. No subject-matter concept appears; you
could not tell from it whether this kernel schedules threads or routes packets. It is the same
family the table already books as plumbing: *no alias*, *frame condition: what is not touched*.

**And it cannot fall by construction.** The last reader stops being one at `mov sp, x0` in the
vector epilogue — an instruction below every type system, in a window that opens *before* it and
closes *after*. There is no ownership discipline that reaches it, because the holder of the
reference is the hardware stack pointer.

**What caprock actually does is the sharpest part of the case.** It does not discharge the
obligation. It **counts the opportunity** — `ZOMBIE_UNTER_FUESSEN`, incremented when the current
frame lies inside the region just released for pickup — and it records that a canary at the
bottom of the region found *"0 Diebstaehle"* over **4295 windows in 108 runs** before being
removed.

> That is an assurance drawn from the **absence of a refutation** — **R15** and **W10**, in real
> kernel code, written by people who knew exactly what they were doing and had nothing better
> available.

#### The decision

**The dividing line holds. What breaks is a second claim that was riding on it unstated:** that
*plumbing* and *must fall by construction* are the same set. They are not.

| | discharged by | |
|---|---|---|
| **logic** | the programmer writes the proof | as before |
| **plumbing** | falls by construction | as before |
| **plumbing that CANNOT fall** | **nobody — it is named, and counted** | *the third outcome* |

The third row is not a loophole; it is what the **axiom layer** has been all along, and it is why
that layer is countable and ratchetable rather than a footnote. *This case belongs in it, beside
`release_stellt_sichtbarkeit_her` and `sperrabdruck_haelt_fremde_kerne_fern`.*

#### Does the abort condition fire?

The abort condition reads: *"a **named** plumbing obligation remains **that the programmer has to
discharge by hand**."* Here the programmer discharges nothing by hand — **nobody discharges it at
all.** It is assumed, named, and counted. **So it does not fire.**

**But only because the axiom layer exists.** Without a place to name such an obligation, this
site would be exactly the thesis-ending shape: a plumbing obligation, left to the programmer, in
the one language construct that was supposed to make plumbing disappear. *The escape is not that
the case is mild — it is that the layer it lands in is finite, named and ratcheted.*

Gabbro's answer to this specific site is **`H015`** (built 2026-08-21): a `rcu … reclaims` now
**demands** a named grace-period assumption, the way `S003` demands one at `progress`. It is worth
being precise about what that buys, because it is less than it sounds: *the assumption is named,
not established.*

> **And the residue is measured, not estimated.** Of the 27 assumptions in the corpus that name a
> falsifier, **none exists as a runnable probe** — see [`messung/AXIOMSCHICHT.md`](../messung/AXIOMSCHICHT.md).
> Naming is not discharging, and the axiom layer is where that debt is visible instead of
> dissolved.

*Where a static check **can** reach, caprock reaches:* `crates/caprock-sync/src/lib.rs`:198-206
turns the IRQ-masking assumption into a `const _: () = assert!(…)` that fails the build on a
bare-metal target without masking. **That is the line.** Findings of the kind above lie on the
far side of it, and the criterion's job is to say so out loud rather than to count them as
plumbing that will one day fall.

---

### What that does to the existing measurements

**The numbers stay, their reading changes** — and both measurements are consequently **not yet
broken down**. That is the next paper step, not a claim:

| Measurement | Number | **open: which share is logic?** |
|---|---|---|
| `delete_leaf` (checker) | ~~3,6–6 : 1~~ **unevidenced, replaced by 1,75 : 1** (2026-08-15, breakdown below) | chain finiteness and index bounds are **plumbing** and would have to fall; `child_points_back` and `refcount_matches` are **formulations of invariants**, i.e. logic |
| `Endpoint::call` (designer) | 1,8–2,3 : 1 | `msg_copied` is **logic** and was bound to nothing (G2); the missing `locks` effect (G3) is **plumbing** that should never have arisen at all |

- [ ] **Break both measurements down into logic/plumbing.** Only then do they say anything about
      the criterion. **A number without that split is from now on not a measured value.**

---

### The abort condition gets sharper, not softer

Until now: *"above 3 : 1"* — a number, measurable only once there is a compiler.

**Now:** *"a **named** plumbing obligation remains that the programmer has to discharge by
hand."*

That is **checkable on paper, per construct**, and thereby incomparably cheaper. Every such site
is either a missing construct or the end of the thesis.

**Two of them already stand there today, both from the paper tests:**

1. **`self.queues[p]` after `31 - leading_zeros()`** (`caprock-sched/src/lib.rs:1996`) needs the
   data-structure invariant in order to discharge the index obligation. **Pure plumbing** — and
   today not covered by construction. Either M1 carries it, or the criterion is violated at this
   site.
2. **The refinement**, if the lowering is not flat enough. It never mentions the subject and is
   therefore plumbing by definition — every refinement lemma is a breach.

---

### Why the criterion is better than the number

* **It is decidable per construct**, without a compiler and without a corpus.
* **It cannot be flattered by short false promises** — the finding from
  [`MESSUNGEN.md`](MESSUNGEN.md) loses its force, because what counts is no longer the
  **quantity** but the **kind**. A false `ensures` is logic that is false; it does not make the
  number better.
* **It says what Gabbro is**, in one sentence you can refute: *everything except the logic falls
  out by construction.* Whoever finds a plumbing obligation that stays hanging has refuted the
  sentence at that point — and at the same time said which construct is missing.
* **It makes the number honest:** 2 : 1 of pure logic is a success. 0,5 : 1 with hand-written
  range checks is not.

---

### What it does not mean

* **The dividing line is a decision, not a law of nature.** "Mentions only the machine" is sharp
  enough for the cases above and will have to be argued over at some borderline case. **The
  disputed case then belongs here, not in a footnote.**
* **It does not replace the measurement, it orders it.** Without the breakdown every number stays
  what it was before: a proxy.


---

# The gaps between proof obligation and Gold

## What Gabbro lacks for GOLD — apart from the logic proof and the expressive power

**2026-08-14.** Two items are explicitly **not** meant: the **logic proof** (the programmer
writes that, in every language) and the **expressive power** (that all programs, above all
Caprock, fit inside — that is the running backlog, see `PLAN.md` A3/A5/A6/A7).

**What is left when you take both away?** The answer is uncomfortable and short:

> **Gabbro produces proof obligations. There is nothing that discharges them, and nothing they
> speak ABOUT.**

A proof obligation needs three things: a **language**, a **model** in which it has a meaning, and
a **prover**. Gabbro has the language — half of it. Model and prover it does not have at all.

---

### L1 — A MACHINE MODEL. **Designed on 2026-08-14** ([`BEWEIS.md`](BEWEIS.md)): 106 axioms, ~130 names — and the 20 arch-neutral families already stand in `caprock-hal/*/cpu.rs`

#### The original version of the gap

`axiom write_cr3(p: Pa) effects { writes tlb, writes active_table }` names an **effect on a state
that does not exist.** There is no `tlb`, no `active_table`, no machine state — only a word in an
effect list.

**With that it is not sayable today what a privileged instruction DOES**, only that it touches
something. But a Gold proof over a kernel is at its core a proof **over machine states**: "after
`write_cr3(p)` every access translates according to the table at `p`".

| | |
|---|---|
| **What is missing** | a state space (registers, TLB, page tables, device state) and per axiom a **transition function** over it |
| **Why it is not "logic"** | the programmer proves over *his* program; the machine model is **beneath** him and the same for all programs |
| **Order of magnitude** | seL4 has its own model in Isabelle for this. **That is not a side item, that is a subproject** |

---

### L2 — A MEMORY MODEL. **Decided: RC11 without SC** — and the choice is less load-bearing than assumed here, because Caprock claims only RMW atomicity and per-address coherence ([`BEWEIS.md`](BEWEIS.md))

#### The original version of the gap

`atomic X : bool publishes { Y } release;` is today a **notation without a meaning.** What
`release` formally means — which prior writes become visible for which `acquire` — stands
nowhere.

**Without a memory model nothing can be proved about a concurrent kernel.** And Caprock is
concurrent: **2 231 `Ordering::` sites**, 872 of them in a single file.

> **This is the item seL4 SIDESTEPPED**, not solved — the seL4 proof is sequential at its core.
> Whoever wants to prove a concurrent kernel gold enters territory the models themselves have not
> entered.

---

### L3 — **DECIDED 2026-08-14** ([`BEWEIS.md`](BEWEIS.md)): three kinds of obligation, templates into Isabelle, program obligations via a **certificate checker**. **And the ceiling: Gold in the seL4 sense is not reachable on this path**

#### The original version of the gap

The type checker discharges **plumbing**. The **logic** obligations — `ensures`, `maintains`,
`invariant` — Gabbro produces and **nobody discharges them**.

Formerly the answer was "an existing prover" (Verus/GNATprove/Frama-C). **With the decision
"output is C + iasm, Gabbro checks for itself" that route is closed** — and no replacement is
named.

- [ ] **To be decided, and it is a decision about direction:** an SMT connection of one's own
      (Z3/CVC5 behind `pred`), or emitting the obligations into an existing system (Why3,
      Isabelle), or after all a second emission. **Every answer costs something different**, and
      today none of them stands there.

---

### L4 — **DECIDED 2026-08-14**: there are **three** lowerings, not one; a coverage certificate per run; and the unnamed crack is **which C** ([`BEWEIS.md`](BEWEIS.md))

#### The original version of the gap

"Syntax-directed and non-optimising" is the condition under which the refinement becomes cheap.
**Nothing checks it.** The proof lies on the source, what is shipped is the C — that both do the
same thing is **unproved**, and exactly this gap seL4 closes with binary verification (a project
of its own, filed under "Later").

---

### L5 — One's own TCB cannot be named

The assumption set in the artefact ("proved under A1…An") covers the **hardware**. It does **not**
cover:

| | unverified |
|---|---|
| the Gabbro type checker | yes |
| the lowering to C | yes |
| the **ghost-theory templates** (that is where the structural induction lives) | yes |
| the axiom layer | yes, and it is the largest surface |

**For Gold you have to be able to say what you trusted.** Today you can say it for the hardware
and for nothing else.

---

### L6 — The BEGINNING is missing

A proof begins in a state. **Which state holds before the first Gabbro code runs?** The boot phase
is there as a token (`BootPhase`, linear, `boot_end` unmaps `.boot`) — but what **holds** when it
is consumed stands nowhere. seL4 has an initialisation proof of its own for this.

---

### What explicitly is NOT on this list

* **Liveness and progress** — no mechanism addresses them, and that is a stated limit, not a
  backlog.
* **The logic proof** — it is the point of the exercise, not a defect.
* **The expressive power** — it is the running backlog (19 hanging plumbing obligations, no
  fragment in the folder — *both figures are from 2026-08-14 and the folder has overtaken them:
  the fragments stand written out in [`FRAGMENTE.md`](FRAGMENTE.md), and the 19 were never
  evidenced, see W7*), but it was excepted.

---

### The honest balance

**Four of the six items (L1, L2, L3, L6) are each a subproject**, not an open item. L2 is on top
of that one the models did not solve but **sidestepped**.

> **With that the question "what is missing for Gold" cannot be answered today with a list of
> constructs.** The language can **set up** the obligations; it has neither the model in which
> they have a meaning nor the tool that discharges them.
>
> **That is not a refutation** — Gabbro's promise was never to carry out the proof. It is the
> observation that between "produces good proof obligations" and "Gold" lies **not the last mile
> but the road**.

- [ ] **The cheapest step against this is L3, and it is a decision, not work:** where do the logic
      obligations go? As long as that is open, every further grammar rule is a line for a
      recipient that does not exist.


---

### What the gaps COST — the bill, drawn together (2026-08-14)

**The question is not whether there are gaps, but in which currency they are paid.** There are
exactly two, and the difference is the whole design:

| Currency | means | Example |
|---|---|---|
| **Reach** | the sentence holds **relative to named assumptions**. You know what you have proved, and what it hangs on | "memory-safe **under A1…An**" |
| **Validity** | you do **not** know what you have proved, because the assumption is unnamed | an `unsafe` block with a comment |

> **Gabbro's design consists at its core in transferring every gap from the second currency into
> the first.** Which is why the assumption set stands **in the artefact** and not in a footnote.

#### The four gaps, itemised

| Gap | costs | Number |
|---|---|---|
| **Axiom layer** | reach | **~130 names** for two architectures (A1–A25 counted, plus MSRs, CPUID leaves, device assumptions). **Ratchet: may only fall** — and `port` has just relieved it by **70 sites** |
| **Memory model** | reach | **2 assumptions** (`c11_release_acquire_x86`/`_aarch64`), each with a litmus falsifier (MP/SB/LB) |
| **Trust base of the tools** | reach | **4 items**: checker, lowering, **one** `iasm` emission site, N ghost-theory templates. All named, none estimated |
| **Seam CPU ↔ device** | reach, **but without a model to follow** | the device side is `assume` + probe, the **connection** has no mechanised model. For the MMU there is prior work, for DMA there is none |
| **Liveness (D8)** | reach | every progress statement is a `progress` **assume** with a falsifier (the watchdog). **96 infinite loops** measured; how many need a progress statement is uncounted |
| **Functional correctness outside the structural induction** | **unknown** | **that is the only gap without a number** — and it is exactly the open measurement |

#### The sentence a finished Caprock proof carries at the end

```
memory-safe       under A1…An            n ≈ 130, measured, ratchetable
race-free         under c11_*            2, with litmus probes
functionally open on O1…Ok               k UNKNOWN
```

> **The cost of all the gaps together is: `n` is large, but counted and falling — and `k` is
> uncounted.** That is the whole bill. **Knowing `k` is the cheapest step that still moves the
> folder**, and it is the same one as the falsifier of the L3 decision: **classify the 17 measured
> logic obligations** into *by construction · by generated induction scheme · by hand*.

**What the third column costs can be said in advance:** a body that has to be proved by hand costs,
by our own measurement, **5 : 1** on its share. At 5 % of the kernel that is +0,25 on the metric,
at 10 % +0,5. **A single unexpected case there is therefore more expensive than all 130 axioms
together** — they cost reach, it costs work.


---

# L1 and L2 — machine model and memory model

## L1 and L2 — machine model and memory model, designed and measured

**2026-08-14.** The two heaviest items from [`BEWEIS.md`](BEWEIS.md). Load-bearing numbers
re-checked.

---

### L1 — The axiom count: **106**, and the finest find was already there

> **W7 SWEEP 2026-08-15: UNEVIDENCED — TO BE REPLACED.** The number **106** (and the **65**,
> **30**, **~130 names** derived from it) has **no source list in the folder** — neither per axiom
> nor as a re-runnable search path. It is therefore the same class as the 74 proof obligations and
> the 19 hanging ones: *a handed-down aggregate without attribution.*
>
> **Not deleted, because the marking is the finding.** What it needs in order to be replaced: a
> list per axiom with `file:line` in the register manual or in the tree — and **only the x86 half
> is collectable** (the aarch64 figure 58 additionally rests on the sealed tree, see *The aarch64
> gap*). **Until then "memory-safe under A1…An" is again a form without content**, and the
> sentence two paragraphs below, that it has "for the first time a content", stands under this
> reservation.

| | |
|---|---|
| axioms, counted per register and width | **106** — x86_64 40, aarch64 58, MMIO access 8 |
| conservative (parameterised) | **65** |
| of these **pure reads** | **30 (28 %)** — they change no state and are the cheap part |
| plus control-flow primitives, device assumptions | ~8 + ~25 |
| **The assumption set A1…An of a two-architecture kernel** | **around 130 names** |

**With that, "memory-safe under A1…An" has for the first time a content.** 130 is large enough to
justify a ratchet, and small enough to maintain one.

#### Two corrections to my advance measurement, both against me

* **168 `asm!` were never 168 sites** — they are calls **plus** `global_asm!` **plus** doc
  mentions. *(Recounted: 150 + 15; the deviation from the agent's figure is a different search
  pattern, not a different finding.)*
* **Of 129 volatile accesses only 61 are device MMIO.** The other 68 are tokens and `packed`
  structs in normal RAM. **I had equated volatile with device.**

#### The find: the axiom layer already stands in the tree, only without a name

> **The arch-neutral intersection is ~20 families** — derived from two independent directions
> (lowering classes and the intersection of both architectures).
> **Re-checked, and it is exactly 20:** `caprock-hal/src/x86_64/cpu.rs` has 27 public functions,
> `aarch64/cpu.rs` has 20, **the intersection is 20** — identically named:
> `local_irq_save/restore/enable/disable`, `dsb_sy`, `isb`, `csdb`, `csv2`, `csv3`,
> `speculation_barrier`, `array_index_nospec`, `sb_supported`, `core_id`, `mpidr_affinity`,
> `current_el`, `halt`, `wfi`, `irqs_freigegeben`, `hypervisor_present`, `sync_code_range`.

**Caprock built the axiom abstraction without calling it that.** That is the cheapest conceivable
beginning for L1: the interface exists, what is missing are the transition functions behind it.

---

### L2 — RC11 without the SC axis. And the choice is less load-bearing than thought

**No model invented.** Chosen: **RC11 without SC**, with ownership transfer (RSL/FSL/iRC11) as the
surface — **the programmer never sees RC11**, he writes `publishes`.

**The justification is measured, not chosen:**

| | |
|---|---|
| `Ordering::SeqCst` in the whole tree | **0** — recounted |
| `compare_exchange` | 11 |
| non-trivial lock-free algorithms | 3 |
| seqlock, RCU, `AtomicPtr` CAS | **none** |
| share of the ordering annotations in **self-test code** | **70 %** |

*Promising* falls, because its distinguishing feature (out-of-thin-air) has no counterpart in
Caprock; "Rust's model" is not a third candidate but C11 with a different syntax.

> **The sharper version, and it relativises L2 itself:** what Caprock **claims** is **RMW
> atomicity plus per-address coherence** — and that is identical in **all three** models. Every
> Dekker-shaped site in the tree collapses onto it. **The choice of model is thereby considerably
> less load-bearing than the gap assumed.**

---

### What is NOT covered

**The seam CPU ↔ device is research**, and the reason is differentiated rather than blanket:

| Side | State |
|---|---|
| CPU | **mechanical** — over-approximation plus full fence |
| device | **named assumption with falsifier** — that Gabbro can do |
| **the connection** | **no mechanised model to follow.** For the MMU there is prior work (Syeda & Klein), for DMA devices there is none |

**W^X remains unformulable**, and the cause is the same one as known: **a PTE is pointer and
bitfield at once.** New is the consequence — **the TLB design hangs on it.** With that the PTE
construct is no longer an open item but a **blocker with a reason**.

---

### The weakest part — named by the designer himself, and it is the house pattern

> **"The machine state is the set of the linear ghost values."**

True for state a core **holds**. Silently extended to **the** machine state — **exactly the move
`HISTORIE.md` keeps as a pattern**, this time found by an agent on itself. `vspace_wx_ok` is
**one** measured counter-instance, and **how many others there are is not counted**.

- [ ] **This number decides whether L1 is a design or a sketch.** It is cheap to collect and
      stands as the next step.

Secondary, but instructive: **the first axiom count of my own came to 75 instead of 106 — 29 % too
small, and all the omissions in the same direction.** A count whose errors have a sign is not a
count.

---

### Grammar

**One new word** (`result`), four productions, **no new mechanism** — and `result` was
independently needed already: without it **no** function with a return value can assure anything
about it in `ensures`. **The seven domains hold** — paid for with W^X.


---

# L3 and L4 — prover and correspondence

## L3 and L4 — the prover and the correspondence. **And the ceiling is named**

**2026-08-14.** The commissioned question was: do the seven quantifier domains at nesting depth 2
fall into a **decidable** theory? That would have been the strongest finding in the whole folder.

> **Run. Answer: no.** And the reason is not the domain list.

---

### Why it is not decidable — four reasons, each sufficient on its own

1. **The seven are in truth three classes**, and the count was skewed: one disappears at compile
   time (`fields of`), four are finitely indexed, **two are transitive closure** — plus
   `reaches … via`, which is **the same thing** as `chain(…) in`, only written as a predicate.
   **The reachability class is three of eight constructs, not one of seven.**
2. **The array property fragment is directly on point and breaks exactly here:** quantified indices
   may **only** be read directly, `a[b[i]]` is forbidden. **Caprock's CDT is a pointer mesh,
   encoded as indices** — hence `a[b[i]]` throughout.
3. **The three load-bearing invariants of `space.rs` lie in THREE different theories:**
   `cdt_wellformed` (transitive closure), `child_points_back` (nested reads), `refcount_matches`
   (cardinality). **No known combination contains all three plus bitvectors.**
4. **The bound "nesting at most two" does not hold.** It holds over the **source text**, not over
   the **formula**: `maintains` puts a `spec fn` with its own `forall` inside an `ensures` with
   `forall`, and `spec fn` may call `spec fn` — only recursion is forbidden. **Checkable on paper,
   today checked nowhere.**

**And above that stands an item the folder has already measured:** the reordering lemma from
[`MESSUNGEN.md`](MESSUNGEN.md) is **structural induction**, and **no SMT solver does induction**.
With that the direction was decided before the question was asked.

**A constructive counter-finding, and it is the most valuable part:** the proof surface is not the
domain list but the **encoding**. If you model `parent`/`first_child` as **unary functions over an
abstract sort** instead of as array indices, the invariant family moves into the reachability
theory. **At run time it stays an array — the logic never sees an index.** *(Unchecked: the
conclusion comes from the designer, and `refcount_matches` certainly does not fall into it.)*

---

### L3 — The obligations are not ONE kind, but THREE

**The folder treated them as one.** As soon as you separate them, the main reason for a prover
front end disappears.

| Level | Obligation | where to |
|---|---|---|
| **1** | **Templates** (ghost theory, reordering lemma) — finitely many, hanging on the **construct**, not on the program. **Counted since 2026-08-14, as of 2026-08-17: 20, of which 15 unproved** (`gabbro schablonen`) — four are machine-checked (Isabelle2025-2, `beweise/`). **And the numbers are the actual report: four formalisations, the register grew from 17 to 19, the unproved ones fell by ONE — and the emitter added the twentieth (`option.sonderwert`) when it had to choose a representation for `option index into T`.** *The amortisation argument now holds over four cases — and the price for it was splitting two entries, because they were half provable and half over a nothing* — the one item is a **list with a length** | **Isabelle, once, outside the build process.** The **only** item that **shrinks** the trust base — today the template is called "the most trust-critical component, checked by the unverified core" |
| **2** | **Program obligations** | a VC generator of one's own → Z3/cvc5 — **but what stands in the trust base is a certificate checker in safe Rust, not the solver** |
| **3** | the ladder **proved · checked · owed** | **zero new words** — it consists of `invariant … runs online\|offline`, `check` and the assumption set |

**Fail-closed, looked up:** cvc5's Alethe covers only parts, LFSC prints **`trust steps`** — a
certificate with a `trust step` does **not** count as proved. On failure the build **always**
aborts, with **distinguishable** outcomes (`widerlegt` ≠ `unklar` — Caprock's trap, literally),
time bounds in **resources rather than wall clock** (D13), solver version in the fingerprint.

**Hard rule: the ladder applies exclusively to logic.** An unsolved plumbing obligation has
**exactly one rung and no way out.**

#### The ceiling, and it belongs in line 1 of the folder

> **Program-specific induction is thereby excluded** — a user cannot write a template. The ceiling
> is **safety hull plus declared invariants from a finite template library.**

#### CORRECTION (2026-08-14, a few hours later): "impossible" was wrong. It is FORBIDDEN

The version above wrote "excluded forever" and "Gold is not reachable on this path". **Looked up
again: induction fails on three lines, and all three stand in the list "What deliberately does not
exist"** (`SYNTAX.md`:585):

> *user-defined quantifier domains · recursion in `spec fn` · hand-written lemmas*

**Those are design decisions, not theorems.** Whoever takes them back can express induction — and
lands at Verus or F\*, which the line explicitly wanted to avoid. **The difference between
"impossible" and "forbidden by us" is exactly the move `HISTORIE.md` keeps as the house pattern**
— a sentence that would be true had its scope not been widened.

#### And there is a third way that nobody looked at

The version above equates: *templates hang on the **construct*** ⟹ *finitely many* ⟹ *nothing
program-specific*. **The middle step is not right.**

> **An induction scheme does not have to be fixed — it can be GENERATED FROM THE USER'S
> DECLARATION.**

A `table` with `parent`/`first_child`/`next_sibling` **declares a forest**. The structural
induction principle over it follows from the declaration — **just as in cut (c) the mutations
follow from it.** The user writes **no** lemma and **no** recursive `spec fn` and still gets
induction **over his own structure**.

**That is not an invention:** Isabelle and Coq have always derived the induction principle from the
datatype declaration. The only new thing would be applying it to a **declared** table instead of to
a datatype.

**And it would hit the measured case:** the reordering lemma from [`MESSUNGEN.md`](MESSUNGEN.md)
is structural induction **over exactly the declared tree**.

#### Where the difficulty then really sits — and it is real

**A `table` is not an inductive datatype but a mutable array.** "Is a forest" is an **invariant**,
not a type — so the induction principle holds only **as long as the invariant holds**, and that is
precisely what one wants to prove. The standard resolution is an induction over a **well-founded
measure** (say the number of descendants) with the invariant as a **premise**.

**Doable, known — and that is exactly where the work sits.**

**ENTERED 2026-08-14:** `by induction over <domain>` stands in the grammar — **one** new word
(`over` is reused), two productions, no lemma. With that the ceiling reads: **safety hull +
declared invariants + inductive properties over DECLARED structures.**

- [ ] **To be checked, and it is cheap:** does an induction scheme generated from the `table`
      declaration suffice for the 17 measured logic obligations? **This question replaces the
      claim "impossible" with a measurement** — and it is the same one that is due anyway as the
      falsifier of the L3 decision.

#### What stays outside even after that

* **Induction over an arbitrary user-defined recursive function** — that does not exist, and it
  stays that way.
* **Induction over program runs** (liveness) — a stated limit, independently of this.
* **And the reservation against the third way itself:** that the generated scheme really discharges
  the obligations is **unchecked**. Until then it is a design, not a solution.

**On the rejection of the second emission:** it holds, **but the reason in the folder is too
broad.** It hits a second **code** emission (you pay L4 twice) and does **not** carry against an
**obligations** front end like Why3. Why3 falls for a different reason: its use is the manual
fallback — *"a folder with a fallback has no gate."*

---

### L4 — "The lowering" does not exist, there are three

| | Part | is "syntax-directed, non-optimising" … |
|---|---|---|
| **(a)** | flat core | **true** |
| **(b)** | library emissions (`format`, `table`, `device`) | **moot** — a declaration becomes an algorithm, there is no source structure |
| **(c)** | assembler | **not applicable** |

**The condition is formulated, of all things, for the part that generates the fewest lines.**

* **"Non-optimising" becomes checkable as a bijection between evaluation sites** — and **that only
  works because E2 and E3 are already decided** (assignment is not an expression, nothing is
  implicit). Without them it would be semantic and thereby undecidable. **That is the strongest
  justification for E2/E3, and it stood nowhere in the folder.**
* **(a):** coverage certificate per compilation run, recomputed by a **separate** program with its
  own rule table — the `checkfat.py` lesson. **What is accepted is the mutation list, not the
  existence of the checker.**
* **(b):** an **interpreter in the compiler** instead of the handwriting, differential test against
  the descriptor. **Price, named nowhere today: the library layer gets built twice.**

#### The unnamed crack: **which C?**

"Output is C" — **without a named subset and named compiler options the correspondence is not
unproved but UNFORMULABLE.** Four places where Gabbro's own design meets undefined behaviour:
`restrict`, signed overflow, `tagged` → union, volatile. **The set belongs in the artefact, next to
A1…An.**

#### Binary verification: **enabled, and cheaper than thought**

It needs a named C subset and preserved function boundaries — **the same certificate checker
delivers both. One property, two purchases.** And **monomorphisation does not block it** — with
that the contradiction candidate from [`PLAN.md`](PLAN.md) is relieved.

> **But:** seL4 excludes assembler **and volatile accesses**. **With that the whole
> `device`/`mmio` branch would lie outside as well — exactly the part with the most killed
> traps.**

---

### The one rule that applies to **every** emission decision (W6)

> **Omitting a runtime check is justified by M1 alone, never by an invariant.**

The two nets look the same from outside and hang on different things: **M1 hangs on the type and
is recomputed per program; an invariant hangs on the template that preserves it** — that is, on
the unproved surface this folder already keeps as trust-critical. An emission that strikes a range
check *because the proof says it cannot go negative* confuses the two — and releases a claim about
the **model** into the **machine**.

**Mechanically, at every emission decision that cites a proof:** the cited fact must be derivable
from M1 alone, otherwise the check stays in the C. *A prior commitment for a surface that does not
yet exist* — see `WERKZEUGKASTEN.md`, W6.

### The inline assembler: **"one emission site instead of 161" is FALSE today**

L4 does not apply there — assembler is **not lowered but inserted**. What is checkable is only the
**interface**, and **today that is not even sayable**: `prim fn` has **no `abi` block**; `arch`
exists, the register allocation does not.

**The surface therefore does not shrink — it moves into a declaration without content.**

The minimal version is designed (`abi` block, **four new words**); three of the four conditions
fall out of **D2** and **M1**, so not on the programmer. The cheaper two-word version has been
examined and **rejected** — `reserved` would then mean two things, Caprock's most expensive trap
class. **For the block, countability applies, not correctness:** an axiom of its own class
**"emission"** (not "hardware"), plus buildable falsifiers — **three of four already run in
Caprock.** **The block gets no proof, but it gets `check`.**

- [ ] **Not in the grammar yet.** The four words are not in the vocabulary, the two productions not
      in the EBNF, `./instrumente/pruefe-syntax.sh` has not been run against it. **Until then the `abi` part is
      a sketch, not a rule** — and its justification is **weaker than that of every other
      construct**: a language finding, not a paid-for trap.

---

### The weakest part — named by the designer, and it lands

1. **The L3 decision rests on n = 1** (`revoke` → reordering lemma) — **in a folder that has
   measured exactly this error twice.** The falsifier stands right beside it and costs one day:
   classify the **17 measured logic obligations** into *SMT-decidable / needs a template / needs
   **program-specific** induction*. **A single case in the third column refutes the decision.**
2. **The coverage certificate checks STRUCTURE, and there is no argument that structure implies
   meaning.** In between lies a hand-written, hand-trusted table *Gabbro operation → C operation →
   condition*, estimated **40–60 entries** — **A8 scaled up by an order of magnitude, and the only
   item without an instrument.**
3. **Three claims from the literature quoted from memory**; the sentence "under a function
   encoding Caprock's invariant family falls into a decidable fragment" is **a conclusion,
   unchecked**.


---

# Item 2 — which C

## Item 2 — WHICH C, and how the lowering turns from a promise into a statement

**2026-08-14.** The only item on which Gabbro is **structurally** behind seL4
([`BEWEIS.md`](BEWEIS.md)). seL4 solves it by **formalising** a C subset (parser,
Simpl/AutoCorres) — a subproject.

**Gabbro solves it differently, and the difference is the whole answer:**

> **seL4 formalises C. Gabbro emits so little C that its semantics is a FINITE TABLE.** What is
> never emitted needs no semantics.

---

### 1. The target language is not "C" but a closed list of forms

The emitter knows **one C form per construct** (definition §14.1). With that the target language
is **enumerable**, and it is small:

```
Declarations    static, extern, typedef-free struct/union definition, enum-free constants
Types           uint{8,16,32,64}_t, int{8,16,32,64}_t, _Bool, T*, T[N], struct, union
Statements      assignment, if/else, switch (exhaustive, no default), for (counting loop),
                return, goto ONLY as a generated loop exit, call
Expressions     literal, identifier, field access, index, unary !/-, binary
                + - * / % & | ^ << >> == != < <= > >=, call, EXPLICIT cast
Other           volatile access, _Atomic with named ordering, _Noreturn, restrict,
                inline assembler at exactly one emission site
```

**What is NEVER emitted** — and is therefore free of any need for semantics: preprocessor other
than `#if` out of `when`; `void*`; pointer arithmetic; `union` reinterpretation without a tag;
comma operator; assignment inside an expression; `?:`; nested assignment; implicit conversion;
variadic functions; `longjmp`; VLA; bitfields (Gabbro does them itself with mask and shift);
`const` discarding.

- [x] **The list is to be counted and ratcheted**, like the axiom layer. If it grows in order to
      solve an emission problem, that is the same movement as a growing axiom layer.
      **Counted on 2026-08-31 by `instrumente/zaehle-c-formen.py`, ratcheted at 64/30, and
      driven by `abnahme.py` from the day it was written. The result is below, and it is not
      the result this section assumed.**

#### 1a. The list, MEASURED — 2026-08-31

**Denominator:** 102 of 485 versioned `.gab` files emit; **8001 lines of C**, of which 1732
are comment (22 %). Not `grep` but a lexer: line splicing, comment removal, string and
character literals as one token. *The generated C explains itself in English, and `for`,
`if`, `while`, `case` are English WORDS too — `grep` finds `for` 73 times, a statement it is
**49** times.* The counter is TOTAL over the token stream: every keyword and every punctuator
must map to a catalogue entry, and what does not is printed under `UNBEKANNT`. That is why
`float`, `&&`, `sizeof`, `while`, `inline` and `__attribute__` were noticed at all — *a
checklist can only find what somebody already suspected.*

| | | |
|---|---:|---|
| **A** erlaubt und benutzt | **34** | the actual table — what needs a C semantics |
| **B** erlaubt und NIE benutzt | **6** | dead entries; the list can lose them |
| **C** benutzt und NICHT erlaubt | **30** | the findings |
| | | **7** on the never list — a CONTRADICTION |
| | | **19** on neither list, and no generous reading covers them |
| | | **4** on neither list, but a generous reading does |
| **Forms in the emitted C** | **64** | = A + C, and this is the ratchet |

**B — the six dead entries, and the first is the important one:** `#if` out of `when` · `#else`
· `#elif` · `extern` · `_Bool` · unary `-`.

> **This section's own example is dead.** The allow list says *„preprocessor other than `#if`
> **out of `when`**"*. Of the five `#if` in the entire corpus, **not one** comes out of a
> `when`; all five are `#if defined(__GNUC__)` around `__builtin_unreachable()`, written by
> the emitter. *The permitted form is never emitted, and the emitted form was never
> permitted.* Until the counter split the entry in two it booked the one as the other and
> looked green (W25).

**C1 — used and on the NEVER list.** Seven, and two of them are large:

| form | sites | note |
|---|---:|---|
| **pointer arithmetic** | **491** | `d->basis + 8`, `v->bytes + 4`. `basis` is `volatile uint8_t *`, `bytes` is `uint8_t *` — checked against the declarations. **This contradicts §2 row 2 directly**, which says *„the emission generates **no** pointer arithmetic \| residual risk: none"* |
| **index on a pointer** | **156** | `p[1]` where `p` is `const uint8_t *p`. `p[i]` **is** `*(p+i)` by C's own definition; the allow list says „index" and does not say whether it means this too |
| `#include` | 408 | preprocessor other than `#if` |
| `typedef` | 240 | the list says *„**typedef-free** struct/union definition"* |
| `#define` | 210 | preprocessor other than `#if` — but *„enum-free constants"* plainly means it |
| `enum` | 28 | the list says *„**enum-free** constants"* |
| **`?:`** | **8** | ruled on below |

**C2 — used and on NEITHER list, and no generous reading covers them.** Nineteen: `void` (930,
the type row does not name it) · `__attribute__` (766) · `inline` (440) · `const` (419) ·
`*` dereference (141) · `&` address-of (111) · `~` (98) · `break` (51) · `++`/`--` (42) ·
`sizeof` (27) · `&&`/`||` (23) · `double` (18) · `while` (11) · `__typeof__` (9) · `float` (8) ·
`__builtin_unreachable` (5) · `#if defined(__GNUC__)` (5) · `continue` (3) · `_Static_assert` (1).

> **Two of these are not omissions but decisions nobody took.** `float`/`double` — the type
> row knows no floating point at all, and 26 sites of it are emitted. `&&`/`||` — the binary
> row names `&` and `|`, not `&&` and `||`, and those two are exactly the operators that,
> like `?:`, evaluate CONDITIONALLY. *Refusing `?:` while emitting `&&` refuses a class at
> one of its three doors.*

**C3 — used, unnamed, but a generous reading covers them.** Four: `->` (704, „field access") ·
`bool` (350, `<stdbool.h>` rather than `_Bool`) · `true`/`false` (211) · `+=`/`|=`/`-=` (24,
„assignment"). *They are listed so that the count of 30 carries its own two readings; under
the generous one the findings are 26.*

**What the SECOND instrument says, and it is good news:** `cc -std=c11 -Wconversion
-Wsign-conversion -Wcast-qual -Wvla -Wdouble-promotion -Wfloat-equal` finds **zero** hits over
the **101** units it compiles. **Implicit conversion, `const` discarding and VLA hold — and
they hold measured.** Row 7 of §2 below demands of implicit conversion *„none, but to be
checked mechanically"*; that is the mechanical check. *(The 102nd unit,
`beispiele/gift/414-tabellenspeicher-heisst-so.gab`, does not compile, and the tool says so
rather than booking it as zero warnings — W1.)*

**What stays UNMEASURED, by name:** `union` reinterpretation without a tag (a question about
the Gabbro program, not about its C) · whether every `goto` really is a generated loop exit
(the count is of `goto`, not of what for) · whether `asm` really sits at exactly one emission
site *in `emit.rs`* · the comma operator outside a grouping paren. Set B is an UPPER bound: a
103rd program can revive a dead entry.

#### 1b. Two rulings, each with a calculation

**`?:` — the GENERATOR is wrong. Measured, not preferred.**

All eight sites are one and the same line, `z = (z > v) ? z : v;`, out of one emission site
(`emit.rs`, `MergeOp::Max`/`Min`). Three forms of the same fold, `cc (GCC) 16.2.1`, x86-64:

| | `?:` | `if/else` naive | `if` tight |
|---|---:|---:|---:|
| `-O0` | 34 | 36 | **34** |
| `-O2` | 11 | 11 | 11 — **byte-identical bar the `.file` line** |
| `-Os` | 11 | 11 | 11 — **byte-identical bar the `.file` line** |

*`if (v > z) { z = v; }` costs nothing at any level.* And what would `?:` cost on the list? It
is, besides `&&`/`||`, the only operator that evaluates conditionally — and the only one that
forms its result type by the **usual arithmetic conversions** over its two arms. Putting it on
the list drags an implicit-conversion rule into a table that the compiler has just certified
free of one. **A rule that costs a semantics and buys zero instructions is the wrong side of
the trade.**

- [ ] `emit.rs` writes `if (v > z) { z = v; }` for `MergeOp::Max`/`Min`. Then C1 loses `?:`
      and both marks fall by one. *Not done here: `emit.rs` was held by another lane.*
- [ ] **And it does not close the class.** `&&`/`||` remain, 23 sites, with the same
      conditional evaluation. Either the binary row admits them by name, or they go the same
      way. **Deciding `?:` alone would look like a solved class and be one door of three.**

**`__builtin_unreachable` — BOTH: the generator is wrong four times, and the list was wrong
once.**

Deleting the whole `#if` block and compiling with `cc -std=c11 -Wall -Wextra -Werror`:

| site | `-O0` | `-O2` | |
|---|---|---|---|
| `08-bereiche` | ok | ok | **deletable** |
| `34-markierter-wert` ×3 | ok | ok | **deletable** |
| `40-werte-und-griffe` | **`-Werror=return-type`** | ok | **load-bearing — and only at `-O0`** |

**And the rule behind it is mechanical: exactly the four deletable sites carry a `return 0;`
directly after the `#endif`, the load-bearing one does not.** So at four sites two adjacent
lines contradict each other — `__builtin_unreachable()` says *„being here is undefined"*, the
`return 0;` under it says *„if we are here, return 0"*. **Only one of the two can be meant**,
and the first turns the second into dead code the optimiser may remove. *Four sites export a
Gabbro promise into C's UB rules and get nothing for it.*

- [ ] `emit.rs` emits the block only where no `return` follows — measured: 1 of 5.
- [x] **The remaining one goes ON the list, and its price is said.** It is not a convenience:
      at that site the C compiler is TOLD that the fall-through is unreachable, and that rests
      on `D005` plus the invariant that a tag only ever holds a declared variant. **That is a
      proof export into C's rules — the same class as row 11 (`restrict`) below**, and it
      belongs in the UB inventory as such, not in the syntax list alone.
- [ ] **Its `#if defined(__GNUC__)` is a second deviation at the same construct**, and a
      sharper one than it looks: under a non-GNU compiler the emitted program is a DIFFERENT
      program. §3 pins the compiler options into the artefact with a fingerprint; a `#if` on
      the compiler's IDENTITY belongs in the same place, or the artefact is not one artefact.

#### 1c. What the count decides — and it is not what this section assumed

**The table did not stay small because the list was obeyed; it stayed small because Gabbro is
small.** 64 forms over 8001 lines is a real result and it does hold the load-bearing sentence:
this is an enumerable target language, and AutoCorres is not needed for it. **But 30 of the 64
were never decided**, and two of them — pointer arithmetic at 491 sites, `void` as a type at
930 — are not oversights at the margin. *A list that 30 forms walk past is not a ratchet, and
until today nothing counted it.*

- [ ] **The 19 unnamed forms of C2 are to be RULED ON, one by one, the way `?:` was**: onto the
      list with the price of their semantics, or out of the generator with the price of the
      change. **Ruling by taste is what produced a list with 30 holes in it.**
- [ ] **§2 row 2 is to be rewritten.** It says pointer arithmetic has residual risk „none"
      because the emission generates none. The emission generates 491 sites of it.

---

### 2. The UB inventory — every class, and what kills it

**The proofs live in Gabbro. The danger is that the EMISSION devalues them through C's own
rules.** Which is why the list is not "which UB can Gabbro code have" (none) but **"which UB can
the generated C have"**:

| # | UB class in C | dies through | residual risk |
|---|---|---|---|
| 1 | **signed overflow** | M1 proves the bound — **but C does not know that.** Emission uses unsigned types where possible; otherwise `-fwrapv` as a belt | none, if both stand |
| 2 | **out-of-bounds access** | M1/M4 in the source type; the emission generates **no** pointer arithmetic | none |
| 3 | **division/remainder by zero** | M1: the denominator range excludes 0 | none |
| 4 | **shift by ≥ width** | M1 bounds the shift amount | none |
| 5 | **strict aliasing** | **no cast between pointer types is ever emitted**; `-fno-strict-aliasing` as a belt | none |
| 6 | **evaluation order / sequence points** | **E2**: assignment is not an expression, one effect per statement. **The whole class disappears** | none |
| 7 | **implicit conversion / integer promotion** | **E3** in the source text; the emission places **explicit casts everywhere** | none, but **to be checked mechanically** |
| 8 | **uninitialised read** | E3: nothing is implicit, every declaration has a value | none |
| 9 | **null pointer** | Gabbro has no `null`; `option` is `tagged` — **but a `ptr` initialised to a NUMBER is one in C**, and the emission now writes it through `(uintptr_t)` | **the `extern` boundary, and the fixed-address idiom below** |
| 10 | **`union` reinterpretation** | `tagged` writes and reads **via the tag**; C11 explicitly permits reading another member | padding bytes stay unspecified — **never read** |
| 11 | **`restrict` wrong** | generated from `effects`. **If `effects` is wrong, that is C UB** — a **proof export into C's rules** | **a real trust transfer, named** |
| 12 | **`volatile` semantics** | weakly specified; MMIO practice. **seL4 excludes exactly this** | **axiom, named** (A12/A17) |

> **Two rows carry real residual risk, and both are named rather than covered:** `restrict` (11)
> exports a Gabbro promise into C's UB rules, and `volatile` (12) is an axiom anyway. **Everything
> else dies on a rule that is already there for another reason** — E2 and E3 pay a second time
> here.

#### Row 9 was right about the language and wrong about the product (2026-09-02)

*"Gabbro has no `null`"* is true of the source language and was not true of the emission.
`beispiele/38-unveraenderlicher-zeiger.gab` writes

```
static tz : ptr<normal, rw> Platz = 0;      -- 4 items, 0 errors, 0 hints
```

and until this date that lowered to `static Platz * const tz … = 0;`. **The `0` is a null
pointer constant** (C11 6.3.2.3p3), the body below it writes `tz->slots[i].a = 5;`, and that
is undefined behaviour under 6.5.3.2p4. The file is not at the `extern` boundary, which is
the only residual risk the row named.

**Found by `clang --analyze` over the emitted C** — `core.NullDereference`, the single such
finding in 121 emitted units, in the audit method of 2026-09-01: hand an output the project
already produces to a tool that did not write it.

*The intent was never wrong.* On bare metal address 0 is a vector slot, and naming it is what
this language is for. The spelling was wrong, and **the emitter already held the right one**:
the MMIO path has written `(volatile uint8_t *)(uintptr_t)GERAETEBASIS` since it existed, and
converting an *integer* to a pointer is implementation-defined (6.3.2.3p5) rather than
undefined. Two spellings for one thing were `W7`; there is now one. Held by
`crates/gabbro-check/tests/komplement.rs::ein_zeiger_aus_einer_zahl_traegt_den_uintptr_cast`,
which falls in both directions.

---

### 3. The compiler options are part of the artefact, not of the environment

```
-std=c11 -ffreestanding -fno-builtin
-fwrapv -fno-strict-aliasing -fno-delete-null-pointer-checks
-fno-common -fno-stack-protector
```

**They belong in the artefact, next to A1…An** — and with a **fingerprint**. The lesson stands in
the register: *"`cargo build` runs through" is no evidence as long as nobody binds the
CONFIGURATION* (`CAPROCK_FLAGS_FP`). A lowering whose validity hangs on options nobody records is a
promise about somebody else's machine.

- [ ] **Fail-closed:** if somebody compiles the generated C **without** the named options, it must
      **break**, not quietly mean something different. Mechanism: a generated `_Static_assert`
      preamble that checks `__OPTIMIZE__`-independent features, plus the fingerprint in the image.

---

### 4. How the lowering turns from a promise into a STATEMENT

**"Syntax-directed and non-optimising" is prose today.** It becomes checkable as a **bijection
between evaluation sites** — and **that only works because E2 and E3 are already decided**:
without them the question would be semantic and thereby undecidable.

The emitter produces a **coverage certificate** per compilation run:

```
site  gabbro:space.gb:412:9   ->  c:space.c:1187:5   form ASSIGN_INDEX
site  gabbro:space.gb:413:5   ->  c:space.c:1188:5   form CALL
form  ASSIGN_INDEX  =  "<lhs>[<idx>] = <rhs>;"        from rule R17
```

An **independent** program with its **own** form table recomputes:

1. **Completeness** — every Gabbro evaluation site appears **exactly once**.
2. **Order** — the C sites stand in the same order.
3. **Closure** — every C form stands in the list from §1.
4. **No additional effect** — the C contains no evaluation site without a Gabbro preimage.

**The `checkfat.py` lesson applies literally:** the recomputer is **a second program with its own
pattern**, not the same code called twice. **And what is accepted is the mutation list, not the
existence of the checker** — a deliberately displaced evaluation site must be noticed.

---

### 5. What that achieves — and what explicitly not

**Achieved:**

* **The target language is named and closed**, which makes the correspondence formulable at all —
  before, it was not.
* **Ten of twelve UB classes die on existing rules**, not on new ones.
* **The lowering is recomputed per run**, by a second program.
* **Binary verification stays possible** and even becomes easier: a named subset and preserved
  function boundaries are exactly what it demands.

**Not achieved, and the difference from seL4 remains:**

* **This is NOT a formal C semantics.** It is a **reduction of the surface plus a structural
  recomputation.** What the twelve forms *mean* stands in a table a human wrote — **40–60 entries,
  hand-trusted** (named as such already in [`BEWEIS.md`](BEWEIS.md)).
* **Structure does not imply meaning.** The certificate shows that the sites **correspond to each
  other** — not that the C form **does** the same thing. The gap in between is exactly that table,
  and it is the **only item in the whole folder without an instrument**.
* **`restrict` and `volatile` remain trust**, named in the manifest.

### The instrument that does exist after all — witness pairs

**"The only item without an instrument" was wrong.** The tool lies in our own box: **every table
entry gets an executable witness pair** — a Gabbro fragment, the expected C, the expected behaviour
—, run through the **real** C compiler and compared. With that the table is **checkable instead of
hand-trusted**, and an entry without a witness pair is incomplete.

### `restrict` becomes a priced option, not a default export

`restrict` exports a Gabbro promise into C's UB rules (row 11 of the inventory). **Which is why it
is NOT emitted by default** — only where the differential benchmark demands it. The cost truth
measures against handwriting anyway; **the UB transfer is therefore paid exactly where it buys
something measurable**, and nowhere else.

### The common-mode failure of the coverage certificate, named

Two programs with **their own** form tables are N-versions — **but both tables come from the same
specification text.** An error *in the text* stands in both. **The common-mode failure remains and
is thereby a named item**, not a closed one; the witness pairs above are the only thing that helps
against it, because they measure against the **compiler** instead of against a second reading.

- [ ] **The next step is the form table itself** — 40–60 entries, each *Gabbro operation → C form →
      condition*. It is small enough to write, and large enough to **count and to ratchet**. **Only
      once it stands has item 2 moved from "unformulable" to "named"** — and this design claims
      nothing more.


---

# What seL4 needs besides the logic

## What an seL4 verification needs BESIDES the logic proof — and what Gabbro has for it

**2026-08-14.** Gabbro's promise reads "everything except the logic proof falls out by
construction". **Then one has to know what "everything except" really is at seL4** — otherwise one
is comparing a design with an impression.

> **Reservation, and it holds for the whole file:** the seL4 figures are **from memory**. The
> folder has needed the same class once before (the 20:1 split) and it was confirmed — **that is
> no evidence for these here.** Where a number stands, it stands as an order of magnitude.

---

### The six items besides the logic

| # | Item | what it is at seL4 | what Gabbro has for it |
|---|---|---|---|
| **1** | **Machine model** | a model of its own in Isabelle: registers, memory, MMU; what is not modelled is **axiomatised** | the **axiom layer**, ~130 names for two architectures, **ratchetable** and in the artefact. `port` has just relieved it by 70 sites |
| **2** | **C semantics** | a **C parser** together with a formalisation of a C subset (Simpl/AutoCorres) — a subproject in itself | **nothing equivalent.** Gabbro replaces it with "one emission, syntax-directed, non-optimising" — **and this correspondence is claimed**, not formalised. *But the shortfall is smaller than "no" — see the row on item 4* |
| **3** | **The assumption list** | explicitly maintained: assembler unproved, boot code initially left out, hardware as modelled, DMA restricted, **verified configuration single-core** | **the obligation manifest** — the same thing, but machine-readable, with classes and a ratchet over names. **Sharper in the DESIGN**: seL4's list exists as an artefact, Gabbro's as a specification (§15) — it is not emitted today |
| **4** | **Binary verification** | **translation validation PER BUILD** (graph-refine/SydTV, `tools/asmrefine` = 10 651 lines) — **not** a verified compiler, but a certificate per run. **Assembler and volatile are excluded** | **TV-lite is built, TV-full is reachable, a verified emitter is not needed.** The coverage certificate per run **is** already the light form; and **the syntax-directed lowering is precisely the property that makes per-build validation possible**, where for optimising compilers it is heroic. **Only the whole `device` branch would lie outside** |
| **5** | **Properties above correctness** | integrity, confidentiality, authority confinement — **theorems of their own with specifications of their own**; measured **+23,5 %** on top of correctness (`proof/infoflow` + `proof/access-control`, see [`MESSUNGEN.md`](MESSUNGEN.md)) | **not the theorem, but a checkable approximation** — see below |
| **6** | **The upkeep** | **the item nobody counts along** — see below |

---

### The 239 458 lines prove a SINGLE-CORE kernel — and that cuts both ways

**The verified seL4 configuration is single-core.** With that everything that makes the scheduler
area hard — address-ordered locking, queue surgery under fine-grained locks, every real
concurrency — lies **outside what the 40 / 32 / 28 split ever surveyed.**

> **seL4 did not prove the concurrency, it removed it by configuration** — route 5 of the counting
> rule ([`PLAN.md`](PLAN.md)) at the largest possible scale.

**What that means for Gabbro cuts both ways:**

* **No model to follow.** Whoever looks for an seL4 reference at the scheduler finds none. The lock
  order, the `Held` witnesses, the pairing — for those there is **no proved precedent** to measure
  against.
* **But also no unfavourable comparison.** Gabbro is not *behind* seL4 there, but **beyond the
  surveyed front**, where nobody has proofs.

**This line stands here before somebody reads the 40 % as transferable to an SMP kernel.** They are
not; they are measured on a kernel that, by configuration, does not have the hardest class.

> **And Gabbro's goal has explicitly been multicore WITH DMA since 2026-08-14.** With that the
> simplification seL4 chose is **excluded** — and three things follow from it:
>
> 1. **The pairing (pass 7) is load-bearing, not a "later".** Without it there is no race freedom,
>    and without race freedom none of the other promises is stable on a multicore machine: a fact
>    that holds on one core does not hold when a second one writes.
> 2. **The `dma` space must carry statements, not merely classify.** A device that writes is a
>    second actor without a lock and without `Held` witnesses. **Concretely and immediately:** a
>    carrier whose fields only the generated `ops` may write must lie in **no `dma`-reachable
>    region** — a **placement rule** as with the GDT, otherwise the write-right promise is a
>    promise with an open door.
> 3. **For this part there is no proved precedent.** No unfavourable comparison, but also no model
>    to follow: what is built here is built without a reference.

---

### Item 5 has a floor — the theorem is unreachable, an approximation is not

**Non-interference is a hyperproperty over *pairs* of runs.** Ordinary Hoare logic and refinement
**cannot structurally express** it; it can therefore **never come out of M1–M4**, however far one
builds them. That is the categorical statement, and it stands.

**But it is not a total loss.** Out of existing rules there falls a **syntactic flow discipline**
as an **over-approximation**: `effects` names what is read and written, and M3 separates the
address spaces — **what is not in the effect set is not read by the generated code.** That is
checkable, it is half built today (the body reconciliation checks writes and `locks`, not reads),
and it is the difference between

> *"unreachable"* and *"the **theorem** is unreachable, a **checkable approximation** exists."*

**What the approximation does not cover belongs written down beside it:** timing behaviour,
scheduling, indirect flows via control flow and occupancy state. An over-approximation that does
not carry this list is once again a promise instead of a condition.

---

### Item 6: the upkeep, and here lies Gabbro's strongest argument

**The real cost of a Gold verification is not the first proof but the fact that it has to be
maintained.** Every kernel change breaks proofs; the proof base (order of magnitude 200 000 lines)
is a **permanent** item, not a one-off. Which is why verified code is in practice code one **no
longer likes to touch**.

> **Gabbro's answer to this is structural and has so far been stated nowhere:**
> **if plumbing falls out by construction, a code change cannot break it.** A new index, a new
> subtraction, a new lock acquisition produce **no** new proof work — they compile or they do not.
> **The upkeep effort scales with the LOGIC share, not with the code size.**

**That is the one axis on which Gabbro does not reproduce seL4 but beats it** — and it stands and
falls with the same uncounted number: **how large is the logic share really?**

#### The silent precondition — and it is measurable

**"Plumbing cannot break" holds only as long as the change stays INSIDE the constructs.** A change
that needs a **new construct** breaks no proofs — **it breaks the language.** And then **language
upkeep** replaces proof upkeep, only under a different name.

**Our own history shows the price is real:** eleven plumbing classes became twelve; `keeping`
became `mirrors`; `transition` became `transset`; `forever` got `leaves` — all within days.

> **The bet is that the vocabulary converges, and it is MEASURABLE:** *new constructs per
> written-out fragment must fall.* **The four missing domain fragments — scheduler, MMU, loader,
> parser — are precisely the instrument for that**, and that is why they are not merely a coverage
> gap but the probe on the folder's strongest product argument.

---

### Where Gabbro is worse, without embellishment

1. **No C semantics.** seL4 has a formalisation; Gabbro has a **promise about its own lowering**.
   That is item 2, and it is the largest shortfall.
2. **No proof about the checker.** seL4's proofs run in Isabelle, whose kernel is small and
   checked. Gabbro's checker is **unverified Rust**, and everything hangs on it.
3. **No security statements.** Integrity and information flow are **theorems of their own** at
   seL4; Gabbro does not deliver them and does not claim to.
4. **Maturity.** seL4's chain has been run, repeatedly, on real hardware.
   **Gabbro has had compiler and checker code since 2026-08-14** (lexer, parser over the complete
   EBNF; on that date five of nine passes, **today ten passes and none open**, `gabbro paesse`)
   — **and it came into being in breach of our own ordering rule.** "No
   checker line before the result of measurement 2" held and holds; measurement 2 has not been run.
   The breach happened **on announcement, not silently**, and stands as a breach in
   [`HISTORIE.md`](HISTORIE.md) and in [`MESSUNGEN.md`](MESSUNGEN.md).
   *This line carries the rule status along, because the fact alone would smooth it over — and that
   is the error class from commit `5904cae`.*

---

### What the comparison says for the hard promises

[`SPRACHE.md`](SPRACHE.md) makes induction automatic instead of heuristic — that addresses **the
proof part**, i.e. exactly the item seL4 pays for with 200 000 lines.

**But the comparison shows that this is the smaller half:** of the six items besides the logic, the
step promise touches **one** (the proof effort over declared structures). **Items 2 and 5 remain
untouched, item 4 stands under "Later", item 3 is well solved, item 1 is half there.**

- [ ] **The honest consequence for the plan:** the next piece of work is **not** a further
      sharpening of the proof automation, but **item 2** — what does "which C" mean, and how does
      the lowering turn from a promise into a checkable statement? That stands in
      [`BEWEIS.md`](BEWEIS.md) as L4 and is the only item on which Gabbro is **structurally**
      behind seL4 rather than merely behind in maturity.


---

# The performance of the generated C — what is measured (nothing) and what follows

**2026-08-14.** The folder has on this subject a **table of claims** (definition §14.2) and **no
measurement**. What follows from that stands here, separated by direction — and the item the table
does **not** name.

## Where it should be faster than today's Rust kernel

| | Reason | Number |
|---|---|---|
| **Range checks** | Rust checks **every** indexing, unless LLVM can optimise it away. **Caprock bypasses that nowhere** — recounted: **0** `get_unchecked`, **0** `unreachable_unchecked`, **0** `assert_unchecked`. Gabbro **proves** and emits **none** | **1 398** variable indexings in the tree |
| **`accumulates`** | one cell per core plus a merge at read time instead of a CAS loop | measured on `sync:572–592` **strictly better than the original**, which additionally has an accepted race site there |
| **`transition`/`mirrors`** | **one** store with a constant mask instead of read-modify-write | per device transition |
| **Ghosts, contracts, `check`** | disappear before code generation; `check` compiles only under `when TESTBUILD` — **built 2026-08-28 («TB»), and until then the second half of this line was a plan**: the emitter did not read `Item::when`, so a gated `check` reached the C like any other item. Measured now at `beispiele/52`: **39 lines of shipping C against 77** | **0 bytes** |

## Where it should be the same

Range types → bare C type · `tagged`+`match` → union with tag, `switch` · `traverse` → `for`
without bound checks · `format` readers → accesses **after one** length check · `lock`/`locks` →
the existing primitive.

## Where it will be SLOWER — and the table does not name it

### 1. The loop bounds cost a counter that was not there before

`retry`/`forever` demand `bounded N ops`. **A wait loop that spins without a counter today gets
one** — increment and comparison per iteration. On a contended lock that is measurable. Measured:
**96 `spin_loop` hints** in the tree, **2** raw `loop {` in `caprock-sync` alone.

- [ ] **A remedy, designable and not yet designed:** the bound does not have to be checked **per
      iteration**. If it is a **watchdog** bound (and it is, since `progress` carries the
      termination), a check **every 2^k iterations** suffices — cost falls to ~1/2^k, the promise
      remains "breaks after at most N + 2^k". **That belongs decided before the first benchmark
      runs**, otherwise it measures a construct nobody would build that way.

### 2. `restrict` is now OFF by default

The UB transfer is paid only where the differential benchmark demands it. **The price for that is
more conservative C code at exactly those places** where handwriting would have set `restrict` —
and those are the copying paths, i.e. the hot ones.

### 3. The structural item: **lowering flat and being fast stand in tension**

**"Syntax-directed, non-optimising" is the condition under which the refinement becomes cheap**
(M-Gold-2) — and it means: **the emitter does not restructure.** Where a human would have fused a
loop, hoisted a computation or reduced a strength, Gabbro emits the naive form and **relies on the
C compiler**.

> **The folder has so far priced this tension only on the correctness side.** On the performance
> side it is unpriced: **the lowering is a bet that LLVM/GCC handle the form Gabbro produces
> well.** Whether that is true nobody knows — it hangs on the form table, which is not yet written.

## What decides it — and it is not this file

**The differential benchmark per module** (P3/P5 gate): generated C against hand-written, triggering
at "generated slower than handwriting plus measurement noise". **Until then every number here is an
expectation.**

**The honest summary in one sentence:** *In the counting and access paths the generated C should be
faster than today's Rust kernel, because 1 398 range checks fall away
(**W7 sweep 2026-08-15: UNEVIDENCED — to be replaced.** A recount over `[…]` accesses in the tree
gives **2 143**, not 1 398; which search path led to 1 398 stands nowhere. The numbers probably
measure different things — *probably* is the point); in the waiting paths slower at first, until
the bound check is amortised; and over the whole thing hangs an unpriced bet on the C compiler.*


---

## The alias item — named as an obligation, and the mechanism is missing

**Entered 2026-08-14.**

`SYNTAX.md`:10 imposes on every grammar rule that it discharge a plumbing obligation by
construction, and lists **"alias"** among them. `SPRACHE.md` §0 likewise carries it under what
Gabbro itself bears. **The mechanism for it is nowhere to be found:**

* **M3 gives address spaces, not separation.** `ptr<normal, rw>` and `ptr<normal, rw>` can point
  at the same object; the space says only *which* barrier applies.
* **`effects` declares, it does not condition.** `writes c.slots, writes o.slots` over two
  parameters that are the same thing is a true statement about a false assumption.
* **And this file's own inventory says so** (row 11): *"`restrict` wrong — generated from
  `effects`. **If `effects` is wrong, that is C UB** — a proof export into C's rules",* kept as a
  **real trust transfer**. `restrict` is therefore **off** by default now. That defuses the C side;
  **it does not answer the Gabbro side.**

**With that the frame statement rests on a promise instead of a condition** — exactly what this
file's criterion forbids: *an obligation that stays hanging on the programmer is a refutation at
that point, not a blemish.*

### The proposal stands in the folder, only not in the grammar

The derivation table in `SPRACHE.md` §3b carries *"`region`, ownership → **M2** → a linear block is
its region"*. The intention is there; but `own` is today a **right on the pointer type**, and
pointer types are copyable. **A pointer carrying `own` would have to be a linear value** — then
separation falls out of M2, and Gabbro keeps four mechanisms.

**The paper test for this stands as A1 in [`PLAN.md`](PLAN.md), with a two-sided gate.** If it
comes out red, separation needs a **fifth mechanism** — and the opponent for that is not Verus but
**Rust's borrow checker**, which supplies it. That would be the most expensive conceivable answer
to the question whether this language justifies itself.

---

## The breakdown into logic/plumbing — run 2026-08-15

> *"Break both measurements down into logic/plumbing — `delete_leaf` (3,6–6 : 1) and
> `Endpoint::call` (1,8–2,3 : 1). **Without that split a number is not a measured value.**"*
> (`TODO.md`:524)

Measured against `../caprock-messbasis` @ `a1bf707`, `crates/caprock-cap/src/space.rs:1062-1095`.

### `delete_leaf` — 34 lines, of which 12 code and 15 comment

**The criterion (`BEWEIS.md`, above):** *if the obligation names only the machine it is plumbing;
if it names the subject it is logic.*

| Line | Obligation | Class | why |
|---|---|---|---|
| `slots[slot].object` | index in bounds | **K** | names only the memory |
| `unlink(slot)` | chains stay well-formed | **L** | names the CDT, i.e. the subject |
| `release_slot(slot)` | slot is free afterwards | **K** | state of a place |
| `refcount -= 1` | no underflow | **K** | «B29», pure representation |
| `refcount -= 1` | counter == number of references | **L** | **the connection invariant, «B13»** |
| `if refcount == 0` | release exactly at zero | **L** | names the lifetime of the subject |
| `match kind` — `Memory` | region belongs to the RAM allocator | **L** | the 5 comment lines 8–12 are the evidence |
| `match kind` — `Dma` | release only after proof | **L** | comments 14–17 and 22–25: **ordering across system boundaries** |
| `match kind` — `Reply` | caller is unblocked | **L** | names the IPC protocol |
| `gen.wrapping_add(1)` | wraparound is intended | **K** | representation — *and in Gabbro sayable since «B32»* |
| `objects[obj] = EMPTY` | no reference survives | **L** | names the subject |

**Split: 4 K, 7 L.** Ratio **L : K ≈ 1,75 : 1** — the plumbing is the **minority**.

> **And that stands against the number the folder carries.** `delete_leaf` was booked at **3,6–6 :
> 1** — as evidence that plumbing predominates. Broken down it tips: **the majority of this
> function's obligations name the subject.**

**Why the old number came out differently, as far as it can be reconstructed:** it apparently
counted **proof steps** (every index, every range, every alias individually), not **obligations**.
A `match` over ten variants yields ten plumbing steps and **one** logical obligation. *Both are
legitimate ways of counting, but they answer different questions* — and the folder's question
("what is left for the human?") is answered by the **obligation** count, not by the step count.

**The comment share is the second finding:** 15 of 34 lines are comment, and **every single one of
them carries a logical obligation** (which kind of object holds RAM, why `Dma` is the exception,
why the release comes only after proof). *What a human has to write down so that the next reader
does not break the function is a good estimator for the logic share* — and it points in the same
direction.

### `Endpoint::call` — **not broken down, and why**

The function lies in `kernel/src/system.rs` and is interwoven with `SCHEDS`/`FP_OWNER` via the IPC
fastpath; a breakdown by the same criterion needs the lock situation **per line**. That is doable,
but it is **the work of the scheduler fragment** (wave 4) and not the work of this measurement.
**Blocked, with a reason and a source reference** — not silently omitted.


---

# The value thesis has shifted — measured, with source references

**The folder's founding assumption was the parser.** The traps that triggered the design were
format traps: wrong offsets, swapped byte order, a header of 10 instead of 12 bytes. `format` was
the first construct and the most plausible one.

**Two independent measurements now say the opposite.**

## `format` stands there twice without evidence

| Measurement | Result | Source |
|---|---|---|
| **Base rate** | **5 formats, 5 touching commits in 53 days, 0 occurred errors of the class.** The one near miss stands there as **avoided** — a warning, not an obituary | `MESSUNGEN.md`, *Basisrate*; `done.md:1745-1750` |
| **«B40», DTB fragment** | The only parser of the core that reads foreign bytes checks **145 lines without error, without a language and without a tool**. `be32(data, n)?` is already *"check, otherwise refuse"* | `FRAGMENTE.md` F10; `crates/caprock-dtb/src/lib.rs` |

> **`format` wins brevity there, not safety.** The gain is real — a declaration instead of a
> control-flow discipline at every access — **but it is not the gain the folder promises.**

## The kernel side carries its evidence — all of it

| Construct | Evidence | Kind of evidence |
|---|---|---|
| `table … count N` | `M103`, fragment `revoke` | a **measured** error would otherwise be possible |
| `lock … rank … held` | `K002`/`K004`, `H001`–`H005` | 419 lock acquisitions; `held` carries the latency statement |
| `locks shared` | **33 `read()` against 44 `write()`** | the hottest path was **not writable** |
| Pairing | 2 276 atomic accesses, 824 stores | `V001`/`V002` — the orphaned half reads valid garbage |
| `walk`/`embeds` | four-level descent, 9 named bits | `FRAGMENTE.md` F9 |
| `BootPhase` | **7 sites against a gate of 5**, among them a **paid-for** error | `main.rs:251` — *"exactly this line was missing on ARM"* |
| M1/overflow | «B29» in the delete path, **survived five rebuilds** | `space.rs:1067` |
| `traverse … over <domain>` | **0 of 571 `for` loops** run over something that is not a domain; what stays non-traversable is **584 of 60 756 lines** | `MESSUNGEN.md`, *B3*; the three gaps as «B41» |

**Eight constructs, eight pieces of evidence — and three of them are paid-for errors**, not
plausible scenarios.

> **The eighth piece of evidence carries its counter-evidence in the same sentence.** B3 shows the
> loop stock as load-bearing *and* names three domains that are missing («B41»). **Both are the
> same measurement** — whoever quotes the 0,96 % quotes the three gaps along with it.

## The sentence that follows from it

> **The language justifies itself at the kernel, not at the parser.**

That is **the opposite of the founding assumption**, and it is the folder's most useful shift: it
says where building continues (carriers, locks, ordering, descents) and where **not** (formats, as
long as the base rate does not rise).

**What it does NOT say:** that `format` should go. It carries ELF, the manifest and the DTB
brevity, and the near miss shows that the class is real — *its detection today hangs on
attention*. It means: **`format` is no longer the justification of the language but one of its
conveniences**, and whoever wants to justify it needs an argument other than the error frequency in
this tree.

*Both measurements stand there with a search path (W7) — recountable, and thereby refutable.*

---

# The actual result of the whole measurement chain: **the expensive obligations are many, but small**

Two measurements that were run separately together yield a sentence that neither of them carries
alone:

| | Result | Reading |
|---|---|---|
| **K/A/W** (`N_L = 73`) | **W = 38 against 36,5** — the value statements are the **majority** | the ceiling of the step promises covers a **minority** |
| **B3** (`p = 0,96 %`) | surcharge **+0,05** — below the resolution of the metric | the code form costs **almost nothing** |

**Both together mean: the distance to the floor hangs almost entirely on the W column itself.** Not
on loop forms, not on domains, not on the loop stock — on the question of how many obligations are
**value statements**.

**And the size distribution says how that can be.** In the population in which the lines are
measured (81, `F = 1 389`):

```
W:      40 obligations,  474 lines   ->  11,9 lines per obligation
K + A:  41 obligations,  915 lines   ->  22,3 lines per obligation
```

> **A W obligation is on average half the size of a K or A obligation** — 52 % of the obligations,
> but only 34 % of the lines. **The majority is a majority by head count, not by extent.**

**What that means for the thesis, in both directions:**

* **In favour:** the ceiling covers a minority of the obligations and **costs almost nothing** —
  the plumbing is not the problem. Whoever wants to attack the design attacks the W column, not the
  loop forms.
* **Against:** *"many, but small"* is **not a consolation but a warning**. Small proof bodies are
  cheap to write and expensive to **maintain**: 38 places where a human has to claim something
  about a **value** are 38 places that have to be re-checked on every change. **The effort scales
  with the count, the metric with the lines.**

*That is the tension the measurement chain produced, and it stands here instead of in a summary:
**the metric turns out well because the expensive obligations are short — not because there are
few of them.***

## That is why the dashboard needs a **second** number

**The metric measures writing cost. The W count measures proof cost. They can diverge** — and this
folder has just measured that they do:

> **A language can reach 0,5 : 1 and leave 38 small hand proofs open in the process.**
> The line ratio would then look like a victory, and the upkeep would be unchanged.

**The second number is therefore `W` obligations per thousand lines** — the **upkeep predictor**,
carried beside the line ratio, not beneath it:

| Metric | measures | State |
|---|---|---|
| **proof lines : code lines** | **writing cost** — once | ~~**≥ 1,90**~~ **unbekannt, > 0,5** *(zurückgezogen 2026-08-19: `w` war an VERUS-Zeilen gemessen, Gabbro beweist in Isabelle/HOL)* |
| **W obligations per 1 000 lines** | **proof cost** — on **every** change | **≥ 0,63** (38 of 60 756) |

**The second is explicitly a lower bound, and its direction is known.** The denominator is the whole
measurement base; the numerator comes from the areas for which **somebody wrote a Verus proof**.
Areas without a proof contribute **zero** obligations — not because they have none. *The sharp
number needs the code lines of the proved areas; those lie in a tree that is not available here,
and that is a small, named measurement, not a reservation.*

> **Why the second number is needed at all, in one sentence:** *otherwise the folder optimises for
> the denominator that shines instead of the one that costs.*

---

# The trust base is the EMITTER, and the certificate is the only thing that does not depend on it

*2026-08-31, drawn from the wildcard sweep (`messung/WILDCARD-ZWEIGE.md`).*

Everything above measures what a **person** still owes. It says nothing about the party that
writes the C, and that party is a few thousand lines of Rust without a proof:

> **Gabbro's trust base is not the `assume` list. It is the emitter.** Closing points 1 to 4
> in the type system changes nothing as long as the lowering is allowed to guess.

## What a guess looks like, measured

`emit.rs::breite_von` used to be four lines:

```rust
U8|I8 => 1,  U16|I16 => 2,  U32|I32 => 4,
_ => 8,
```

Under all four hardware points lies this one arm. A ninth integer word, and the emitter
silently writes `volatile uint64_t *` onto a device register: checker `0 errors`,
`cc -Werror` clean, and the device gets an access of the wrong width. **No Gabbro program can
defend itself against that** — the defect sits below every pass, in the translation.

It fired **146 times** over 499 corpus files, and the previous count had booked it as
*silent*. It is now a table with eight entries, a `C001` for anything else, and four tests
that hold the table against `kw::ALLE` and `ist_intty`.

## Why the CERTIFICATE is the structurally different answer

Every other safeguard in this folder is a pass, and a pass is code by the same author as the
emitter. The translation certificate is not:

> **A certificate that vouches for two different programs vouches for neither** — and that
> property can be checked without believing the emitter.

Until 2026-08-31 it did not hold. Two programs differing in one line
(`messung/proben/probe-zeugnis-injektiv-{a,b}.gab`, `threads` against `queue r`) had
**byte-identical** certificates apart from the file name in the header: five of the nine
traversal domains ran together on one word.

The cure was not nine labels but **nine reasons** — each domain rests on a different bound,
and three rest on none at all (`chain(…) in`, `fields of`, `threads`). *The single mark hid
exactly the places where termination does not follow from the declaration.*

`crates/gabbro-check/tests/zeugnis_injektiv.rs` measures both directions: the pair must
differ, two equal programs must agree, all nine domains must be pairwise distinct — and every
comparison renders under the **same** file name, so the header cannot do the work.

## What this does NOT claim

* **An injective certificate is not a proof.** It cannot become false while the program
  changes, which is a different and weaker property than being right.
* **It is injective in the traversal domains, not in general.** Nothing here says that no two
  other programs share a certificate; the measurement covers the case that was found and the
  thirty-five neighbouring pairs.
* **The emitter still has arms that answer `None`** rather than a value — those hand the
  decision to a caller that refuses. The sweep struck the arms that answered with a
  *plausible value*; the honest-unknown ones stay, and the reasoning stands in
  `messung/WILDCARD-ZWEIGE.md`.
