# Gabbro — the plan

**One plan, one goal: a kernel in Gabbro in which you prove ONLY THE LOGIC.**

> **The goal is a kind, not a quantity** ([`BEWEIS.md`](BEWEIS.md)). Everything that mentions only
> the machine — index, overflow, alias, frame, lock, race, refinement — falls by construction. What
> mentions the subject is written by the programmer. **The metric 0,5 : 1 stays as a diagnostic;
> even 2 : 1 is good if the lines are logic.**

What does not stand here does not exist. Earlier versions carried a narrow format generator as a
fallback and the kernel as a branch "for later" — both are struck. The format generator is the
library layer of the language ([`SPRACHE.md`](SPRACHE.md)), not a path of its own.

As of 2026-08-13. **None of this is built.**

*That sentence was true on 2026-08-13 and has been false since 2026-08-14 — the compiler
exists (`gabbro paesse`: ten passes, none open), and it came into being **in breach of this
folder's own ordering rule**, booked as a breach in [`HISTORIE.md`](HISTORIE.md). It stays here
unchanged rather than being pulled up: smoothing the claim instead of surveying the tree is the
error class of commit `5904cae`.*

---

## The target figure 0,5 : 1 — the floor, and it measures the distance instead of judging

> **Subordinated since 2026-08-13.** What follows here is the derivation of the target figure. The
> **criterion** stands above it and in [`BEWEIS.md`](BEWEIS.md): *prove logic only, nothing
> else.* Whoever confuses the two is measuring a proxy again.

seL4's 20 : 1 breaks down into about **0,5 : 1 abstract specification** and **19,5 : 1 proof**.
Only the first item is untouchable.

> **0,5 : 1 therefore does not mean "little proof" but: NO HAND-WRITTEN PROOF.**
> What gets written is the abstract specification — and nothing else.

**This is a GOAL, not a threshold.** The difference is not cosmetic: a threshold you can hit says
in the end only "passed". A goal at the theoretical floor makes the metric **diagnostic** — every
tenth above it is a **nameable proof item that is still written by hand**, and thereby a work order
instead of a verdict.

**The abort is an entirely different mark: > 3 : 1.** There the proof is the dominating item again
and the premise "cheap" is refuted — even if 3 : 1 would still be an improvement over seL4's
20 : 1. Building a language together with a compiler in order to move the proof from *dominant* to
*dominant* is not worth it; Verus gives away a good part of it for free. **The number 3 is chosen,
not derived** — it stands here so that it is not chosen later.

The arithmetic shows how fast the distance grows: if **5 %** of the kernel needs hand-written
functional proofs at 5 : 1, that alone is **+0,25** — i.e. 0,75 instead of 0,5. At 10 % it is 1,0,
at **25 %** about **1,75**.

> **THE 10 % ASSUMPTION CONTRADICTS THIS FOLDER'S OWN MEASUREMENT, and it carries the whole
> conditional yes.** Measured are **45 851 lines of algorithmic remainder (68,8 %)**; the
> folder's own list of the not-to-zero items (IPC fastpath, scheduler, `revoke`) plus
> **872 `Ordering::` sites in `threads/mod.rs` alone** says: **in a MICROkernel the
> algorithmic core is not a tenth, it IS the kernel.** If the share lies at 25–30 %, the mean
> stands beyond 1,5. **This is the least supported number in the folder**, and it is not
> decided by `revoke` — see P0.4.

**Three conditions follow from that — they are the actual design brief:**

| | Condition | if it falls |
|---|---|---|
| **B1** | **Invariants live at the structure, not at the loop.** If the *generated* mutation preserves the invariant, the loop needs none of its own | every loop gets a hand-written invariant — the largest single item returns |
| **B2** | **Algorithmic bodies consist of traversals.** ~~The solver gets the invariant for free~~ — **that was overreach no. 3**: what it gets for free is the **safety hull** (range, termination, frame). **Functional** loop invariants — partial sums, sortedness, tree shape in the middle of the mutation — are still written down by someone; that is the entire Verus/Dafny experience. What helps are **constructs whose postcondition IS their abort condition** (see `by consuming` in [`MESSUNGEN.md`](MESSUNGEN.md)) — and those exist per case or they do not | proof hints per body |
| **B3** | **What cannot be written that way must be vanishingly small.** Candidates: IPC fastpath, `revoke`, the scheduler's queue surgery | each of these bodies costs 5 : 1 on its share |

**That is why P0.1 (`revoke` on paper) is not one gate among many but THE gate.** If `revoke` needs
a hand-written proof, 0,5 : 1 is lost on that day — independently of everything else.

- [ ] **Check the seL4 breakdown.** It carries this whole derivation and is quoted from
      memory.

---

## 1. The evidence — 100 paid-for traps, classified

A plan made of constructs somebody considers good is a wish list. The constructs below are derived
from the **base rate**: the 100 entries of the list "traps this project has already paid for".
Every entry is classified individually in
[`fallen-klassifikation.tsv`](../fallen-klassifikation.tsv); the numbers below are **derived** with
`./instrumente/zaehle-fallen.sh`, not written down beside them.

| Class | Share | means |
|---|---|---|
| **S** — language | **36 %** | a construct makes it unformulable |
| **M** — measurement discipline | **36 %** | the checker was the problem, not the code |
| **W** — tool/process/build | **18 %** | CI, git, Cargo, scripts — **no language helps** |
| **B** — meaning | **10 %** | the descriptor was wrong — **no language ever helps** |

**The ceiling for the language share is therefore 72 %, not 100 %.** 28 of the 100 traps would have
happened in exactly the same way in a perfect language too.

### The domain, from real sites

| Pattern | where it occurs in Caprock |
|---|---|
| wire format with version header | manifest, checkpoint, sidecar, virtio descriptors, GPT, FAT |
| table with invariants | cap-space + CDT, page tables, IRTE, DMAR |
| enumeration with refusal | error codes, `MANGEL_*`, `LocalReason` |

"Five times the same pattern by hand is five times the same trap" — **and precisely that sentence
is uncounted.** It contradicts the measurement discipline this folder invokes.

- [ ] **Count the base rate before anything is built.** How many formats does Caprock really
      have? How often do they change? **How many errors of this class have actually arisen per
      year** (countable from `done.md`)? At around six stable formats, careful one-off
      hand-writing plus differential fuzzing against a second model is probably **cheaper** than
      a compiler you build *and maintain*.
      **If the count comes out small, the most honest result of this folder is not
      "EverParse carries it" but "the trap is too rare for a language".**

---

### What the LIBRARY LAYER covers on its own — measured, 2026-08-13

Until now a **list** of what is missing stood here. A list has no order of magnitude. Measured over
`kernel/src`, `crates/*/src` and `programs` (Rust, without blank lines): **66 651 lines.**

| | Lines | Share |
|---|---|---|
| **`format` — hard** (`caprock-part` 462, `caprock-fat` 652, `checkpoint.rs` 862) | 1 976 | 3,0 % |
| **`table` — hard** (`space.rs`, cap-space + CDT) | 1 105 | 1,7 % |
| **together, hard** | **3 081** | **4,6 %** |
| generously added: ELF/manifest part of the loader, DTB, ABI, ACPI `dmar`, virtio descriptors | ~2 900 | |
| **ceiling, generously counted** | **~6 000** | **≤ 9 %** |

**And the `table` half only counts in cut (c)**, which is not decided. At (a) the hard rate falls
to **3,0 %**.

What lies structurally **outside** the seven constructs, counted in the same tree:

| | Sites |
|---|---|
| `Ordering::` (atomics) | **2 231** |
| `unsafe {` | 482 |
| raw pointers `*const`/`*mut` | 403 |
| lock acquisitions `.lock()`/`.read()`/`.write()` | 406 |
| `asm!`/`naked_asm!`/`global_asm!` | 161 |
| `read_volatile`/`write_volatile` | 125 |

**The 2 231 atomics are the answer to the question**, and they agree with what the list below
already carried as the largest single item: 872 of them stand in `threads/mod.rs` alone. A language
that cannot express "the caller holds the lock" does not cover the core of the kernel — not badly,
but **not at all**.

> **A rewrite is thereby not narrowly missed but an order of magnitude away.** For what Gabbro is
> designed for it covers ≤ 9 % — and that is not an objection to the language but the confirmation
> of its cut. It is an objection to the word *rewrite*.

### And the 15,7 % about which Gabbro says nothing at all

`bringup.rs`, `fuzz.rs`, `selftest.rs`, `dmatests.rs` and the three `*mark.rs`: **10 471 lines,
15,7 %** — reporting, measurement and self-test scaffolding. **That is the part that found the
errors**, and it is more than three times as large as everything the seven constructs cover hard.

Whoever considers a rewrite is computing against the wrong size as long as this item does not stand
beside it.

### The finding that rearranges the plan

Broken down by construct, the distribution looks like this:

| Construct | traps killed |
|---|---|
| **`check`** (measurement discipline as a construct) | **33** |
| `linear` (real linearity) | 5 |
| `device` (register descriptor) | 5 |
| `assume`/`falsifier` | 3 |
| formerly *"lock, region, wirkung, einheit, grundmenge, absage, ableitung, stellentyp, arithmetik"* | 2 each |
| `state`, `atomic`, `barrier`, `bitfeld`, `platzierung`, `menge`, `recht` | 1 each |

> **The most valuable construct of a full Gabbro version is not a type-system property.**
> It is the **measurement discipline of this project, pulled into the language** — and it kills more
> traps (33) than all the type constructs together (S = 36, spread over twenty constructs, the
> largest with 5).

That fits the other number that fell out of the measuring: **15,7 % of Caprock is reporting,
measurement and self-test scaffolding**, and that is the part that found the errors. No existing
language — not Rust, not SPARK, not Verus, not F\*, not ATS — says anything about it.

**If this folder has a right to exist as a full language, then it is here.** Everything else is a
rebuild of what exists.

---

---

## 3c. How a GOLD proof becomes cheap — the core of the thesis

Gold means functional correctness, and **Gabbro does not prove it.** The question is where seL4's
**20 : 1** goes and which part of it a language can take away. Three items, and only the first is
untouchable:

| Item | who carries it | does a language take it away? |
|---|---|---|
| **The abstract specification** — *what* the kernel is supposed to do | the human | **no, never.** That is the statement itself |
| **Invariant preservation** — every mutation preserves every invariant | the proof, and that is the largest item | **yes** |
| **Refinement** — abstract → executable → C, over three languages (Isabelle/Haskell/C) with a seam at every boundary | the proof | **for the most part** |

### The word "Gold" carries two meanings

The metric of this folder is *lines of specification per line of code*: **seL4 about 20 : 1**
(Isabelle over C), HACL\* in the same order of magnitude.

**Only that is a number for full functional correctness.** In AdaCore's adoption ladder for SPARK
this level is called **Platinum**; *Gold* stands there one rung lower for "central integrity
properties", and *Silver* for absence of runtime errors. What the seven constructs deliver lies
between **Silver and Gold in that sense** — and was compared with a **Platinum** number.

- [ ] **Check the ladder, do not quote it from memory.** From this machine no SPARK documentation
      is reachable; the assignment of the five levels is from recollection and carries no argument
      that way.

**The consequence is not word-splitting but a measurement rule:** as long as it does not say *which
level* is being measured, every ratio delivers the number somebody wanted. The protocol for that
stands in [`PLAN.md`](PLAN.md) as the measurement protocol.

---

### M-Gold-1 — invariants at the structure, mutations generated

The invariant item is large **because every hand-written mutation has to be shown against every
invariant.** If the mutation is **generated** from structure + invariant, the proof falls **once per
operation in the generator** instead of once per call site.

**That is cut (c) — and it thereby has a reason beyond ergonomics for the first time.**
The old note "the effort does not appear in any phase" still holds; what is new is that the
alternative (hand-written mutation) **keeps** the most expensive item of the Gold proof.

### M-Gold-2 — syntax-directed, NON-optimising lowering

The refinement source → C is cheap if the lowering is **flat and structure-preserving**. That is
Low\*'s arrangement, and it is the reason why "non-optimising" is a **condition** here and not a
restriction.

**The price stands beside it:** optimisation happens afterwards, in the C compiler, and that is then
**not** part of the promise. Whoever wants performance *and* a flat refinement shifts the trust to
LLVM — the same boundary at which seL4 puts binary verification.

### M-Gold-3 — specification and implementation in THE SAME language

seL4 pays at **every seam** between Isabelle, Haskell and C. Gabbro has two levels and no seam:

```gabbro
spec fn cdt_wellformed(c: CapSpace) -> bool      -- mathematisch, nicht ausfuehrbar,
    = forall s: c.parent_chain(s) ends_at Root;    -- keine Ressourcengrenzen

impl fn delete_leaf(c: &mut CapSpace, s: SlotIdx)
    maintains cdt_wellformed                       -- die Verfeinerungspflicht wird ERZEUGT
```

**That is the real answer to "makes seL4 proofs easy":** not that Gabbro proves, but that it **makes
the three languages one** and sets up the refinement obligation itself.

### The prediction — and it corrects the folder's own goal downwards

**≤ 1 : 1 was set for `format`**, where the descriptor *is* the complete specification.
**For a kernel the floor is the abstract specification**, and nobody takes that away.

> **Honest prediction: 20 : 1 → about 0,8 : 1** — derivation below. An earlier version said
> **5 : 1** here; it treated the proof effort as indivisible and measured against the wrong denominator.

- [ ] **If Gabbro misses 2 : 1 by a clear margin, the Gold thesis is refuted**, and what remains are
      promise 1 (memory safety) and 2 (race freedom). That would **still** be more than today's
      Rust — but it would not be *"makes seL4 proofs easy"*.

### What < 1 : 1 would demand

> **CORRECTION (2026-08-13, a few hours after the first version).** A calculation with the **wrong
> denominator** stood here: specification lines against the *hand-written Rust reference*.
> Rust is irrelevant here — the point is a kernel **written in Gabbro** and then verified. The
> denominator is **Gabbro code**. The wrong version arrived at "for Caprock as a whole: no"; with
> the right denominator the answer is **conditionally yes**, and the condition is nameable.
> *(The earlier version had a justification of its own — as the question "is the switch worth it",
> not as the question "is the proof cheap". Two questions, one fraction.)*

### The counting rule has to stand first, otherwise it measures nothing

**The actual problem of this metric in Gabbro:** many constructs are **both** — a range statement, a
`device` block, an `over`/`by` are specification *and* program. Whoever counts them as code gets a
shining number without a statement; whoever counts them as specification gets a bad one.

> **Rule: specification is what stands in the GABBRO SOURCE and is deleted before code generation.**
> Everything that arrives in the generated C is code. **What the compiler derives is output — and
> counts in neither of the two pots.**

> **CORRECTED TWICE on 2026-08-13.** Version 1 said only "no runtime effect" — with that the
> generated ghost theory would have counted **into the numerator** and **the Gold mechanism would
> have worsened the metric the better it works** (found by [`MESSUNGEN.md`](MESSUNGEN.md)).
> Version 2 said "what a **human** writes" — that leaves a gap in a project with an AI co-author
> and, worse, **a detour: have a macro layer generate source that then counts as written.** The
> version that holds up is **source versus derived** — it is decidable at the artefact and needs no
> statement about who typed.

It is the only one that cannot be won by shifting text around:

| counts as **specification** (deleted) | counts as **code** (in the C) |
|---|---|
| `spec fn`, invariants, `requires`/`ensures` | `device` blocks (they generate the accesses) |
| loop invariants, descent measures | `format` descriptors (they generate readers/writers) |
| `linear ghost` values, lock witnesses | ordinary function bodies |
| `touches`, refinement annotations | range **checks** that stay in |

> **THE BIGGEST GAP IN THE RULE, found on 2026-08-13 by
> [`MESSUNGEN.md`](MESSUNGEN.md):** a metric made of **unchecked promises rewards
> false promises — they are short.** Evidenced at an `ensures` that is not merely unproven but
> **false** and stood in the numerator anyway; at a named property that was bound to **no**
> postcondition; and at an `effects` that was missing a lock.
>
> **Without a validity check every measured number is a lower bound with a NAMED
> error direction.** Three rules without which no measurement happens: (1) every counted `ensures`
> is held against the real code; (2) a named property that is bound to no postcondition counts
> **not at all**; (3) `effects` is checked against the actual accesses.
>
> **And `effects` fail-open is the same hole from the other side:** an omitted effect
> is **at once the strongest promise and the shortest specification**.

**Two further ways to prettify it** — both likewise belong in the protocol:
* **Checking instead of proving.** Whoever checks a property at runtime instead of proving it
  shifts lines from above to below. That is not cheating — it is a **different program**, slower,
  and precisely that is what gets shipped. The number stays honest if the runtime measurement
  stands beside it.
* **Verbose code.** That is why counting is done in **statements**, not in lines.


> **TWO FURTHER WAYS, ENTERED 2026-08-14 — BEFORE the next count, so that they count as
> entered in advance.** Both have the same form as the already booked `effects` fail-open hole:
> *the strongest promise is at the same time the shortest specification.*
>
> **Way 4 — the obligation migrates into the manifest and disappears from both pots.** The
> ground rule says: *"What the compiler derives is output — and counts in neither of the two
> pots."* The **obligation manifest is derived output**. So every obligation Gabbro
> **cannot express** drops out of the metric — and thus it holds:
> **the weaker the predicate language, the better the number.**
> **Rule:** *an `obligation` line of the manifest counts into the **specification pot**, with the
> extent its statement would have in Gabbro if the language carried it — and where that is not
> estimable, the measurement is reported as **incomplete**, not as good.*
>
> **CORRECTED WHILE ENTERING IT:** the first version of this paragraph drew from it a law with
> **two** exits — prove or remove. **Strictness has three**, and this folder has gone down the
> third three times already: **move the obligation into a GENERATED FORM whose proof
> falls ONCE.** `by consuming` for leafness, `accumulates` for the composite tear,
> `transset` for the half-set. **A prohibition is the exit when no construct is
> found — not the exit of first choice.** Way 5 below keeps its entry
> nonetheless: **every move into a construct is one more word, and the convergence bet
> pays for it.**
>
> **Way 5 — the obligation is settled by a PROHIBITION, and prohibitions cost the number nothing.**
> Strictness settles plumbing by **removing programs**: no `while`, no
> closures (64 measured sites), no genericity, static lock ranks instead of
> address-ordered acquisition, tables instead of pointers. Each of these **does not shrink the
> denominator but the set of writable programs** — and these costs appear in neither of the two
> pots.
> **Rule:** *beside every metric stands which rewrites it cost — site
> in the Rust original against site in Gabbro. A metric without that list is a number
> over what was left over.*
>
> **The K-condition** (*"by construction" holds only if ALL mutations of the carrier are
> generated operations*) already stands in the measurement protocol for measurement 2 in
> [`MESSUNGEN.md`](MESSUNGEN.md) — it holds for the metric too, and it delivers the
> `breaking` list for L3 on the side.

### The floor is not 5 : 1 — it is the abstract specification, and that is small

seL4's 20 : 1 is **not a single item**. Split up (numbers from memory, order of magnitude, see the
open item):

| | roughly | does Gabbro take it away? |
|---|---|---|
| **abstract specification** — *what* the kernel does | about **0,5 : 1** | **no, never** |
| **proof** — that the code satisfies it | about **19,5 : 1** | **that is the point** |

**The floor is therefore ≈ 0,5 : 1 and not 5 : 1.** My earlier 5 : 1 prediction stems from the same
confusion as the denominator: it treated the proof effort as indivisible.

- [ ] **Check the seL4 breakdown**, do not quote it from memory. It carries an argument here.
      From this machine no source is reachable.

### What has to go to zero — and what cannot

| Proof item | in Gabbro | Lines |
|---|---|---|
| memory safety, freedom from range and overflow errors | **M1 + M4**, in the type | **0** |
| frame conditions, non-interference | **M2**, effects as capabilities | **0** |
| data races, lock discipline, protocol phases | **M2** | **0** |
| **invariant preservation** — the largest item at seL4 | mutations **generated** from structure + invariant (cut (c)) | **near 0** |
| **refinement code ↔ specification** | syntax-directed lowering, `spec`/`impl` in **one** language | **near 0** |
| **functional correctness of algorithmic bodies** | IPC fastpath, scheduler, `revoke` | **NOT zero — real work stays here** |

> **< 1 : 1 is reachable if the first five items really go to zero** — then what remains is the
> abstract specification (≈ 0,5) plus the functional proofs for the safety-critical core.

**The rough calculation, with its assumptions spoken out loud:** if about a tenth of the kernel
needs functional correctness (capability system, IPC, the authority parts of the scheduler — in
Caprock roughly 5–8 klines of 66,7 k) and this part costs 5 : 1, while the rest carries only its
specification (≈ 0,3), then the mean lies at about **0,8 : 1**.

**That is a calculation, not a measurement**, and it hangs on three assumptions that can all be
wrong: the share, the factor 5, and that the first five items actually become zero. **The third is
the riskiest** — "near 0" at invariant preservation presupposes cut (c), and that one is
undecided.

### The three conditions without which it does not work

1. **The declaration IS the annotation.** Whoever writes `device` *and* invariants *and*
   proof hints has three numerators instead of one.
2. **The lowering has to stay flat.** Every refinement lemma is a line in the numerator, and
   they grow fast.
3. **`revoke` has to be expressible in the constructs** — otherwise the most dangerous mutation
   stays hand-written, and with it invariant preservation returns as a proof item. The
   paper test thereby decides not only the cut but **the metric**.

- [ ] **The cheapest check, without a compiler: ONE module twice on paper** — as Gabbro source
      and with what a prover would need beyond that. `space.rs` is the right case, because it
      contains both: descriptive structure **and** algorithmic `revoke`.

---

## The cut is DECIDED: (c)

**It was open for a long time. With the goal 0,5 : 1 it no longer is:** if the mutation stays
hand-written, somebody has to show that it preserves **every** invariant — at seL4 the largest
proof item of all. **(c) is thereby not an option but a precondition.** What follows below is the
derivation; the decision has been taken.

**A format reader is a pure function at a boundary**: bytes in, structure or named refusal out.
There "by construction" is a clean term — the generated code is the **only** one that touches the
bytes.

**A table like the cap-space is MUTATED STATE**, and the mutation is done by hand-written kernel
code. The folder's own sites show it:

* `refcount -= 1` without a condition lives in the **mutation** code, not in the checker. A
  generated `gabbro_capspace_audit` would find the silent wraparound **afterwards** — that is a
  better `audit_cdt`, not an unformulability.
* S1a is unformulable only if **the traversal code itself is generated** *and* the kernel is
  forced to use it.

**Phase 4 therefore hangs on a question the language design answers nowhere:**

| | Gabbro generates … | consequence | **where the invariant can run** |
|---|---|---|---|
| **(a)** | only the checker | cheap and honest — but the benefit is "`audit_cdt` without its errors". **Runtime check, not construction.** S1a and S1b drop out as acceptance criteria, and with them the sharpest justification for phase 4 | **offline/idle only** — diagnostics, not protection |
| **(b)** | checker + access helpers | range safety when reading, mutation stays by hand | likewise offline only |
| **(c)** | checker + access + **mutation** (`insert`/`remove`/`revoke`) | the generated C **owns** the data structure, the kernel calls into it. A massive interface intervention — under the core lock, with a latency budget. **The effort does not appear in any phase.** | **incrementally possible** — and only here |

**The cost model helps decide the cut; it is not an independent open item.**
A complete check of `kind_zeigt_zurueck` is naively **O(n · chain length)** over
80 256 slots. `colors.rs` today holds **42 ticks** under a lock and counts as a debt item for that
reason — an order of magnitude above that is unthinkable in any hot path. Two ways out remain:

* **check offline/idle** — then it is **diagnostics, not protection**. Legitimate, but a
  *different* claim from the one in the first draft.
* **check incrementally** — only what a mutation has touched. That presupposes that the checker
  knows the **delta**, and the delta is known **only to the mutator**.

> **Whoever wants invariants in the hot path has already chosen cut (c) — whether they wrote it
> down or not.**

- [ ] **This decision belongs BEFORE phase 0.** Because it changes what phase 0 can kill at all:
      **EverParse does exclusively the `format` half.** If the real value lies with
      `table` — and much speaks for that, since verified wire parsers are a solved problem and
      generated invariant infrastructure for kernel-internal tables is not — then EverParse
      cannot finish Gabbro off **at all**, only strike half of its right to exist.

---

---

## What Gabbro could do like SPARK — and what better

Both are measured, not estimated: two SPARK experiments on the cap-space and on the scheduler, plus
the Verus gate of 2026-08-13.

### Like SPARK — and M1/M2 deliver it structurally

| SPARK strength | in Gabbro |
|---|---|
| **Every indexing, every piece of arithmetic is an obligation** — the reason S1a/S1b fell | **M1**: range types. It is not a default setting somebody can flip but the type |
| `Global`/`Depends` — **63 of 63** data dependencies proved | **M2**: effects are ghost capabilities in the parameter |
| **coverage ratchet** (34 of 34 under `SPARK_Mode => On`, no `Off`) | the ratchet over the **axiom set** — same mechanics, different subject |

### Better than SPARK — five points, each at a measured weakness

| | SPARK today | Gabbro |
|---|---|---|
| **Linearity without allocation** | "leak **proved**" is SPARK's strongest single point — **but it hangs on an allocation** (measured, and the price stands in Caprock's register) | **M2**: ghost linear values, deleted before code generation. **No byte, no heap** — measured against Verus. Strictly better on SPARK's own field |
| **"The caller holds the lock"** | **no form of expression** — stays a comment | **M2**: linear ghost witness. Verus can do it today, which shows that it works |
| **Address spaces, MMIO rights** | four volatility variants, but no `write_only` register, no address space, no barrier domain | **M3** — and with it four paid-for traps (1, 2, 4, 5) unformulable |
| **Termination** | Silver does **not** demand it | **M4**: obligation. Exactly the gap I5 that was open in our own Verus model |
| **Boot phase with a sequencing proof** | does not exist | **M2 + M3**, two-stage, falsifiable (§3e) |

Plus the difference that is not a language question: **SPARK checks existing code, Gabbro generates
it** — which is why invariant preservation falls once per operation instead of per call site (§3c).

### Worse than SPARK — and that is what decides in practice

* **Maturity.** GNATprove has been automated over decades and is industrially certified (DO-178C).
  Gabbro has none of it, and the Verus run showed how expensive immaturity gets: four crashes,
  one sealed interface, missing specifications for iterator adapters.
* **SPARK's leak check fires by itself.** Gabbro's has yet to show that it does — "works in
  principle" is the weakest of all statements about a checker.
* **A single data point per claim.** Two experiments are not a survey.

---

## 4. What does not get better even then — 28 %

| | | Example |
|---|---|---|
| **W (18)** | tool, build, process | `.git/info/exclude`; `grep -q` under `pipefail`; a CI gate in the format of the wrong server; two suites that set the same device up differently |
| **B (10)** | meaning | "bottom first" was a coincidence of the size relation; the loader reports its own memory as free; one store per role |

Plus the hardware: `assume`/`falsifier` makes assumptions **countable**, not true.

**A rewrite that expects 100 % is computing with 72 % — in the best case, with perfect
implementation of every stage.**

---

---

## TRIGGERED 2026-08-13: abort condition 2 has bitten for M2

The counter-calculation "what can Rust + Verus + Loom already do today?" has been run for the
heaviest item, and it came out **against** this plan.

| Stage | measured state against Verus/Rust today |
|---|---|
| **M2 at the lock witness** | **head justification fallen.** "The caller holds the lock" is a `tracked` witness in Verus: correct core `verified`, foreign core proof error, self-built witness type error — `no_std`, without a byte in the artefact. **What stays unmeasured** is lock order ⇒ deadlock freedom and `haelt_hoechstens`; traps 41 and 93 are therefore not yet given away |
| **M1 + M2 (arithmetic/linearity)** | **arithmetic and index bounds: fallen.** Verus finds S1a and S1b on the real code for **0 lines** (one switch). **Linearity: half** — `tracked` is affine, a leak check costs a balance written down by hand. Rust's `Parked` delivers the other half at zero cost |
| **M3 (`device`)** | **unmeasured — and the opponent is not Verus at all.** Typed register accesses (`tock-registers`, `svd2rust` kind) are a **Rust library**. The question is not "can a language do this" but "what is the library missing": transitions over bits, conditions across register boundaries, barrier domain in the type |
| **M3 (placement)** | **unmeasured**, and `#[link_section]` exists. The gap is that nobody **checks** it — a lint can do that |
| **Entry (TAL)** | kills **0** paid-for traps and has a prover nowhere |
| **`check` over M2** | **no opponent found.** Neither Rust nor SPARK nor Verus nor Loom says anything about the speech test, gating, lower bound or isolating counter-probe |

> **The honest balance after the first counter-calculation: what remains is the linear check
> obligation (`check` over M2), the lock order and M3 — and M3's opponent is a Rust library, not a
> language.** As an *effect* the linear check obligation needs no language: V−1 builds it as a
> macro library. What it needs as a *mechanism* is real linearity — and Rust does not have that.

The order is thereby no longer "V−1 first, because it is cheap" but **"V−1, because everything else
has just found its opponent".**

---

# The path — eight phases, each with a gate

## P0 — Paper. Three questions, each can kill the thesis

One to two days in total, no code. **That is the cheapest point of the whole undertaking.**

### P0.1 — express `revoke` in the constructs

The (since struck) *"decrement requires"* was a precondition **on a field**. The correctness condition of
`revoke` is **structural**: a subtree disappears, and that `kind_zeigt_zurueck` and
chain finiteness still hold afterwards is a statement about tree shape.

> **Gate:** If it works, cut (c) is load-bearing and the 0,8 : 1 prediction holds its riskiest
> assumption. If it does not work, the **most dangerous** mutation stays hand-written — then
> invariant preservation returns as a proof item, **and the metric falls with it**.

### P0.2 — `vtd.rs` as a `device` block

1 448 lines of Rust against a description of the same unit.

> **Gate:** a factor of ≥ 5 smaller. Otherwise the concision thesis is refuted, and with it the
> declaration gain at every site.

### P0.3 — write `space.rs` down twice

As Gabbro source **and** with what a prover would need beyond that. The right case, because it
contains both: descriptive structure **and** algorithmic `revoke`.

> **Gate:** the first real number for the metric, following the protocol below. Above 2 : 1 ⇒ abort.

- [ ] **In addition, independently and likewise paper: count the base rate.** How many formats does
      Caprock really have, how often do they change, how many errors of this class have arisen per
      year (countable from `done.md`)? If it comes out small, the most honest result is not "it
      works" but "the trap is too rare for a language".

---

## P1 — `check` as a Rust macro library, without a language

The only construct without a precedent, and it needs **no compiler**. Held retrospectively against
the 33 measurement-discipline traps, each with a mutation.

> **Gate:** **≥ 5 of the 33** caught retrospectively, evidenced with a mutation. Below that `check`
> is ergonomics — and with it falls the only justification that belongs to Gabbro alone.

**Useful even if Gabbro never comes into being.** That is the reason this phase stands before all
the others.

---

## P2 — The core as a CHECKER, without code generation

M1 (range types) + M2 (linear, also ghost values) + M4 (no unchecked index) as a type checker over
a minimal language. No C yet.

> **Gate:** S1a and S1b are **not formulable**, and that with **0 lines** of annotation. If any are
> needed, Gabbro is at this point only a more cumbersome Verus.
>
> **CORRECTED 2026-08-13:** "0 lines" is not a decidability question but a **heuristics question**.
> **M1 is called "range type" and is a solver** — checked at `caprock-sched/src/lib.rs:1996`:
> `31 - bitmap.leading_zeros()` needs flow-sensitive inference, and `self.queues[p]` one line
> below additionally needs the **data-structure invariant**. The gate stands, but it measures the
> strength of an inference, not the form of a type.

Additionally to be shown here, because it is the only mechanism without an existing tool:

> **Gate 2:** the **boot-phase marker** carries — a `roh` function after `boot_ende` does not
> compile, and neither does an attempt to copy or manufacture the marker.

---

## P3 — Lowering to C, syntax-directed

One module all the way through to C, non-optimising, plus a differential test against the Rust
version.

> **Gate:** differential test green (same inputs, same outputs, same **refusal codes**) **and**
> cycles per call measured against the hand-written reference. "Permanently slower and the cause
> not fixable" is an abort condition.

---

## P4 — M3 and `device`

Address spaces and access rights at the pointer; `vtd.rs` translated.

> **Gate:** the DMA suite stays green, **and four mutations do NOT compile** — the paid-for
> traps 1 (`STE.S1STALLD`), 2 (CD without `R`), 4 (`GCMD` as RMW), 5 (x2APIC `EN`+`EXTD`).

---

## P5 — Axiom layer and entry

One declared effect per privileged instruction; a syscall entry without hand-written assembler.

> **Gate:** the axiom set is **enumerated and numbered** (ratchet, may only fall), every axiom
> has a `falsifier` or a named reason why none can be run. **Without the number, "memory-safe
> under A1…An" is a form without content.**

---

## P6 — `spec fn` / `impl fn` and the generated refinement obligation

The Gold mechanism.

> **Gate:** the metric measured on **two** modules, both reported (best and worst case) — **together
> with a breakdown of which item produces the distance to 0,5 : 1.** A number without that
> breakdown is worthless, because it contains no work order. Abort only at > 3 : 1.

---

## P7 — Race freedom

Data races out of M2/M3; **protocol races** via linear phases.

> **Gate:** the **D0 form** is not formulable — a thread that becomes runnable before it has its
> authority does not compile. That is the case every data-race checker in the world would have let
> through.

---

## P8 — Migration by the strangler pattern

Module by module, **both versions alive at the same time**, a differential test in between. Never a
big cut.

> **Acceptance, in three parts:** (A) the 14-point series green, both architectures, all RAM sizes ·
> (B) differential test against the Rust version, module by module · (C) repeat measurement with
> cross-comparison, null findings with a sample size.
>
> **(B) is not optional:** across the fixes for D8, D9 and D10 the x86 signature stayed
> **byte-identical** (500 runs per state). Three real core errors, not one of them triggered.

**The test suite is the LAST move, not the first.** It is 15,7 % of the code and consists of
`check` promises; it stays in Rust until the Gabbro version is proved **against it**. Whoever
rebuilds their instrument first measures the rebuild with the rebuild.

---

## Later, explicitly not now

* **Binary verification** (seL4 style, generated C against machine code). The path exists but is a
  project of its own — and it is the only one that takes the lowering out of the trust base.
* **Reusable specification theories** (capability system, page tables). They help the **second**
  project, not the first — which is why they may not be counted into any cost calculation as long
  as there is only one kernel.
* **~~Rust output~~, ~~Ada output~~** — struck on 2026-08-13. They were only necessary as long as a
  *foreign* prover was supposed to conduct the proof.
* **Page-table descriptors.** Tempting (the missing `US` at the intermediate level would not have
  been formulable), but page tables are hardware contracts; a wrong descriptor generates a provably
  correct wrong kernel.

---

## The abort conditions — here, so that they are not negotiated

Gabbro ends when **one** of them occurs:

1. **The base rate is too small** (P0) — too few formats, too few errors of this class.
2. **`check` catches retrospectively fewer than 5 of the 33 traps** (P1). Then the only
   justification that belongs to Gabbro alone falls.
3. **Rust + Verus + Loom already cover a mechanism.** For M2 at the lock witness and for M1 that
   **occurred** on 2026-08-13; what remains is real linearity. If it occurs for that one too,
   the core is empty.
4. **The metric lies above 3 : 1** (P6). *Not* "it misses 0,5 : 1" — that is the **goal**
   at which the distance is measured, not a threshold. Abort happens only once the proof is again
   the dominating item.
5. **The generated code is permanently slower** than the hand-written reference and the cause is
   not fixable (P3).
6. **A piece of kernel logic can only be expressed by growing the axiom layer.** The ratchet may
   only fall. If it grows in order to cover a language deficit, "memory-safe under A1…An" is
   worth a little less each time — and nobody notices, because the promise formally still holds.
7. **The migration forces a big cut** (P8). An undertaking that switches off the acceptance series
   in order to build itself has no checker any more — and this project has measured what happens
   then: ten days red, without anybody seeing it.

A folder that does not name its own abort conditions is never ended — only forgotten.

---

## The measurement protocol for the metric — in advance, because otherwise it delivers the wished-for number

The rules stand here **before** the measurement, for the same reason the IPC threshold of
2000 cycles is fixed in advance: a threshold you choose after the result is not one.

**1. Two modules, both reported — otherwise the choice decides the result.**

| | Module | expected |
|---|---|---|
| **best case** | the **manifest reader** (`format`) | close to the goal — here the descriptor *is* the specification |
| **worst case** | a **(c) mutation module** on the cap-space | clearly above it — loop invariants, ghost code, auxiliary lemmas |

**Reporting only the first is the manipulation**, and it needs no intent: you measure the module
that is finished.

**2. Counting rule for the numerator — proof code IS specification.** What the downstream prover
needs in addition counts too: **loop invariants, ghost code, auxiliary lemmas, `assert` chains,
ACSL annotations**. Whoever counts only the Gabbro descriptor measures half the load — and exactly
the half that explodes at (c).

**3. Counting rule for the denominator — GABBRO CODE.** Not the hand-written Rust reference: what
is measured is whether a kernel **written in Gabbro** is cheap to verify; Rust does not appear in
it. **The dividing line is the runtime effect:** what the compiler deletes before code generation
is specification; what arrives in the generated C is code. Counting is done in **statements**, not
in lines — otherwise verbose code wins. And whoever **checks** a property at runtime instead of
proving it shifts lines downwards: allowed, but the runtime measurement belongs beside it.

**4. The level stands beside it.** Whether safety hull, declared invariants or functional
correctness was measured belongs next to the number — seL4's 20 : 1 is a number for the
**strongest** level. A ratio without a level compares across a chasm.

**5. The proof route IS decided** (2026-08-13): Gabbro checks by itself, the output is C + iasm, no
downstream prover. That drops the ACSL load out of the numerator and the correspondence obligation
with it. **What belongs in the numerator instead:** `spec fn` lines and the refinement annotations
— and for a kernel that is the floor that makes 1 : 1 unreachable (§3c there).

**Goal and abort are two different things, and confusing them was an error of its own:**
**the goal is 0,5 : 1**, the theoretical floor — it is not "passed"; instead the **distance** to it
is broken down. **Abort** happens at **> 3 : 1**, where the proof dominates again.
The 3 is chosen, not derived; it stands in advance so that it is not chosen later.

---

## The acceptance criterion: Caprock completely in Gabbro, suite green

**The demand is falsifiable, and that is its value.** Not "it feels better" but: the
Gabbro-built kernel passes **the existing acceptance series** — 14 points, x86 in five RAM sizes,
loader suite, aarch64 build **and** suite, host tests, core boundary, guardians.

**But the suite alone is not enough, and that is measured, not feared:**

> Across the fixes for **D8, D9 and D10** the signature of the x86 suite stayed
> **byte-identical** (`e419003d625f`, 500 runs per state). Three real core errors, and the suite
> triggered none of them. **"All tests green" is therefore a necessary and not a sufficient
> criterion for a rewrite.**

From that follows acceptance in **three** parts, not one:

| | Criterion |
|---|---|
| **A** | the 14-point acceptance green, in all RAM sizes and on both architectures |
| **B** | **differential test against the Rust version**, module by module: same inputs, same outputs, same refusal codes. That is the part that would have caught D8/D9/D10 |
| **C** | the **repeat measurement** holds: `RUNS` signature comparison with cross-comparison between the streams — and a null finding needs its sample size, not merely a green field |

**The order is forced, not chosen:** module by module, both versions alive at the same time.
A big cut switches off, for its duration, exactly the series that found every one of the 100
entries — abort condition 4.

- [ ] **The test suite itself is the last move, not the first.** It is 15,7 % of the code and
      consists of `check` promises; it stays in Rust until the Gabbro version is proved **against
      it**. Whoever rebuilds their instrument first measures the rebuild with the rebuild.

---

## 6. The costs, honestly

**The compiler.** The seven constructs were "a generator of weeks". Stages 0–6 are the
class ATS / F\*-Low\*-KaRaMeL / Verus — the work of several research groups over years.
**I do not have a defensible estimate**, and an invented one would be worse than none; which is why
gates stand above instead of a date.

**The migration.** 66 651 lines, and the denominator is no argument in itself: what matters is that
every migrated module brings its differential test with it.

**The counter-calculation that has to be done first:** class S (36) and class M (36) are today
**not unaddressed**. Rust-today found `Parked`. Verus can do resource invariants via linear ghost
permissions. Loom found the weakened ordering as soon as the cell was in the model.
**For every stage this belongs answered: what can Rust+Verus+Loom already do today, and what is
left over?** Only the remainder justifies a language.


---

# The finish line

## DONE — when plan and syntax stand

**This file exists because this folder has a pattern.** `HISTORIE.md` carries it: **every fallen
gate was survived by refounding**, and the hard gate migrated behind the compiler in the process.
An autonomous run without a named finish line is the same pattern with more throughput.

**Here stands the finish line, in advance, and it is mechanically checkable where that is possible.**

> **Since 2026-08-14 there is a sharper plan with the same properties:**
> [`SPRACHE.md`](SPRACHE.md) §6 — **P0 to P7, every stage with a two-sided gate, and the
> ordering rule "no checker line before gate P1"**. It does not replace this file, it makes it
> concrete: A1 is P1, A4 is P0.

> **The run does not abort.** What used to be an abort has been **escalation** since 2026-08-14 —
> see section C. Aborting happens only at **proven** impossibility, and what that would look like
> stands there as well, so that the reason is not empty.

---

### The goal that is checked against

> **A language in which you write kernels, drivers and programs DIRECTLY — hardware access via
> hardware assumptions — and which delivers everything for a Gold proof EXCEPT the logic proof itself.**

---

### A — The syntax stands when all eight points hold

| | Condition | checkable by | State |
|---|---|---|---|
| **A1** | The grammar is **closed**: no used, never defined non-terminal | `./instrumente/pruefe-syntax.sh` | **satisfied** (100 rules, 0 open) |
| **A2** | All open items are **decided or measured** | counting them out | **satisfied** — `SPRACHE.md` §18 decides F1–F9; what remains are measurements |
| **A3** | **Every Caprock area has a verdict** — expressible / needs construct X / not expressible —, **each with a written-out fragment as evidence** | `FRAGMENTE.md` | **6 of 10** — scheduler, MMU, loader, parser/checkpoint are missing |
| **A4** | The **logic/plumbing split** is measured on at least five fragments, and **no plumbing obligation is left hanging unnamed** | `BEWEIS.md` | **never measured** |
| **A5** | A **driver** is completely written out | `FRAGMENTE.md` | **satisfied, with a finding** |
| **A6** | A **userspace program** is completely written out | `FRAGMENTE.md` | **does NOT fit** — `forever` had no exit; since today `leaves`/`leave` |
| **A7** | The **test scaffolding** is written out | `FRAGMENTE.md` | **satisfied, with a finding** |
| **A8** | **Every construct has its C lowering written down**, not claimed | per rule | 18 claims open |

#### The areas for A3

`caprock-cap` (table+CDT) · `caprock-sched` (queues) · IPC/`threads` (concurrency,
872 `Ordering::`) · `mmu` (hardware contract+algorithm) · IOMMU (`vtd`/`irte`/`dmar`/`smmu`) ·
`caprock-virtio` (rings, device ownership) · parser (`part`/`fat`/`checkpoint`) · loader (code as
data) · test scaffolding · `programs/` (userspace).

---

### B — The plan stands when

| | Condition | State |
|---|---|---|
| **B1** | Every phase has a **gate**, and as long as it is checkable without a compiler, that is what it is | satisfied |
| **B2** | The abort conditions stand on the **criterion**, not on a number | satisfied |
| **B3** | The phases are **consistent with the measured results** — no gate that a measurement has already refuted | to be checked after every result |
| **B4** | There is **no second path** and no fallback cut | satisfied |

---

### C — ESCALATION instead of abort

**Decided on 2026-08-14: the run does not abort.** Aborting happens **only at proven
impossibility** — and a finding "does not work" is not one. It is a **design task**, exactly as in
[`SPRACHE.md`](SPRACHE.md): not *"is that possible?"* but *"what must
minimally stand there for it to be possible?"*

| Situation | **formerly: abort** | **now: escalation** |
|---|---|---|
| A **plumbing obligation is left hanging** and no construct takes it off | run ends | **the construct that takes it off is designed** — with a minimal statement and a C lowering. If that does not succeed, the **impossibility is written down**, the work is not ended |
| A point from **A** has been touched three times and not closed | run ends | it becomes a **named blocker** and gets its own targeted round instead of further attempts on the side |
| Two rounds produce **more design than measurement** | run ends | **the number is reported, not obeyed** — see below |

#### What remains of abort reason 2: the number, without the effect

The counter is **kept running and named in every round**: new lines in `SYNTAX.md`,
`SPRACHE.md`, `PLAN.md` against new lines in result files. **It no longer stops anything, but it
stays visible** — a signal you switch off is not there the next time, and exactly this class is
carried by `HISTORIE.md` as trap 30 ("a guardian that keeps screaming after its fix gets switched
off"). Here the solution is to **decouple** it from the verdict instead of removing it.

#### What "proven impossible" would mean

So that the only remaining abort reason is not empty, here is what it would look like. **Two
forms, and only these:**

1. **A demanded property is not decidable** and also not replaceable by a named
   assumption. *Example of the form:* general liveness ("this thread runs
   eventually") over unbounded executions — no type system decides that, and a
   `progress assume` replaces it only if a falsifier can be built.
2. **Two demanded properties contradict each other.** *The candidate already known today:*
   **genericity demands monomorphisation, and that is the first non-flat lowering** —
   it attacks M-Gold-2 ("syntax-directed, non-optimising"). Wanting both at once is
   possibly contradictory; **that is to be shown, not to be presumed.**

**Both have to be written down, with the argument.** "I see no way" is not a proof —
that would be a null finding without a size, and that trap stands in the register.

### D — What does NOT count as completion

* **A compiler.** It stands as P3 in the plan, behind five gates. This file describes paper.
* **A pretty number.** The criterion is a kind, not a quantity (`BEWEIS.md`).
* **"All constructs present".** A construct without a written-out fragment and without a
  C lowering is a claim.
* **A green guardian.** `pruefe-syntax.sh` checks closure and vocabulary — **not** whether real
  code fits into it. It has itself already delivered a false green.

---

# A — The path to the goal "everything except functional correctness"

**Entered 2026-08-14, after a re-sorting of the 31 fragment findings against this goal.**

The goal is narrower than the original ambition and **therefore reachable**: Gabbro is to carry
the **plumbing** completely — index, overflow, alias, frame, lock, race, termination, phase,
leafness, publication, refinement — and to leave the **logic** to the human. Functional
correctness (Gold) is **outside**, not postponed.

## The re-sorting — what the goal takes away

The fragment balance (`FRAGMENTE.md`, 31 findings) was judged against the **full** ambition.
Read against this goal, the greater part drops out:

| Finding | against Gold | against this goal |
|---|---|---|
| **«B13»** no aggregation, no cross-table domain — `refcount_matches` unformulable | **deadly**, "the most expensive finding at F1" | **out.** `o.refcount == count(…)` names *the subject*, not the machine — that is logic |
| **«B29»** `refcount -= 1` falls only via that invariant | connected with B13 | **in, but local:** `if refcount >= 1 { … }`, V1 carries it. You lose "the counter is correct", you keep "it does not run under" |
| **«B12»** no numeric-range domain | postconditions over message words | **out** — frame statements run over `slots of` |
| **«B15»** no genericity | — | **cost, not impossibility** (duplication per table) |
| **«B7»** no composite literal · **«B27»** no `abi` block | — | **they block the WRITING, not the PROVING** — additive constructs |
| **«B9»** `fnptr` without a contract | — | **in and load-bearing** — see A2 |

**Four items remain.** Three are designed and unbuilt; **one is not solved but merely grazed**,
and it therefore stands first.

---

## A1 — `own` linear. **Paper, not a line of code. The only item that can force a fifth mechanism**

### The finding

`SYNTAX.md`:10 counts **"alias"** among the things every rule settles by construction. **The
mechanism for it is nowhere to be found.** M3 gives address *spaces*, not separation within
one space; nothing forbids calling `delete_leaf(c : ptr<normal,rw> CapSpace, o : ptr<normal,rw>
CapObjects, …)` with the same pointer for both. `effects` only **declares**, and
`BEWEIS.md` says it itself: *"`restrict` generated from `effects`. **If `effects` is wrong, that
is C UB**"*. **The frame statement thereby rests on a promise instead of on a condition** —
exactly what the criterion forbids.

### The proposal, and it comes from the folder itself

The derivation table in `SPRACHE.md` §3b says: *"`region`, ownership → **M2** → a linear
block is its region."* The **intention** stands there, the **grammar** does not: `own` is today a
right on the pointer type, and pointer types are copyable.

> **A pointer that carries `own` is a linear value.** Two of them onto the same object cannot
> exist; separation falls out of M2 instead of out of a promise. Borrowing works as with the
> boot phase: `requires` names the witness, `consumes` in `effects` consumes it.

### The test — and the place at which it will fail, if it fails

Two fragments, by hand, against the new rule:

1. **F1 `delete_leaf(c, o, a, rf, s)`** — four pointers, two of them with `own`
   (`PhysAllocator`, `Finalized`).
2. **F1 `revoke`** — and **here sits the question**: the body calls `delete_leaf` in a
   `traverse` loop. **A linear value that goes into a loop body is consumed after the
   first pass.** Either `own` pointers are handed over on loan (`requires`
   instead of `consumes`), or the loop is not writable.
3. **F3 IPC fastpath** — the counter-probe on a body without a traversal.

> **Gate, two-sided:**
> **Green** — both fragments stay writable, the loan carries the loop, and **no construct** is
> added beyond the one grammar line. Then separation is M2, Gabbro
> keeps four mechanisms, and A2–A4 follow.
> **Red** — separation needs a **fifth mechanism of its own**. An entry in
> `HISTORIE.md`, and then the counter-calculation rule of this plan applies: **for every further
> mechanism the opponent is to be measured — and the opponent here is called Rust.** Rust's
> borrow checker *delivers* separation. The justification of the language today stands on **one**
> mechanism (real linearity); if it needs a fifth that Rust already has, it becomes
> narrower, not wider. **That is not an abort, but it is the most expensive conceivable answer.**

**Effort:** half a day to a day of paper. **Not a line of checker code before this gate** — the
folder's rule, and this time it is being observed.

---

## A2 — Count dynamic calls. **One `grep`, and it decides whether a construct is necessary**

### The finding

`fnptr` carries no contract («B9»). **At every call through a function pointer the frame
statement is empty** — you do not know what the callee touches, so no
`effects` list covers it. Caprock uses `&mut dyn SchedOps`; `fnptr` is the replacement and loses
exactly what it was there for.

### The measurement, before the design

Count: **every site in the core** at which a call is not statically resolved
(`dyn`, function pointers, jump tables) — with the site, and separated into *replaceable by
`match`* and *not replaceable*.

> **Gate, two-sided:**
> **≤ 10 and all replaceable** — dynamic calls are **prohibited**. No new construct,
> the prohibition list grows by one line, and the frame statement is total everywhere.
> **Otherwise** — `fnptr` gets `requires`/`ensures`/`effects`, and **the effects of the
> caller must cover those of the pointer type**. That is a grammar change plus a
> pass share, and it then belongs in the same stage as A4.

**Effort:** one hour. **It stands before A3 and A4, because it is cheap and can save a
construct.**

---

## A3 — `table … count N`. **One line of grammar, and it lifts M4 from a convention onto the language**

### The finding (G8, 2026-08-14)

A `table` **does not name its slot count**. `index into T` thereby has no ceiling from the
declaration; the bound hangs on an index type **chosen to fit by hand**
(`type SlotIdx = u32 in 0 ..< NSLOTS`), and **nothing binds the two together**. "No
unchecked indexing" rests at this point on a convention. That is why the compiler today checks
indices only against `[T; N]`.

### The proposal

```
table    = "table" ident [ "count" constexpr ] "{" { … } "}" ;
slottype = … | "index" "into" ident | "option" "index" "into" ident | … ;
```

`index into T` inherits the bound from `T`'s `count`. The index type is **generated**, not
written.

> **Gate, two-sided:**
> **Green** — every `index into` site of the six fragments gets its bound without a
> hand-written index type, and the `narrow` number over the corpus **does not grow**.
> **Red** — a table whose capacity is only fixed at runtime (allocated at boot).
> Then `count` does not carry it, the bound stays a declaration, **and that is to be booked as
> a finding instead of defined away as a special case.**

**Effort:** one day (grammar, parser, M1 share, bringing the fragments up to date). **Before A4,
because the traversal costs need a domain bound.**

---

## A4 — The cost model. **Pass 9, and without it termination is declared instead of checked**

### The finding

`costs`, `held`, `per_pass`, `bounded` were **declarations that nobody recomputes** — *until the
cost pass was built. Since then `gabbro kosten` prints the computed body figure next to the
promised one and the computed hold time next to `held` / `shared held` (`kosten.rs`, `K001`–`K004`,
WERKZEUGKASTEN W2). The finding below is therefore a record of 2026-08-13, not a state.*
Thus it holds:

* `retry … bounded N ops` **claims** termination, it does not check it;
* the lock hold time on which the whole latency statement hangs (§9.3: *"higher-ranked hold ≤
  their `held` sum"*) is unevidenced;
* `forever … per_pass bounded N ops` — the only form that is allowed to run forever — carries
  its justification in an unchecked number.

### The model already stands (`SPRACHE.md` §7)

**1 op = one Gabbro primitive** (assignment, arithmetic operation, load, store); a
call counts the declared `costs` of the callee; a traversal counts body costs ×
domain bound; branches count the maximum. **Static, no solver.**

> **Gate, two-sided — and it measures the declarations, not only the pass:**
> **Green** — the computed bounds of the written-out fragments fit inside their
> declared ones: `unlink` ≤ 40, `delete_leaf` ≤ 200, `revoke` ≤ 4096.
> **Red** — they do not fit. Then **it has to be said which side is wrong**: the model (one
> primitive is not one op) or the declarations (the numbers were guessed). *An
> adjustment without that statement is exactly the movement the measurement protocol is
> written against.*

**Effort:** two to three days. **Needs A3.**

---

## A5 — Acceptance of the four items

Only once A1–A4 are green:

1. **Pull the six fragments up to the fourth version** and judge them anew — with the
   compiler, not by hand.
2. **The full `narrow` count with the compiler** over Gabbro source text. That makes the
   bar `≤ 24` **really decidable for the first time** — today it is missed by a factor of 6–13
   with an uncalibrated counter, and whether that hits the language or the counter is open.
3. **The four areas never written out** (scheduler, MMU, loader, parser) as fragments.
   *An area without a fragment is a presumption* — and that is where the forms sit that do not
   fit into `traverse`.

## What is NOT contained in A1–A5

**Five checking passes are still missing** — D1/D2, M3, M2, pairing, costs. A4 is the last of
them; *(as of 2026-08-13. `gabbro paesse` counts **ten** passes today, none open — three fully
built, seven partial, each partial one resting on a named item.)* **M2 is the precondition for A1 being checked at all** (A1 decides the
grammar, M2 enforces it). The order is therefore:

> **A1 (paper) → A2 (grep) → A3 (grammar) → M2 pass → A4 (costs) → A5 (acceptance)**

And further out, unchanged: **pairing** (race freedom), **M3** (rights at the pointer),
**D1/D2**, the **C emission** and the **C form table** (40–60 entries, unwritten).

## The abort condition for this path

**A1 red AND the fifth mechanism is Rust's borrow checker.** Then an existing
tool delivers two of the five mechanisms (separation and — affinely — linearity), and the
question from `TODO.md` *"is one mechanism enough to justify a language?"* answers itself
downwards. **That is not a proof of impossibility and therefore not an abort under section C** —
but it is the point at which a contribution to Verus would be cheaper than this language, and
that would then belong written down instead of circumvented.

---

# COVERAGE — what the syntax carries, what it does not, 2026-08-16

**This assessment is written against measurements, not against expectation.** Where a number
stands, its source stands beside it; where none stands, the sentence says *"estimated"*.

## What is covered — and the strongest number is one nobody expected

| | Coverage | Source |
|---|---|---|
| **loop forms** | **0 of 571 `for` loops** in the kernel run over something that is not a domain | B3, full count R14(c) |
| **traversability** | **99,04 %** of the kernel lines are writable as a traversal | B3 (`p = 0,96 %`) |
| **plumbing** | **8 of 11** classes carried | re-survey + frame post-booking |
| **checker** | 10 passes, **90 refusals**, 63/63 mutations | `gabbro paesse` |
| **convergence** | four area fragments, **0 new constructs**; one measurement, **1** | convergence metric, «B41» |

> **The 0 of 571 is the finding that carries the language** — and it went against expectation.
> The non-traversability sits entirely in `while`, `loop` and in loopless
> bodies, not in the loops one would have suspected.

## What is NOT covered — cut by necessity, not by effort

### NEEDED — **four**, not five (corrected 2026-08-16 after the closure count)

| | Gap | measured |
|---|---|---|
| ~~1~~ | ~~**Closures**~~ — **struck.** The count found two large patterns and both are decided: 25× allocator callback (= A2) and 3× edge function (= «B41», the line stands) | 64 instead of 89, gate void |
| **2** | **The emission** — C and annotation, **both at zero** | 0 of 2 surfaces, 0 mutations |
| **3** | **The preservation** of the group invariant — the form stands, the proof obligation has no recipient | S16/S17, 15 templates unproven |
| **4** | **Genericity** — without it every table needs its own `traverse` | unmeasured (estimate) |
| **5** | **Error propagation** — `let … else` is the only one, and `U006` has shown that it is at the same time the **quietest door out** | 1 form for everything |

> **The item that was the only one called *"whether"* was not hard — it was blurred.** After
> the count of 2026-08-16 it has fallen apart into **two already decided *"how"s***, and what
> remains of P2 (441 closure literals) is correctly called *"does Gabbro need iterator
> adapters?"* and hangs on **genericity** — item 4, not on closures.
>
> **The hardest of the remaining four is thereby the emission**, and with it the
> question is *how*.

### PRACTICAL — small build, measured need, immediate yield

* **`ancestors of`** — one domain line, the same generation logic as `descendants of`.
  **4 bodies in DMAR/PCIe**, and it is the first construct need *measured* by the convergence
  metric.
* **Variable lengths in `format`** — the hard 20 % of every parser generator. *The yield is
  smaller here than it looks:* «B40» measured that `format` **wins brevity, not
  safety**.
* **`touches` finer** — today too coarse for *"changes the set only by removal"*.
* **Amortised bound checking** — `bounded N ops` does not have to check on every pass.

### THEORETICALLY POSSIBLE AND INTERESTING — this is where the research lies, not the work

**1. The chain via a declared edge function.** The general case of `chain(a,b)`:
`traverse … over chain via f` with `f` pure and M1-typed, like the `update` body of
`exchange`. **It would swallow `ancestors of` along with it** and reduce the three «B41» gaps
to one. *The open question is not the implementation but the line:* a
declared function inside a domain is a step towards a stock of quantifiers, and that is exactly
where the boundary between "language" and "prover" migrates if nobody pays attention.

**2. Traversal that mutates the structure it has walked.** Union-find with path compression:
`find` writes the chain it walks. **That is not a missing domain but the
entanglement from P0.1 attempt 1, disguised as a read operation.** Theoretically interesting,
because a domain with a *mutable witness ordering* needs a well-foundedness argument that
survives the mutation — and that is exactly the template nobody has written. **My
prediction stands: it gets no traversal form.**

**3. The lock order as an order instead of as a number.** `rank 2` is a total order where a
**partial order** would suffice — two locks that never meet each other need no
rank comparison. *Practically: the numbers work and have been recomputed since `H006`.
Theoretically: a partial order would be more honest and would wrongly reject less.* No
measured need — not yet.

**4. Binary verification.** The only path that takes the **lowering** out of the trust base.
Everything else in this folder shifts trust; this item removes it.

**5. Reusable specification theories.** They help the **second** project, not
this one — and may therefore appear in no metric of this folder.

## The verdict in two sentences

> **The syntax is nearly finished, and that is the less important half.** Four
> area fragments demanded zero new constructs, the whole kernel one — the vocabulary
> converges demonstrably.
>
> **What does not converge is the trust surface.** 19 templates, 4 of them proved (as of
> 2026-08-17) — and **the four made the register grow, not shrink**: two
> of them were added on a single day. *Whoever asks how much of Gabbro is still missing is
> measuring against the wrong denominator as long as this list has no length in progress.*


---

# K100 — der Weg auf 100 % Klempnereiabdeckung

**Ziel, in der Fassung des Auftrags:** *der Programmierer beweist nur noch seine eigene Logik —
im Vertrauen auf Gabbro und seine Hardwareannahmen.*

**Ausgangslage, gemessen 2026-08-17** ([`PFLICHTEN.md`](PFLICHTEN.md)): 173 Klempnereipflichten
über den zehn Fragmenten, **137 getragen**, **31 hängend**.

---

## Die Falle steht im Plan, nicht in der Rückschau

**Klempnereiabdeckung und Vertrauensfläche sind kommunizierende Röhren.**

Jedes Konstrukt, das eine Pflicht schließt, ist eine **Schablone** — eine Beweispflicht des
Erzeugers, die *einmal* fällt, aber heute unbewiesen dasteht. Das Register führt **20 Einträge,
16 unbewiesen, 4 davon lebend.** Die 24 Notationslücken zu schließen kostet nach heutiger
Schätzung **sieben weitere Einträge**.

> **Ein Plan, der nur `H` verfolgt, erreicht 100 % und ist danach schlechter dran.** Er hätte
> die Klempnerei vom Menschen in eine unbewiesene Fläche verschoben und die Verschiebung nicht
> gezählt — *dieselbe Bewegung, gegen die die Ratsche steht.*

**Deshalb hat K100 ZWEI Zahlen, und beide sind Tore:**

| | |
|---|---|
| **`H → 0`** | keine hängende Klempnereipflicht über dem Korpus |
| **`L ≤ 4`** | die **lebend unbewiesene** Schablonenfläche wächst nicht — jeder neue getragene Eintrag kostet vorher einen Isabelle-Lauf |

*Wer nur die erste erreicht, hat die These nicht eingelöst, sondern umgetopft.*

---

## Und ein Teil der 31 wird nicht geschlossen, sondern UMGEBUCHT

**Der Auftrag sagt es selbst: *„mit Vertrauen auf Gabbro und seine Hardwareannahmen."*** Fünf
der 31 sind Aussagen über die Maschine, nicht über das Programm:

| | |
|---|---|
| «B19» | welche Barriere eine Veröffentlichung an ein Gerät braucht |
| «B38» | dass `masks IRQ` denselben Schutz gibt wie eine Sperrgrenze |
| «B39» | dass die MMU `A`/`D` schreibt **und nichts sonst** |
| `at dma` | welche Barriere ein DMA-Zugriff verlangt |
| `atomic release` | dass ein Release-Speichern die Sichtbarkeit **herstellt** |

**Für sie gibt es den richtigen Ort schon:** `assume … falsifier …`. Eine Pflicht dorthin zu
bewegen heißt **nicht**, sie zu erledigen — es heißt, sie **beim Namen mit einer Sonde** zu
führen, und genau das ist die Vertrauensform, die der Auftrag gewährt.

> **Die Umbuchung ist nur dann ehrlich, wenn sie gezählt wird.** `gabbro annahmen` steht heute
> bei **14**; nach K100 muss dort **19** stehen, und die fünf neuen müssen ihre Sonde nennen
> oder ihren Grund, warum es keine gibt.

---

## Die vier Phasen

### K100.1 — Die Messgröße schärfen *(keine Zeile Code, und sie senkt `H` um 2)*

**Drei der 31 sind handgeschriebene `narrow`. Sie sind nicht dasselbe:**

| Stelle | `else`-Zweig | was es ist |
|---|---|---|
| `FRAGMENTE.md`:1660 (F10) | **erreichbar** — ein feindliches DTB nimmt ihn | **Logik**, kein Klempnerrest: die Aussage *„dieser Eingang ist feindlich"* ist die des Programmierers |
| `:268` (F1) | erreichbar, wenn die Buchführungsinvariante schon gebrochen ist | das zweite Netz, mit Absicht |
| `:1100` (F6) | **kann nicht genommen werden** und muss dastehen | **ein Loch in M1** — die Schranke fällt aus der Domäne, und M1 sieht es nicht |

**Nur die dritte ist eine Klempnereipflicht.** Die erste ist Logik, die zweite eine bewusste
Doppelung.

* **Tor:** `zaehle-bereichspflichten.py` unterscheidet die drei Fälle. *Ein Maßstab, der eine
  Prüfung nicht von einem Ritus trennt, misst das Falsche.*
* **Ertrag:** `H = 31 → 29`, und die Zahl bedeutet zum ersten Mal etwas Einheitliches.

### K100.2 — Die Umbuchung in die Axiomschicht *(5 Pflichten)*

Die fünf oben, jede mit `assume … falsifier <sonde>` oder `unfalsifiable "<grund>"`.

* **Tor:** `gabbro annahmen` meldet **19**, und `pruefe-emission.sh` findet alle neunzehn im
  erzeugten C wieder (der Kanal steht seit dem 2026-08-17).
* **Preis, ausgesprochen:** die Vertrauensbasis wächst um fünf Sätze über die Hardware. **Zwei
  davon werden vermutlich unfalsifizierbar sein** — eine Sonde für „die MMU schreibt nur `A` und
  `D`" müsste die MMU anhalten.
* **Ertrag:** `H = 29 → 24`.

### K100.3 — Die acht Notationslücken *(24 Pflichten, der Hauptteil)* — **AUSGEFÜHRT**

| Lücke | was fehlt | Schablone? |
|---|---|---|
| «B3» | `Held(Lock)` — `typedecl` verlangt `params`, die Beispiele schreiben Typen | nein |
| «B6» | eine Bindung für den Rückgabewert in `ensures` | nein |
| «B7» | ein Verbundliteral — eine Funktion kann heute keinen `structty` **herstellen** | **ja** |
| «B14» | `option` in `typeexpr`, und `let … else` auf einem `place` | **ja** |
| «B21» | `accumulates max/min/+` — 213 RMW-Stellen | **ja** |
| «B22» | ein mehrzeiliges `claim` | nein |
| «B25» | eine Wertemenge statt eines Intervalls | nein |

* **Reihenfolge:** die vier ohne Schablone zuerst — sie kosten Wortschatz, aber keine
  Vertrauensfläche. Die drei mit Schablone **je einzeln, und jede mit ihrem Isabelle-Lauf
  davor**, sonst reißt `L ≤ 4`.
* **Tor je Lücke:** ein Giftbeispiel, das ohne das Konstrukt **fällt** — und `pruefe-wortschatz.py`
  hält die Terminalzahl gegen die Tabelle.
* **Ertrag:** `H = 24 → 0` bei den Notationsposten. **Es bleiben die sieben Absenkungen.**

> **AUSGEFÜHRT 2026-08-17. `8 von 8`, und der Ertrag kam anders als geplant.** Fünf der acht
> waren **bereits zu** — der Plan las den eingefrorenen Befundtext, nicht die Grammatik
> (`./instrumente/pruefe-notation.py` misst jetzt am Prüfer). Gebaut wurden «B22», «B14b» und «B7».
>
> **«B7» war die einzige echte Entscheidung, und sie war keine Notationsfrage:** ein
> geschweiftes Literal wäre die erste Ausdrucksform, die mit `{` weitergeht, und an 76
> Korpusstellen folgt ein `{` direkt auf einen Ausdruck. *Der Fehlerfall eines
> Kontextschalters ist still.* Gewählt ist der markierte Ruf `P(a: …, b: …)` — und die
> Markenpflicht kommt aus dem Beweis, nicht aus dem Geschmack: `deckt fs zs ⟷ map fst zs = fs`.
>
> **Das Tor je Lücke ist erfüllt und um seine Gegenrichtung erweitert:** sechs Gegenproben,
> je eine Form, die die Entscheidung verbietet, mit dem Absagecode, den sie auslösen muss.
> *Eine Entscheidung, die kein Wächter kennt, ist eine Meinung.*
>
> **Und `L ≤ 4` hält:** `verbund.konstruktor` ist jetzt **getragen** und war **vorher**
> bewiesen. `lebend_ungedeckt()` steht unverändert bei 4 — genau dafür stand das zweite Tor.

### K100.4 — Die Verfeinerung *(7 Pflichten, und sie ist die härteste)* — **Weg (b) gebaut**

Sieben Fragmente sind nicht abgesenkt. **Fünf davon sind durch Befunde gesperrt**, nicht durch
Arbeit — «B10», «B12», «B17», «B24» und die Domänenschranke von `mappings of`. *Die fallen mit
K100.3 und den Entscheidungen, nicht mit Erzeugercode.*

**Aber `H = 0` an den zehn Fragmenten ist NICHT die Verfeinerung.** Verfeinerung ist eine Aussage
über **jede** Absenkung, und zehn gemessene Dateien sind keine.

**Dafür gibt es genau zwei Wege, und der Plan muss einen wählen:**

| | |
|---|---|
| **(a) verifizierter Erzeuger** | `emit.rs` selbst nach Isabelle. *Groß, einmalig, und es ist das, was CompCert getan hat* |
| **(b) Übersetzungsvalidierung** | je Übersetzung ein maschinell geprüftes Zeugnis, dass **dieses** C **dieses** Gabbro erhält. *Kleiner je Schritt, aber jedes Mal fällig* |

> **(b) passt zu diesem Ordner.** Die Differenztests sind bereits die schwache Fassung davon —
> sie messen **ein** Ergebnis statt aller. *Der Weg von hier ist, aus `pruefe-emission.sh` ein
> Zeugnis zu machen, nicht eine längere Liste von Beispielen.*

> **AUSGEFÜHRT 2026-08-17.** `gabbro zeugnis <datei>` — fünf Abschnitte je Datei: Annahmen,
> Schablonen, direkte Absenkung, Gelöschtes, **Fremdes**. *Es beweist die Übersetzung nicht; es
> zählt auf, worauf sie ruht* — und damit wird aus „ich vertraue Gabbro" eine Liste mit Länge.
>
> **Die Einordnung ist eine ZWEITE Lesung**, unabhängig von der `match`-Kaskade des Erzeugers
> geführt. Senkt der Erzeuger etwas ab, das keine Einordnung kennt, meldet das Zeugnis
> `UNZUGEORDNET`. *Das ist der Fall „der Erzeuger ist gewachsen und hat es niemandem gesagt".*
>
> **Und genau den fand die Kreuzprobe beim ersten Lauf.** `lock KAPPEN protects … rank 3;`
> senkt zu vier Prototypen ab; `beispiele/10` und `/13` übersetzen damit sauber, und keine
> Einordnung kannte die Form. Daraus wurde die fünfte Klasse **FREMD**: weder direkt (die
> C-Form IST nicht die Gabbro-Form) noch erzeugt (es entsteht kein Rumpf), sondern **ein
> Versprechen an eine Funktion, die es in dieser Übersetzungseinheit nicht gibt.**
>
> **Das Zeugnis wird verglichen, nicht gedruckt:** je Übersetzungseinheit steht sein Befund
> gebucht in `pruefe-emission.sh`. Wer eine Form umklassifiziert, fällt dort.
>
> **Was (b) NICHT ist, und es steht in derselben Ausgabe:** ein Zeugnis über *diese* Übersetzung
> ist keine Aussage über *alle* Eingaben. Die vier Zeilen sagen, worauf die Übersetzung ruht —
> nicht, dass sie hält. *Die stärkere Fassung von (b) bliebe ein maschinell geprüftes Zeugnis je
> Übersetzung; dies ist die aufzählende Vorstufe davon, und sie ist als Vorstufe benannt.*

---

## Wann K100 erreicht ist — und wann die Zahl lügt

**Erreicht:**

```
H = 0        über dem Fragmentkorpus, mit ./instrumente/zaehle-pflichten.py neu abgeleitet
L ≤ 4        lebend unbewiesene Schablonen
A = 19       Annahmen, jede mit Sonde oder mit Grund
```

**Und die Zahl lügt, wenn eines davon fehlt:**

> **Die zehn Fragmente sind nach ihrer SCHWIERIGKEIT gewählt, nicht zufällig.** `H = 0` über
> ihnen ist keine Aussage über Gabbro. **K100 ist erst dann eine Messung, wenn ein ZWEITER
> Korpus danebensteht, den niemand beim Bauen angesehen hat** — sonst ist es Falle 80 in
> Reinform: eine Zahl, die man erreicht, indem man auf sie hin baut.

*Der zweite Korpus gehört in denselben Plan wie das letzte Konstrukt, nicht danach.*

---

## Stand am 2026-08-20 — und das erste Tor hat einen BODEN

| | Ziel | heute | |
|---|---|---|---|
| `H` | 0 | **12** | 5 verankert + 7 Absenkungen; Start war 31 |
| `L` | ≤ 4 | **1** | getragen und unbewiesen; daneben aber **9 Prämissen ohne Pass** |
| `A` | 19 | **32** | jede mit Sonde oder mit ausgeschriebenem Grund |
| zweiter Korpus | vorhanden | **«K2», fünf Fragmente** | fremde Autorenlinie; drei sind ganze Module, alle drei prüfen sauber und senken ab |

**`H = 0` über diesem Korpus ist nicht erreichbar, und der Grund ist kein Arbeitsrest.**
Die Absenkungspflicht lautet *„das erzeugte C rechnet, was das Fragment sagt"* — **an der
Ausführung gemessen**. F5 ruft `map_window`, `pool_new`, `probe_ecam` und deklariert keins
davon; F2 und F9 lassen Bitlagen unbenannt. **Das sind keine Lücken in Gabbro, das sind die
Merkmale eines AUSSCHNITTS** — und `FRAGMENTE.md` trägt seinen Einfriersatz.

> *Ein Ausschnitt lässt sich nicht ausführen.* Diese zwei zu schließen hieße, eine
> eingefrorene Datei zu ändern — das ist nicht das Schließen einer Pflicht, sondern das
> Verschieben des Maßstabs.

**Es ist dieselbe Bewegung wie K100.1, eine Ebene höher und dort nicht zu Ende geführt.**
Jene Phase trennte unter drei handgeschriebenen `narrow` die Prüfung vom Ritus. Die
Absenkungsspalte zählt bis heute *„Gabbro kann das nicht"* und *„dieser Text ist kein
Programm"* in einer Zahl.

> **Und die Aufteilung ist nicht fünf zu zwei — sie ist sieben zu allen.** Der Satz oben
> stand eine Stunde lang als *„fünf der sieben gehören Gabbro, zwei dem Korpus, der Boden
> ist `H = 2`"*. **Beides falsch, und die Auszählung hat es gesagt:** *jedes* der sieben
> trägt mindestens einen korpusseitigen Riegel. 41 Stellen nennen 20 Namen, die niemand
> deklariert; neun `let … else` rufen Rümpfe, die diese Einheit nicht kennt; sechs Bitlagen
> sind unbenannt; eine Tabelle nennt kein `tree`. **F4 — das reinste — braucht genau eine
> Zeile: `MAX_POLL`.**
>
> **Der Boden von `H` aus Gabbros Richtung allein ist damit `7`, nicht `2`.** Die fünf
> verankerten Pflichten lassen sich bauen; **die Absenkungsspalte fällt um keinen einzigen
> Punkt**, ohne in eine Datei zu schreiben, die von sich sagt, sie sei ein Bericht und bleibe
> unangetastet.
>
> *Das ist die schärfere Fassung desselben Befundes: sieben Zwölftel von `H` messen die
> Vollständigkeit des Korpus, nicht die Deckung von Gabbro.*

### Und damit steht eine Entscheidung über den MASSSTAB an, nicht über den Prüfer

Drei Wege, und nur einer ist ehrlich:

| | |
|---|---|
| **(a) den Einfriersatz aufheben** | dann ist der Bericht kein Bericht mehr, und jede frühere Zahl über ihm wird unnachrechenbar |
| **(b) die Pflicht auf eine VERVOLLSTÄNDIGTE KOPIE verlegen** | `messung/fragmente/` — dieselben zehn, um ihre fehlenden Deklarationen ergänzt, ausführbar. Die Absenkung wird dort gemessen, `FRAGMENTE.md` bleibt Bericht. **Derselbe Zug, den «K2» schon gemacht hat**: nachgebildet, nicht übersetzt — und dort ausdrücklich gesagt |
| **(c) die sieben als „nicht anwendbar" buchen** | `H` sinkt, ohne dass etwas geprüft wurde. *Falle 80 in Reinform* |

**(b) ist der Weg.** Er kostet die ~60 fehlenden Zeilen einmal, er lässt den eingefrorenen
Bericht in Ruhe, und er sagt in der Kopfzeile der Kopie, was ergänzt wurde — damit bleibt
nachrechenbar, welcher Teil gemessen und welcher geschrieben ist.

### AUSGEFÜHRT 2026-08-20 — [`messung/fragmente/`](../messung/fragmente/)

```
$ ./instrumente/zaehle-fragmente.py
7 von 10 prüfen sauber        (über den Ausschnitten: 5)
4 von 10 senken ab            (über den Ausschnitten: 3)
```

Ergänzt wurden **nur** Deklarationen, die ein Ausschnitt ruft und nicht nennt — 20 Namen, fünf
`extern fn` mit Fehlerkanal, zwei `assume` mit Sonde, sieben `reserved`-Felder, ein Träger für
`irq`. Nichts umgeschrieben, nichts weggelassen, keine Absage wegdefiniert.

> **Wo ein Fehler nach der Vervollständigung stehen bleibt, gehört er Gabbro** — und genau das
> ist der Ertrag. Aus *„der Ausschnitt ist unvollständig"* wird eine Liste mit Adressen.

**Drei Befunde, die der eingefrorene Korpus nicht zeigen konnte**, weil sie erst sichtbar
werden, wenn die fehlenden Deklarationen da sind:

| | |
|---|---|
| **`A::B` parst und wird nie aufgelöst** | Der Namenspass liest die **erste Silbe** eines Pfades und schlägt sie als Wert nach. `IpcResult::Ok` fällt als `M119` — gleichgültig ob `module`, `reason` oder Variantentyp, alle drei gemessen. **Null Korpusstellen benutzen einen qualifizierten Namen als Wert** |
| **Ein `reason`-Wert hat keinen Erzeuger** | `primary` (`SYNTAX.md`:405) kennt keine Produktion. **Jede `-> T or R`-Signatur im Korpus steht an einem `extern fn`** — an einem Rumpf, den Gabbro nie sieht. *Der Fehlerkanal existiert an der Deklaration und hat keine Schreibform.* **Dieselbe Gestalt wie «B9» bei `fnptr`: erst der Erzeuger, dann der Vertrag** |
| **Eine Zeile, die ICH ergänzt habe, senkt nicht ab** | `static irq : IrqMarke = IrqMarke(…)` — ein `static` eines Verbunds mit gewöhnlichem Anfangswert. *Steht so im Kopf von F6, statt die Zeile wegzulassen* |

*Damit ist `H`s Absenkungsspalte zum ersten Mal auf einem Korpus messbar, der sie tragen kann
— und die Zahl, die dort steht, misst Gabbro und nicht die Vollständigkeit eines Berichts.*

**Und die drei zuletzt geschlossenen Zeilen sagen zusammen einen Satz, der in den Plan
gehört:** «B33» stand als *Zusage* im Ordner und der Prüfer tat das Gegenteil; die
Registerklasse stand als *erledigt durch `R002`/`R003`* und die prüfen Zeigerrechte; «B26»
an :764 stand als *„kein benannter Ausgang"* und hat in Wahrheit **gar keinen Leser**.
*Drei Zeilen, drei Mal dieselbe Richtung: die Buchung war optimistischer als der Code.*
**Eine Zahl, die aus Buchungen summiert wird, misst die Buchungen.**

---

# PL — die LOGIK des Prüfers beweisen

**Der Auftrag sagt „zumindest die Logik des Prüfers", und das ist die richtige Verkleinerung.**
Den Prüfer als Rust zu verifizieren ist CompCert-Größenordnung. **Seine Logik zu beweisen ist
etwas anderes und viel kleineres** — und dieser Ordner hat die Form dafür schon dreimal gebaut.

## Der Befund, mit dem der Plan anfängt: der Prüfer hat als einziger keine Zählspalte

| Fläche | Ratsche | Stand |
|---|---|---|
| Wortschatz | `pruefe-wortschatz.py` | 195 gegen 195 |
| Axiomschicht | `gabbro annahmen` | **19**, jede mit Sonde oder Grund |
| Erzeuger-Schablonen | `gabbro schablonen` | 20, davon 4 bewiesen, **4 lebend unbewiesen** |
| **die Pässe** | **keine** | **10 Pässe, 0 gezählte Beweispflichten** |

> **Zehn Pässe entscheiden über jedes Programm, und keiner von ihnen schuldet einen Satz.**
> *Das ist dieselbe Lage, in der die Schablonen vor ihrer Auszählung waren — monoton wachsend
> und unbeziffert.*

## Die Trennung, auf der alles ruht

**Ein Pass besteht aus zwei Dingen, und nur eines davon ist Rust:**

| | | beweisbar wie |
|---|---|---|
| **die REGEL** | *unter `a >= b` hat `a - b` den Typ `0 .. a.max − b.min`* (V2) | **Isabelle, über einem abstrakten Modell** — ganz ohne den Prüfer |
| **die UMSETZUNG** | dass `typen.rs` genau diese Regel rechnet | Mutationen, Differenztests, Sprechproben |

**Die Regeln sind Mathematik über Bereichen, Mengen, Ordnungen und transitiven Hüllen.** Sie
reden über keinen Rust-Wert. *Genau darum sind sie beweisbar, ohne den Prüfer anzufassen.*

> **Und die zweite Zeile ist heute schon besser bewacht, als es aussieht:** `148 von 148`
> Mutationen, und **null unbeschädigbare Zeilen** im Prüfer. Was fehlt, ist nicht die Umsetzung
> — es ist der Satz, gegen den sie umgesetzt wird.

## PL.1 — Das Passregister anlegen *(die billigste Zeile des ganzen Plans)*

Wie `schablonen.rs`, mit denselben zwei Zähnen: **je Pass die Sätze, die er behauptet**, jeder
mit Fundstelle und Stand (`Entworfen` · `Getragen` · `Bewiesen`).

**Erste Schätzung, aus den Absagecodes abgeleitet:**

| Pass | Sätze, grob |
|---|---:|
| M1 + V1–V3 (`M101`–`M105`) | **5** — Bereichsarithmetik, Breite, Nenner, Indexschranke, die drei V-Regeln |
| Sperren (`H001`–`H006`) | **3** — Rangordnung ist azyklisch · geteilt/exklusiv · Haltezeit |
| Wirkungen (`E005`–`E010`) | **3** — Abschluss über dem Aufrufgraphen · Zyklus als untere Schranke · Leseseite |
| Kosten (`K001`–`K004`) | **3** — Summation, Zweigmaximum, Domänenschranke |
| Schleifen · Paarung · Gruppe · M2 · M3 · Namen | **~8** | |
| | **≈ 22** |

* **Tor:** `gabbro paesse` meldet je Pass seine Satzzahl, und ein Test nagelt sie an — *eine
  Zahl, die sich still mitbewegt, ist keine Ratsche.*
* **Und der zweite Zahn sofort:** **kein neuer Absagecode ohne seinen Satz.** Heute gibt es 52
  Codes und null Sätze.

## PL.2 — Die drei Sätze zuerst, an denen etwas hängt

**Nicht in Reihenfolge der Größe, sondern in Reihenfolge der TRAGLAST:**

1. **`K001` — die Summationsregel.** *Anweisungen addieren sich, außer hinter einem Zweig, der
   immer verlässt; eine Traversierung kostet Rumpf × Domänenschranke; Zweige das Maximum.*
   **An ihr hängt jede Kostenzusage des Ordners** — und sie hat heute schon einen gemessenen
   Fehler (`mappings of`: 2 048 gegen 512⁴). *Der Beweis würde ihn erzwingen.*
2. **`H006` — die Rangordnung.** *Wenn jede Sperre einen Rang trägt und jeder Pfad sie
   aufsteigend nimmt, ist kein Verklemmen möglich.* Der klassische Satz, klein, und die Klasse
   *Sperre* steht auf ihm.
3. **V2 — die relationale Verengung.** *Unter `a >= b` ist `a - b` im Bereich
   `0 .. a.max − b.min`.* **102 Stellen** hängen daran, und M1 ist der Pass, den alles benutzt.

* **Tor je Satz:** die Theorie übersetzt ohne `sorry`, und **eine Mutation, die den Satz im
  Rust verletzt, wird gefangen** — sonst ist der Beweis über einem Modell geführt, das der Code
  nicht ist.

## PL.3 — Die Brücke, und sie ist der eigentliche Posten

**Ein Beweis über einem Modell sagt nichts über Rust.** Drei Wege, und der Plan wählt:

| | | |
|---|---|---|
| (a) | den Prüfer in Isabelle/HOL schreiben und extrahieren | CompCert-Weg, **Jahre** |
| (b) | das Modell aus dem Rust ableiten (Übersetzer ins Modell) | ein zweites Werkzeug, das selbst unbewiesen ist |
| **(c)** | **je Satz eine Sprechprobe, die den Rust gegen das Modell fährt** | **das Geschirr steht** |

> **(c), und der Grund ist nicht Bequemlichkeit:** `mutiere-pruefer.py` beschädigt heute schon
> je eine Regel und verlangt, dass etwas fällt. **Der Satz sagt, WELCHE Beschädigung fallen
> muss.** *Aus 132 Mutationen ohne Satz werden 132 Mutationen mit einem — und aus einem grünen
> Lauf wird eine Aussage.*

**Was (c) nicht leistet, und es gehört in denselben Absatz:** es zeigt, dass der Rust die
*geprüften* Fälle wie das Modell behandelt, nicht dass er es *überall* tut. **Der Rest bleibt
Vertrauensbasis** — aber ein benannter, gezählter, und um genau die 22 Sätze kleinerer.

## Was PL am Ende ändert, in einem Satz

> **Heute:** *„die zehn Pässe finden keine hängende Pflicht mehr"* — eine Aussage über ein
> unverifiziertes Werkzeug.
> **Nach PL:** *„die 22 Sätze, auf denen die zehn Pässe beruhen, sind bewiesen; dass der Rust
> sie umsetzt, ist an 132 Beschädigungen geprüft."*

*Der zweite Satz ist nicht der Beweis des Prüfers. Er ist die Auskunft darüber, wieviel man
noch glauben muss — und die gibt es heute nicht.*

---

# K11 — auf **elf von elf** Klempnereiklassen

**Neun sind getragen** (`DONE.md`). Zwei stehen offen, und sie stehen aus verschiedenen
Gründen offen — *das ist der ganze Plan.* Dazu ein Rest von «B37», der beim Bauen benannt
wurde und nicht verschwunden ist.

```
Rennen        das SPEICHERMODELL  → gebucht als A10, nicht falsifizierbar
Verfeinerung  die ABSENKUNG       → 8 Übersetzungseinheiten, 7 Fragmente ohne C
«B37»-Rest    der ZWEIG           → O005 meldet, entscheidet nicht
```

---

## K11.1 — «B37» zu Ende bringen *(klein, und der Rest ist benannt)*

`O005` sagt heute: *„ein Phasenschritt steht in einem Zweig oder einer Schleife"* — und
entscheidet nicht. **Die Meldung war richtig; sie ist keine Lösung.**

**Die Entscheidung, die vor die erste Zeile gehört:** was ist die Stufe einer Marke *nach*
einem `if`?

| | |
|---|---|
| **(a) alle Zweige müssen dieselbe Stufe erreichen** | refuse rather than interpret — die Bauart dieses Ordners. Ein Bootpfad, der je nach Zweig woanders endet, ist zwei Bootpfade |
| (b) die Vereinigung tragen, der nächste Schritt muss alle akzeptieren | permissiver, und der nächste Schritt braucht dann eine Stufenmenge statt einer Stufe |

**Empfehlung: (a)**, neuer Code `O006`. *Wer (b) will, kann später lockern; wer mit (b)
anfängt, kann nie mehr verschärfen.*

* **Tor:** `O005` verschwindet vom Korpus, eine Giftprobe mit auseinanderlaufenden Zweigen
  fällt mit `O006`, und **eine zweite Giftprobe, in der beide Zweige dieselbe Stufe erreichen,
  geht durch** — sonst hat (a) nur alles verboten.
* **Preis:** eine Passerweiterung, zwei Giftproben. *Keine Grammatik, keine Schablone.*

---

## K11.2 — Rennen, und der erste Schritt ist NICHT der Speichermodell-Teil

**Gemessen am 2026-08-17, und es ist der Befund, mit dem dieser Plan anfängt:**

```gabbro
table K count 8 { slot { a : u32, } }
lock KAPPEN protects { K } rank 3 held <= 40 ops;

impl fn schreib(i : index into K) -> bool
    effects { writes K } costs <= 4 ops
{ K.slots[i].a = 1; return true; }      -- kein `locks KAPPEN`

→ 4 Items, 0 Fehler, 0 Hinweise
```

> **`protects` beisst nicht.** Der Platz ist erklärtermaßen geschützt, der Zugriff steht ohne
> Sperre da, und kein Pass sagt etwas. *Die Klasse Rennen hängt heute nicht am Speichermodell —
> sie hängt an einer Regel, die niemand gebaut hat.*

`H001`–`H006` prüfen die **Disziplin** einer genommenen Sperre (geteilt gegen exklusiv,
Rang, Haltezeit). Sie prüfen nicht, **dass sie genommen wird.**

### K11.2.1 — `protects` muss beissen *(die tragende Regel)*

Jeder Zugriff auf einen Platz, den ein `lock … protects { … }` nennt, steht unter dieser
Sperre — **oder die Funktion deklariert sie** (`effects { locks P }`), und dann gilt sie
transitiv über den Aufrufgraphen. *Das Geschirr dafür steht: `H005` löst genau diese
Zwischenregel an der Aufrufgrenze, und die Hülle ist gebaut.*

* **VORHER MESSEN, und das ist Vorabfestlegung, nicht Vorsicht:** 17 `protects`-Klauseln in 9
  Dateien. Wie viele Zugriffsstellen fielen unter der neuen Regel? **Eine Regel, die den
  eigenen Korpus zerlegt, ist ein Befund und keine Regel** — dann gehört die Zahl ins Protokoll
  und die Regel auf den Prüfstand, nicht der Korpus in die Reparatur.
* **Tor:** die Giftprobe oben fällt; `beispiele/10` und `/13` bleiben grün; die Zahl der
  gefallenen Korpusstellen steht im Protokoll, bevor eine Zeile Korpus angefasst wird.
* **Der dritte Zustand gilt (W10):** wo der Aufrufgraph unvollständig ist, ist die
  Sperrenmenge eine **untere** Schranke — daraus wird weder abgesagt noch bestätigt.

### K11.2.2 — Die Ausführungskontexte benennen

> **Die erste Hälfte steht seit dem 2026-08-19 (`H013`) — und der Satz, der hier stand, war
> von seinem eigenen Konstrukt überholt.** Er lautete: *„Gabbro sagt heute nicht, wer
> nebenläufig ist."* **`entry … dispatch f` sagt es**: jeder Eintritt ist ein Weg, auf dem der
> Kern von aussen betreten wird, und seit demselben Tag trägt der Aufrufgraph die Wirkungen
> modulbewusst, über `observes` hinweg und mit Argumentabbildung. *Die Zutaten lagen
> nebeneinander; es fehlte die Zeile, die sie zusammenbringt.*
>
> Was `H013` prüft: **ein Platz, den ein Eintritt schreibt und den kein `lock … protects`,
> `rcu … protects`, `atomic` oder `accumulates … per cpu` als geteilt ausweist, fällt.**
> Und **ein** Eintritt reicht — auf mehreren Kernen stehen zwei Kerne im selben Syscall.
>
> **Was NICHT gefallen ist, ist die Vorbedingung unten**, und sie ist der Grund, warum diese
> Phase offen bleibt: *auf diesem Korpus hat die Regel **null Biss**.*

**Rennfreiheit ist eine Aussage über NEBENLÄUFIGKEIT.** Was Gabbro heute nicht sagt, ist die
FEINERE Hälfte: welche Kontexte einander ausschliessen (`masks IRQ`, `per cpu`, `ist nested`)
und welche wirklich gleichzeitig laufen. `H013` nimmt die grobe Antwort — *jeder Eintritt ist
ein Kontext* — und die ist in die sichere Richtung grob.

Ohne das lässt sich der eigentliche Satz nicht sagen:

> *jeder Platz, den zwei Kontexte berühren, ist unter einer Sperre, atomar, oder gehört
> genau einem Kern (`per cpu`).*

* **VORAB GEMESSEN 2026-08-17, und das Ergebnis ändert diese Phase:**

  ```
  Kontextwurzeln im Korpus:                 4   (3 × entry, 1 × boot)
  davon mit einem Rumpf, den Gabbro sieht:  0
  ```

  **Alle vier `dispatch`-Ziele sind `extern fn`.** `syscall_verteiler`, `nmi_verteiler`,
  `rust_eintritt` — jedes ein fremder Rumpf. Die Hülle über einer Kontextwurzel ist damit
  **leer**, und die Regel *„jeder Platz, den zwei Kontexte berühren, ist gesperrt oder
  atomar"* kann auf diesem Korpus **nicht ein einziges Mal feuern**.

  > **Dieselbe Lage wie `E010`, und sie gehört vor die Regel und nicht dahinter.** Eine Regel,
  > deren Beleg nur aus Giftproben kommen kann, ist nicht falsch — *aber wer das erst
  > nachher merkt, hat eine Zahl gebaut, die grün aussieht und nichts misst* (W1).

  **Damit hat diese Phase eine Vorbedingung, die vorher nicht sichtbar war:** ohne einen
  Korpus, in dem eine Kontextwurzel einen Rumpf hat, ist K11.2.2 nicht messbar. *Sie hängt
  am zweiten Korpus, und der steht ohnehin als Bedingung über K11.*

  > **Am 2026-08-19 nachgemessen, und die Zahl steht unverändert: 4 Kontextwurzeln, davon 0
  > mit einem Rumpf.** `H013` ist gebaut und fällt an Giftprobe 146 — **am Korpus fällt es
  > kein einziges Mal.** *Das ist genau der Fall, vor dem der Absatz darüber warnt, und er
  > hat ihn zwei Tage vorher benannt.* Die Regel ist damit gebaut und **unbelegt**, und beides
  > steht so im Zeugnis.

* **Tor:** je geteiltem Platz ist die Kontextmenge ableitbar und wird gedruckt; ein Platz, den
  zwei Kontexte ohne Sperre/Atomic/`per cpu` berührt, fällt — **und die Zahl der berührten
  Plätze steht daneben**, damit ein leerer Lauf nicht wie ein bestandener aussieht.
* **Preis, ausgesprochen:** das ist der **grösste** Posten dieses Plans. Er braucht ein
  Nebenläufigkeitsmodell, und `masks IRQ` («B38», heute in der Axiomschicht) gehört dann
  hinein statt daneben.
* **Risiko, benannt:** `ist nested` heisst, ein Interrupt kann sich selbst unterbrechen.
  *Wer das übersieht, baut eine Regel, die auf einem Kern falsch ist.*

### K11.2.3 — Die Absenkung von `release`/`acquire`

Heute weigert sich der Erzeuger benannt. Unter **A10** (`release_stellt_sichtbarkeit_her`,
gebucht als **nicht falsifizierbar**) ist die Absenkung `_Atomic` mit der deklarierten Ordnung.

* **Tor, und es ist ein ehrliches:** das erzeugte C trägt **strukturell** die Ordnung, die die
  Quelle deklariert — geprüft am Text, nicht an einem Lauf.
* **Was hier NICHT geht, und es gehört danebengeschrieben:** *ein Differenztest kann die
  Abwesenheit eines Rennens nicht zeigen.* Ein erfolgreicher Lauf sagt nur, dass die Umordnung
  diesmal ausblieb — genau der Satz, mit dem A10 als nicht falsifizierbar gebucht ist.

---

## K11.3 — Verfeinerung, und das Messgerät steht schon

`gabbro zeugnis` misst **beide Achsen**, je Datei, seit dem 2026-08-17:

```
0 Annahmen, N Schablonen (M davon UNBEWIESEN), K direkte Formen, F fremde Rümpfe
UNZUGEORDNET: …
```

| Achse | Messgrösse | heute |
|---|---|---|
| **Breite** — jede Form wird abgesenkt | `UNZUGEORDNET = 0` **und** kein `C001` über dem Korpus | 8 von 22+3 Einheiten senken ab |
| **Tiefe** — jede benutzte Schablone ist bewiesen | `davon UNBEWIESEN = 0` | **9 von 20 bewiesen, 1 lebend getragen** *(K11.3.2, 2026-08-17)* — **acht der neun Übersetzungseinheiten melden `0 davon UNBEWIESEN`**; `accumulates.monoid` ist bewiesen, **bevor** das Konstrukt absenkt |

### K11.3.1 — Breite: die Weigerungen abbauen, **in der Reihenfolge ihrer Sperre**

Nicht alle `C001` sind gleich. **Fünf sind durch BEFUNDE gesperrt, nicht durch Arbeit** —
«B10», «B12», «B17», «B24» und die Domänenschranke von `mappings of`; `descendants of` nennt
seine Kante nicht. *Die fallen mit einer Entscheidung, nicht mit Erzeugercode.* Der Rest
(`static`, `reason`, `publishes`, `awaits`, `exchange`, `forever`, `let … else`) ist Bauarbeit.

* **Reihenfolge:** erst die **Entscheidungen** (sie kosten keine Zeile und lösen fünf), dann
  die Bauarbeit — *jede mit ihrem Differenztest, keine ohne.*

### K11.3.2 — Tiefe: **je Schablone ein Isabelle-Lauf, und der Beweis kommt VOR dem Konstrukt**

Das zweite Tor aus K100 gilt weiter: `lebend_ungedeckt() ≤ 4`. **Wer eine Form absenkt, hebt
ihre Schablone von `Entworfen` auf `Getragen`** — und ohne Beweis davor steigt die lebende
Fläche. *Genau so ist `verbund.konstruktor` gelaufen, und deshalb bewegte sich die Zahl nicht.*

Die lebend getragenen zuerst, weil sie **heute schon** getragen werden. **`table.absenkung`
ist am 2026-08-17 gefallen** (`beweise/Table_Absenkung.thy`) — und zwar zuerst, weil die
anderen darauf aufsitzen: *`option.sonderwert` braucht die Länge für den Sonderwert,
`table.induktion` die Schranke für die Terminierung.*

**`format.roundtrip` und `device.konstruktor` sind am selben Tag gefallen.** Es bleibt
**einer**: `option.sonderwert` — und er bleibt bewusst *getragen*, weil seine offene Hälfte
der Eintrag selbst als **die eigentliche** führt (*„dass keine erzeugte Rechnung den Sonderwert
HERSTELLT"*), nicht als generische Brücke. *Ihn jetzt umzubuchen wäre genau das Verkleinern
durch Umschreiben, das die Ratsche verbietet.*

### K11.3.3 — Und die starke Fassung von (b), als Grenze benannt

**Ein Zeugnis über DIESE Übersetzung ist keine Aussage über ALLE Eingaben.** Die starke Fassung
wäre je Übersetzung ein maschinell geprüftes Simulationszeugnis; **Weg (a), der verifizierte
Erzeuger, bleibt ausdrücklich draussen** — er ist CompCert-Grössenordnung und würde diesen
Plan zu einem anderen Projekt machen.

*Die Vorstufe ist als Vorstufe gebucht, damit die Zahl nicht mehr verspricht, als sie misst.*

---

## Wann K11 erreicht ist — und wann die Zahl lügt

**Erreicht:**

```
11 von 11    Klempnereiklassen getragen, jede mit ihrer benannten Grenze
O005 = 0     kein unentschiedener Phasenschritt im Korpus
protects     beisst, und die Zahl der gefallenen Stellen stand VORHER im Protokoll
UNZUGEORDNET = 0   über jeder Datei, die absenkt
L = 1        lebend unbewiesene Schablonen — K11.3.2 hat drei bewiesen
```

**Und die Zahl lügt, wenn eines davon fehlt:**

> **`11 von 11` über den zehn Fragmenten ist keine Aussage über Gabbro.** Sie sind nach ihrer
> Schwierigkeit gewählt. **K11 ist erst dann eine Messung, wenn der ZWEITE Korpus danebensteht**
> — derselbe Satz wie bei K100, und er ist seither nicht eingelöst.

> **Und eine zweite Falle, die K11 eigenhändig aufstellt:** eine Klasse gilt als *getragen*,
> sobald eine Regel greift — nicht, sobald sie *alles* greift. Jede der neun getragenen führt
> ihre Grenze mit. **Eine zehnte und elfte ohne Grenze wären verdächtiger als mit.**

---

# Wozu Gabbro taugen wird — und wozu nicht, wenn die Pläne aufgehen

**Die Frage war: wie gut lässt sich Gabbro für alltägliche Programme nutzen, wenn es sich nach
den Plänen entwickelt — und wäre comptime sinnvoll?**

## Die Antwort auf die erste Hälfte ist unbequem: **es wird nicht besser darin, und das ist kein Versäumnis**

**Kein Plan in dieser Datei bewegt Gabbro in Richtung Alltag.** K100, K11 und PL schließen
Klempnereipflichten für Code *kernelförmigen Zuschnitts*. Was den Alltag ausmacht, ist von
Gabbro **absichtlich ausgeschlossen**:

| alltäglich | in Gabbro | was es kostet, das zu ändern |
|---|---|---|
| Schleife bis EOF, bis Nutzereingabe, bis Abbruch | **drei Formen, alle beschränkt** | **Terminierung** fällt zurück an den Menschen |
| dynamische Sammlungen | `table … count N`, fest | **Index** fällt zurück — `count N` IST die Schranke |
| Allokation nach Bedarf | `allocs` benennt, mehr nicht | eine **zwölfte Klasse**, die es heute nicht gibt |
| ~~Gleitkomma~~ **gefallen 2026-08-18** | `f32`/`f64` mit Bereich, NaN- und Unendlichbit | — |
| „das kostet, was es kostet" | `costs <= N ops`, **Pflicht** | die Latenzaussage je Wartestelle fällt |

> **Das ist ein Regler, kein Mangel.** *Gabbros Alltagstauglichkeit und seine
> Klempnereiabdeckung sind dieselbe Stellschraube* — jede Lockerung gibt genau eine der elf
> Klassen zurück, und zwar die, deren Beweis sie trug.
>
> ## Und die Ausnahme gehört dazu, sonst wird der Satz zum Verbotsprinzip
>
> **Es gibt einen dritten Ausgang, und er lockert, ohne zurückzugeben:** die Pflicht wird in
> eine **erzeugte Form** verlegt. *Pools, `ops`, `recurse bounded` sind alle von dieser Art* —
> der Nutzer bekommt die Freiheit, und die Beweislast wandert in den Erzeuger.
>
> **Der Preis ist dann keine zurückgegebene Klasse, sondern ein Schabloneneintrag.** Und das
> ist die Stellschraube, die in der Kurzfassung fehlte.
>
> **Vollständig:**
>
> > **Jede Lockerung kostet entweder eine KLASSE oder eine SCHABLONE — und nur die zweite
> > Sorte ist abtragbar.**
>
> *Eine zurückgegebene Klasse ist fort; eine Schablone fällt einmal und dann nie wieder.*
> **Genau deshalb ist die Schablonenratsche die schärfste Buchführung dieses Ordners** — sie
> zählt den Preis der zweiten Sorte, und ohne sie sähe „in eine erzeugte Form verlegt" wie
> ein Geschenk aus.

**Wofür Gabbro taugen wird, wenn die Pläne aufgehen:** Kernel, Treiber, Bootstrecken,
Interruptbehandler, Protokollzustandsmaschinen, alles mit einer harten Latenzaussage —
**Code, bei dem jemand die Schranken ohnehin von Hand ausrechnet und in Kommentare schreibt.**
*Dort nimmt Gabbro Arbeit ab. Anderswo verbietet es nur.*

## Und comptime? **Die Antwort steht schon im eigenen Register**

**Gabbro ist heute voller comptime — es ist nur nicht vom Nutzer schreibbar.** `const`,
`when constexpr`, `count N`, `index into T`, die erzeugten Konstruktoren, `sizeof`/`lenof`/
`aligned`, `walk levels`, `mirrors`, die Kostenrechnung: **alles wird zur Übersetzungszeit
gerechnet.**

Jeder dieser Erzeuger hat einen Eintrag in `schablonen.rs` — und die Liste hat eine Ratsche:
**Grundmarke 18 plus ein Platz je bewiesener Schablone.**

> **Ein comptime, das der Nutzer schreibt, ist ein Erzeuger, dessen Beweispflicht niemand
> aufgeschrieben hat.** Die Schablonenmenge würde unbeschränkt und unbeziffert — genau der
> Zustand, gegen den die Ratsche gebaut ist.

### Aber die Linie verläuft nicht zwischen „comptime ja/nein", sondern hier:

```
comptime, das WERTE rechnet   →  kostet keine Schablone
comptime, das CODE erzeugt    →  kostet eine, und die will bewiesen werden
```

**Und die erste Hälfte fehlt Gabbro wirklich.** Heute rechnet `konst_wert` nur Literale und
`const`-Ketten; eine Schranke wie `count NSLOTS * 2` oder `costs <= laenge(T) + 4` lässt sich
nicht schreiben. Der kleinste Zusatz wäre:

```gabbro
const fn zellen(kerne : u32) -> u32 requires kerne <= 256 costs <= 4 ops
{ return kerne * 4; }

table Warteschlange count zellen(NKERNE) { … }
```

* **Ein `const fn` erzeugt keinen Code, also keine Schablone.** Es liefert eine Zahl, und die
  Zahl steht dann in `count`, in `costs`, in einer Bereichsgrenze.
* **Seine Beweispflicht ist Totalität — und die trägt die Sprache schon:** drei beschränkte
  Schleifenformen, keine Rekursion ohne Schranke, `effects { pure }` erzwungen. *Ein `const fn`
  ist ein `impl fn`, dem der Prüfer glaubt, weil er es nachrechnen kann.*
* **Der Gewinn ist nicht Bequemlichkeit, sondern Ableitbarkeit:** heute steht `NSLOTS` an
  drei Stellen und ihr Zusammenhang in einem Kommentar.

### Was NICHT dazugehört, und der Grund ist derselbe

* **Kein comptime, das Deklarationen erzeugt** (Makros, Templates, `derive`). Jede erzeugte
  Deklaration ist eine Schablone ohne Eintrag.
* **Kein comptime mit Effekten.** Ein Erzeuger, der beim Übersetzen liest oder schreibt, macht
  das Erzeugnis von etwas abhängig, das im Zeugnis nicht steht.
* **Kein Turing-vollständiges comptime.** *Eine Sprache, die zur Laufzeit keine unbeschränkte
  Schleife erlaubt und zur Übersetzungszeit schon, hat die Regel nicht, sondern eine Ausnahme.*

## Die ehrliche Zusammenfassung

**Gabbro wird nach den Plänen ein Werkzeug, mit dem man Kernelcode schreibt, ohne die
Klempnerei zu beweisen — und mit dem man kein Textverarbeitungsprogramm schreibt.** Das war die
Entscheidung, bevor die erste Zeile stand; die Pläne führen sie aus, sie erweitern sie nicht.

*Wer beides will, braucht zwei Sprachen — oder gibt die elf Klassen einzeln zurück und schreibt
je Rückgabe auf, welche.*

---

# Zwei Fragen, die die Grenzen beschreiben

## Was man in Gabbro **nie** wird schreiben können

Nicht „noch nicht" — **nie**, weil die Form mit einer der elf Klassen unvereinbar ist. Die
Trennlinie ist scharf und liegt nicht dort, wo man sie vermutet:

| geht **nicht** | woran es scheitert |
|---|---|
| **alles mit unbekannt vielen Objekten** — Compiler, Datenbank, Editor, Webserver mit Verbindungen nach Bedarf | `table … count N` **ist** die Indexschranke. Ohne feste Zahl fällt die Klasse *Index*, und mit ihr `M103` |
| **Rekursion über Daten** — Baumtraversierung, Parser, Auswerter | der Kostenpass rechnet Rümpfe und Rufe; Rekursion trägt eine **Annahme statt einer Rechnung**. `descendants of` gibt es, aber über einer Tabelle mit Schranke |
| ~~**allgemeine Zeichenketten**~~ **gefallen 2026-08-19** | Der Satz vermengte zwei Dinge. Ein Puffer mit einer Länge daneben ist schreibbar (`beispiele/32-zeichenkette.gab`) — es hing an einer VERGRÖBERUNG in M1, nicht an der Sprache. *Offen bleibt nur die zweite Hälfte: variable Längen in einem `format`* |
| ~~**Gleitkomma-Numerik**~~ — **die einzige Zeile dieser Tabelle, die gefallen ist** *(«F», 2026-08-18)* | M1 trägt `FBereich` mit außen gerundeter Arithmetik. **Was bleibt, ist kleiner und benannt:** Produkt, Quotient und die Null haben ihren Satz noch nicht |
| **alles, was Speicher anfordert und freigibt** | `allocs` **benennt** eine Wirkung, mehr nicht. Eine zwölfte Klasse gibt es nicht |
| **Selbstbeherbergung** — Gabbro in Gabbro | steht schon unter *„What deliberately does not exist"*. Ein Übersetzer ist ein Baumverarbeiter mit Rekursion und dynamischem Speicher — **also die drei Zeilen oben zusammen** |

> **Und die Gegenprobe, damit die Liste nicht größer aussieht, als sie ist:** eine Dienstschleife,
> die Jahre läuft, geht (`forever … per_pass bounded … progress … leaves`). Ein Zustandsautomat
> geht. Ein Ringpuffer geht. Ein Treiber geht. **Was fehlt, ist immer dasselbe: eine Zahl, die
> zur Übersetzungszeit niemand kennt.**

*Das ist keine Reihe von Lücken, sondern eine Entscheidung, sechsmal sichtbar.*

## Eine eigene Bibliotheks-ABI für verifizierte Gabbro-Bibliotheken?

**Ja — und der Ordner hat das Werkzeug dafür schon gebaut, ohne es so zu nennen.**

`gabbro zeugnis` gibt heute je Übersetzungseinheit genau das aus, was eine solche ABI
transportieren müsste:

```
A  die Annahmen           was die MASCHINE leisten muss
B  die Schablonen         worauf der Erzeuger sich stützt, mit Beweisstand
C  die direkte Absenkung  was 1:1 übergeht
E  die fremden Rümpfe     was jemand anderes schuldet, mit Vertrag
```

**Eine Bibliotheks-ABI ist genau die Frage: was muss der Rufer mitnehmen, damit die Zusage der
Bibliothek bei ihm noch gilt?** Und die Antwort ist nicht die Signatur, sondern diese vier Listen.

### Was sie tragen muss, und jedes Stück hat schon eine Zeile

| | warum es in die ABI gehört |
|---|---|
| **die Annahmenmenge** | „bewiesen unter A1…An" ist wertlos, wenn A7 beim Rufer nicht gilt. **Zwei Bibliotheken mit widersprüchlichen Annahmen dürfen nicht in ein Programm** — `manifest::vereinige` weigert sich heute schon bei gleichem Namen mit anderem Inhalt |
| **die Schablonen mit Beweisstand** | die Vertrauensfläche des Rufers ist die **Vereinigung** der Flächen aller Bibliotheken. Eine Bibliothek, die auf einer unbewiesenen Schablone ruht, vergrößert sie — *und heute sähe man es nicht* |
| **`effects`, `costs`, `requires Held(…)`** | schon in der Signatur, aber **die Kostenzahl ist eine ABI-Zusage**: `K001` rechnet beim Rufer damit. Ändert die Bibliothek sie, bricht die Latenzaussage, ohne dass ein Typ sich rührt |
| **die Sperrordnung (`rank`)** | **das ist der schärfste Posten.** `H006` rechnet die Ordnung nach; zwei Bibliotheken mit unabhängig vergebenen Rängen ergeben zusammen einen **Zyklus**, den keine von beiden allein sehen kann |

### Und der Grund, warum sie **nötig** ist und nicht bloß hübsch

> **Gabbros ganze Zusage ist eine Aussage über eine Übersetzungseinheit.** Jede der elf Klassen
> wird an einem Baum geprüft, den ein Lauf ganz sieht. **Eine Bibliothek durchschneidet genau
> das** — und ohne eine ABI, die die vier Listen mitführt, fällt die Zusage an der Schnittstelle
> lautlos auf „untere Schranke" zurück, genau wie bei einem unbekannten Gerufenen (`E009`).

### Was sie nicht sein darf

* **Kein C-ABI mit Kommentaren.** Die Zusage muss maschinenlesbar sein, sonst prüft sie niemand.
* **Keine Versionsnummer als Ersatz.** *Eine Ratsche über einer Kardinalzahl greift nicht gegen
  Austausch* — derselbe Satz, mit dem `SYNTAX.md` §12 die Annahmenmenge als **Menge von Namen**
  verlangt statt als Zahl.
* **Kein Vertrauen ohne Zeugnis.** Eine Bibliothek ohne Zeugnis ist ein fremder Rumpf — und die
  gehören in Abschnitt E, nicht in Abschnitt B.

**Der Weg dahin ist kurz, weil das Format steht:** `gabbro zeugnis` schreibt, `gabbro pruefe`
liest die Zeugnisse der gerufenen Bibliotheken mit und vereinigt Annahmen, Schablonen und
Sperrränge — **mit denselben Weigerungen, die es innerhalb einer Einheit schon gibt.**

*Das ist der erste Posten, bei dem Gabbro etwas gewinnt, das es heute nicht hat, ohne eine
Klasse zurückzugeben.*

---

# BERICHTIGUNG zu §1 der Erweiterung — der Rahmen ist der der Maschine

**Der Einwand trifft, und er trifft eine Überstrenge, die ich selbst eingebaut hatte.** Das
`1 ..= 65_536` an `count` war eine erfundene Konstante an einer Stelle, an der zwei Kanten
ohnehin existieren. Der Bereich wird **optional** (Voreinstellung: Darstellungsbreite), die
Pflicht wandert an den **Erzeugungsort**, und §7 verliert seine erste Zeile.

**Aber die beiden Kanten tun verschiedene Arbeit, und nur eine ist geschenkt:**

| Kante | wovor sie schützt | wer sie liefert |
|---|---|---|
| **Darstellungsbreite** | dass die Index*rechnung* überläuft | die Maschine — **gratis**, M1 rechnet ohnehin mit `IntBereich::voll(breite, …)` |
| **Regionskapazität** | dass der *Speicher* reicht | der Erzeugungsort — **nicht gratis**, das ist der eine `narrow` |

*Sie zusammenzuziehen („mehr als der Adressraum passt ohnehin in keine Struktur") verdeckt,
dass nur die erste umsonst ist.* Die zweite ist genau der Punkt, an dem der Rahmen die
Wirklichkeit berührt — und der Einwand sagt das an anderer Stelle selbst.

## Und der Kern der Sache ist bereits gemessen, mit einem unbequemen Ergebnis

Die parametrische Zusage ist **heute schon schreibbar** — und **vollständig leer**:

```gabbro
impl fn schleife(n : u32 in 0 .. 1000) -> u32 effects { pure } costs <= 0 * n ops
{ return n; }

→ 3 Items, 0 Fehler, 0 Hinweise          (der Rumpf kostet 1)
```

`kosten.rs` sagt es im eigenen Kopf: *„die Schranke **darf von Eingaben abhängen** … in dem
Fall **schweigt der Pass**."* Und `gabbro kosten` druckt ehrlich `zugesagt --`.

> **Die Erweiterung führt den parametrischen Vertrag also nicht ein — sie macht ihn tragend.**
> Ihr eigentlicher Preis steht damit nicht in der Grammatik, sondern in **Pass 9: er muss
> symbolische Ausdrücke VERGLEICHEN, statt zu schweigen.** *Ein Vertrag, den niemand liest,
> ist keine Zusage, sondern eine Zeile.*

**Was dabei bereits passt:** `Kosten::Zahl(i128)` — `40 · 2⁶⁴ ≈ 7,4·10²⁰` liegt weit unter
`i128::MAX`. Die im Einwand vermutete Prüferzeile ist schon geschrieben.

**Und was ebenfalls schon passt:** `beweise/Table_Absenkung.thy` ist über **natürlichen
Zahlen** formuliert, nicht über Konstanten — `feldindizes m = indextyp N ⟷ m = N` gilt
unverändert, wenn beide Werte statt Literale sind. *Der Satz war allgemeiner gefasst, als das
Konstrukt ihn brauchte.*

## Die eine Stelle, an der der Rahmen NICHT wachsen darf

**Innerhalb eines `locks`-Blocks muss er zu einer Zahl zusammenfallen.**

`held <= N ops` ist keine Kostenaussage, sondern eine **Latenzaussage**: sie sagt, wie lange
ein anderer Kern höchstens wartet. Ein `held <= 40 · n` mit symbolischem `n` ist eine Sperre,
die **unbeschränkt lange gehalten wird** — und damit ist die Aussage, um derentwillen `rank`,
`held` und `K002` existieren, leer.

> Der Prüfer sagt es selbst, in derselben Ausgabe: *„`Luft` ist bei `costs` oft richtig, bei
> `held` fast immer falsch — die Latenzaussage rechnet mit der ZUSAGE, nicht mit der Rechnung."*

**Also die Regel, die die Erweiterung mitbringen muss:** parametrisch überall, **außer unter
einer Sperre**. Dort muss `n` durch eine Konstante gebunden sein, sonst fällt `K002`. *Das ist
keine Ausnahme, sondern dieselbe Trennung noch einmal: die Kostenklasse verträgt Symbole, die
Sperrklasse nicht.*

## Und die Konstante verschwindet nicht, sie zieht um

`costs <= 40 · n` bei einem Rufer, der `costs <= 500` zusagt, verlangt eine Schranke für `n`.
**Parametrische Verträge entfernen die Zahl nicht — sie schieben sie nach außen**, bis an den
Rand: den `entry`-Stapel, die Region, den `per_pass`-Rahmen einer Dienstschleife.

*Das ist die richtige Stelle.* Der Einwand sagt es für die Stapeltiefe schon; es gilt für die
Ops genauso. **Am Rand steht ohnehin ein `narrow` mit benanntem Ausgang — dort landet der
Rahmen, und dort gehört er hin.**

## §7, berichtigt

**Alt:** *„Echt Unbeschränktes (eine Struktur ohne deklarierte Obergrenze)."*

**Neu:** **Rahmenloses bleibt unmöglich — aber der Rahmen ist der der Maschine, nicht der der
Sprache.** Unmöglich bleibt: eine Struktur, deren Erzeugung *keinen* Erschöpfungszweig hat ·
Rekursion ohne Maß · ein impliziter Haufen · Selbst-Bootstrap.

*„Beliebig viel" ist zulässig. „Beliebig viel, ohne je einen Erschöpfungszweig zu sehen" nicht
— denn dieser Zweig IST die Stelle, an der der Rahmen die Wirklichkeit berührt.*

---

# Was an WIRKLICHEN Programmen unmöglich ist — drei Spalten, nicht eine

**Die Frage nach Compiler, Laufzeit, Renderer, Netzwerkstack lässt sich nicht mit einer Liste
beantworten**, weil drei sehr verschiedene Gründe „geht nicht" heißen können: *heute nicht
gebaut* · *nach den Plänen möglich* · *nie, weil eine Klasse daran hängt.*

| System | heute | nach der Erweiterung | für immer draußen |
|---|---|---|---|
| **Netzwerkstack** (TCP/IP) | ~~blockiert an **einer** Entscheidung~~ **schreibbar seit 2026-08-19** — «B24» entschieden, gebaut und abgesenkt (`beispiele/24-ip-kopf.gab`, 36 Zeilen C) | ✓ | — |
| **Renderer**, 2D, Festkomma, über Syscalls | teilweise | ✓ | — |
| **Renderer**, 3D mit Gleitkomma | **teilweise** — die Zahlen gehen, die Matrizen sind Bauarbeit | ✓ | ~~Gleitkomma~~ *(gefallen 2026-08-18)* |
| **Sprachlaufzeit** mit Pool-Halde | ✗ | ✓ | — |
| **Sprachlaufzeit** mit wachsender Halde | ✗ | ✗ | **kein Erschöpfungszweig** |
| **Compiler** | ✗ | ✓ *(schreibbar, nicht angenehm)* | — |
| **JIT** | ✗ | ✗ | **erzeugter Code trägt keine Zusage** |

## Der Netzwerkstack ist am nächsten dran — und hängt an «B24»

**Alles Übrige ist schon da:** eine Verbindungstabelle ist `table … count NCONN` (jeder
ernsthafte Kernel hat diese Konstante ohnehin), Paketpuffer sind ein Pool, die Prüfsumme
läuft über eine Länge ≤ MTU, Neuübertragung ist `retry … bounded`, und die Zeitgeber sind
`forever … per_pass`.

~~**Was blockiert, ist der IP-Kopf.**~~ **Entschieden und gebaut am 2026-08-18**
(`beispiele/24-ip-kopf.gab`, «B24»); seit dem **2026-08-19** auch im Prüfer statt nur im
Erzeuger (`N007`/`N008`). Was hier stand, war der Stand davor — er ist ein Feld aus Bitlagen:

```
version:4 · IHL:4 · DSCP:6 · ECN:2 · flags:3 · fragment offset:13
```

~~`format` weigert sich für jede davon~~ — **es trägt sie.** Die Entscheidung lautet: *eine
Lage liegt im **eigenen Wort** des Feldes; jenseits davon gibt es nichts zu bedeuten*, und
*das Wort wird zuerst in der erklärten Bytereihenfolge gelesen, dann werden die Bits aus dem
**Wert** gezogen* — Bitnummern zählen über den Wert, nicht über die Bytes.

> **Und die Kachelung ist die Wortgrenze selbst, nicht eine Prüfung darüber:** ein Wort endet,
> wenn seine Bits vollständig sind. *Der erste Anlauf las alle aufeinanderfolgenden Bitfelder
> gleicher Breite als EIN Wort und meldete an `dscp @[7:2]` eine Überlappung mit
> `version @[7:4]` — zwei Bytes des IP-Kopfs, als eines gelesen.*

> *Das ist keine Bauarbeit und keine Beweisarbeit — es ist eine Entscheidung, und sie ist die
> einzige zwischen Gabbro und einem Netzwerkstack.* **Von allen offenen Posten hat dieser die
> beste Hebelwirkung.**

## Der Renderer: die Trennlinie läuft durch ihn hindurch, nicht um ihn herum

Ein Bildspeicher ist eine Region, ein Blitter eine beschränkte Schleife, die Syscalls sind
`extern fn` — **fremde Rümpfe, die das Zeugnis zählt.** Ein 2D-Renderer mit Festkomma ist nach
§1 schreibbar.

<!-- widerruf:aus -->
> **Widerrufen am 2026-08-18, und zwar von diesem Ordner selbst.** Was hier stand, war:
> *„Ein 3D-Renderer ist es nicht … M1 ist über Intervallen **ganzer** Zahlen gebaut; eine
> Gleitkommazahl hat keinen Bereich, den `M101` vergleichen könnte."* **Der Satz war zum
> Zeitpunkt seines Schreibens richtig und ist es seit «F» nicht mehr** — `typen.rs` führt
> `FBereich { breite, lo, hi, kann_nan, kann_unendlich, literal, gerundet }`, und `M101`
> vergleicht ihn. *Er blieb sechs Abschnitte lang stehen, während vier Abschnitte weiter
> unten der Bauplan lag.*
<!-- widerruf:an -->

**Ein 3D-Renderer ist heute teilweise schreibbar, und die Grenze läuft woanders.** Die
*Zahlen* gehen: `f32`/`f64` mit deklariertem Bereich, außen gerundete Intervalle, NaN- und
Unendlichbit, und ein geglückter Vergleich räumt das NaN-Bit auf beiden Seiten ab. Was fehlt,
ist keine Zahlenfrage, sondern dieselbe wie überall: **eine Transformationskette ist eine
Matrix, und eine Matrix ist `table … count 16`** — schreibbar, aber ohne Generizität je
Größe eine eigene Deklaration.

*Festkomma ist ganzzahlig und geht ebenfalls. Wer die fremde Bibliothek ruft, bekommt weiter
einen Eintrag in Abschnitt E des Zeugnisses statt einer Zusage — nur ist das jetzt eine Wahl
und kein Zwang.*

## Compiler und Laufzeit: schreibbar heißt nicht angenehm

Die Erweiterung macht beide möglich — **und teuer.** Jede Tabelle nennt ein `count`, jede
Rekursion ein Maß, jede Allokation einen Erschöpfungszweig, jede Funktion ihre `costs`.

> **Ein Compiler in Gabbro wäre nicht falscher als einer in Rust — er wäre länger, und jede
> zusätzliche Zeile wäre eine Zahl, die heute in einem Kommentar steht.** *Ob das ein guter
> Tausch ist, entscheidet, wie sehr einen ein Absturz im Compiler stört.*

**Der GC ist der interessante Fall:** eine markierende Sammlung über einen Pool ist über die
Poolgröße beschränkt, die Markierungstiefe ebenso — also `recurse bounded pool.count`. *Ein GC
mit fester Halde ist schreibbar; einer, der die Halde wachsen lässt, ist es nie, weil das
Wachsen der Punkt ohne Erschöpfungszweig wäre.*

## Der JIT ist die schärfste Grenze, und sie ist keine der elf Klassen

Ein JIT schreibt Maschinencode in einen Puffer und springt hinein. **Das Schreiben geht** — es
ist ein Feld aus Bytes. **Der Sprung nicht:** was danach läuft, hat keine `effects`, keine
`costs`, keinen Rahmen, kein Zeugnis.

> *Es ist nicht so, dass Gabbro den Sprung verböte — es ist so, dass ab dort keine einzige
> Aussage dieses Ordners noch etwas bedeutet.* **Dasselbe gilt für jedes nachgeladene Modul
> ohne Zeugnis**, und das ist genau der Grund, warum die Bibliotheks-ABI ein eigener Posten ist.

## Die kürzeste Fassung

**Gabbro kann heute alles, dessen Größen jemand aufschreiben kann.** Nach der Erweiterung
alles, dessen Größen jemand *bei der Erzeugung* aufschreiben kann. **Nie: alles, was keinen
Punkt hat, an dem „es reicht nicht" gesagt wird** — ~~plus Gleitkomma,~~ plus alles hinter
einem Sprung ins Ungezeugte. *(Der Gleitkommazusatz ist am 2026-08-18 entfallen; die
Aufzählung hat damit zwei Glieder statt drei.)*

---

# Gleitkomma: was wirklich bricht — und „nur auf der GPU" ist keine Erweiterung, sondern eine Ablesung

## Was an Gleitkomma bricht, ist **nicht** M1

Der Einwand hat recht, dass „für immer draußen" einen Grad zu absolut war — aber der Grund
liegt anderswo, als beide Fassungen vermuteten. **Intervallarithmetik über IEEE-754 ist
gebaut und bekannt**; jede Operation weitet um ein ulp, das ist Handwerk.

**Was bricht, ist die NEGATION einer Vergleichsbedingung** — und damit V1–V3.

```gabbro
if x < y { … } else { … }
```

Über ganzen Zahlen gibt der `else`-Zweig `x >= y`. **Über Gleitkomma gibt er nichts**: ist
eines von beiden NaN, sind *alle* Vergleiche falsch, und `!(x < y)` folgt `x >= y` nicht.
Trichotomie hat vier Ausgänge statt drei.

> **`m1::fakten_aus(bedingung, negiert = true)` ist genau diese Operation, und sie wäre
> unsicher.** Das ist keine Ungenauigkeit im Randbereich — *es ist die Maschinerie, mit der
> jede Verengung in dieser Sprache arbeitet.*

Zwei Auswege, beide teuer: NaN durch Konstruktion ausschließen (Prüfung an jeder Operation —
und W6 verbietet eine Laufzeitprüfung, die nicht M1-begründet ist), oder die Negation eines
Gleitkommavergleichs **kein Faktum** liefern lassen (sicher, und dann ist Gleitkomma genau
dort ungeprüft, wo man es prüfen wollte).

*Die ehrliche Fassung ist damit nicht „unmöglich", sondern:* **eine zweite Faktenlogik neben
V1–V3, kein zweiter Zahlentyp.**

## „Nur auf der GPU" trifft — und es ist **schon so**, gemessen

Der Vorschlag ist keine Spracherweiterung. Er ist die Feststellung, dass ein Treiber
Gleitkommazahlen **bewegt und nicht ausrechnet** — und das braucht **keine Arithmetik**:

```gabbro
opaque type F32 = u32;
table Eckpunkte count 4096 { slot { x : F32, y : F32, z : F32, } }
→ 4 Items, 0 Fehler, 0 Hinweise
```

**Das geht heute, ohne eine Zeile Änderung.** Ein Gleitkommawort ist vier Bytes; wer es nur
in einen Puffer legt, braucht keinen Zahlbegriff. *Es `f32` zu nennen wäre die schlechtere
Wahl — der Name verspricht Arithmetik, die es nicht gibt.*

**Und die Trennlinie liegt genau dort, wo sie hingehört:** was der Renderer selbst ausrechnen
müsste (Transformationsmatrizen), rechnet dann die GPU im Shader — *und der Shader ist
Gastcode, also dieselbe Konstruktion wie der JIT: Isolation statt Beweis.*

## Aber: der Vorschlag verlangt, dass `opaque` HÄLT — und es hielt nicht

```gabbro
opaque type F32 = u32;
impl fn unsinn(a : F32, b : F32) -> F32 { return a & b; }
→ 3 Items, 0 Fehler, 0 Hinweise
```

**Bitweises Und behält die Breite, also schweigt die Überlaufregel — und der undurchsichtige
Typ wird als sein Träger gerechnet.** Zwei Gleitkommazahlen bitweise zu verunden ergibt
Unsinn, und nichts sagt es.

> ~~**Gemessen 2026-08-18, und seither behoben.**~~ `D003` nimmt einem `opaque type` die
> Rechnung seines Trägers, `D004` schließt die implizite Umwandlung an der Modulgrenze.
> **Der Kasten oben ist der Zustand VOR dem Fund und bleibt als Messung stehen** — das
> Ergebnis `3 Items, 0 Fehler` gilt heute nicht mehr.

Dass `a + b` fällt, ist **Zufall**: es fällt an `M104` (die Breite läuft über), nicht daran,
dass der Typ undurchsichtig ist. *Wo die Breiten aufgehen, geht der Unsinn durch.*

Die Passliste sagt es selbst — D1/D2, teilgebaut: *„undurchsichtige Neutypen ohne Umwandlung
ebenfalls nicht [gebaut]."* **Der Posten war gebucht; hier ist zum ersten Mal gemessen, was er
kostet.**

> **Damit hat „Gleitkomma nur auf der GPU" einen Preis, und er ist klein und benannt:**
> `opaque` muss beißen. Ein undurchsichtiger Typ hat **keine** Operationen seines Trägers —
> weder Rechnung noch Vergleich noch Bitverknüpfung —, bis eine Umwandlung dasteht. *Das ist
> D1/D2, nicht Gleitkomma; es fällt für jeden undurchsichtigen Typ zugleich.*

## Die Reihenfolge, wie vorgeschlagen — mit einem Einschub

1. **«B24»** — billigste Entscheidung, größter Ertrag (Netzwerkstack). *Und die Anmerkung
   trifft: `embeds [hi:lo]` gibt es, `device`-Register nehmen Mehrbitfelder längst. Es ist
   eine Vereinheitlichung zweier vorhandener Formen.*
2. **`entrust`** — ein Wort, öffnet JVM/JIT/jedes Gastmodul. *Der Einwand hat recht: der
   Sprung ins Ungezeugte ist ein Adressraumwechsel, kein Kontrollflusssprung, und Gabbro
   schuldet dem Gast nichts.*
3. **`opaque` zum Beißen bringen** — ~~eingeschoben~~ **GEBAUT 2026-08-18** (`D003` die
   Rechnung, `D004` die Wand an der Modulgrenze). Klein, D1/D2, und es fällt für alle
   undurchsichtigen Typen zugleich. *Offen bleibt die Tür: es gibt keine Form, einen
   undurchsichtigen Typ ABSICHTLICH zu öffnen — ein Verbot ohne Ausweg.*
4. **Festkomma** — ~~als Fragment~~ **gemessen und geschlossen, 2026-08-18.** M1 trägt die
   doppelte Zwischenbreite nicht und muss es nicht: es rechnet mit dem deklarierten BEREICH.
   `type Q16 = i64 in -2147483648 .. 2147483647` mit `(a*b) >> 16` geht sauber durch, ohne
   Laufzeitprüfung. *Der Träger ist die Breite, der Bereich ist die Zusage.* Offen bleibt der
   Nebenbefund: **eine Zwischenbreite lässt sich nicht NENNEN** — dieselbe Bauart wie `opaque`
   ohne Tür.
5. **Gleitkomma** — ~~als Memo~~ ~~**geschrieben und beschlossen, 2026-08-18**~~
   **GEBAUT, am selben Tag** («F», weiter unten). Das Memo
   ([`MEMO-GLEITKOMMA.md`](MEMO-GLEITKOMMA.md)) empfahl **nicht bauen**, und die Empfehlung
   stand auf einer Zählung — **0 rechnende Stellen in 139 Kerneldateien**; beide
   `f64`-Erwähnungen stehen in Kommentaren, und die erste verneint den Bedarf ausdrücklich.
   **Die Entscheidung des Ordners lautete anders, und «F0» nennt den Ersatz für den fehlenden
   Bedarf statt ihn zu erfinden.** *Der teuerste Fund des Memos steht unberührt: Gleitkomma
   ändert die AUFRUFKONVENTION, und das trifft die Bibliotheks-ABI, auch wenn Gabbro nie eine
   Gleitkommazahl kennt.*

---

# Die Klasse hat jetzt einen Namen und einen Wächter — *deklariert, exportiert, nie gelesen*

Dreimal in zwei Wochen dasselbe Muster, und jedes Mal von Hand gefunden:

| | | |
|---|---|---|
| `rank` | deklariert, im Zeugnis | von keinem Pass gegen die Sperrordnung gehalten |
| `opaque` | deklariert, ein **Verbot** | biss an keiner Rechenstelle |
| `ensures` | deklariert, im Zeugnis **gezählt** | gegen keinen Rumpf gehalten |

**Ein Muster, das dreimal von Hand gefunden wird, ist kein Zufall, sondern ein fehlendes
Werkzeug.** Und die vierte Fundstelle ist teurer als die dritte, weil auf ihr dann schon etwas
steht: die wertgetragenen Indextypen bauen auf `opaque`, die Bibliotheks-ABI baut auf
`ensures`. *Den Boden reparieren, bevor das Stockwerk kommt, ist billiger als danach.*

`./instrumente/pruefe-klauseln.py` hält jedes `pub`-Feld jeder `pub struct` aus `ast.rs` — **die ganze
Fläche, die der Leser füllt, ohne Auswahl** — gegen die Menge der Felder, auf die irgendein
Pass zugreift. Die Leser zerfallen in zwei Lager, und die Trennung *ist* die Aussage: unter
`gabbro-check/src` wird **geprüft**, in `emit.rs`/`zeugnis.rs`/`gabbro-cli` nur **abgesenkt und
berichtet**.

## Es waren nicht vier, es sind neunundvierzig

```
131 Feldnamen · 23 Leserdateien, davon 4 tragend

  nur getragen   21   abgesenkt oder berichtet, von keinem Pass geprüft
  ungelesen      28   der Leser füllt sie, niemand sieht hin

  ZUSAGE         18   eine Aussage über Verhalten, die kein Pass hält  ← die Klasse
  ABSENKUNG       6   der Erzeuger ist ihr richtiger und einziger Leser
  TOT            25   das Bauteil ist gelesen und sonst nirgends
```

**Die Stufe ist gemessen, die Klasse ist ein Urteil** — das Werkzeug sagt beides getrennt an,
statt das eine als das andere auszugeben.

Vier Funde, die nicht in der Erwartung standen:

- **`fortschritt` (`progress`) liest niemand.** `schleifen.rs` steigt in den Rumpf jeder
  `forever`- und `retry`-Schleife und sieht den Zeugen nicht an. *Das ist genau die Zusage, an
  der ein Kernel hängt, der Jahre läuft* — und sie ist heute ein Wort ohne Leser.
- **`versatz` liest nur der Erzeuger.** Dass zwei Register einander nicht überlappen, ist der
  **Hauptsatz** von `Device_Konstruktor.thy`. Der Beweis steht; die Prüferzeile fehlt.
  *Ein bewiesener Satz ohne Pass ist eine Zusage über ein Programm, das so nicht geprüft wird.*
- **`entry` gibt es nicht.** Zwölf Felder — `regs_in`, `regs_out`, `preserves`, `clobbers`,
  `stack`, `vektor`, `via`, `ist`, `verschachtelt`, `dispatch`, `pro_kern` — und **keine Datei
  außerhalb des Lesers nennt `EntryDecl`.** Der Eintrittsvertrag ist geschriebene Grammatik
  und sonst nichts. *Das ist der Vertrag, den `entrust` erben soll.*
- **`pub` ist wirkungslos.** Kein Pass, kein Erzeuger liest `oeffentlich`. Sichtbarkeit wird
  weder geprüft noch abgesenkt — und eine Bibliotheks-ABI beginnt bei genau diesem Wort.

## Die Vergröberung geht in die sichere Richtung

Gemessen wird **je Name, nicht je Struktur**: heißt ein Feld in zwei Strukturen gleich und
liest ein Pass nur das eine, gilt der Name als gelesen. Der Bericht ist damit eine **untere
Schranke** der Klasse (W10) — was er nennt, ist echt; was er verschweigt, kann trotzdem da
sein. *Er darf verpflichten und nicht freisprechen.*

Und weil ein Zähler, der immer null sagt, dasselbe Rot wie Grün liefert, weist das Werkzeug
seine Messfähigkeit nach (R14): `span` **muss** als gelesen herauskommen, `section` **muss** es
nicht. Fällt eine der beiden Proben, bricht es ab, statt zu schweigen. Die Ratsche klemmt in
beide Richtungen — eine neue Fundstelle schlägt an, **und eine gestiegene Zeile auch**. *Eine
Tabelle, die nur wächst, ist eine Ausnahmeliste.*

---

# Der Beweiswächter sang über einem Lauf, der nichts gebaut hatte

`isabelle build -D .` wählte **keine Sitzung aus**, tat nichts, endete mit 0 — und
`pruefe-beweise.sh` meldete darüber *„ALL PASS — 9 Theorien"*. Die Zahl kam aus `ROOT`, nicht
aus dem Bau. **Ein Werkzeug, das Schweigen für Zustimmung nimmt, misst nicht** (W7, R14).

Drei Änderungen, jede mit einer Probe, die anschlägt:

| | |
|---|---|
| die Sitzung **benennen** (`-d . Gabbro`) | ein unbekannter Name ist ein Fehler, kein Schweigen |
| einen **Nachweis** verlangen | frische Fertigmeldung *oder* ein Bauwerksbuch, das jünger ist als jede Quelle |
| `ROOT` gegen den **Ordner** halten | eine `.thy` ohne Eintrag ist ein Beweis, den niemand führt |

Die dritte fand ihren Anlass in der eigenen Geschichte: `Verbund_Konstruktor.thy` lag genau so
im Ordner, bevor sie in `ROOT` kam.

**Vier Proben, vier Bisse:** Waise ohne Eintrag → Abbruch · alte Fassung plus geänderte Quelle
→ *ohne Nachweis* · kaputter Beweisschritt → `FEHLER` mit Zeilennummer · wiederhergestellt →
`Finished Gabbro (0:00:22)`. *Der grüne Lauf trägt seitdem seinen Nachweis im Text.*

---

# Die symbolische Kostenrechnung hat eine KANTE — und sie wird vor der ersten Zeile gezogen

Der Block ist **kleiner, als er wirkt**, solange die Ausdrucksform geschlossen bleibt. Und die
Form steht bereits im Prüfer, ohne dass jemand sie als Grenze ausgesprochen hätte —
`kosten.rs`:

```rust
struct Term { fest: i128, glieder: BTreeMap<String, i128> }
```

Das *ist* die geschlossene Form. Was fehlt, ist der Satz, dass sie geschlossen **bleibt**:

```
zulässig    K                    eine Zahl
            K · n                eine Zahl mal einem DEKLARIERTEN Maß
            K₀ + K₁·n₁ + … + Kₘ·nₘ

Vergleich   nur bei identischen Maßen, koeffizientenweise
            (Nichtnegativität ist Prämisse und wird geprüft)

verboten    freie Arithmetik · `min` · Fallunterscheidung
            Vergleich verschiedener Maße
```

**Sobald jemand `min`, Fallunterscheidungen oder den Vergleich verschiedener Maße will, ist es
ein Löser** — und dann ist die Linie überschritten, die diesen Ordner definiert. Ein Prüfer,
der `min(40·n, 2^32)` gegen `40·m` hält, sucht; er rechnet nicht mehr.

> Das ist dieselbe Kante wie bei `@[66:64]`: **die Weigerung ist die Antwort.** Wer zwei Maße
> vergleichen will, nennt das zweite Maß — so wie ein 128-Bit-Eintrag zwei Wörter sind und der
> Programmierer das zweite benennt.

*Eine Kante, die vor der ersten Zeile gezogen wird, kostet einen Absatz. Nach der ersten Zeile
kostet sie einen Rückbau.*

---

# Die Reihenfolge nach HEBELWIRKUNG statt nach Größe

Die vorige Liste sortierte nach Größe. Das ist die falsche Achse: **ein kleiner Posten, auf dem
etwas gebaut werden soll, ist teurer als ein großer, der allein steht.**

1. **DIE RESERVE UND DIE HINTERLEGUNG — `count N` mit `backed k`, samt Freiliste.**
   *Neu an Position 1 am 2026-08-18, und der Bedarf ist gemessen, nicht geschätzt.* Er hat
   drei Teile, und der dritte ist das Tor:

   **(a) Die Freiliste muss schreibbar werden.** `index into T` in einem Slotfeld verliert
   seine Schranke, wenn `T` beim Auflösen noch nicht fertig ist — bei Selbstbezüglichkeit
   also **immer**. Damit ist heute keine verkettete Struktur schreibbar: keine Freiliste,
   keine CDT, kein Objektgraph. *Ohne (a) gibt es keinen Allokator, über den (b) und (c)
   reden könnten.*

   **(b) Die Hinterlegung wird eine Zahl.** Eine Tabelle nennt zwei Größen statt einer:

   ```gabbro
   table Halde count 1000000000        -- die RESERVE: Adressraum, ~30 GiB
       backed  hinterlegt              -- die HINTERLEGUNG: ein WERT, monoton
   ```

   Das trennt, was heute zusammenfällt: **`count` ist Adressraum, `backed` ist Speicher.**
   30 GiB zu deklarieren und 100 MiB zu hinterlegen ist damit eine Aussage der Sprache und
   keine Hoffnung an den Seitenfehlerpfad. *Und `allocs` bekommt endlich eine Bedeutung* —
   heute ist es ein Wirkungswort mit genau einer Fundstelle, die nur den Namen herauszieht;
   morgen ist es die Wirkung der einen Funktion, die `hinterlegt` erhöht.

   **(c) Das Tor ist KEINE neue Prüfung — es ist dieselbe gegen die richtige Zahl.**
   `M103` hält jeden Index gegen die deklarierte Schranke. Heute ist das `N`, die Reserve.
   Darf es `hinterlegt` sein, prüft **derselbe Pass dieselbe Sache** — nur gegen die Zahl,
   auf die es ankommt. Gemessen am 2026-08-18:

   ```
   narrow i to 0 ..< N   (Konstante)   ->  0 Fehler, der Zugriff geht durch
   narrow i to 0 ..< k   (Wert)        ->  von der GRAMMATIK angenommen,
                                           M1 lässt die Tatsache fallen
   ```

   **Die Form steht also schon da; es fehlt der Träger.** Was M1 lernen muss, ist eine
   Bereichsgrenze, die ein Wert ist — und für den Vergleich zweier solcher Schranken gilt die
   Kante von oben: geschlossene Form, identische Maße, kein Löser.

   > **Und die Gefahr ist nicht das Wachsen, sondern das SCHRUMPFEN.** Eine Tatsache `i <
   > hinterlegt`, die vor einer Verkleinerung gewonnen wurde, ist danach falsch. Also
   > entweder **monoton** — die einfache, ehrliche Fassung — oder das Verkleinern ist ein
   > Phasenschritt, nach dem kein alter Index überlebt. *Für das Zweite gibt es die
   > «B37»-Maschinerie schon (`order`/`advances`), und für das Erste braucht es nichts.*

   *Damit wäre ein GC schreibbar: die Objektgraph-Hälfte kann Gabbro längst — `by unvisited`
   ist zyklensicheres Markieren, `table.induktion` gibt die Terminierung, die Kosten sind
   beschränkt.*

2. **`opaque`** — ~~bekommt eine Tür~~ **Wand UND Tür, 2026-08-18.** Beim Bauen fiel auf,
   dass die Diagnose falsch war: es fehlte nicht die Tür, sondern die **Wand**. Gemessen:

   ```gabbro
   opaque type Pa = u64;
   impl fn hinein(x : u64) -> Pa { return x; }   -- 0 Fehler
   impl fn hinaus(p : Pa) -> u64 { return p; }   -- 0 Fehler
   ```

   **D1 — die erste der beiden Deklarationsregeln — war gar nicht durchgesetzt.** `D003` biss
   an der Rechnung, die Zuweisung ging in beide Richtungen still durch. *Eine Tür in einer
   Wand, die es nicht gibt, ist keine.*

   `D004` schließt sie, und die Tür steht da, wo die Dokumente sie hinstellen — *„opaque, one
   generator"* mit **Modulgrenze**: im erklärenden Modul ist die Darstellung bekannt,
   außerhalb nicht. **Damit bekommt die Modulgrenze ihre erste Bedeutung in diesem Prüfer.**

   > **Und die Regel hat auf diesem Korpus NULL Biss** — dieselbe Lage wie bei `E010`. Alle
   > zwölf `opaque`-Deklarationen der Beispiele erklären und benutzen im selben Modul. *Das
   > ist eine Eigenschaft des Korpus, nicht der Regel — und ein weiteres Argument für den
   > zweiten.*
3. **`ensures`** — ~~wird gelesen~~ **gelesen seit 2026-08-18.** `M109`/`M110`/`M111` prüfen
   die **Wohlgeformtheit**, nicht den Beweis — *ob der Rumpf die Zusage einlöst, bleibt
   Beweisersache, und das ist die Arbeitsteilung dieses Ordners.* Geprüft wird: auflösende
   Namen, `result` nur wo es eins gibt, und **keine Zusage ohne einen Ort, an dem die
   Funktion sie herstellen könnte** — die dritte hält sie gegen `effects`, also gegen eine
   Klausel, die gelesen wird.

   > **Beim ersten Lauf fiel ein Fund im Korpus an:** `ensures unberuehrt <= s.len` nannte
   > den **Funktionsnamen** statt `result`. Die Vorlage kam aus einer Sprache, in der der
   > Name das Ergebnis bezeichnet — *und die Zeile stand seit dem Schnitt da, weil `ensures`
   > von keinem Pass gelesen wurde.*

   Keine Kleinigkeit: eine Zusage, die im Zeugnis erscheint, in der
   Bibliotheks-ABI getragen werden soll und heute nirgends gegen den Rumpf **oder auch nur
   gegen die Wohlgeformtheit** geprüft wird. Der Wächter hat siebzehn Geschwister dazu benannt.
4. **Der zweite Korpus** — **abgeschlossen 2026-08-18: fünf Fragmente, vier tragen ohne
   Rest.** Drei Funde, die ein eigener Korpus nicht geliefert hätte: **RCU als Klasse**
   (gebaut), **ein Zählerüberlauf** im fremden Code (`M101` beim ersten Rendern), und **der
   Fortschrittszeuge als Kommentar** (`free_pid() will awaken this task` — Gabbro macht daraus
   eine Annahme mit Falsifikator). Der eine Rest ist ein Befund über die Sprache: `atomic` ist
   ein Item und kein Slotfeld, also ist ein Zähler *im* Objekt nicht atomar deklarierbar.
   *Fünf Fragmente sind keine Aussage über 64 000 Dateien — es sind Nachbildungen, und
   gemessen ist die Form, nicht der Rumpf.* — angefangen hatte er beim ersten Hinsehen
   geliefert, wofür er da ist: einen **Konstruktfund**. RCU (578 Leseseiten in `kernel/`+`mm/`
   eines Linux-Baums) hat in Gabbro kein Wort — *keine Nachlässigkeit, sondern die Klasse,
   die der erste Korpus nie zeigte.* Dazu die zwei Zielgrößen an fremdem Code: `BUG_ON`/
   `WARN_ON` **2034** (was Gabbro ersetzt) und `goto` **2669** (was Gabbro absichtlich nicht
   hat, und was in vier Formen zerfällt, von denen es drei gibt). *Gemessen sind Formen, nicht
   Übersetzbarkeit — Fragmente sind noch keine geschnitten.* Als einziger der großen Blöcke
   **entsperrt** er andere, statt selbst
   zu wachsen: K11.2.2 hängt daran, jede Null im Zeugnis hängt daran, und die Konvergenzmetrik
   bekommt erst mit ihm einen zweiten Datenpunkt aus einer anderen Autorenlinie. *Die
   aarch64-Lektion in neuer Form: ein Korpus, den derselbe Autor für dieselbe Sprache
   schreibt, misst Passung, nicht Übertragbarkeit.*
5. **Dann erst die übrige Erweiterung** — mit der Kante oben, bevor die erste symbolische Kostenzeile
   geschrieben wird. *Die Erweiterung ohne zweiten Korpus verlängert die Sprache um Konstrukte,
   deren Bedarf nur der eine Baum belegt.*

`entrust`, Festkomma und das Gleitkomma-Memo bleiben, wo sie standen — sie tragen nichts, was
vorher fallen müsste.

---

# Die sechste Klasse: **bewiesen, und von nichts hergestellt**

Die fünfte Klasse hieß *deklariert, exportiert, nie gelesen*. Die sechste kehrt sie um, und
sie ist teurer:

| | |
|---|---|
| **fünfte** | eine Klausel steht da, kein Pass liest sie — *niemand weiß etwas* |
| **sechste** | ein Satz ist **bewiesen**, und seine Prämisse stellt niemand her — *man weiß etwas Falsches* |

`device.konstruktor` steht als **bewiesen** im Register. Sein Hauptsatz
`getrennte_register_treffen_getrennte_zellen` setzt `getrennt r s` voraus. Kein Pass rechnet
das nach — `versatz` wird nur abgesenkt. **Wer das Zeugnis liest, schließt aus „bewiesen" auf
Überlappungsfreiheit**, und der Beweis deckt die Lücke zu, statt sie zu zeigen.

## Zahn 3 — jede bewiesene Schablone bindet ihre Prämissen

Zahn 1 zählt Einträge, Zahn 2 begrenzt die unbewiesenen; **beide sehen nach vorn.** Der dritte
fragt zurück: *welche Prämisse stellt welcher Pass her?* Jede `Bewiesen`-Zeile trägt jetzt
ihre Liste, und `durch` unterscheidet zwei Stärken:

```
ein PASS            deckt jedes Programm, das der Übersetzer je sieht
eine MUTATIONSPROBE deckt den ERZEUGER, einmal -- die Brücke aus PL.3
None                NIEMAND -- der Satz hängt in der Luft
```

**Gemessen bei 9 bewiesenen Schablonen: 17 Prämissen, 8 ohne Hersteller.** Der Zeitpunkt ist
richtig gewählt — bei zwanzig bewiesenen wäre die Spalte Nacharbeit an zwanzig Sätzen.

Der schärfste Nebenfund: **`by consuming` liest kein Pass.** Beide Prämissen von
`consuming.ordnung` sind damit nicht bloß unhergestellt, sondern unherstellbar — und für die
erste (*Entfernen, nicht Umhängen*) führt `Consuming.thy` K-2 ein **Gegenbeispiel**.

---

# `progress` hat einen Leser — und was dabei NICHT versprochen wird

`S003`/`S004` in `schleifen.rs`. **D8 steht unverändert**: *„`progress` nennt Annahmen,
beweist keine Lebendigkeit."* Ein Pass, der hier mehr verspräche, wäre genau die Sorte Zusage,
gegen die dieser Ordner gebaut ist.

Geprüft wird, was die Sprache verspricht — `progress` nennt eine **Annahme mit Falsifikator**:

```
S003   der Name gehört keiner Annahme -- die Schleife ruht auf einem Wort,
       das niemand aufgeschrieben hat, und im Zeugnis steht es nirgends
S004   die Annahme ist `unfalsifiable` -- dann endet die Schleife, weil es
       dasteht, und keine Sonde kann je widersprechen
```

**Am ersten Tag fiel er an fünf Stellen des eigenen Korpus**, darunter dreimal in
`04-schleifen.gab` — der Datei, deren Kommentar die Regel erklärt. *Ein Beispiel, das seine
eigene Regel erklärt und nicht befolgt, ist die Lage, die ein Wort ohne Leser erzeugt.*

In `02-geraet.gab` war der Zeuge ein **Synonym**: `geraet_quittiert` meinte die erklärte
`vtd_srtp_quittiert`, und nichts verband die beiden.

> Und die Ratsche des Klauselwächters hat beim nächsten Lauf **nach oben** angeschlagen:
> `fortschritt` ist gestiegen, der Eintrag war veraltet. *Genau dafür klemmt sie in beide
> Richtungen.*

---

# `entrust` steht — ein Wort, ein Item, eine Zeugniszeile, drei Absagen

Der Vorschlag lautete: *„ein `code`-Raum, dessen Inhalt Gabbro nicht kennt, mit deklariertem
Eintrittsvertrag und einem `assume`-Eintrag im Zeugnis. Ein Wort, eine Zeile Zeugnisformat,
kein neuer Pass."* So steht es, mit einer Abweichung und einem Fund.

```gabbro
entrust jitpuffer at Gastbild arch x86_64 {
    regs in { eintritt : rdi, kappe : rsi, }
    stack  gaststapel
    assume gast_bleibt_in_seinem_raum;
}
```

**Bewusst kleiner als `entry`:** kein `regs out`, kein `preserves`, kein `clobbers`, kein
`dispatch`. *Über das, was der Gast zurückgibt, kann Gabbro nichts sagen — eine Klausel dafür
wäre eine Zusage über ein Programm, das der Übersetzer nie sieht.*

## Die Abweichung: `at` nimmt einen NAMEN, keinen Ausdruck

Der erste Entwurf ließ dort einen Ausdruck zu. Dann wäre `raum` sofort die einundfünfzigste
ungelesene Klausel gewesen — an dem Tag, an dem der Wächter dafür gebaut wurde. **Ein Name
ist prüfbar** (`N006`), und die Begründung ist keine Bequemlichkeit: *ein `entrust` auf einen
gerechneten Wert wäre ein Sprung an eine ausgerechnete Adresse* — genau das, was nicht
nennbar sein soll.

## Der einzige Leser, den `entrust` bekommt — und er ist derselbe wie bei `progress`

| | |
|---|---|
| `N004` | die Annahme ist **nicht erklärt** — sie steht in keinem Manifest, kommt in kein Zeugnis |
| `N005` | die Annahme ist `unfalsifiable` — *keine Isolation, sondern ein Wunsch* |
| `N006` | der Raum ist hier nicht deklariert |

Derselbe Sammler wie `S003`/`S004`, damit die Antwort dieselbe ist. **Über den Rumpf des
Gastes sagt Gabbro nichts** — keine Kosten, keine Wirkungen, keine Terminierung. *Was bliebe,
wenn auch die Annahme ungeprüft wäre, ist eine Deklaration, die nichts behauptet.*

## Und eine vierte Klausel-Klasse, mit scharfem Kriterium

`regs_gast` und `stapel` liest kein Pass — und das ist richtig, denn der Gast steht nicht im
Baum. Sie sind **FREMD**, nicht ZUSAGE. Damit die Klasse keine Ausnahmeliste wird, hat sie
eine Bedingung:

> **FREMD ist nur zulässig, wenn das Zeugnis die Klausel DRUCKT.** Wer nicht prüfen kann,
> exportiert. *„Kann man nicht prüfen" ist keine Buchung.*

Die `entrust`-Zeile in Abschnitt E trägt den ganzen Vertrag:

```
jitpuffer   GAST auf `x86_64`, Stapel `gaststapel`, Register { eintritt: rdi, kappe: rsi }
            -- Gabbro sagt ueber den Rumpf NICHTS; es gilt `assume gast_bleibt_in_seinem_raum`
```

## Was NICHT dasteht: die Absenkung

Der Erzeuger weigert sich benannt (`C001`). Die Übergabe ist ein Registervertrag plus Sprung —
**dieselbe Baustelle wie `entry`, und die ist gemessen leer.** *Wer `entrust` absenkt, senkt
den Eintrittsvertrag zum ersten Mal ab.*

---

# «F» — f32 und f64, vollständig. Der Plan.

> **Beschlossen 2026-08-18.** Das Memo empfahl *nicht bauen*; die Entscheidung lautet anders,
> und sie ist die des Ordners. Was hier steht, ist der Weg — mit der einen Abweichung vorn,
> statt versteckt.

## F0 — Die Abweichung, und was sie ersetzt

Die Regel des Ordners heißt **kein Bau ohne gemessenen Bedarf** (W3), und der Bedarf ist
gemessen **null** (139 Kerneldateien, 0 rechnende Stellen). *Eine Regel, die man kennt und
bricht, braucht keinen weiteren Satz — sie braucht einen Ersatz.*

**Der Ersatz ist der Korpus, und er kommt ZUERST.** Drei bis fünf echte Gleitkommafragmente
von außerhalb dieses Baums — eine Transformationskette, ein Filter, ein Integrationsschritt,
der Messpfad, der in Caprock eine Nachkommastelle brauchte. Jedes Fragment nennt mindestens
ein Konstrukt, das es braucht.

> **Ohne F0 entwirft man für eine vorgestellte Verwendung**, und das ist genau die Bewegung,
> gegen die R7 und W3 stehen. *Der Bedarf darf entschieden werden; er darf nicht erfunden
> werden.*

**Tor F0: ERREICHT 2026-08-18.** Vier Fragmente aus *Fraktaler 3* liegen in
`FRAGMENTE.md` — und F0 hat seine Aufgabe sofort erfüllt: **es hat F1.5 gekippt**, bevor eine
Zeile Code dafür geschrieben war. *Genau dafür kommt der Korpus zuerst.*

## F1 — Sieben Entscheidungen VOR der Grammatik (R7)

**1. Die Ebene.** Gemessen: lokal ist nur *reell + Fehlerschranke* baubar
(`HOL-Library.Float` sind dyadische Rationalzahlen, `Interval_Float` liegt daneben, **IEEE-754
in Isabelle ist nicht installiert**). Und der Prüfer macht ohnehin Klempnerei, nicht Numerik.

> **Die Entscheidung: die Gleitkommatatsache ist die Ganzzahltatsache plus ZWEI BITS.**
> Ein Intervall über den reellen Zahlen, dazu `kann_nan` und `kann_unendlich`.

*Das ist kein Löser* — es ist Intervallfortpflanzung, dieselbe Bauart wie der Bereich, den M1
schon trägt. Die Kante von oben gilt unverändert: geschlossene Form, keine freie Arithmetik.

**2. Der Rundungsmodus.** Zunächst **nur RNE**. `f64` heißt `f64<RNE>`; jeder andere Modus
wird **benannt abgelehnt** (`F003`). Die Tür bleibt offen — die Form dafür steht schon fest
(`ptr<…>`-Gestalt, vierte Instanz des Musters).

**3. Die Negation — das Herzstück.** Nicht *Gleitkomma bekommt keine Fakten*, sondern:

```
!(x < y)  liefert  x >= y   GENAU DANN, wenn beide Operanden
                            als NICHT-NaN bekannt sind
```

**Nicht-NaN-Sein ist selbst eine Tatsache, die M1 führt.** Damit ist die Verengungsmaschinerie
nicht abgeschaltet, sondern **bedingt** — man wird NaN einmal los und rechnet danach normal.
*Ohne diese Entscheidung ist Gleitkomma in Gabbro unbrauchbar; mit ihr ist es gewöhnlich.*

**4. Wie man NaN loswird.** Über die vorhandene Form: `narrow x to finite else { … }`. Die
Prüfung bleibt im erzeugten C, bis M1 sie wegbeweist (W6) — genau wie bei jedem Bereich.

**5. Literale — BERICHTIGT durch F0 am 2026-08-18.** Die geplante Regel lautete *exakt
darstellbar, sonst Absage*. **F0 hat sie gekippt:** an 340 Literalen eines echten Renderers
gemessen wären **53 abgelehnt worden, darunter ln 2 und 2π**. Eine transzendente Konstante ist
in keiner binären Breite exakt; ihre Dezimalform ist schon eine Näherung.

*Aber dieselbe Messung sagt, wo die Grenze wirklich liegt:* die exakten 84 % sind
Strukturkonstanten (`0.0`, `1.0`, `0.5`), die inexakten 16 % sind Näherungen an reelle Zahlen.

> **Verboten ist nicht das Inexakte, sondern das STILLSCHWEIGEND Inexakte.**

```gabbro
const TAU : f64 = 6.283185307179586 rounded;
```

Ein Wort, und es hat ein Geschwister im Ordner: `u32 wrapping` sagt *der Überlauf ist erklärt
und darum kein Befund* — `rounded` sagt dasselbe über die Rundung. **Dieselbe Form, dieselbe
Begründung, kein neues Muster.** `F002` trifft nur noch das unerklärte Literal.

Und der Leser bekommt eine gemessene Aufgabe: `0..100` ist heute gültig, also ist `1.5` gegen
`1..5` echt mehrdeutig — **`..` frisst zuerst** (maximal munch), `1.` allein wird abgelehnt.

**6. Gleichheit** bleibt erlaubt. `x == x` ist für NaN falsch, und genau das führt die
Faktenmaschine. *Ein Verbot wäre eine Härtung ohne gemessenen Bedarf.*

**7. `accumulates` weigert sich mechanisch.** `merge add|max|min` über einem Gleitkommatyp
bricht die Prämisse einer **bewiesenen** Schablone (`accumulates.monoid`: `add` ist nicht
assoziativ, `max` mit NaN ist kein Verband). `F004`, und die Prämisse ist bereits geteilt.

## F1a — Das F002-Loch, und warum es VOR `narrow` fiel

**Die Regel biss überall außer am Hauptschauplatz.** `F002` fiel im Funktionsrumpf und schwieg
in der `const`-Deklaration — und die 53 inexakten Literale, die F0 gemessen hat, sind ln 2,
2π und Schwellwerte. *Die leben in Konstanten.* Eine Regel, deren Bedarfsbeleg aus genau der
Deklarationsform kommt, die sie nicht erreicht, ist nicht stichprobenhaft, sondern **umgekehrt
gemessen**.

**Gemessen war die Ursache größer als der Befund:** M1 lief bis 2026-08-18 **nur über
Funktionsrümpfe**. `const`, `static`, alles andere sah er nie.

```
vorher   M1 = Funktionsrümpfe
nachher  M1 = Funktionsrümpfe + const/static-Initialisierer (leere Lage, volle Umgebung)
```

**Der Bestand hat die Erweiterung unverändert überlebt** — 126 Proben, keine neue Absage. Und
sie misst, statt nur zu schweigen: `const ZU_GROSS : u8 = 300;` fällt jetzt an `M101` und tat
es vorher nicht. *Ohne diese Gegenprobe wäre die Reichweite ein Nebeneffekt und keine Zusage.*

## F1b — Die Faktenart für `finite`, und der Entwurf steht vor dem Bau

**Der Bedarfsbeleg ist eine DISJUNKTION, kein einzelnes Prädikat.** FF1 lautet:

```c
if (Zz2 < ER2 || isnan(de.x) || isinf(de.x) || isnan(de.y) || isinf(de.y))
```

Im `else`-Zweig von `a || b` gelten `¬a` **und** `¬b` — beide Bits fallen gleichzeitig. Wer nur
das einzelne Prädikat verengt, deckt genau den Fall nicht ab, den F0 als Bedarfsbeleg gefunden
hat.

**Gemessen: der Zweig dafür EXISTIERT bereits.**

```rust
ExprArt::Binaer(BinOp::Oder, a, b) if negiert => {
    self.fakten_aus(a, true, lage);
    self.fakten_aus(b, true, lage);
}
```

Was fehlt, ist nicht der Weg durch die Disjunktion, sondern **die Faktenart am Ende**. Und die
darf keine Bereichsverfeinerung sein:

> **Endlichkeit ist im Gitter kein Intervall.** `kann_nan` und `kann_unendlich` sind zwei Bits,
> die **unabhängig** gelöscht werden — `isnan(x)` löscht das eine, `isinf(x)` das andere, und
> die Disjunktion löscht beide. Ein Intervall kann das nicht ausdrücken: NaN liegt in *keinem*
> Intervall, und dieselbe Aussage ist trotzdem nicht „der Bereich ist enger".

Daraus die Form: `Fakt::Endlich { schluessel, indizes, nan: bool, unendlich: bool }` — zwei
Flanken, einzeln setzbar, und `narrow … to finite` setzt beide auf einmal.

## F1c — Was der Vergleich GESCHENKT hat, und was die Intervalle kosten werden

**Ein geglückter Vergleich impliziert Nicht-NaN auf beiden Seiten.** Im Dann-Zweig von
`if x < y` sind beide Operanden nan-frei, **ohne jedes `narrow`** — bei `<`, `<=`, `>`, `>=`
und `==` gleichermaßen. Nur `!=` gibt nichts her, denn `NaN != NaN` ist wahr.

> **Genau darum waren zwei Bits richtig:** der Vergleich löscht **eins**, `narrow … to finite`
> löscht **beide**. Wäre Endlichkeit ein Prädikat, hätte der Vergleich nichts beitragen können.

Und `x == x` fällt damit von selbst in seine Rolle — im Korpus die Handschrift für `isnan`,
hier ein gewöhnlicher Vergleich, dessen Dann-Zweig das NaN-Bit löscht. *Er muss nicht als
Idiom erkannt werden.*

### Drei Stellen, an denen die ganzzahlige Gestalt trägt und die Arithmetik darunter nicht

**1. Die Schranken müssen nach AUSSEN runden.** `[a,b] + [c,d]` ist `[RD(a+c), RU(b+d)]`,
nicht `[a+c, b+d]`. Rechnet der Prüfer seine Schranken mit Wirtsdoubles in RNE, sind sie um
bis zu ein Ulp **zu eng** — unsound in der Richtung, die nichts meldet.

> *Der Prüfer selbst braucht `rounded`, im selben Sinn, in dem FF4 es für Literale verlangt:*
> verboten ist nicht das Inexakte, sondern die Stelle, an der nicht dransteht, dass gerundet
> wurde.

**2. Die Null hat zwei Werte, aber nur einen Vergleichsplatz.** `-0.0` liegt in `0.0 .. 1.0`,
weil alle Vergleiche das sagen — `1.0 / x` liefert dafür aber `-inf` statt `+inf`. **Ein
Intervall, das die Null enthält, schränkt das Vorzeichen des Kehrwerts nicht ein**; die
Division muss dort in beide Richtungen unbeschränkt antworten, nicht nur nach oben.

**3. Solange nicht gerechnet wird, ist die weiteste Antwort die einzige ehrliche.**
Gleitkommaarithmetik gibt heute den **vollen** Bereich zurück, NaN eingeschlossen. *Keine
Fortpflanzung heißt nicht „keine Aussage", sondern die weiteste — sonst wäre das Schweigen
eine Zusage.*

## F2 — Wortschatz und Grammatik

| | |
|---|---|
| drei Wörter | `f32`, `f64`, `rounded` — der Wortschatzwächter hält `kw.rs` gegen die Tabelle |
| `intty` → `numty` | die EBNF-Regel wird verallgemeinert, die Ganzzahlform bleibt darin |
| Literalform | Gleitkommaliteral im Leser, mit der `..`-Regel aus F1.5 |
| Bereiche | `f64 in 0.0 .. 1.0` — erlaubt, und die Grenzen müssen exakt darstellbar sein |

## F3 — Typmodell und M1

`Typ::Gleitkomma(FBereich)` mit `FBereich { lo, hi, kann_nan, kann_unendlich, breite }`.
**Die sechzehn gemessenen Stellen** (`umgebung` 6, `m1` 6, `typen` 4) entscheiden je, was sie
mit der neuen Variante tun — *keine darf stillschweigend durchfallen.*

Die eine numerisch heikle Stelle: die Fortpflanzung für `+ − × ÷` muss **nach außen gerundet**
werden, um ein Ulp. Dort verdient `Interval_Float` seinen Platz.

## F4 — Die Absagen, Familie `F` (gemessen frei)

```
F001  hier kann NaN oder Unendlich entstehen, und niemand behandelt es
F002  das Literal ist im Zieltyp nicht exakt darstellbar
F003  ein anderer Rundungsmodus als RNE
F004  `merge` über einem Gleitkommatyp
F005  eine Verknuepfung, die es fuer Gleitkomma nicht gibt (Bitweise, Schieben,
      Rest) -- UND die Mischung mit einer Ganzzahl, solange keine Umwandlungsform dasteht
F006  `long double` und `f16` -- benannt abgelehnt, mit dem Grund
```

**Gebaut 2026-08-18: `F001`, `F002`, `F004`, `F005`.** Offen: `F003` (Rundungsmodus, an
`f64<RNE>` haengend) und `F006`.

*`F005` trägt zwei Fälle statt des geplanten einen, und der zweite ist der wichtigere:* eine
Bitverknüpfung stillschweigend mit dem vollen Bereich zu beantworten wäre eine **Erlaubnis** —
dieselbe Bauart wie `opaque` vor `D003`, wo bitweises Und die Breite behielt und der
undurchsichtige Typ als sein Träger gerechnet wurde.

## F5 — Absenkung und ABI

- `float`/`double`; **`-ffast-math` niemals**, und der Erzeuger sagt die verlangten Schalter an.
- **x86 verlangt SSE2** (Excess precision, Doppelrundung am x87) — das wird eine Annahme mit
  Falsifikator in der Axiomschicht, nicht eine Fußnote.
- **Die Einheit benutzt Gleitkomma** — das ändert die Aufrufkonvention *und* den
  Kontextwechsel. Es gehört ins Zeugnis, nicht in einen Kommentar.

## F6 — Zeugnis

Abschnitt A bekommt die Gleitkommaannahmen (Rundungsmodus gepinnt, SSE2, kein fast-math), und
es kommt **eine neue Zeile** dazu: *diese Einheit rechnet mit Gleitkomma.* **Der Leser des
Zeugnisses muss es sehen, ohne den Quelltext zu lesen** — denn für einen Kernel ist es eine
Aussage über Preemption und Kontextgröße, nicht über Zahlen.

## F7 — Schablonen und Beweise

| | |
|---|---|
| `accumulates.monoid` | Prämisse bereits geteilt und geschärft — nichts weiter zu tun |
| **neu** `float.intervall` | die nach außen gerundete Fortpflanzung ist korrekt |
| **neu** `float.nichtnan` | die Verengung stellt Nicht-NaN-Sein her |

**Beide brauchen nach Zahn 3 ihre Rückrichtung**, bevor sie als bewiesen gelten: welcher Pass
stellt welche Prämisse her.

## F8 — Die Tore

```
P-F1   jede vorhandene Probe bleibt grün, und der GANZZAHLPFAD ist bitgleich
       -- eine Differenzeinheit weist es nach, nicht ein Eindruck
P-F2   je Entscheidung aus F1 eine Giftprobe, die beißt (sieben)
P-F3   die Fragmente aus F0 gehen durch, oder die Weigerung ist benannt
P-F4   `lebend_ungedeckt()` waechst NICHT: jede neue Schablone ist bewiesen,
       oder der Erzeuger weigert sich
```

**P-F1 ist das wichtigste Tor.** Die sechzehn Stellen sind alle auf dem Ganzzahlpfad; wer dort
etwas verschiebt, beschädigt eine Sprache, deren Bedarf gemessen ist, zugunsten einer, deren
Bedarf entschieden wurde.

## Verhältnis zu Punkt 1

**«F» steht neben Punkt 1, nicht davor.** Die Reserve/Hinterlegung hat einen gemessenen
Bedarf und entsperrt einen Allokator; «F» hat einen entschiedenen. *Beides ist zulässig, und
der Unterschied gehört aufgeschrieben, damit er später nicht als gleichrangig gelesen wird.*

---

# «W» — der WIDERRUF hat keinen Wächter, und er hat fünf Stellen gekostet

> **Gefunden 2026-08-19 beim Ablesen des Standes, nicht beim Bauen.** Der Fund ist nicht,
> dass fünf Sätze falsch waren — es ist, **dass niemand sie halten musste.**

## Der Befund

`pruefe-todo.py` hält `TODO.md` gegen sechs Klassen, darunter *stehengebliebene Zahl* und
*Erledigtes in einer Datei, die „ausschließlich Offenes" behauptet*. **Er sieht genau eine
Datei.** Am selben Tag, an dem «F» f32 und f64 baute, standen vier Abschnitte weiter oben in
**derselben Datei** fünf Sätze, die das Gegenteil sagten:

<!-- widerruf:aus -->
| Zeile | stand da | falsch seit |
|---|---|---|
| 1742 | „Gleitkomma — nicht im Kern" | «F1», `typen.rs` |
| 1826 | „M1 ist über Intervallen ganzer Zahlen gebaut" | `FBereich` |
| 1983 | 3D-Renderer: **für immer draußen** | dieselbe Spalte |
| 2018 | „hat keinen Bereich, den `M101` vergleichen könnte" | `M101` vergleicht ihn |
| 2158 | Punkt 5: **nicht bauen** | am selben Tag gebaut |
| 2150 | Punkt 3: `opaque` zum Beißen bringen — **eingeschoben** | `D003`/`D004`, derselbe Tag |
<!-- widerruf:an -->

**Es waren sechs, nicht fünf** — die sechste fiel beim Schreiben des Wächters auf, nicht beim
Ablesen. *Das ist kein Zufall, sondern der Grund für den Wächter:* eine Liste, die man
anlegen muss, wird beim Anlegen länger als die, die man im Kopf hatte.

## Und der erste Lauf fand ZWEI weitere Dateien

**`pruefe-widerruf.py` ist beim ersten Lauf rot geworden** — und zwar an Stellen, die von Hand
nicht gefunden worden waren, weil von Hand nur `PLAN.md` angesehen wurde:

<!-- widerruf:aus -->
| | |
|---|---|
| `dokumente/SPRACHE.md`:614 | *„Lexis unchanged (… no floating point in the core …)"* |
| `dokumente/SYNTAX.md`:165 | *„**No floating point in the core.**"* |
<!-- widerruf:an -->

**Damit sind es acht Stellen in drei Dateien**, und die beiden neuen sind die teureren: sie
stehen in der **Spezifikation**, nicht in einem Planungstext. *Ein Satz in `SYNTAX.md` ist die
Antwort auf die Frage „was ist erlaubt" — er wird gelesen, nicht überflogen.*

> **Das ist die Umkehrung von R11.** Eine Probe, die beim ersten Lauf durchgeht, ist
> verdächtig; **eine, die beim ersten Lauf zwei unbekannte Fundstellen liefert, hat sich
> ausgewiesen.** Derselbe Verlauf wie bei `pruefe-klauseln.py` (48 statt der erwarteten vier).

**Gemessen und nicht geschätzt:** [`beispiele/26-gleitkomma.gab`](../beispiele/26-gleitkomma.gab)
läuft mit *8 Items, 0 Fehler, 100 % Deckung* — während die Datei daneben schrieb, es gehe nicht.

## Warum es genau diese Klasse ist

Es ist **dieselbe Bauart wie die sechs `gap:`-Zeilen**, die in den Summen längst geschlossen
waren: *die Summe wurde gepflegt, die Quelle nicht.* Und dieselbe wie die Klasse, die
`pruefe-klauseln.py` gefunden hat — **dreimal von Hand gefunden, also fehlt ein Werkzeug, nicht
ein Vorsatz.**

> **Der Unterschied zu einer bloßen Ungenauigkeit:** ein widerrufener Satz sagt nicht *„hier
> ist noch etwas offen"*, sondern *„das geht nie"*. **Er verhindert Arbeit, statt sie nur zu
> verzögern** — und er tut es leise, weil er wie ein Ergebnis aussieht.

## Der Wächter: `pruefe-widerruf.py`

Eine Liste **widerrufener Sätze**. Jeder Eintrag führt vier Dinge, und ohne alle vier wird er
nicht angenommen:

```
muster    was nicht mehr dastehen darf (Regulärausdruck)
datum     wann es widerrufen wurde
grund     WAS es widerrufen hat -- eine Datei, ein Beispiel, eine Kennung
ersatz    was stattdessen gilt
```

**Zahn 1 (Ausnahmen sind benannt):** ein Vorkommen ist erlaubt, wenn es im selben Absatz
durchgestrichen oder als Widerruf markiert steht — *der Ordner streicht durch, er löscht
nicht.* **Zahn 2 (R14):** der Wächter prüft sich selbst, indem er einen widerrufenen Satz in
eine Kopie einsetzt und verlangt, dass er fällt.

> **Und die Grenze, damit die Zahl nicht mehr verspricht als sie misst:** der Wächter findet
> nur, was jemand als widerrufen aufgeschrieben hat. **Er ist ein Gedächtnis, kein Urteil** —
> gegen einen Satz, den niemand als überholt erkannt hat, hilft er nicht.

---

# Was Gabbro nicht kann und können sollte — nach PREIS sortiert, 2026-08-19

> Die Liste ist nicht neu; **die Sortierung ist es.** `TODO.md` führt 116 offene Punkte in vier
> Rollen — *Entscheidungen · Messungen · Bauen · Buchhaltung.* Was fehlte, war die Frage
> **„was davon kostet keine Zeile Code"**, und sie sortiert die Liste anders als die Rollen.

## Erste Spalte — eine ENTSCHEIDUNG, keine Zeile Code

| | Sperre | was danach frei ist |
|---|---|---|
| **«B24»** `format`-Bitlagen | was eine Bitposition jenseits der Wortbreite bedeutet, und wie sie mit `endian` zusammenwirkt | **ein Netzwerkstack** — alles Übrige steht (`count NCONN`, Pool, Prüfsumme ≤ MTU, `retry bounded`, `forever per_pass`) |
| **`atomic` als Slotfeld** | ein atomares RMW ist seine eigene Wechselseitigkeit; heute ist `atomic` ein Item | **die Nachbildung hört auf, strenger zu sein als das Vorbild** (gemessen an K2-F2) |
| **`f64<RNE>`** | Rundungsmodus im Typ, vierte Instanz eines vorhandenen Musters | `F003` wird erreichbar — heute ist es unerreichbar, weil kein anderer Modus schreibbar ist |

## Zweite Spalte — die Grammatik erlaubt es, kein Pass hält es nach

**Das ist die gefährlichste Klasse, weil sie nicht schweigt, sondern VERSPRICHT.**
`pruefe-klauseln.py` zählt sie: **16 ZUSAGE von 49 gebuchten Klauseln.** Die schärfsten:

| | was heute durchgeht |
|---|---|
| **`ensures`** | ~~der Tippfehler fällt nicht~~ — **das war beim Aufschreiben dieser Tabelle schon falsch**, siehe unten. Offen ist die EINLÖSUNG, nicht die Wohlgeformtheit |
| **parametrische `costs`** | `costs <= 0 * n ops` an einem Rumpf, der 1 op kostet — **3 Items, 0 Fehler, 0 Hinweise** |
| **`mut`** | eine Zuweisung an ein unveränderliches Band fällt bei keinem Pass — ein Verbot ohne Biss |
| **`versatz`** | dass zwei `reg` einander nicht überlappen, ist der **Hauptsatz** von `Device_Konstruktor.thy` — und kein Pass rechnet ihn nach |
| **`abstieg`** | an ihm hängt die Terminierung eines `traverse`; `schleifen.rs` geht in den Rumpf und liest ihn nicht |
| **die Gnadenfrist** | `rcu … reclaims` ohne benannte Annahme geht durch — dieselbe Regel wie `S003`, an einem anderen Konstrukt |

Dazu **acht Prämissen ohne Erzeuger** (Zahn 3): Beweise, die auf etwas ruhen, das kein Pass
herstellt.

## Dritte Spalte — Bauarbeit, benannt

`observes` senkt nicht ab · `accumulates` kann nicht absenken (**Zellenzahl und aktueller Kern
fehlen beide als Ausdruck**) · `entry` existiert nicht · `const fn` · Generizität · `?` ·
variable Längen in `format` · der Verbundliteral · die Rückgabebindung.

## Vierte Spalte — die Klasse, die sich auch unter „alles verifiziert" nicht auflöst

**48 fremde Rümpfe im Korpus, NULL sprechen ihre Pflicht aus.** Eine Sperre schuldet
gegenseitigen Ausschluss, Fortschritt und die Rangordnung — *keine Zeile sagt das heute.*
`ensures` an einer rumpflosen Deklaration ist seit jeher grammatisch (geprüft, 0 Fehler), und
**kein Pass liest es.** Daneben die **Bibliotheks-ABI**: Gabbros ganze Zusage ist eine Aussage
über **eine** Übersetzungseinheit.

> **Die zweite und die vierte Spalte sind dieselbe Sache von zwei Seiten** — einmal verspricht
> der eigene Code etwas, das niemand hält, einmal verlässt sich der eigene Code auf etwas, das
> niemand ausspricht. *Und `ensures` steht in beiden.* **Deshalb ist es der nächste Posten:**
> nicht weil es das größte ist, sondern weil es zwei Spalten zugleich berührt.

## Die Reihenfolge, und die Begründung ist die Kante

1. **`pruefe-widerruf.py`** — der Wächter oben. *Eine Datei, die an fünf Stellen das Gegenteil
   des Gebauten sagt, ist teurer als keine.*
2. ~~**`ensures` — die Grundnamen auflösen.**~~ **Beim Messen erledigt vorgefunden**, und
   zwar noch in derselben Stunde, in der Punkt 1 gebaut wurde. `M109`/`M110`/`M111` stehen
   seit dem 2026-08-18 in `m1::ensures_pruefen`; der Tippfehler fällt an einem `impl fn` wie
   an einem rumpflosen `extern fn`. **Was bleibt, ist zweigeteilt:** die zwei Namensarten,
   die `sammle_namen_pred` nicht kennt (**Quantorbinder** und `Self`) — klein —, und die
   **Einlösung durch den Rumpf** — Beweisersache und die eigentliche Hälfte.

<!-- widerruf:aus -->
   > **Und dieser Punkt ist der beste Beleg für Punkt 1, den es geben konnte.** Die Zeile
   > *„kein Pass liest `ensures`"* stand am 2026-08-19 an **sechs** Stellen in vier Dateien —
   > in `MESSUNGEN.md` zweimal, in `TODO.md`, in einem Beispielkommentar **und in dieser
   > Datei, sechzig Zeilen über sich selbst geschrieben.** *Der Wächter hat seinen eigenen
   > Autor gefangen, keine zwanzig Minuten nachdem er entstand.*
<!-- widerruf:an -->

3. **«B24»** — die Entscheidung, hinter der ein Netzwerkstack liegt. *Sie rückt damit auf
   Platz zwei nach.*

---

# «H2» — die zwei letzten handbewiesenen Klempnereipflichten

> **Stand 2026-08-19:** `H = 17` (10 verankert + 7 Absenkungen). **Acht der zehn verankerten
> sind Notationslücken** — die Sprache kann es nicht *sagen* (`«B23»`, `«B9»`, `«B18»`,
> `«B27»`, …). **Zwei sind echte Handarbeit**, und nur um die geht es hier.
>
> *Die verbleibende Klempnerei ist überwiegend ein Notationsproblem, kein Beweisproblem — und
> genau deshalb ist diese Liste kurz.*

## H2.1 — Der Traversierungszähler erbt die Schranke seiner Domäne

### Die zwei Fundstellen, und sie haben dieselbe Form

```gabbro
-- FRAGMENTE.md:1110                         beispiele/19-traversierung.gab:53
let mut i : u64 in 0 .. STACK_MAX = 0;       let mut n : u32 in 0 .. NSLOTS = 0;
traverse w of s over elems of s.worte …      traverse i over slots of w by unvisited …
{                                            {
    narrow i to 0 .. 65535 else { … }            narrow n to 0 ..< NSLOTS else { return n; }
    i += 1;                                      n += 1;
}                                            }
```

**Gemessen: zwei Stellen im ganzen Korpus** — 21 Traversierungen, davon zwei mit einem Zähler
im Rumpf. *Eine Regel für zwei Stellen ist wenig; sie schließt aber die letzte handbewiesene
Bereichspflicht, und das ist der Punkt.*

### Was die Regel sagt

**Ein Zähler, der in einer beschränkten Traversierung höchstens einmal je Durchgang wächst,
ist durch die Domänenschranke gebunden.**

```
n vor der Schleife auf c gesetzt (Konstante)
im Rumpf NUR `n += k`, k > 0 konstant, Summe je Pfad <= K
Domänenschranke B (kosten::domaenenschranke -- gibt es bereits)
--------------------------------------------------------------
an jeder Zuwachsstelle:   n <= c + (B − 1) · K
nach der Schleife:        n <= c + B · K
```

Die Zahl `B − 1` an der Zuwachsstelle ist die schärfere und die richtige: *vor dem k-ten
Zuwachs sind höchstens k−1 geschehen.* **Genau sie macht die beiden `narrow` überflüssig** —
`n ∈ [0, NSLOTS−1]` vor `n += 1`, also `n+1 ∈ [1, NSLOTS]`, und das ist der deklarierte
Bereich.

### Und es ist eine AUSNAHME von einer aufgeschriebenen Regel

[`SPRACHE.md`](SPRACHE.md):657 sagt: **„Loops carry no facts inward."** Diese Regel wäre die
erste Ausnahme, und sie darf nicht stillschweigend danebengestellt werden.

> **Die Rechtfertigung, und sie ist der Unterschied zwischen Ausnahme und Loch:** die Tatsache
> wird nicht von *außen* hereingetragen. Sie wird von der Schleife **selbst erzeugt** — aus
> ihrer Domänenschranke und der Form ihres Rumpfes. *Was verboten bleibt, ist unverändert: ein
> Fakt über einen Platz, der vor der Schleife galt, gilt drinnen nicht weiter.*
>
> Die Zeile in `SPRACHE.md` bekommt darum einen Zusatz, **bevor** die Regel gebaut wird:
> *keine Tatsache von außen; eine aus der Schleifenform selbst.*

### Die Bedingungen, und jede ist eine Absage, wenn sie fehlt

| | |
|---|---|
| 1 | `n` ist eine **lokale** Skalarbindung, vor der Traversierung mit einer Konstante gesetzt |
| 2 | im Rumpf ist `n` **ausschließlich** Ziel von `n += k`, `k` konstant `> 0` |
| 3 | die Domäne hat eine berechenbare Schranke (`kosten::domaenenschranke`) |
| 4 | die Traversierung liegt **nicht** in einer weiteren Schleife — sonst multipliziert sich `B`, und der Pass schweigt (W10) |
| 5 | kein `n` in einer `spec`-Position, keine Adresse darauf — *Gabbro hat kein Adress-von auf Lokalen, die Bedingung ist geschenkt und steht trotzdem da* |

**Fällt eine, gilt die Regel nicht — und der Pass sagt nichts, statt zu raten.**

### Der Bau

1. **Zuerst der Zusatz in `SPRACHE.md`:** die Ausnahme wird aufgeschrieben, bevor sie existiert
   (R7).
2. `m1.rs`: beim Betreten eines `traverse` den Rumpf **einmal vorab lesen** (die
   Zuwachsform), dann die Tatsache in die `Lage` legen.
3. Die Domänenschranke kommt aus `kosten::domaenenschranke` — **sie existiert und wird
   wiederverwendet, nicht nachgebaut.** *Zwei Stellen, dieselbe Rechnung, wäre genau der
   Einwand, den dieser Ordner dreimal gegen sich selbst erhoben hat.*
4. **Zwei Giftproben:** ein Zähler, der zweimal je Durchgang wächst (Bedingung 2 fällt); eine
   verschachtelte Traversierung (Bedingung 4 fällt). *Beide müssen weiter `M101` bekommen.*
5. **Die Gegenprobe ist die eigentliche Messung:** beide `narrow` werden entfernt, und die
   zwei Dateien müssen mit **0 Fehlern** durchgehen. Bleibt eine rot, ist die Regel zu schwach
   und die Zeile bleibt stehen.

### Das Tor

```
H2.1 erreicht:   die zwei `narrow` sind FORT, beide Dateien gruen,
                 zwei Giftproben beissen, `H` faellt von 17 auf 16
```

---

## H2.2 — `(g − f)` unterläuft nicht, und die Fundstelle ist nicht, was sie zu sein schien

### Was dasteht

```gabbro
let g = groesse_gemessen()  else (e1) { return false; }
let f = frei_min_gemessen() else (e2) { return false; }
if f < g / MIND_RESERVE_NENNER { return false; }
return (g - f) + irq.tiefe_max + g / MIND_RESERVE_NENNER <= g;
```

`PFLICHTEN.md` notiert: *„`f < g / N` gibt `f < g` nur über die Division; die V-Regeln rechnen
nicht."*

### Und die Notiz beschreibt den falschen Zweig

**Nachgerechnet 2026-08-19.** Der Vergleich `f < g / N` steht in einem `if`, das
**zurückkehrt**. Auf dem Weg, der die Subtraktion erreicht, gilt das **Gegenteil**:
`f >= g / N`. Das ist eine **untere** Schranke für `f` — und `g − f` braucht eine **obere**.

> **Die Pflicht ist damit nicht durch eine schärfere V-Regel zu schließen.** Division durch
> eine positive Konstante zu monotonisieren (`g/N <= g`) hilft am *genommenen* Zweig und nicht
> an dem, der weiterläuft. *Der Befund vom 2026-08-15 hat die Richtung verwechselt, und das ist
> hier zum ersten Mal nachgerechnet.*

### Drei Wege, und sie sind nicht gleich viel wert

| | Weg | Preis |
|---|---|---|
| **(a)** | **Die Formulierung ändern.** `(g−f) + irq + g/N <= g` ist unter `f <= g` äquivalent zu **`irq.tiefe_max + g / MIND_RESERVE_NENNER <= f`** — *keine Subtraktion, keine Pflicht* | eine Zeile; **aber `FRAGMENTE.md` trägt einen Einfriersatz**, und die Nachbildung zu ändern, um eine Messung zu verbessern, ist die Bewegung, gegen die Falle 80 steht |
| **(b)** | **Die Weltzustandshälfte von Punkt 4.** `frei_min_gemessen` spricht seine Pflicht aus: *das freie Minimum übersteigt die Größe nie* | die Hälfte, die heute nicht gebaut ist — und sie kollidiert mit U4/U5 |
| **(c)** | **Eine Prüfung hinschreiben.** `if f > g { return false; }` | M1-begründet, also W6-konform — **aber es ist genau die Handklempnerei, die hier verschwinden soll** |

### Der empfohlene Weg ist (a), und die Begründung ist unbequem

**Die Pflicht ist ein Artefakt der Schreibweise, nicht der Sprache.** Dieselbe Aussage ohne
Subtraktion hat keine Unterlaufpflicht — und **das ist ein Befund über die Nachbildung, nicht
über Gabbro.**

> *Dieselbe Klasse wie `revoke` (200 zugesagt, 16 452 480 gerechnet) und A4 (4 096 gegen
> 831 488): **ein Mensch hat den typischen Fall geschrieben statt die Schranke.** Zweimal fing
> es der Pass; hier ist es die Formulierung selbst.*

**Und der Einfriersatz wird nicht gebrochen, sondern beachtet:** die Zeile bleibt stehen. Was
danebentritt, ist eine **zweite Fassung mit Datum und Grund** — dieselbe Form, die der Ordner
für Widerrufe benutzt. *Die Messung von 2026-08-14 bleibt lesbar; sie hört nur auf, als
Gabbro-Pflicht gezählt zu werden.*

**Was (b) trotzdem wert bleibt:** es ist der Weg, der die Pflicht *als Pflicht* schließt statt
sie wegzuschreiben. Er bleibt im TODO — **aber nicht als Bedingung für H2**, sonst hängt eine
kleine Pflicht an einer großen Baustelle.

### Das Tor

```
H2.2 erreicht:   die zweite Fassung steht mit Datum und Grund daneben,
                 die Zeile ist als Gabbro-Pflicht abgebucht,
                 `H` faellt von 16 auf 15
```

---

## Was danach gilt — und was ausdrücklich NICHT

**Erreicht:**

```
H = 15    -- 8 verankert (ALLE Notationsluecken) + 7 Absenkungen
N_ritus = 0  -- keine `narrow`-Zeile mehr, deren else-Zweig nicht genommen werden kann
```

**Und dann ist die handbewiesene Klempnerei über den zehn Fragmenten NULL.** Das ist ein Boden,
und er ist echt: die zehn sind nach ihrer *Schwierigkeit* gewählt, nicht nach ihrer
Bequemlichkeit.

> **Aber es ist der Boden der MESSUNG, nicht der Boden der Sprache**, und der Unterschied hat
> drei Namen:
>
> 1. **Die acht Notationslücken bleiben.** Sie sind keine Handarbeit — sie sind Stellen, an
>    denen der Mensch etwas **anderes** schreibt, weil er das Richtige nicht schreiben kann.
>    *Null Handbeweise heißt nicht, dass alles ausdrückbar ist.*
> 2. **Der zweite Korpus hat gar keine `H`-Messung.** Fünf Linux-Fragmente stehen daneben, und
>    über ihnen ist nichts gezählt. **`H = 0` über zehn selbstgewählten Fragmenten ist Falle 80
>    in Reinform**, solange die Zahl nicht über einem Korpus steht, den beim Bauen niemand
>    angesehen hat.
> 3. **Die 13 ZUSAGE-Klauseln bleiben.** Was die Grammatik zu versprechen erlaubt und niemand
>    nachhält, ist Klempnerei, die der Nutzer aufschreibt und **allein trägt** — sie taucht in
>    `H` nicht auf, weil `H` die Fragmente misst und nicht die Sprache.

**Die ehrliche Überschrift für das Ergebnis lautet deshalb nicht *„am Boden"*, sondern:
*über diesen zehn Fragmenten beweist kein Mensch mehr Klempnerei von Hand.*** Alles Weitere ist
der zweite Korpus.

---

# «NL» — der Weg, an dessen Ende der Nutzer nur noch seine eigene Logik beweist

> **Das ist Punkt 1 dieses Ordners, ab 2026-08-19.** Alles Übrige — der zweite Korpus, die
> Bibliotheks-ABI, `entrust`, die Notationslücken — steht dahinter, weil es die These nicht
> berührt. *Die These lautet: Gabbro beweist alles außer funktionaler Korrektheit. Solange ein
> Nutzer Klempnerei von Hand trägt, ist sie unbelegt.*

## Wo wir stehen, gemessen und nicht behauptet

```
H = 12        ueber den zehn Fragmenten kein Handbeweis mehr  (abgelesen, s. u.)
```

**Und `H` beantwortet die Frage nicht.** Es misst die *Fragmente*, nicht die *Sprache*. Was der
Nutzer weiter trägt — **jede Zeile am 2026-08-20 gegen ihren Befehl nachgerechnet, und drei
von fünf standen falsch da**. **Am selben Tag kam eine sechste dazu, die vorher NIRGENDS
stand** — und das ist die schlechtere Sorte Abweichung: eine falsche Zahl widerspricht sich
irgendwann, eine fehlende nie.

| | Zahl | Befehl | was es heißt |
|---|---:|---|---|
| **Erhaltungspflichten** | **3** | `gabbro pflichten` | `maintains I` ist auf Wohlgeformtheit geprüft; dass der Rumpf sie **einlöst**, prüft niemand |
| **ZUSAGE ohne Leser** | **0** | `./instrumente/pruefe-klauseln.py` | *stand als 13.* **Das ist das Tor von «NL» selbst, und es ist erreicht** — die Zahl fiel auf null, und die Tafel schrieb es nicht mit |
| **Fremdpflichten** | **10** | `gabbro pflichten` | *stand als 8.* Annahmen über Rümpfe, die Gabbro nie sieht — **die Zahl ist GESTIEGEN**, mit dem Korpus |
| **Vorbedingungen am Rufort** | **12** | `gabbro pflichten` | *neu am 2026-08-20, und sie stand vorher NIRGENDS.* `M115` weist ab, wo der Bereich des Arguments die Bedingung ausschliesst, und **schweigt sonst** — das ist der Preis dieses Schweigens, je Rufstelle gezählt |
| **Prämissen ohne Pass** | **9** | `gabbro schablonen` | *stand als 7.* Ein Beweis, den nichts herstellt |
| **Absenkungspflichten** | **7** | `zaehle-pflichten.py --haengend` | in `H` enthalten, nicht in den Fragmenten |

> **Drei von fünf, und in beide Richtungen** — eine gefallen, eine gestiegen, eine
> fortgeschrieben. *Eine Buchführung, die in beide Richtungen abweicht, veraltet; sie lügt
> nicht.* Alle sechs stehen seit dem 2026-08-20 in `./instrumente/pruefe-zahlen.py` und werden bei jedem
> Lauf neu abgeleitet. **`H = 15` im Kasten darüber war die vierte.**
>
> **Und die sechste Zeile ist die einzige, die nicht abwich, sondern fehlte.** Die
> Vorbedingung am Rufort war weder falsch gebucht noch veraltet — sie stand in keinem
> Register, weil `gabbro pflichten` Pflichten zählte, die eine DEKLARATION erzeugt, und
> keine, die ein RUF erbt. *Ein Preis, den kein Werkzeug nennt, sieht aus wie null* —
> dieselbe Richtung wie eine ungelesene Klausel, nur eine Ebene höher.

## Das Ziel, in prüfbarer Form

**„Nur noch eigene Logik" heißt:** jede Pflicht, die `gabbro pflichten` druckt, ist eine
**Wertaussage** — keine Erhaltung, keine stille Unterstellung —, und keine Klausel der Grammatik
steht ohne Leser da.

```
NL erreicht:
  ./instrumente/pruefe-klauseln.py        ZUSAGE = 0
  gabbro pflichten            Erhaltung = 0        (erzeugt statt bewiesen)
                              fremd nur mit AUSGESPROCHENER Pflicht
  gabbro schablonen           Praemissen ohne Pass = 0
```

**Und die Gegenrichtung gehört ins Tor, sonst misst es sich selbst grün:** eine Zusage darf die
Liste **nur verlassen, indem ein Pass sie liest oder ihr Konstrukt fällt** — nicht durch
Umbuchung. *Das ist Zahn 2 der Klauselratsche, und sie klemmt bereits in beide Richtungen.*

---

## NL.1 — `ops` bekommt eine Wortmenge *(die größte Spalte: K = 28 von 73)*

`table.ops.erhaltung` ist bewiesen, was die Mathematik angeht
(`beweise/Table_Ops_Erhaltung.thy`), und **`entworfen`, was die Auslieferung angeht: es gibt
keinen Erzeuger.** Der Grund steht seit dem 2026-08-19 gemessen da:

```
opdecl = "ops" identlist ";"      -- beliebige Bezeichner, null Korpusstellen
```

**Aus einem Namen fällt keine Wirkung.** Zwei Auswege, und sie sind nicht gleich viel wert:

| | |
|---|---|
| **(a)** eine **geschlossene Wortmenge** mit je definierter Wirkung — wie `merge add\|max\|min` | der Erzeuger kann emittieren, S5 fällt, K wird getragen |
| **(b)** der Nutzer schreibt die Wirkung, der Erzeuger prüft sie | **dann ist es keine ERZEUGTE Mutation mehr, und Schnitt (c) fällt** |

> **(b) ist kein Ausweg, sondern die Aufgabe des Ziels.** Der ganze Ertrag von Schnitt (c) ist,
> dass der Beweis *einmal je Operation im Erzeuger* fällt statt je Aufrufstelle. Schreibt der
> Nutzer den Rumpf, schreibt er auch den Beweis.

**Diese Entscheidung gehört dem Ordner und nicht mir** — welche Operationen die Wortmenge führt,
ist eine Messung am zweiten Korpus (*welche braucht ein echter Kernel?*) und danach ein Urteil.
*Der erste Korpus hat null `ops`-Stellen und kann sie nicht liefern.*

---

## NL.2 — die dreizehn Zusagen bekommen Leser oder fallen

**Nach Biss geordnet, und die Reihenfolge ist die Bauarbeit:**

| | Zusage | was heute durchgeht |
|---|---|---|
| 1 | **`veraenderlich`** (`mut`) | `let x = 1; x = 2;` — **0 Fehler.** Ein Verbot ohne Biss, und es ist eine Sicherheitslücke, keine Buchhaltung |
| 2 | **`touches`** | die Wirkungsmenge eines `traverse`, nie gegen den Rumpf gehalten — dieselbe Maschinerie wie `E010` |
| 3 | **`abstieg`** | **an ihm hängt die Terminierung**; `schleifen.rs` geht in den Rumpf und liest ihn nicht |
| 4 | **`ghost`** | ein Geisttyp darf im erzeugten C nicht vorkommen — ein Verbot, das kein Pass durchsetzt |
| 5 | **`pro_kern`** | `per cpu N` gegen `NCORES` |
| 6 | **`offset_into`** | die Schranke wird nicht geprüft |
| 7 | **`obermenge`** · **`bedingung`** · **`embeds`** · **`mirrors`** · **`verlaesst`** · **`gates`** · **`counterprobe`** | der Rest, je mit eigener Fundstelle |

**Jede einzeln, jede mit Giftprobe, jede mit Korpusmessung vorher.** *Eine Regel, die den
eigenen Korpus zerlegt, ist ein Befund und keine Regel.*

---

## NL.3 — der fremde Rumpf spricht seine Pflicht, und der Rufer trägt sie

Gebaut (Punkt 4, 2026-08-19): die numerische Nachbedingung (`aus_ensures`), die relationale
(`beziehung_aus_ensures`), die nachweislich falsche Vorbedingung (`M115`).

**Was fehlt, ist die häufigere Form: `ensures` über WELTZUSTAND.** `ensures mmu_an_zahl == 1`
steht siebenmal in `beispiele/22`, und keine Zeile trägt.

> **Sie kollidiert mit U4/U5** — *ein Aufruf tötet jeden nichtlokalen Fakt*, eine Regel mit
> eigener Mutation. **Die Wiederherstellung aus `ensures` wäre die erste Ausnahme davon**, und
> sie gehört gemessen, bevor sie gebaut wird — genau wie «H2.1» die Ausnahme von
> `SPRACHE.md`:657 vorher aufgeschrieben hat.

Dazu die zweite Hälfte: **28 fremde Deklarationen, eine spricht.** Solange sie schweigen,
unterstellt der Rufer.

---

## NL.4 und NL.5 — die Prämissen und die Absenkungen

**Sieben Prämissen ohne Pass**, und seit dem 2026-08-19 sagt jede, *womit* man sie füllt. **Drei
der sieben brauchen keine Prüfarbeit, sondern eine Sprachform** — eine Wortmenge (NL.1), eine
Grammatikzeile, die Ausführungskontexte. *Sie fallen mit NL.1 und K11.2.2, nicht einzeln.*

**Sieben Absenkungspflichten** sind der Rest von `H`: Formen, für die der Erzeuger sich weigert.
Sie kosten keinen Beweis, aber sie halten die Zusage *„dieses C erhält dieses Gabbro"* an einer
Datei fest, die es gar nicht erst erzeugt.

---

## Was «NL» ausdrücklich NICHT liefert

1. **Die acht Notationslücken bleiben.** Sie sind keine Handarbeit — sie sind Stellen, an denen
   der Nutzer etwas **anderes** schreibt, weil er das Richtige nicht schreiben kann. *Null
   Handbeweise heißt nicht, dass alles ausdrückbar ist.*
2. **Der zweite Korpus bleibt die Bedingung über allem.** `ZUSAGE = 0` über einer selbst
   geschriebenen Sprache ist Falle 80, solange kein Korpus daneben steht, den beim Bauen
   niemand angesehen hat.
3. **Die funktionale Korrektheit fällt nicht.** Sie ist der Zweck des Ziels, nicht sein Opfer:
   *am Ende von «NL» beweist der Nutzer seine Logik — und nur die.*

---

# «K5» — vollständige Abdeckung der fünf Klempnereiklassen

> **Was „vollständig" hier heißt, und es ist eine strenge Fassung:** *jede Verletzung der
> Klasse ist ein Übersetzungsfehler, und was nicht fällt, ist **benannt** — als Axiom, als
> Entscheidung oder als unentscheidbarer dritter Zustand.* **Ein stiller Durchlass zählt
> gegen die Abdeckung, ein `E009` nicht.**

Der Anlass war eine Rezension, die fünf Klassen als *nicht getragen* führte. Nach elf
Schliessungen am 2026-08-19 fielen vier von fünf an allen Proben. **Dieser Plan handelt vom
Rest — und der Rest ist gemessen, nicht erinnert.**

## Die Vorabmessung, 24 + 7 Programme

Die Batterie steht in [`MESSUNGEN.md`](MESSUNGEN.md) (dritter Durchgang). Sieben weitere
Proben suchten gezielt nach dem, was die Batterie nicht abfragte:

| Probe | Ergebnis | Urteil |
|---|---|---|
| Nutzlast wird **nach** dem release-Speichern geschrieben | **STILL** | **Loch** |
| Nutzlast wird **vor** dem acquire-Laden gelesen | **STILL** | **Loch** |
| Rang nicht konstant auswertbar | **STILL** | **Loch** |
| Sperrzyklus über zwei getrennte Ketten | `H012` | trägt |
| Ruf über einen Funktionszeiger | `E009` `K003` | **benannt** — kein Loch |
| Wechselrekursion | `E009` `K001` | **benannt** — kein Loch |
| `masks IRQ` statt einer Sperre | `H013` | trägt, **zu grob** |

> **Die drei Löcher sind alle von derselben Bauart:** eine Zusage, deren *Reihenfolge* oder
> *Vorbedingung* niemand nachrechnet. Das ist nicht die Bauart der elf Befunde vom Vormittag
> (dort fehlte die Weiterreichung eines fertigen Werkzeugs) — **hier fehlt die Regel selbst.**

---

## K5.1 — Publikation: die Reihenfolge *innerhalb* der Funktion *(zuerst, weil still)*

Die Paarung prüft seit dem 2026-08-19 `(Atomic, Nutzlast)` über das ganze Programm. Was sie
**nicht** prüft, ist die Stelle, an der die Ordnung entsteht:

```gabbro
F = true publishes { n };   -- das release-Speichern
n = v;                      -- ... und die Nutzlast DANACH
```

**Ein release-Speichern veröffentlicht, was vor ihm geschah.** Was danach geschrieben wird,
sieht der Leser nicht — die Zeile `publishes { n }` ist dann eine Zusage über eine Schreibung,
die zum Zeitpunkt der Zusage nicht existiert. *Spiegelbildlich auf der Leseseite:* ein `let
vorher = n;` **vor** dem `awaits` liest an der Erwerbung vorbei.

* **Was gebaut wird.** Zwei Regeln über demselben Rumpf, beide rein syntaktisch und beide
  ohne Speichermodell:
  * `V006` — jede Stelle der Nutzlast eines `publishes` wird im selben Rumpf **vor** dem
    Speichern geschrieben. *Wird sie gar nicht geschrieben, ist das kein Fehler: sie kann von
    einem Gerufenen kommen — dann muss der Ruf davor stehen.*
  * `V007` — jede Stelle der Nutzlast eines `awaits` wird im selben Rumpf **nach** dem Laden
    gelesen. Ein Lesen davor fällt.
* **Warum das keine Aussage über das Speichermodell ist.** A10 (`release_stellt_sichtbarkeit_her`)
  sagt, *dass* release/acquire die Sichtbarkeit herstellen. Diese beiden Regeln sagen, dass
  das Programm die Form hat, für die A10 überhaupt gilt. **Das Axiom trägt eine Voraussetzung,
  und niemand prüfte, ob sie erfüllt ist.**
* **Tor:** beide Proben fallen, beide Gegenproben (richtige Reihenfolge) schweigen, Korpus 0.
* **Preis:** klein. Der Rumpf wird ohnehin in Reihenfolge durchlaufen.

## K5.2 — Sperre: ein Rang, den niemand ausrechnen kann, ist keine Ordnung

`H006` und `H012` überspringen beide eine Sperre, deren `rank` nicht konstant auswertbar ist
(`rang: Option<i128>`, und beide `continue` bei `None`). Gemessen: `lock LA … rank woher()`
neben `lock LB … rank 1`, verschachtelt in der falschen Richtung — **null Fehler.**

* **Was gebaut wird.** `H014`: eine `lock`-Deklaration, deren `rank` nicht feststeht, fällt an
  der Deklaration. **Nicht am Zugriff** — dort wäre es eine Meldung je Fundstelle für einen
  Fehler, der einmal gemacht wurde.
* **Warum ein Fehler und kein Hinweis.** Der Rang *ist* die Ordnung; ohne ihn gibt es keine.
  Eine Sperre ohne auswertbaren Rang ist dieselbe Klasse wie `bounded` ohne Zahl. *Die
  Grammatik verlangt `rank` schon heute — was fehlt, ist, dass er etwas bedeutet.*
* **Tor:** die Probe fällt, `rank 0`/`rank NKERNE` schweigen, Korpus 0.

## K5.3 — Rennen: die Kontexte schliessen einander aus, und `H013` weiss es nicht

`H013` nimmt die grobe Antwort — *jeder Eintritt ist ein Kontext* — und die ist in die sichere
Richtung grob. **Zu grob an drei Stellen**, und alle drei stehen schon in der Grammatik:

| Form | was sie sagt | was `H013` daraus macht |
|---|---|---|
| `masks IRQ` | schliesst den Interruptkontext aus | nichts |
| `per cpu` | gehört genau einem Kern | nichts |
| `nested never` | der Eintritt unterbricht sich nicht selbst | nichts |

* **Was gebaut wird.** Eine **Kontextmatrix**: je Paar von Kontexten steht da, ob sie
  gleichzeitig laufen können. `masks IRQ` streicht die Interrupteinträge, `nested never`
  streicht die Diagonale, `per cpu` streicht alles ausser dem eigenen Kern. `H013` fragt
  danach statt „irgendein Eintritt".
* **Und die Zeile, die dabei ehrlich bleiben muss:** *auf mehr als einem Kern schliesst
  `masks IRQ` gar nichts aus.* Die Matrix braucht darum eine **Annahme mit Namen** —
  `ein_kern` bzw. `mehrere_kerne` — und die gehört in die Axiomschicht, nicht in den Pass.
* **Tor:** je Platz wird die Kontextmenge gedruckt (`gabbro kontexte`), und **die Zahl der
  berührten Plätze steht daneben** — sonst sieht ein leerer Lauf aus wie ein bestandener (W1).
* **Vorbedingung, unverändert:** `H013` hat am Korpus **null Biss**, weil alle vier
  Kontextwurzeln `extern fn` sind. **K5.3 ist ohne den zweiten Korpus nicht messbar** — das
  ist dieselbe Bedingung wie über K11.2.2, und sie ist die einzige in diesem Plan, die nicht
  an Bauarbeit hängt.

## K5.4 — Termination: die Rekursion bekommt ein Mass

Heute nennt `K001` die Rekursion und `E009` die Unentscheidbarkeit — **das ist ehrlich und
nicht vollständig.** `costs` an einer rekursiven Funktion ist eine Annahme.

* **Was gebaut wird.** `decreases <expr>` an der Signatur, geprüft wie das Abstiegsmass einer
  `traverse` (`S005` prüft heute schon die *notwendige* Bedingung: das Mass muss sich bewegen
  können). Für den Zyklus im Aufrufgraphen: jede Kante muss das Mass echt verkleinern.
* **Was das NICHT liefert:** *dass* es fällt, bleibt Beweisersache (`consuming.ordnung`) —
  dieselbe Trennung wie bei `S005`. **Die Notation trägt, der Beweis bleibt beim Nutzer**, und
  genau das ist die Zielform.
* **Preis:** eine Grammatikzeile, ein Pass, eine Schablone. *Die einzige Spalte dieses Plans,
  die die Sprache verbreitert* — und darum die letzte.

## K5.5 — Rahmen: die Argumentabbildung, eine Ebene tiefer

Seit dem 2026-08-19 bildet der Graph Parameternamen auf Argumente ab — **über den Grundnamen,
und nur den.** `f(g(x))` und `f(a.b)` behalten den Namen des Gerufenen.

* **Was gebaut wird.** Die Abbildung nimmt den ganzen Ortsausdruck statt der Basis; ein
  Argument, das kein Ort ist, macht die Hülle an dieser Kante **unvollständig** statt sie
  stillschweigend grob zu lassen (`E009` statt eines geerbten Namens).
* **Warum das kleiner ist, als es klingt:** die heutige Grobheit ist *in die sichere Richtung*
  — sie sieht mehr Wirkungen als da sind. **Was fehlt, ist nicht Sicherheit, sondern
  Brauchbarkeit:** ein geerbter fremder Parametername steht in der Meldung und niemand findet
  ihn im eigenen Rumpf wieder.

---

## Die Reihenfolge, und die Begründung ist die Stille

```
K5.1  Publikation, Reihenfolge     zuerst -- zwei STILLE Loecher, klein zu bauen
K5.2  Rang ohne Wert               danach -- ein STILLES Loch, eine Zeile
K5.5  Argumentabbildung            danach -- kein Loch, aber jede Meldung wird lesbar
K5.3  Kontextmatrix                danach -- braucht eine Annahme mit Namen
K5.4  decreases                    zuletzt -- verbreitert als einzige die Sprache
```

**Zuerst fällt, was still ist.** Ein `E009` ist ein Eintrag; ein Schweigen ist eine falsche
Zusage — und die drei Löcher oben stehen heute in einer Datei, die *„0 Fehler"* meldet.

## Was «K5» ausdrücklich NICHT liefert

1. **A10 fällt nicht.** Dass `release`/`acquire` die Sichtbarkeit *herstellen*, ist eine
   Aussage über die Maschine. K5.1 prüft, ob die **Voraussetzung** des Axioms erfüllt ist —
   das ist die andere Hälfte und nicht dieselbe.
2. **`protects` bleibt eine Angabe.** Ob eine Sperre die *richtigen* Plätze nennt, kann kein
   Pass wissen; er kann nur nachhalten, dass die genannten eingehalten werden (`H007`, `H011`).
3. **Ohne den zweiten Korpus ist die Abdeckung von *Rennen* eine Zahl über Giftproben.**
   `H013` fällt heute an genau einer Datei, und die habe ich selbst geschrieben. *Das ist
   Falle 80, und es steht hier, damit es nicht später als Fund verkauft wird.*

---

# «Z» — Zwischenspeicher für Prüfen und Erzeugen

> **Die Regel, die diesen ganzen Block trägt:** *ein Zwischenspeicher ist ein stiller
> Fail-open.* Trifft der Schlüssel nicht, was die Antwort bestimmt, liefert er **„0 Fehler"
> für ein Programm, das fallen würde** — und das ist genau die Bewegung, gegen die dieser
> Ordner sonst schreibt. Ein Cache ohne Sprechprobe ist schlimmer als kein Cache.

## Die Messung zuerst, damit der Plan nicht geraten ist

Gemessen 2026-08-19, Release, ein Faden, synthetische Einheit mit **120 005 Zeilen**
(20 000 Funktionen; `crates/gabbro-cli/examples/umgebungsmass.rs`):

| Größe | Zeit |
|---|---:|
| Lesen (Lexer + Parser) | 183 ms |
| **Alle zwölf Pässe** | **672 ms** |
| davon: *eine* `Umgebung::sammle` | 20 ms |
| davon: *ein* Aufrufgraph | 42 ms |
| Ganzer Lauf `gabbro pruefe` | ~899 ms |

Der Durchsatz ist **linear** — 6 k / 30 k / 60 k / 120 k Zeilen ergeben 24 / 231 / 440 /
899 ms, also **~7,5 µs je Zeile, 133 000 Zeilen/s**. Caprock hat 75 294 Zeilen Rust; die
ganze Einheit läge damit bei **~570 ms**.

**Und jetzt der Befund, der die Reihenfolge dieses Plans bestimmt:**

```
14 Module rufen Umgebung::sammle   ->  18 Aufrufe je Lauf  ->  358 ms
 6 Module bauen den Aufrufgraphen  ->   6 Aufrufe je Lauf  ->  252 ms
                                                    zusammen  610 ms
```

**610 der 672 ms Passzeit sind der Neubau derselben zwei Datenstrukturen.** Die eigentliche
Passlogik kostet ~60 ms. *Ein Zwischenspeicher über einer Arbeit, die man auch weglassen
kann, ist die teurere Lösung* — deshalb steht «Z0» vor «Z1».

## Z0 — teilen, bevor gespeichert wird

Eine `Umgebung` und einen `Graph` je Übersetzungseinheit bauen und **allen Pässen
durchreichen**. Nichts wird gespeichert, nichts kann veralten, die Frage der
Schlüsselvollständigkeit stellt sich gar nicht.

* **Erwartete Wirkung:** 899 ms → **~290 ms**, Faktor 3. *Erwartet, nicht gemessen* — die
  Zahl gilt erst, wenn sie nach dem Umbau dasteht.
* **Der Preis:** `pruefe` bekommt eine Signatur mit zwei Argumenten mehr, und die Pässe
  hören auf, für sich allein aufrufbar zu sein. Das ist eine echte Einbusse: heute lässt
  sich jeder Pass einzeln fahren, und die Mutationsproben nutzen das.
* **Die Gegenprobe:** die Ausgabe muss über den ganzen Korpus **bitgleich** bleiben. Ein
  geteilter Zustand, der zwischen Pässen mitwandert, ist die klassische Stelle, an der ein
  Pass den nächsten beeinflusst.

## Z1 — der Zwischenspeicher je Übersetzungseinheit — **optionales Merkmal, später**

> **Entschieden 2026-08-19: Z1 wird ein `cargo`-Merkmal, standardmässig AUS.** Nicht weil er
> schwer wäre, sondern weil er eine Klasse eröffnet, die dieser Ordner sonst jagt — und weil
> die Zahl ihn heute nicht verlangt: Caprock prüft nach «Z0» in ~190 ms.
>
> ```toml
> [features]
> default = []
> speicher = []     # gabbro build --features speicher
> ```
>
> **Ein Merkmal, das aus ist, ist keine Vorstufe, sondern eine Wahl mit Adresse.** Wer es
> anschaltet, bekommt die Geschwindigkeit *und* das Risiko, und beides steht an derselben
> Zeile. Die Voreinstellung entscheidet, was ein *unbedarfter* Lauf tut — und der soll
> rechnen, nicht glauben.

### Woran man erkennt, dass die Zeit für Z1 gekommen ist

Drei Auslöser, und **jeder einzelne** genügt. *Sie stehen hier, damit sie nicht im Moment
des Wunsches erfunden werden* (R7):

1. **Ein Lauf über den gemeinten Korpus dauert > 3 s.** Das ist die Schwelle, ab der ein
   Mensch beim Tippen wartet, und sie ist gemessen worden, nicht gefühlt.
2. **Dateiübergreifende Übersetzungseinheiten sind da.** Dann rechnet ein Lauf über 100
   Dateien 100-mal dieselben Nachbarn durch, und der Gewinn wächst mit dem Quadrat.
3. **Der Prüfer läuft in einem Wächter, der bei jedem Commit fährt.** Dort zählt nicht die
   einzelne Sekunde, sondern die dreihundertste.

Bis dahin ist Z1 **geplant und nicht gebaut**, und das ist der Zustand, den «CARRY» meint:
*was ein Plan sagen kann, sagt er — und wo der Rest liegt, steht daneben, mit Namen.*

### Was ihn heute billig macht — und was das kostet, wenn es sich ändert

Gemessen: **eine Datei ist heute eine ganze Übersetzungseinheit.** `gabbro pruefe` und
`gabbro emit` schleifen über die Dateien und behandeln jede für sich; Module sind *in* der
Datei geschachtelt, es gibt kein Binden über Dateigrenzen. **Damit hat eine Einheit keine
Abhängigkeiten**, und der Schlüssel ist trivial vollständig.

> **Das ist der Satz, der zuerst falsch wird.** Sobald `use` über Dateigrenzen greift, ist
> der Inhalt einer Datei nicht mehr die ganze Eingabe, und ein Schlüssel, der nur sie
> hasht, liefert veraltete Antworten. *Dieser Absatz gehört in denselben Commit wie die
> erste dateiübergreifende Auflösung — nicht danach.*

### Der Schlüssel, vollständig

```
SHA-256( Quelltext der Einheit )
       + Bauzeichen des Prüfers      -- sonst antwortet ein NEUER Prüfer mit ALTEN Absagen
       + Name des Unterbefehls       -- `pruefe` und `emit` sind zwei Antworten
       + [später] die Hashes aller Einheiten, aus denen die Einheit liest
```

**Das Bauzeichen ist der Teil, den man vergisst.** Wer heute eine Regel schärft und morgen
den Korpus prüft, bekommt aus dem Speicher das Urteil von gestern — und der Korpus ist
grün, weil die neue Regel nie lief. Genau die Klasse, in der an diesem Ordner schon
`pruefe-luecken`, der Mutationskatalog und die MSRV standen: **eine Zahl, die niemand
nachhält.**

Mechanisch: `option_env!("GABBRO_BAU")` reicht nicht (nur gesetzt, wenn jemand daran denkt).
Tragfähig ist ein Hash über die eigenen Quellen, im `build.rs` gerechnet und als Konstante
eingebacken — *der Prüfer trägt sein eigenes Prüfsummenzeichen.*

### Was gespeichert wird

Die **Absagenliste** (Code, Stufe, Spanne, Text, Notizen) und der **erzeugte C-Text**. Beide
sind reine Funktionen der Eingabe: gemessen ist der Prüfer frei von Uhr und Dateisystem —
die einzige Umgebungsberührung im ganzen `gabbro-check` ist `GABBRO_ZEIT`, und die schreibt
nur auf `stderr`.

Und die Ausgabe hängt **nicht an `HashMap`-Reihenfolge**: 25 Läufe von `pruefe` über eine
Giftdatei, 25 von `emit` über ein Beispiel und 15 über `01-tabelle` ergaben je **einen**
SHA-256. *Rusts `HashMap` hat je Prozess einen anderen Startwert; wäre eine Ausgabe daran
gebunden, hätte diese Probe es gezeigt.*

### Wo er liegt

`.gabbro-cache/<zwei Hexziffern>/<Rest des Hashes>` im Arbeitsbaum, wie `ccache`. Kein
Netz, kein Dämon, kein Sperrprotokoll: das Schreiben geht über eine temporäre Datei und
`rename`, das ist auf jedem POSIX-Dateisystem atomar. Alt wird nichts — bei zwei Bytes je
Absage ist Aufräumen ein Problem, das dieser Ordner in Jahren nicht bekommt.

## Z2 — die C-Seite

Hier ist **nichts zu bauen**, und das ist eine gute Nachricht: `ccache` erledigt es, wenn
das erzeugte C sich nicht bewegt. Gemessen ist es das — kein Zeitstempel, kein absoluter
Pfad, kein Zufall im Kopf, und derselbe SHA-256 über 25 Läufe.

Was Gabbro dafür schuldet, ist eine **Zusage statt einer Beobachtung**: dass die Emission
reproduzierbar ist, muss ein Wächter halten, nicht mein Gedächtnis. `pruefe-emission.sh`
schreibt heute C und übersetzt es; ihm fehlt eine Zeile — *zweimal erzeugen und die Hashes
vergleichen.*

## Die Sprechprobe, ohne die der Speicher nicht geglaubt wird

Für **jeden** der drei Schritte, in beide Richtungen:

1. `--kein-speicher` fährt ohne Zwischenspeicher. Der Korpus muss **bitgleich** dieselbe
   Ausgabe liefern wie der Lauf mit — sonst ist der Speicher ein zweites Register.
2. **Die Gegenrichtung, und sie ist die eigentliche Probe:** eine Regel schärfen, ohne den
   Quelltext des Korpus anzufassen. Der Speicher **muss** verfehlen. Trifft er, ist das
   Bauzeichen nicht im Schlüssel — und der Wächter hat gerade den Fehler gefunden, für den
   es ihn gibt.
3. Ein Eintrag von Hand verfälscht → der Lauf muss fallen, nicht die verfälschte Antwort
   ausgeben. *Ein Speicher, der seinem Inhalt glaubt, ist ein Erzeuger fremder Urteile.*

## Die Reihenfolge, und warum sie so herum steht

| | Arbeit | erwarteter Gewinn | Risiko |
|---|---|---|---|
| **Z0** | Umgebung und Graph teilen | 899 → ~290 ms | keins: nichts wird gespeichert |
| **Z1** | Speicher je Einheit — **Merkmal, aus** | ~290 → ~2 ms bei Treffer | **stiller Fail-open** |
| **Z2** | `ccache` + Reproduzierbarkeitswächter | Sache von `cc` | keins |

**Z0 bringt den Faktor 3 ohne jedes Risiko, Z1 den Rest mit dem ganzen Risiko.** Wer Z1
zuerst baut, hat einen Speicher über einer Rechnung, die zu 85 % überflüssig ist — und
misst danach nie mehr, wie teuer sie eigentlich war.

## Die Abbruchbedingung — und sie hat schon gegriffen

**Wenn der ganze Caprock-Korpus nach Z0 unter einer Sekunde prüft, wird Z1 nicht
eingeschaltet.** Ein Zwischenspeicher, der eine Sekunde spart und eine Klasse stiller
Fehlurteile eröffnet, ist ein schlechtes Geschäft. *Die Zahl entscheidet, nicht der Wunsch
nach einem Cache* — und heute deutet sie auf **~190 ms für ganz Caprock nach Z0**.

Also: **Z0 wird gebaut, Z1 wird geschrieben und ausgeschaltet ausgeliefert.** Der Unterschied
zwischen „nicht gebaut" und „gebaut und aus" ist nicht Kosmetik — ein Merkmal, das nie
übersetzt wurde, verrottet lautlos, während eines, das im Bau steht und in der Sprechprobe
läuft, sich meldet, sobald es bricht. *Dieselbe Erfahrung wie mit dem Mutationskatalog: was
nicht mitgefahren wird, misst irgendwann nichts mehr.*

**Deshalb gehört zu Z1 von Anfang an ein Wächterlauf `--features speicher`**, der die drei
Sprechproben oben fährt. Ohne ihn ist das ausgeschaltete Merkmal genau der tote Anker, den
dieser Ordner am 2026-08-19 fünfundzwanzigmal aus dem Katalog gezogen hat.

---

# «C» — vollständige Absenkung nach C

> **Was „vollständig" hier heisst, und es ist dieselbe strenge Fassung wie bei «K5»:** *jede
> Form, die die Grammatik erlaubt, senkt ab — und was nicht absenkt, ist **benannt**: als
> Sprachentscheidung, als Axiomschicht oder als **gezogene Linie**.* **Ein `C001` ohne
> Adresse zählt gegen die Abdeckung, ein `C001` mit Begründung nicht.**

## Der Stand, gemessen am 2026-08-19

**17 von 33 Beispielen senken ab. Zwölf Übersetzungseinheiten gehen die ganze Kette** —
`.gab` → C → `cc -Werror` → **ausgeführt** → Ergebnis verglichen, dazu die Sprechprobe, dass
verfälschtes C fällt (`pruefe-emission.sh`). **46 Weigerungen, alle `C001`, keine stille.**

Und zwei Zusagen, die eine Absenkung erst brauchbar machen, sind gemessen statt geglaubt:
das erzeugte C ist über **25 Läufe bitgleich**, ohne Zeitstempel und ohne absoluten Pfad.

## Die 46, nach dem, was sie WIRKLICH blockiert

Die Klassen aus der Fehlerausgabe verdecken die Abhängigkeiten. Nach Ursache sortiert:

| Ursache | Weigerungen | Art |
|---|---:|---|
| **`option` hat keine Darstellung** | **≈ 13** | ENTSCHEIDUNG — und sie ist bewiesen |
| **`tagged type` als Wert** | **5** | Bauarbeit |
| sieben Item-Arten ohne Absenkung | 10 | Bauarbeit + Axiomschicht |
| drei Anweisungsarten | 5 | folgt aus `rcu` und `reason` |
| `descendants of` / `ancestors of` | 3 | ENTSCHEIDUNG — Grammatik |
| `accumulates` ohne `per cpu N` | 2 | ENTSCHEIDUNG |
| Kleinkram (`u64::max`, `[T; N]`-Static) | 3 | Bauarbeit |
| **gezogene Linien, kein Loch** | **3** | bleiben `C001` |

### Die drei, die Linien sind und bleiben

Sie zählen **nicht** gegen die Abdeckung, und sie stehen zuerst, damit niemand sie später
als Rest liest:

* `forever` mit `per_pass … ops` — die Schranke ist eine **Übersetzungszeit**-Aussage, also
  hat `on_exceeded` keinen Auslöser zur Laufzeit; die Klausel wegzulassen verwürfe sie
  still. *«B11»: es gibt dort auch keinen Ausgang.*
* Eine Bitlücke in einem `format` — *ein Format sagt, welche Bits EXISTIEREN.* Wer die Lücke
  will, nennt sie `reserved`; der Erzeuger zählt nicht mit.
* `table` ohne `count` — das Feld hätte keine Grösse. **Eine Zahl, die niemand nennt, wird
  nicht geraten.**

## C1 — `option`, und der Beweis liegt schon da

**Die grösste einzelne Ursache**, und die Entscheidung ist keine offene Frage: `beweise/`
trägt seit jeher **`Option_Sonderwert.thy`**. Die Absenkung ist ein **Sonderwert** im
Indexraum — `count` selbst, also der erste Index, den es nicht gibt —, und der Satz, dass
das injektiv ist, steht in Isabelle.

Die Theorie sagt es in vier Sätzen, und **einer davon ist die Preisklausel**:

| Satz | Aussage |
|---|---|
| `sonderwert_ausserhalb` | `N ∉ indextyp N` — der Sonderwert ist kein gültiger Index |
| `kodiere_injektiv` | die Kodierung ist auf dem gültigen Bereich **injektiv** |
| `sonderwert_kollidiert_bei_vollem_wort` | **bei vollem Wort KOLLIDIERT er** |
| `kodiere_wort_injektiv` | injektiv, sofern das Wort nicht voll ist |

> *Ein Beweis, der dasteht und den kein Erzeuger benutzt, ist genau die Hälfte, die «NL»
> beklagt.* Hier ist er die ganze Begründung, und die Arbeit ist die Verdrahtung — **samt
> der Bedingung, die der dritte Satz nennt: der Erzeuger muss sie prüfen, nicht annehmen.**

Was daran hängt: 3 Konstruktoren (`None`, `Some(i)`), 2 `static … = None`, 3 `match` über
`option index into T`, und die `let`-Bindungen, deren Typ heute unauflösbar ist, weil das
Feld ein `option` trägt. **Eine Entscheidung, ein Dutzend Weigerungen.**

* **Preis der Wahl:** `count` als Sonderwert kostet einen Index des Adressraums. Füllt
  `count N` das Wort genau aus (`N = 2^k`), **kollidiert der Sonderwert mit einem gültigen
  Index** — `sonderwert_kollidiert_bei_vollem_wort`. Der Erzeuger muss dann eine Breite
  weiter gehen, und **das ist eine Absage wert, keine stille Verbreiterung**: wer `count 256`
  auf `u8` schreibt, hat 256 Zellen und keinen Platz für „keine". *Die Alternative — ein
  Beiflag — kostet ein Byte je Zelle und bricht die Bitlage; deshalb der Sonderwert.*
* **Gegenprobe:** eine Giftprobe, in der `Some(count)` geschrieben wird, muss fallen. Sonst
  ist der Sonderwert ein gültiger Wert, und die Injektivität ist weg.

## C2 — `tagged type` als Wert: Marke plus Vereinigung

`ObjektArt`, `Nachricht`. Blockiert 2 Feldtypen, 1 Parametertyp, 2 `match`. Die Prüferseite
ist **fertig**: `D005` verlangt seit dem 2026-08-19 das erschöpfende `match` über `tagged`,
und ohne Sammelzweig. Was fehlt, ist die Absenkung nach `struct { tag; union { … } }`.

* **Was dabei zu entscheiden ist:** die Breite der Marke (kleinster Typ, der die Varianten
  fasst) und ob die Vereinigung **benannt** oder anonym ist. Beides ist Handwerk, keine
  Sprachfrage.
* **Was NICHT dabei entschieden wird:** ob C's `union` das Typrecht verletzt. Es tut es
  nicht, solange nur das zuletzt geschriebene Feld gelesen wird — und genau das erzwingt
  `D005` eine Ebene höher. *Der Erzeuger darf sich darauf berufen, weil ein Pass es hält.*

## C3 — die sieben Item-Arten, in der Reihenfolge ihrer Abhängigkeit

| | Item | was es braucht | zieht nach sich |
|---|---|---|---|
| a | `reason` | eine Fehlerwert-Darstellung (Marke + Nutzlast) | **`let … else (e) { … }`** (2 Anweisungen) |
| b | `rcu` | Zeigertausch + Gnadenfrist als **benannte Fremdform** | **`observes`** (1 Anweisung) |
| c | `group` | nichts zur Laufzeit — die Gruppe ist eine Beweisaussage | — |
| d | `walk` | die Schrittfunktion aus `levels`/`node`/`down` | — |
| e | `entry` | **Axiomschicht**: Vektor, Stapel, `iretq` | 3 Weigerungen |
| f | `boot` | dito, plus Multiboot-Kopf als `format` | — |
| g | `entrust` | dito, plus die Vertrauensfläche im Zeugnis | — |

**c ist der billigste Posten des ganzen Plans**: eine `group` erzeugt nichts. Sie *darf*
nichts erzeugen — sie ist die Verbindungsaussage über zwei Trägern, und was sie zur Laufzeit
kostet, ist null. **Eine Zeile, die heute `C001` sagt, muss morgen schweigend durchgehen.**

**e/f/g gehören zusammen und liegen NICHT in diesem Plan allein**: ein `entry` senkt in eine
IDT-Zeile ab, und dass eine IDT-Zeile tut, was sie tut, ist die **Axiomschicht** — dieselbe
Klasse wie `A10`. *Die Absenkung ist Handwerk, die Zusage darunter ist ein Axiom, und es
gehört gezählt, nicht versteckt.*

## C4 — `exchange`, beide Formen

`let alt = z.wert exchange update(v) { … }` und
`let g = BESITZER exchange f when old(BESITZER) == 0 returns erfolg`. Zwei Anweisungen im
Korpus, beide auf `atomic`. Absenkung: `atomic_exchange_explicit` bzw.
`atomic_compare_exchange_strong_explicit` mit **der deklarierten Ordnung** — und das ist die
Stelle, an der der Erzeuger schon einmal geschummelt hat: der Mutationskatalog führt
`veroeffentlichung-nimmt-die-vorgabeordnung` und `laden-nimmt-die-speicherordnung`, weil ein
`=` statt der Ordnung `seq_cst` bedeutet und *das erzeugte Programm dann etwas anderes sagt
als die Quelle.*

## C5 — die drei Entscheidungen, die keine Bauarbeit sind

1. **`descendants of` nennt seine KANTE nicht.** `CapSpace` trägt vier Kandidaten (`parent`,
   `first_child`, `next_sibling`, `prev_sibling`), und `chain(a, b) in` zeigt, dass die
   Grammatik eine Kante zu benennen **schon kann**. *Das ist eine Asymmetrie der Grammatik,
   kein fehlender Erzeugercode* — und ihre Auflösung ist eine Grammatikzeile, keine
   Erzeugerzeile.
2. **`accumulates` ohne `per cpu N`.** Die Absenkung ist eine Zelle je Kern; wie viele Kerne
   es gibt, steht nicht in der Deklaration. Entweder wird `per cpu` pflichtig, oder es gibt
   einen Vorgabewert — und ein Vorgabewert für die Kernzahl ist **eine Annahme über die
   Maschine** und gehört dann ins Zeugnis.
3. **`u64::max` als `const`-Wert** und `static mut kernlast : [Zaehler; 64] = 0;`. Der erste
   ist Handwerk (der Auswerter kennt die Grenzen bereits, `typen.rs`); der zweite fragt, ob
   ein skalarer Anfangswert ein ganzes Feld füllt. *In C tut `= {0}` genau das — aber es
   hinzuschreiben heisst zu entscheiden, dass `0` hier „alle" meint.*

## Die Reihenfolge, und was jede Stufe an Weigerungen schliesst

| Stufe | schliesst | kumulativ von 46 | Art |
|---|---:|---:|---|
| **C1** `option` | ≈ 13 | 13 | Verdrahtung eines vorhandenen Beweises |
| **C2** `tagged` | 5 | 18 | Bauarbeit |
| **C3a/b** `reason`, `rcu` | 4 + 2 Anw. | 24 | Bauarbeit |
| **C3c/d** `group`, `walk` | 2 | 26 | `group` erzeugt NICHTS |
| **C4** `exchange` | 2 | 28 | Bauarbeit, Ordnung ist die Falle |
| **C5** die drei Entscheidungen | 6 | 34 | ENTSCHEIDUNG, dann Handwerk |
| **C3e/f/g** `entry`, `boot`, `entrust` | 5 | 39 | **Axiomschicht** |
| Kleinkram | 4 | 43 | Handwerk |
| **gezogene Linien** | 3 | **46** | bleiben `C001` |

**Die Zielaussage ist damit nicht „0 Weigerungen", sondern „3 Weigerungen, und jede ist eine
Linie mit einem Satz Begründung."** *Eine Absenkung, die alles frisst, hat keine Meinung
mehr — und `C001` ist die einzige Stelle, an der der Erzeuger noch nein sagen kann.*

## Die Sprechprobe, und sie muss mitwachsen

Heute stechen **zwölf** Übersetzungseinheiten durch. Jede Stufe oben schuldet **mindestens
eine weitere**, und zwar nach demselben Muster: erzeugen → `cc -Werror` → **ausführen** →
Ergebnis vergleichen → verfälschtes C muss fallen.

> **Ein Erzeuger, der übersetzbares C liefert, das etwas anderes rechnet, ist schlimmer als
> einer, der nichts liefert — er sieht aus wie ein Ergebnis.**

Dazu die zwei Zeilen, die `pruefe-emission.sh` heute fehlen:

* **zweimal erzeugen, Hashes vergleichen** (die Reproduzierbarkeit ist gemessen, aber nicht
  zugesagt — s. «Z2»),
* **je Stufe eine Mutation** in `mutiere-pruefer.py` auf die neue Absenkung. Die
  Emissionsfläche stand am 2026-08-17 bei 0 Mutationen und ist heute bei 44; *was 0
  Mutationen hat, ist nicht gedeckt, sondern unbeschädigbar.*

## Die Abbruchbedingung

**Wenn eine Stufe eine Sprachentscheidung erzwingt, die nur der Absenkung dient, wird sie
nicht getroffen.** Die Grammatik ist für den Menschen da, der Gabbro schreibt, nicht für den
Erzeuger, der es liest. *Wo beides auseinandergeht, gewinnt der Mensch und der Erzeuger sagt
`C001`* — mit Begründung, wie an den drei Linien oben.

---

# «OPT» — schnelles und sicheres C, und der Assembler als versiegeltes Loch

> **Die Regel, die diesen Block trägt:** *eine Optimierung darf keine Zusage verbrauchen.*
> Jede Zeile hier gibt dem C-Übersetzer etwas, **das ein Gabbro-Pass hält** — und wo kein
> Pass es hält, wird es nicht hingeschrieben. **Ein `restrict`, das nicht stimmt, ist keine
> Optimierung, sondern eine stille Fehlübersetzung.**

## Die Messung zuerst, und sie dreht die Frage um

Gemessen 2026-08-19, `cc -O2`, dieselbe Maschine, jede Zahl über mehrere Runden stabil.

### Was der Erzeuger heute schon tut

```c
uint32_t stand(const Objekte *o, uint32_t i) {
    return o->slots[i].zaehler;          /* KEINE Schrankenpruefung */
}
```

**Die Schrankenprüfung ist nicht wegoptimiert — sie war nie da.** `M103` hat `i < count`
zur Übersetzungszeit bewiesen; was nicht bewiesen werden kann, ist ein `M103`-Fehler und
kein Laufzeitzweig. Und `effects { reads o }` wird `const Objekte *o` — *die Wirkungsliste
ist schon heute eine Optimierungsangabe.*

Der eine Fall, in dem eine Prüfung dasteht, ist der gewollte:

```c
if (!(i < hinterlegt)) { return 0; }     /* aus `narrow i to 0 .. hinterlegt else { … }` */
```

**Genau ein Vergleich, mit benanntem Ausgang.** *Eine geprüfte Schranke ist keine
Nachlässigkeit, sondern die Stelle, an der der Mensch entschieden hat, was bei Verletzung
passiert.*

### Was die Schrankenprüfung wirklich kostet

| Gestalt | ohne Prüfung | mit Prüfung | Faktor |
|---|---:|---:|---:|
| Index, den `cc` selbst beweist (`k & (N-1)`) | 117 ms | 117 ms | **1,00** |
| Index aus einem undurchsichtigen Feld | 156 ms | 210 ms | **1,34** |

> **Der erste Messwert ist der wichtigere.** Wo der C-Übersetzer die Schranke selbst
> beweist, löscht er die Prüfung — und Gabbros statischer Beweis kauft **nichts**. Der
> Gewinn entsteht **nur dort, wo `cc` es nicht gekonnt hätte**, und dann sind es 34 %.
> *Ein Vorteil, den man nicht so einschränkt, ist eine Werbeaussage.*

### Und was der wirklich grosse Hebel ist

| Gestalt | ohne `restrict` | mit `restrict` | Faktor |
|---|---:|---:|---:|
| Zeiger, deren Herkunft `cc` sieht | 23,0 ms | 23,1 ms | **1,00** |
| Zeiger aus einer anderen Übersetzungseinheit | 66,0 ms | 23,2 ms | **2,85** |

**2,85 gegen 1,34.** Die Aliasfrage ist der grösste ungenutzte Hebel des Erzeugers, und
Gabbro hat genau die Angabe, die C fehlt. *Der erste Anlauf an dieser Messung ergab 1,15 /
1,69 / 1,00 über drei Runden — kein Messwert, sondern Rauschen, weil das Zielfeld in place
verändert wurde und die zweite Runde andere Daten sah. Erst mit frischen Daten je Runde
steht die Zahl.*

## OPT1 — `restrict`, und was es voraussetzt

**Der Gewinn ist gemessen, die Voraussetzung ist offen, und das ist die ganze Nachricht.**

`restrict` sagt dem C-Übersetzer: über diesen Zeiger allein wird dieses Objekt in diesem
Bereich erreicht. Gabbro **darf das heute nicht behaupten**: `own` kauft keine Exklusivität
(`R004` deckt nur die syntaktische Hälfte — derselbe Ort an zwei `own`-Stellen eines Rufs),
und zwei `ptr<normal, rw>` auf dasselbe Objekt sind ununterscheidbar. **Das ist M3s offener
Rest, und er hat ab heute einen Preis: 2,85.**

Die Stufen, von der billigsten zur teuersten:

| | Wann `restrict` gesetzt werden **darf** | trägt es heute ein Pass? |
|---|---|---|
| a | Ein Parameter ist `own` **und** kein zweiter Parameter derselben Signatur ist es | **`R004`, halb** — der Ruf ist geprüft, die Herkunft nicht |
| b | Zwei Parameter, deren `effects` **disjunkte** Orte nennen (`writes a` gegen `reads b`) | **nein** — der Rahmen nennt Orte, nicht Objekte |
| c | Ein Zeiger auf eine `table`, die kein anderer Parameter erreicht | **nein** — braucht Erreichbarkeit |

* **a ist der einzige Schritt, der ohne neue Analyse geht** — und selbst er braucht die
  Zusicherung, dass ein `own`-Argument nicht *anderswoher* schon zeigt. Das ist die
  Sprachentscheidung, die «K5» als `own`-Rest gebucht hat: `own` als **Freigabeoperation**
  (der Rufer gibt ab und behält nichts) trägt `restrict`; `own` als blosser
  Signaturvermerk trägt es **nicht**.
* **Die Gegenprobe ist Pflicht und sie ist unangenehm:** ein falsches `restrict` erzeugt
  Code, der *manchmal* richtig ist. Ein Differenztest, der einmal läuft, findet es nicht.
  **Deshalb: je `restrict`-Regel eine Giftprobe in C, die unter `-O2` ein ANDERES Ergebnis
  liefert als unter `-O0`** — genau das ist der Fingerabdruck einer falschen
  Alias-Zusicherung.

> **Solange kein Pass die Bedingung hält, schreibt der Erzeuger kein `restrict`.** Die 2,85
> stehen als *Preisschild an einer offenen Entscheidung*, nicht als Versprechen.

## OPT2 — was Gabbro sonst weiss und heute verschenkt

Alles hier ist **ohne neue Analyse** zu haben, weil ein Pass es bereits hält:

| Angabe | woher | C-Form | was sie bringt |
|---|---|---|---|
| `effects { pure }` | `E008`, kompositional geprüft | `__attribute__((const))` | Rufe werden zusammengefasst und aus Schleifen gezogen |
| `effects { reads X }` ohne `writes` | derselbe Pass | `__attribute__((pure))` | dito, eine Stufe schwächer |
| `-> never` / `effects { diverges }` | `S006`, `E00x` | `_Noreturn` | der Rückweg entfällt, Register bleiben frei |
| `tagged type` | `D005`, erschöpfend | `switch` **ohne `default`** | Sprungtabelle statt Kette |
| Wertebereich `u32 in 0 .. 63` | `M101`/`M104` | der **kleinste** C-Typ | schmalere Felder, bessere Cachelage |
| `costs <= N ops` | Pass 9 | *nichts* | **siehe unten** |

**`costs` gehört ausdrücklich nicht dazu.** Die Zusage ist eine Aussage über das *Programm*,
keine über die *Maschine*; sie in eine `#pragma unroll` zu übersetzen hiesse, eine
Iterationszahl für eine Zeitmessung zu halten. *Der Ordner trennt das seit «B24», und ein
Erzeuger darf die Trennung nicht kassieren.*

**Und `const`/`pure` haben eine Falle**, die genannt gehört: GCCs `const` verbietet **jedes**
Lesen von Speicher, auch von Parametern über Zeiger. `effects { pure }` in Gabbro erlaubt das
Lesen von Parametern. **Die richtige Zuordnung ist deshalb `pure` → `__attribute__((pure))`
und nur eine Funktion ganz ohne Zeigerparameter → `((const))`.** *Zwei Wörter, die dasselbe
heissen und Verschiedenes bedeuten — genau die Klasse, in der `kandidaten_oeffentlich` stand.*

## OPT3 — der Assembler als **versiegeltes** Loch

Es gibt heute **kein `asm`** in der Sprache; `entry`, `boot` und `entrust` senken nach «C3»
in die Axiomschicht ab und brauchen dort Maschinenbefehle: `iretq`, `lgdt`, `wrmsr`, `in`/`out`,
Barrieren.

**Ein `asm`-Block ist ein Loch in JEDEM Pass.** M1 kennt die Bereiche nicht, `effects` sieht
die Berührungen nicht, `costs` kennt die Zahl nicht, M2 sieht den Verbrauch nicht. Wer ihn
ohne Versiegelung einlässt, macht alle zwölf Pässe zu einer Aussage über das, was *vor* dem
Block stand.

Deshalb die Form — **jede Zeile davon ist eine Pflicht, keine Verzierung**:

```gabbro
asm x86_64 {
    "outb %[wert], %[tor]"
    in     { tor : u16, wert : u8 }
    out    { }
    clobbers { memory }
    effects  { writes GERAET }
    costs    <= 1 ops
}
```

* **`arch` ist pflichtig** — ein `asm` ohne Bogen ist eine Übersetzungseinheit, die auf einer
  anderen Maschine still etwas anderes tut. *`aarch64` bleibt versiegelt; ein `asm aarch64`
  ist damit ein Fehler und keine Lücke.*
* **`effects` ist pflichtig** und wird vom Rufer wie jeder andere Ruf getragen — das ist die
  Zeile, die den Rahmen rettet. Ohne sie ist der Block ein `E009` auf ewig.
* **`costs` ist pflichtig**, sonst reisst die Terminierungskette.
* **`clobbers memory` ist die Vorgabe**, nicht die Ausnahme. *Wer die Vorgabe umdreht, spart
  eine Zeile und verliert eine Zusage.*
* **Und alles davon ist eine ANNAHME**, keine Prüfung: Gabbro liest den Befehlstext nicht.
  Deshalb gehört jeder `asm`-Block **ins Zeugnis**, in denselben Abschnitt wie `extern fn`
  und `entrust` — *wer nicht prüfen kann, exportiert.*

> **Die Zahl, die dabei entsteht, ist die eigentliche Aussage:** *wie viele Zeilen Assembler
> trägt ein in Gabbro geschriebener Kern?* Sie gehört neben die Kennzahl, denn sie ist die
> Fläche, über die der Ordner **nichts** sagt.

## Was die Sprechprobe dafür braucht — und heute nicht hat

`pruefe-emission.sh` übersetzt mit `-Wall -Wextra -Werror` und **ohne `-O`**. Nachgemessen:
die erzeugte Einheit liefert bei `-O0`, `-O2` und `-O3` dasselbe Ergebnis und läuft sauber
unter `-fsanitize=undefined`. **Aber gemessen habe ich das, nicht der Wächter.**

Drei Zeilen fehlen ihm, und jede fängt eine eigene Klasse:

1. **Jede Einheit bei `-O0` UND `-O2`, und die Ergebnisse müssen gleich sein.** Eine
   Abweichung ist der Fingerabdruck von undefiniertem Verhalten — und **die einzige
   Probe, die ein falsches `restrict` findet.**
2. **`-fsanitize=undefined,signed-integer-overflow` auf jede Einheit.** Gabbro beweist
   Überlauffreiheit; *dann darf der Sanitizer nichts finden, und wenn doch, ist es ein
   Befund über M1, nicht über C.* (`address` läuft auf diesem Rechner nicht — der gehärtete
   Kern kollidiert mit dem Schattenspeicher. **Das ist keine bestandene Probe, sondern eine
   nicht gefahrene**, und sie gehört so gebucht.)
3. **Die Vergleichsmessung, die P5s Tor verlangt** — *„erzeugt ≤ Handschrift + Rauschen"*.
   Sie existiert bis heute **nicht**, und ohne sie ist jede Aussage über die
   Geschwindigkeit des Erzeugnisses eine Vermutung.

## Die Reihenfolge, und warum sie so herum steht

| | Arbeit | gemessener Gewinn | Voraussetzung |
|---|---|---|---|
| **OPT0** | `-O0`/`-O2`-Gleichheit + UBSan in den Wächter | **0** (es ist die Probe) | keine |
| **OPT2** | `pure`/`const`/`_Noreturn`/`switch`/schmale Typen | ungemessen — *zuerst OPT0* | keine |
| **OPT3** | `asm`, versiegelt | ermöglicht «C3e/f/g» | Zeugnisfläche |
| **OPT1** | `restrict` | **2,85** in der harten Gestalt | **Aliasanalyse / `own`-Entscheidung** |

**Die stärkste Optimierung steht zuletzt, weil sie die einzige ist, die etwas kaputt machen
kann.** Und OPT0 steht zuerst, obwohl es nichts beschleunigt: *ohne die Probe ist jede
folgende Zeile eine Behauptung.*

## Die Abbruchbedingung

**Keine Optimierung ohne einen Pass, der ihre Bedingung hält.** Nicht „meistens richtig",
nicht „im Korpus richtig" — gehalten. Und **keine Zahl ohne Vergleichsmessung**: solange P5s
Tor nicht steht, wird über die Geschwindigkeit des erzeugten C **nichts** behauptet.

*Ein Erzeuger, der schnelles C liefert, das manchmal etwas anderes rechnet, ist schlimmer als
einer, der langsames liefert — er sieht aus wie ein Ergebnis.*

---

# «ABI» — Bibliotheken, die sich mischen lassen

> **Der Satz, der den ganzen Block trägt:** *eine Bibliotheksgrenze ist kein Riegel, sondern
> eine **Brücke mit Maut**.* Was über sie geht, wird an derselben Stelle geprüft wie
> innerhalb einer Einheit — oder es geht nicht. **Eine ABI, die Zusagen ungeprüft
> weiterreicht, macht aus elf geprüften Klassen elf behauptete.**

## Der Stand, gemessen am 2026-08-20

```gabbro
module bib { pub impl fn tu() effects { writes z } … }
module app { use bib::tu; impl fn ruft() effects { pure } costs <= 4 ops { tu(); } }
```

```
E009  `tu` is unknown to the graph                     (Hinweis)
K003  promises costs, but `tu` is not declared here    (FEHLER)
```

**Die Datei geht nicht durch.** Der ältere Eintrag im `TODO.md` sagte, die Zusage falle
„lautlos auf eine untere Schranke zurück" — *gemessen fällt sie nicht durch, sie fällt.*
**Es fehlt kein Riegel, es fehlt eine Brücke.** Und `pub` hat seit dem 2026-08-19 einen Leser
(`N025`), also steht die Sichtbarkeitshälfte bereits.

## Das Artefakt: `.gabi` — das Zeugnis, maschinenlesbar

`gabbro zeugnis` schreibt heute **für Menschen**, was die Übersetzung trägt. Die ABI ist
dieselbe Aussage in einer Form, die `gabbro pruefe` **liest**:

```
lib caprock::cap  @abi 1  arch x86_64
  signatur  aushaengen(c : ptr<normal, rw> CapSpace, s : index into CapSpace)
            requires Held(KAPPEN), …   ensures …
            effects  { writes c.slots, locks KAPPEN }   costs <= 200 ops
  darstellung  CapSpace  count 1048576  option-sonderwert 1048576
  sperre    KAPPEN  protects { … }  vor { OBJEKTE }        -- ORDNUNG, keine Zahl
  annahme   mmu_folgt_ihrem_modell  "…"  falsifier sonde_pf_bei_p0
  schablone option.sonderwert  BEWIESEN  praemisse N < 2^w
  fremd     rust_eintritt  effects { consumes t, diverges }
  asm       3 Ruempfe, 7 Befehlszeilen
```

**Fünf Dinge müssen sich vereinigen lassen, und jedes hat seine eigene Falle.**

### 1. Signaturen — das ist der einfache Teil

`effects`, `costs`, `requires`, `ensures` sind schon heute die Sprache der Aufrufgrenze. Der
Rufer trägt sie, wie er die eines `extern fn` trägt — mit dem Unterschied, dass hier ein
**geprüfter** Rumpf dahintersteht und nicht ein angenommener. *Das ist der einzige Posten,
bei dem eine Bibliothek die Vertrauensfläche VERKLEINERT.*

### 2. Sperrränge — der schärfste Posten, und er verlangt eine Änderung der Sprache

`lock KAPPEN … rank 0` ist eine **absolute Zahl**. Zwei unabhängig geschriebene Bibliotheken
vergeben beide `rank 0`, und beim Mischen ist die Ordnung entweder willkürlich oder
widersprüchlich. **Absolute Zahlen komponieren nicht.**

> Die ABI trägt deshalb **keine Ränge, sondern eine ORDNUNG**: `KAPPEN vor OBJEKTE`. Beim
> Vereinigen entsteht ein gerichteter Graph über allen Sperren aller Bibliotheken, und
> `H006`/`H012` rechnen auf ihm weiter wie heute. **Ein Zyklus ist eine Absage** — und zwar
> genau die, *die keine der beiden Bibliotheken allein sehen kann.*

Innerhalb einer Einheit bleibt `rank N` schreibbar und wird beim Export in die Ordnung
übersetzt. *Eine Zahl ist eine Ordnung mit einer willkürlichen Einbettung; die Einbettung
gehört nicht über die Grenze.*

### 3. Darstellungen — zwei Bibliotheken, ein Typ, zwei Bilder

`option index into T` senkt auf den Sonderwert `count` ab (`Option_Sonderwert.thy`). Trägt
Bibliothek A `count 1048576` und B einen anderen Wert für denselben Typ, sind die abgesenkten
Bilder **nicht dasselbe**, und ein Zeiger von A nach B ist Unsinn. Die ABI nennt die
Darstellung, und **Ungleichheit ist eine Absage, keine Umrechnung.**

### 4. Schablonen mit Beweisstand — die Vereinigung ist die Vereinigung

Ein `UNPROVED` in irgendeiner Bibliothek färbt das ganze Erzeugnis. *Das ist kein
Pessimismus, sondern Arithmetik: die Vertrauensfläche einer Mischung ist die Vereinigung, nie
der Durchschnitt.*

### 5. `arch` — verschieden heisst Absage

Zwei Bibliotheken mit verschiedenem `arch` mischen nicht. `asm`-Rümpfe machen es scharf, aber
es gilt auch ohne sie: die Axiomschicht ist bogenweise.

## Die Annahmen, und was ein `override` WIRKLICH ist

Der Wunsch: *Hardwareannahmen sollen beim Import je Bibliothek gestellt werden können und die
der Bibliothek überschreiben; sonst gelten deren eigene.* Die Vorgabe ist damit klar — **die
Annahme der Bibliothek gilt, bis jemand etwas anderes hinschreibt.**

```gabbro
use caprock::cap
    annimmt {
        mmu_folgt_ihrem_modell = kein_mmu   -- diese Maschine hat gar keine MMU
        tlb_ist_nach_cr3_leer  entfaellt    -- hier BEWIESEN, nicht angenommen
    };
```

**Und jetzt der Satz, an dem der ganze Entwurf hängt:**

> Eine Bibliothek wurde **unter** ihrer Annahme geprüft. Wer die Annahme austauscht, tauscht
> die Voraussetzung ihrer Beweise aus — **die Beweise wandern nicht mit.**

Ein `override` ist deshalb **keine Ersetzung, sondern eine Beweispflicht.** Drei Fälle, und
sie werden unterschieden, nicht zusammengeworfen:

| Fall | was der Übersetzer tut |
|---|---|
| **wortgleich** (derselbe Text, derselbe `falsifier`) | nichts. Die Annahme wandert unverändert in die vereinigte Menge. |
| **stärker** — die neue Annahme impliziert die alte | die alte verlässt die Annahmenmenge, und `A_neu ⟹ A_alt` wird eine **gezählte Pflicht** in `gabbro pflichten`. *Die Implikation ist nicht mechanisch entscheidbar; also wird sie gezählt und nicht geraten.* |
| **`entfaellt`** — der Importeur behauptet, sie sei hier bewiesen | dieselbe Pflicht, nur ohne Ersatzannahme: `⊢ A_alt`. Sie steht mit Namen im Zeugnis, damit niemand sie für erledigt hält. |
| **schwächer oder unvergleichbar** | **Absage.** Wer das will, schreibt `reopens { … }` und nennt **einzeln**, welche Zusagen der Bibliothek damit auf *unbewiesen* zurückfallen. |

**`reopens` ist der Riegel gegen die bequeme Bewegung.** Ohne ihn wäre ein `override` das
perfekte Werkzeug, um eine unbequeme Annahme wegzudefinieren — *und das Erzeugnis sähe
danach besser aus als vorher.*

### Der `falsifier` ist der Teil, der nicht verhandelbar ist

Jede Annahme trägt eine Sonde (`falsifier sonde_pf_bei_p0`). **Eine überschreibende Annahme
ohne Sonde ist eine Absage** — nicht weil die Sonde beweist, sondern weil sie *widerlegbar*
macht. Eine unfalsifizierbare Annahme darf nur, wer `unfalsifiable` hinschreibt, und das ist
im Zeugnis eine eigene Zeile (wie `A10` heute).

## Die Reihenfolge

| | Arbeit | was sie freischaltet |
|---|---|---|
| **ABI0** | `gabbro zeugnis --gabi` schreibt maschinenlesbar; ein Test liest es zurück | alles Weitere |
| **ABI1** | `gabbro pruefe --mit lib.gabi` löst Namen auf und trägt Signaturen | `E009`/`K003` verschwinden **weil geprüft**, nicht weil geschwiegen wird |
| **ABI2** | **Ordnung statt Rang** in Sprache und ABI | Mischen ohne Zyklus |
| **ABI3** | die Vereinigung: Annahmen, Schablonen, Darstellungen, `arch` | `gabbro zeugnis` über die Mischung |
| **ABI4** | `annimmt { … }` mit den drei Fällen und `reopens` | der Wunsch dieses Abschnitts |

**ABI2 steht vor ABI3, weil es die Sprache ändert** — und eine Sprachänderung, die man nach
dem Bau der Vereinigung macht, bricht jede schon geschriebene ABI-Datei.

## Die Abbruchbedingung

**Wenn die Vereinigung eine Klasse nur noch behaupten statt prüfen kann, wird die Brücke
nicht gebaut.** Lieber elf geprüfte Klassen in einer Einheit als elf behauptete über eine
Bibliotheksgrenze hinweg. *Der Gewinn einer ABI ist, dass eine Bibliothek die
Vertrauensfläche VERKLEINERT — schafft sie das nicht, ist ein `extern fn` mit Vertrag die
ehrlichere Form, und die gibt es längst.*
