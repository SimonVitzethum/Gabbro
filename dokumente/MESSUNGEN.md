# Gabbro — the measurements

**Everything that was run, in one place.** Pulled together on 2026-08-14; text unchanged.
**What is not here is not measured.**

> **"Text unchanged" is the one sentence in this file that speaks about the whole document
> TODAY, and it has stopped being true.** It described the drawing-together of 2026-08-14 and
> stayed put: since then whole sections dated 2026-08-15, -16 and -17 have been appended, **and
> one existing passage was edited** — the P0.4 findings `G1`–`G3` were renamed to `GP1`–`GP3` on
> 2026-08-16 because they collided with the grammar findings of the same name (the rename is
> recorded at that table).
>
> **What the sentence was protecting stands, and it is worth keeping in the sharper form:** no
> measured figure in this file is pulled up to a later state. A number that fell stays where it
> fell, with its date. *That is a promise about the records, not about the file — and only the
> second one was ever checkable.*


---

# MEASUREMENT PROTOCOL for measurement 2 — IN ADVANCE, before the first obligation was looked at

**These rules stand here before a single one of the 17 logic obligations had been looked at.** The
reason is this folder's documented weakness: **six of nine corrections in
[`HISTORIE.md`](HISTORIE.md) were reinterpretations at a boundary.** And this count has a built-in
**incentive gradient** — descent statements are cheap (automatic induction), value statements
expensive. Whoever sharpens the criterion during the count sharpens it in the convenient
direction.

*(The commit of this section stands in the history **before** the commit of the count. That is the
only evidence that "in advance" is more than a claim about the order.)*

## The three columns — one sentence each, and no more

| Column | Decision rule |
|---|---|
| **K — by construction** | The obligation's statement **mentions only the machine**, OR it is a **declared invariant** whose preservation the generator shows once above the declaration. **A human writes nothing.** — **Condition, to be checked mechanically (see below).** |
| **A — descent statement** | The obligation can be written as *"for all x in ⟨**declared** domain⟩: P(x)"*, and P(x) follows from P on the **strictly smaller** elements **plus exactly one declared step assurance**. |
| **W — value statement** | Everything else: the argument concerns **values a body computes** and that no declaration fixes. |

### The condition on K, and it is mechanical instead of tippable

**"The generator shows it once" holds only if ALL mutations of the carrier are generated
operations.** A single hand mutation — a `breaking` block, a write path outside the `ops` list —
and the preservation is **human work**, hence **A or W**.

**Per obligation that is one mechanical question: are all write sites of the carrier generated?**
The tipping rule would catch the case in case of doubt; **mechanically checkable beats tippable**,
because it does not hang on care during the count.

> **Side yield, free:** the same check delivers the **list of `breaking` sites** — exactly
> item L3 from the remainder list (*"`breaking` restorations without a generated
> closing operation"*).

## The tipping rule — it ALWAYS tips toward W

1. **If an obligation fits two columns, the more expensive one holds.**
2. **If the descent structure would first have to be introduced for the proof** (it is not
   declared), it is **W**.
3. **If the induction needs a strengthened hypothesis**, it is **W** — strengthening is human work
   and exactly the step a solver would have to guess.
3b. **"Exactly one declared step assurance" means PER DESCENT, not per property.** An
   obligation whose proof **composes two descents with one assurance each** stays **A**. One whose
   **single induction step needs two assurances at once** falls to **W**.
   *This reading stands here because this is exactly the place where the first dispute will arise.*
4. **Not split, not rounded.** An obligation counts whole, in one column.

## Record, per obligation

`file:line` · column · **one** sentence of justification. No more — a long justification is a
tipping case defending itself.

**And the rules must stay falsifiable:** if an obligation **cannot** be judged at all with these
three sentences, that is recorded as a **finding about the rules** and not silently pushed to W. A
set of rules that decides every case has no edge.

## The two outcomes, likewise in advance — so that it is measured and not interpreted

| Outcome | what it means |
|---|---|
| **W ≥ 9 of 17** | The ceiling of step assurances covers a **minority**. The 5 : 1 hand-proof price applies to **more** than the assumed 5 %, the 0,8 : 1 estimate moves upward. **That is not a mood-dampener but the number that quantifies `k`** — and only it makes the seL4 comparison honest |
| **W ≤ 8 of 17** | The ceiling **carries**, and the hard step assurances are the **strongest piece of the language** |

**Both outcomes are good results — precisely because they stand here before the counting starts.**

## The WEIGHTS — in advance, otherwise the estimate wanders at will

**"The 0,8 : 1 estimate wanders" is not a statement without weights.** Where it wanders to hangs on
the **line share** the W obligations carry — and the **IPC fastpath weighs differently from a
range check**. If the shares are determined only **after** the count, the temptation to weigh W
obligations small is structural.

**Order, binding:**

1. locate the 17 obligations with `file:line` (otherwise invalid, see below);
2. **per obligation measure the line extent of the body concerned** — **before** the first look at
   the columns;
3. **then** classify.

**The formula, written down for good:**

```
F        = Zeilen der zehn Fragmentruempfe (Rust-Original, ohne Leerzeilen)
W_zeilen = Zeilen der Ruempfe, deren Pflicht als W gebucht ist
w        = W_zeilen / F                     -- Anteil IN DER STICHPROBE
Ueberschlag = w * 5,0  +  (1 - w) * 0,3
```

> **The caveat belongs in the same line, not in a footnote:** the ten fragments are **not a random
> sample** — they were chosen for **breadth**. The extrapolation of `w` to the whole kernel carries
> that bias, and its **direction is unknown**. The estimate is thereby a **substitution with a
> named uncertainty**, not a measurement of the kernel.

## What makes the measurement INVALID (not merely unfavourable)

If fewer than 17 obligations can be found again with `file:line`, the **source** is not
reproducible — the same protocol class as the five scratchpad classes, and then there is no
counting, the basis is established first.

---


---

# P0 — the acceptance measurement, as far as the folder allowed

## P0 RUN — as far as the folder allows

> **ENTERED 2026-08-14.** Three numbers re-checked: `virtio-blk` has **0** `Ordering::`
> (confirmed), `FINE_BLOCKS = 8` stands in `mmu.rs:186` (confirmed), and **side finding (a) is
> corrected** — on x86 FP is **eager**, see below.

**Run on 2026-08-14** against the branch `arch/x86_64` of Caprock (fresh clone) and the
Gabbro folder (state `d910e18`). Three measurements per plan (ERGAENZUNG-2 §6, stage P0), plus
side findings. **The verdict up front, so that nobody has to assemble it from the text:**

| Gate | Result |
|---|---|
| Ordering sample (no fourth outcome) | **passed, 36/36** — with three protocol additions that are not fourth outcomes |
| Hanging plumbing 19 → 0 | **not decidable**: 6 of the 11 classes are documented in the folder and fall; **5 classes lie in the scratchpad, not in the repo** — the measurement basis is not reproducible |
| `narrow` ≤ 24 | **open**: only a form check was possible, the full count is outstanding |

By our own ordering rule it follows: **no checker code.** The next step is not a line of Rust
but the scratchpad classes into the repo — a measurement that does not lie in the folder is, by
trap 80, a number somebody runs parallel to the truth.

---

### Part 1 — the 19 hanging obligations against the constructs

Documented in `MESSUNGEN.md` are six classes with sites. Comparison:

| Class (documented) | Construct | Verdict |
|---|---|---|
| `forever`/`per_pass` ritual (8 loops, ticket spinlock without `try_lock`, Ed25519 over the manifest) | `on_exceeded` obligation, `held <= K ops` at the lock (without it not takeable in service loops), input-dependent bound | **falls** — the spinlock `caprock-sync:821` becomes unwritable instead of wrongly described |
| `per_pass` in cycles (D10) | unit `ops`, defined in FESTLEGUNG §7 | **falls** |
| `publishes` at the declaration (671 sites; `FP_OWNER[core]` self-referential; statement payload; virtio `avail` volatile to the device; counters without a notation) | `publishstmt` at the store, `ghost static` reification, `transition publishes`, `publishes nothing` | **falls** — all four named sub-cases have a notation |
| PTE = pointer AND bitfield → missing eighth domain (`mmu.rs:1283`) | `embeds` + `walk` + `mappings of` | **falls, with one construct extension** (see part 4b) |
| 54 relational preconditions | V2 | **falls in form** (see part 3) |
| `break`/`continue` unmentioned | `leave`/`next` with a target name, prohibition list extended | **falls** |

**The remaining five classes** ("the remaining five classes from the report in the scratchpad",
`MESSUNGEN.md`) **do not exist in the repo.** An estimated 6 of the 19
obligations are therefore not checkable against the specification — not because a construct is
missing but because the measurement is missing. **The gate "19 → 0" is, as formulated, not
decidable, and that is a finding about the protocol, not about the language.** Task: the five
classes with sites into the repo, then repeat this part.

---

### Part 2 — Ordering sample: 36 sites, six layers, no fourth outcome

Population in the branch: `threads/mod.rs` 872, `bringup.rs` 390, `system.rs` 184, `fuzz.rs` 112,
`caprock-sync` 53, `vtd.rs` 41, more below those. Sample systematic (every n-th site
per layer), 36 sites read and classified:

| Class | # | Examples (file:line) |
|---|---|---|
| **Pairing: `publishes`** (release store with payload/flag) | 8 | `threads:2918` (CTRL_DONE), `threads:4154`, `threads:4397`, `bringup:3040` (DRV_STEP), `bringup:3211`, `system:5148` (IRQ_PENDING), `system:6505`, `sync:472` (pointer payload) |
| **Pairing: `awaits`** (acquire load, payload afterwards) | 11 | `threads:1508` (MIG_PROGRESS threshold), `threads:3405`, `threads:3652`, `bringup:807`, `bringup:1435` (bit set), `vtd:104/876/989/1543` (kernel mirror of the device), `system:5561`, `sync:488` |
| **third form: `exchange`** | 6 | `colors:103` (CAS-or loop → bounded `retry`), `system:5189` (slot claim), `system:4502` (init latch), `sync:979`*, `konsole:387`, `vtd:550` (`fetch_or` report-once: branch on the old bit) |
| **counters: `publishes nothing`** | 8 | `threads:705`, `bringup:61/2634`, `system:55/2720/8790`, `sync:510/563` |
| payload read **under an acquired `Vis`** (relaxed after a flag acquire) | 3 | `threads:3898` (RCAP_CLIENT_PD after the RCAP_DONE awaits), `sync:660–675` (report snapshot), `sync:641` |

**No fourth outcome.** But three classes the addendum's protocol did not foresee and that
belong entered there — not refutations but **eliminations**:

* **K1 — "under a lock: the atomic falls away."** `system:1361` (`FP_OWNER` reset in
  `fp_reset_slot`, documented "under held SCHED") is atomic in Rust only because
  `static mut` would be unsafe. In Gabbro it is a slot under `lock … protects` — no atomic,
  no pairing, one class fewer. Part of the 2 231 sites disappears that way.
* **K2 — construct implementation.** `sync:979` (RW writer CAS) and the console CAS are the
  innards of lock/console — in Gabbro **generated** constructs, not user code. They count into
  the template trust surface, not into the sample.
* **K3 — `accumulates` with a compound.** `sync:572–592` is the documented benign race site:
  `fetch_max` keeps the number correct, the `STELLE` pointer may come from the wrong event —
  commented in the code as accepted. Per-core **pairs** `(max, stelle)` with a merge at read time
  keep both consistent: **at this site the construct is strictly better than the original.**
  For that `accumulates` needs compound values in the merge set (small extension, named).

---

### Part 3 — `narrow`: only the form check was runnable

The 255/102/54 count comes from the folder; my sampling was too thin for a proportion of my own
(the regular expression caught a handful of sites, e.g. `alloc.rs:133`
`if start >= r.base && end <= zone_end` — textbook V2). **In form** V2 covers all 54
relational cases: checked comparison of two places, difference in the branch. **Untested and named
as a risk:** the case in which check and use lie **in different functions**
— V facts die at the function boundary, and whether that cut occurs in the tree (check in the
caller, subtraction in the callee) decides whether `requires a >= b` suffices as a contract or
whether the yardstick of 24 breaks. **The full count is the open remainder of P0** and belongs
run with a better pattern (the folder's lesson: "the corpus size hangs on the regular expression").

---

### Part 4 — side findings, two of them needing a decision

**(a) CORRECTED on entry — on x86 it is EAGER, and the conflict lies on the other
architecture.**

`kernel/src/system.rs:1215` says literally: **`x86_64: EAGER. Der Ausloeser des Wechsels ist der
WECHSEL, nicht der erste Zugriff.`** The justification below it is **exactly the addendum's**:
*"Lazy FP across a PD boundary is CVE-2018-3665 on x86 … for a cap system whose
selling point is isolation that would be a contradiction at the core of the claim."* `CR0.TS`
stays off permanently; an `#NM` is by definition a kernel bug.

**The names led astray:** `FP_OWNER`, `fp_switch_count` ("lazy FP owner switches")
and the doc comment at `:1204` describe the **aarch64** path — `CPACR_EL1` is an
ARM register. That is the same class this folder tracks: **a name read instead of the
thing.**

**The conflict remains, but shifted and smaller:** Caprock is **eager on x86, lazy on
aarch64**. The decree "eager only" therefore hits the **aarch64** side, where the
CVE-2018-3665 argument does not bite in this form. What is to be decided is thus not "decree
versus tree" but: **does the eager obligation hold per architecture or globally?**

*The original version of the finding:*
**(a-old) ERGAENZUNG-2 §3.4 collides with the measured code: Caprock x86 runs lazy FP.**
`system.rs` keeps `FP_OWNER` per core and counts "completed **lazy** FP owner switches"
(`fp_switch_count`). The addendum decreed eager-only ("lazy is the CVE trap and is
not offered"). Two outcomes, both with a price: force eager (512-byte `fxsave` per
context switch, rebuild of the measured scheme) **or** lazy as a construct with an ownership
witness (`FpOwner(core)` handover as a pairing — the sample shows that the accesses today partly
run under a lock, K1) plus a probe against the leak class. **Not to be decided here;
entered as a conflict.** A decree that contradicts the measured stock without
naming it would be the overwriting form at architecture level.

**(b) W^X is formulable, but the `mappings` tuple needs level indices.** The real audit
(`vspace_wx_ok`) excludes the shared kernel PTs (`i >= FINE_BLOCKS`). The invariant
therefore reads `forall m in mappings of vspace: m.index[2] >= FINE_BLOCKS => !(m.user && m.writable
&& !m.nx)` — the tuple must carry the slot index per level. One line in the
`walk` domain definition, entered here instead of silently added.

**(c) The `programs/` class (4/4 hanging) confirms the coverage from the other side:**
`virtio-blk/main.rs` contains **zero** atomics — the service loop hangs on volatile
DMA stores and the `forever` form, i.e. exactly on `transition publishes` (F5) and §9.3. The
addendum's classification matches the reality of the program.

---

### What is to be done now, in order

1. **The five scratchpad classes into the repo** (with sites), then repeat part 1 — before that
   the 19→0 gate is undecidable and stays so.
2. **The `narrow` full count** with a more robust pattern, including a targeted search for the
   function-boundary cut.
3. **Decide lazy FP** (4a) — it is the only place at which an addendum decree contradicts the
   measured tree.
4. Extend the protocol of the ordering classification by K1–K3; `accumulates` by compound values,
   `mappings` by level indices.
5. ~~**Only then P1**~~ — **P1 has already been run** (2026-08-14, after the state against which
   this report was written): the specification and all three addenda are in the EBNF,
   **119 rules, 0 open, 189 terminals against 189 vocabulary words**, both guardians green.
   **The rule "no checker line before gate P1" continues to hold unchanged** — and it has not
   been broken.


---

# The logic/plumbing split

## The logic/plumbing split — measured for the first time, and it falls against the design

> **W7 SWEEP 2026-08-15: UNEVIDENCED — TO BE REPLACED.** The breakdown of the **74** is **not in
> the folder**; what stands there is the aggregate (74 / 17 / 57 / 19 / 1) and an area table
> without sites. The whole section carries **one** `file:line`, and that one belongs to the
> eager-FP question. **The count of 17 became invalid by it on 2026-08-15** (see there),
> and `delete_leaf` tipped on the recount from **3,6–6 : 1** to **1,75 : 1**.
> *Not deleted: the marking is the finding.*

**2026-08-14.** Ten hand-translated fragments from eight areas, **74 proof obligations** assigned
individually. The criterion from [`BEWEIS.md`](BEWEIS.md) had until then **never** seen a
measurement.

---

### The aggregate

| | |
|---|---|
| Proof obligations in total | **74** |
| **Logic** (mentions the thing) | 17 |
| **Plumbing** (mentions only the machine) | 57 |
| **of which hangs on the programmer** | **19 — i.e. 33 %** |
| Logic obligations that are **not formulable at all** | **1** |

**By area:** parser 1/9 hanging, IPC 1/8 — **those hold**. Scheduler + SMP 5, MMU 2 plus one
expressiveness hole. **`programs/` breaks completely: 4 of 4**, all at the service loop of
`virtio-blk`.

> **The assurance "everything except the logic proof falls out by construction" is thereby refuted
> at 19 named sites.** By the decision of 2026-08-14 that is **not an abort but an
> escalation**: for each of the eleven classes the construct that takes it over is to be designed.

---

### The three suspected sites — all three confirmed

#### `per_pass bounded n cycles` is a ritual

96 endless loops in the tree. **For eight the assurance is demonstrably false:** their pass contains
a ticket spinlock without a bound (`crates/caprock-sync/src/lib.rs:821` — **re-checked: the
crate has no `try_lock`, zero sites**) or Ed25519 over a manifest of arbitrary length.

**Three errors in one construct, and all three stand in our own register:**

1. **Gabbro says nowhere whether lock waiting time counts in `per_pass`.** If it does, the clause
   is unsatisfiable for **every** locking loop; if it does not, it says **nothing about
   latency** — hence nothing.
2. **`retry` has `on_exceeded` as an obligation, `forever` does not.** A bound without a named
   overflow — **D11 literally**: "whoever introduces a capacity must NAME the overflow".
3. **The only `forever` example stands on `cycles`** — the quantity Caprock measured at **D10** as
   unusable ("an iteration count is a property of the program, a time measurement is
   not").

#### `publishes` sits in the wrong place

671 declarations. **The clause sits at the declaration, the payload arises at the store.**

* `FP_OWNER[core]` publishes `FP_STATES[<the tid it carries itself>]` — **self-referential**,
  and the core index **does not exist at the declaration**.
* `STALE_STEP.store(2)` publishes "there is a dead entry in the `senders` queue" — **no
  `place`** but a statement.
* **The most safety-critical publication in the tree is not an atomic at all:** `Queue::publish`
  (virtio `avail` index) is a volatile store into a DMA region **to a device**.
* For pure counters there is **no correct notation**: the prose says "obligation", the EBNF
  says optional, and `placelist` has **no empty word**.

#### A real property falls out of all seven domains

**W^X over a two-level page table** (`crates/caprock-hal/src/x86_64/mmu.rs:1283`, **run in the
kernel**). The inner quantification would need a domain over a **dereferenced,
computed pointer**; `descendants of` follows the parent relation of *one* table, and
`reaches … via` is a predicate, not a domain constructor.

> **The cause lies one level lower: a PTE is at once pointer AND bitfield**, and for that
> Gabbro has no construct. That is the root, not the missing eighth domain.

---

### And the subtraction measurement tips my `narrow` result

**[`MESSUNGEN.md`](MESSUNGEN.md) is thereby superseded, and the error is mine.**

| | my measurement | the counter-measurement |
|---|---|---|
| Corpus | 94 (25 `-=`, 69 `a - b`) | **255** (27 `-=`, 228 `a - b`) |
| flow-sensitive | 4 (`leading_zeros`) | **102** |
| **of which relational** (`if a >= b { a - b }`) | **0** | **54** |

**What decides is not the number but the form.** An `if a >= b { a - b }` is a
**relation between two variables**, and an interval type **cannot carry** that — it says
something about *one* value. The four `leading_zeros` sites from which I derived *"M1 needs
exactly one flow rule, no general inference"* are **all four unary**: my
sample contained **zero** relational cases.

> **That is the house pattern, applied to me:** a sentence that would be true had I not
> silently widened the scope. From a sample that **structurally excluded** the hard
> form I concluded about all cases. **Open item 1 in `SYNTAX.md`
> goes back from `[x]` to `[ ]`.**

*Recounted: my narrower pattern still yields 25 and 65. The corpus size hangs on the
regular expression; both numbers are lower bounds of different patterns. **That changes nothing
about the form** — 54 relational cases are 54, however one counts the denominator.*

---

### Two finds that were not in the brief

**`keeping` does not kill trap 4 — it NAMES it.** In my own `device` example the
bit list is wrong: **GCMD bit 30 is `SRTP`** (re-checked: `const GCMD_SRTP: u32 = 1 << 30;`,
`vtd.rs:58`) — a **one-step command**, not a state bit. Every command would have re-triggered "Set
Root Table Pointer". And `IRE`/`QIE`, which Caprock **must** carry along, are missing.

> **The evidence against the construct is that its inventor kept it wrong in his own
> example.** Getting the list right **is** the original problem; `keeping` moves it
> from the write site into the declaration. That is better — **once instead of per call** — but it
> is a move, not an elimination, and exactly so it belongs written down.

**There is no `break` and no `continue`.** `breaking` is the invariant construct; the list
"what deliberately does not exist" names `while`, `for`, `goto` — **not `break`**. Presumably
by accident, and it hits exactly the case §8 carries as the `forever` example: **the
main loop of a server**.

---

### The disputed case the dividing line does not decide

`depleted_count -= 1` is **plumbing** (an underflow) — but it falls **only** via the
invariant *"the counter is the number of exhausted accounts"*, and that is **logic**.

**Here an invariant is not PRESERVED but USED** to discharge a range obligation.
[`BEWEIS.md`](BEWEIS.md) does not know this case.

- [ ] **A third column, or "falls out by construction" becomes the convenient booking.** Proposal:
      **plumbing, carried by logic** — it falls, but **only as far as the invariant
      is proved**. It is thereby no longer a free allowance but hangs visibly on a
      logic item. *That is the first disputed case of the dividing line, and it belongs here rather
      than in a footnote.*

---

### What is to be designed now — eleven classes, escalation instead of abort

- [ ] **`forever` needs `on_exceeded`** like `retry`, and a statement about **whether lock time
      counts in `per_pass`.** Without both the clause is a ritual.
- [ ] **`per_pass` in a quantity other than `cycles`** — D10 discarded time as a measure.
- [ ] **`publishes` at the STORE**, not at the declaration; a form for "nothing" and one for
      **volatile stores to a device** that are not atomics.
- [ ] **A construct for "pointer AND bitfield"** (PTE). From it the eighth domain follows by itself.
- [ ] **A form for relational preconditions** (`a >= b`) that an interval type cannot
      carry. **That is the big item** — 54 sites.
- [ ] **`break`/`continue`** to be decided: admit or explicitly forbid.
- [ ] The remaining five classes from the report in the scratchpad.

---

### The counter-design, second round — 15 rules, and three self-refutations

In parallel the completer held the grammar against the whole tree (1 896 lines).
**What of it is worked in IMMEDIATELY**, because it answers a find:

| Rule | replaces | Reason |
|---|---|---|
| `mirrors GCMD from GSTS` **per device** | `keeping` **per transition** | 18 hand-kept entries where `vtd.rs` has **one** constant — the construct was the trap it was built against |
| `publishes nothing`, `relaxed` | `publishes` as a prose obligation and an EBNF optional extra | 41 % of the atomics were unwritable; `relaxed` was missing at **779** occurrences, `seq` stood in the vocabulary at **0** |
| `old`, `offset_into`, `never` as **productions** | words without grammar | **`offset_into` stood in the vocabulary table and in no production** — the ELF lowering was thereby not unchecked but **unwritable** |

**Three findings the completer found against himself:**

1. **"Barriers belong to the address space" is half wrong.** In `Queue::publish` both
   stores lie in the **same** space (`dma`) and still need a barrier. Corrected: **the space
   determines the STRENGTH, `publishes` the PLACE.**
2. **`accumulates max` (high-water mark, 213 RMW sites) lowers to an unbounded
   CAS loop** — **the compiler emits what the language forbids.** Undecided, and
   it is the first candidate for "two demanded properties contradict each other".
3. **His strongest fragment and his weakest assumption are the same construct:** the
   phase tracking at the `device` carries only with *one* owner — and therefore **does not**
   carry exactly where trap 4 sits (VT-d, shared across all cores).

**Three open items he closed, with numbers:** genericity (**16 of 62** real, all on
`Slab`/`SpinLock` — both constructs exist; **0 of 6** traits polymorphic) · version evolution
(**0 of 11** migrations ⇒ **refusal**) · `costs` (cycles fall away, **operations** are
derived — D10 literally).

**His weakest part, named by himself:** `abi { … }` — **5 of 25 new words for a rule
that kills zero paid-for traps**, and **3 of 168** `asm!` sites looked at. A sketch, not a
rule.


---

# P0.1 — revoke on paper

## P0.1 — `revoke` on paper. Result: CONDITIONAL, and the condition is a missing construct

**Run on 2026-08-13**, against `crates/caprock-cap/src/space.rs:619` (real code, not a
sketch). The outcome was neither the prepared yes nor the prepared no.

---

### What had to be shown

`revoke(s)` deletes the whole subtree under `s`. Three obligations:

| | Obligation |
|---|---|
| **T** | **Termination** |
| **N** | **Postcondition:** afterwards `s` has no descendants |
| **I** | **Invariant preservation:** `cdt_wellformed` and chain finiteness continue to hold |

The real code is an outer loop ("as long as `s` has a child: descend to the leaf, delete the
leaf") with **two** step limits and a counted abort if the subtree is not tree-shaped.

---

### First attempt: as a `traverse`. **Fails, and cleanly at that**

```gabbro
traverse victims over subtree(s) by unvisited touches writes slots { delete(it); }
```

**Does not work.** `by unvisited` presupposes a **stable** set — the progress is "not yet
visited", and the visited set grows against a fixed base set. `revoke` **shrinks the
set it runs over**. A traversal that mutates its own base set is not describable with
`over`/`by`.

**That confirms the prediction from `PLAN.md`: `revoke` does not fit into the existing
constructs.**

### Second attempt: as `loop … variant`. **Works, but costs a HAND PROOF**

```gabbro
loop { let leaf = descend_to_leaf(s); delete_leaf(leaf); } variant descendants(s)
```

`variant descendants(s)` is writable. That it **strictly decreases** is not: for that one needs
*"`delete_leaf(l)` with `l ∈ descendants(s)` shrinks `descendants(s)` by exactly 1"* — a lemma
somebody writes down. **That is exactly the outcome that puts 0,5 : 1 out of reach.**

---

### Third attempt: a construct that is MISSING — and then everything falls out

```gabbro
traverse victims over subtree(s) by consuming touches writes slots
{ delete_leaf(it); }        -- `it : linear Member(subtree(s))`
```

**`by consuming`**: the loop variable is a **linear membership witness**, and the body **must**
consume it. Whoever does not consume it does not compile — M2, without a special rule.

| Obligation | how it falls |
|---|---|
| **T** | the set is bounded by `NSLOTS` (M1) and shrinks by at least one per round, because a linear witness is consumed. **No variant per program — the lemma arises ONCE in the generator** |
| **N** | the loop ends when the set is empty. **But**: "witness set empty ⇒ no descendants" is a correspondence that must hold under **every** mutation — **that IS the loop invariant**, moved into the generated ghost theory |
| **I** | `delete_leaf` is a **generated** operation of the `table` construct (cut (c)). The generator shows **once** that unhooking a leaf preserves `child_points_back` and chain finiteness — above the declaration, not per call site |

> **CORRECTION, and it concerns the wording of all three rows.** The first version wrote
> at **T** "no variant, no lemma" and at **I** correctly "the generator shows it once" —
> **the same statement, one wording honest, the other not.** It is **amortisation, not
> elimination**: zero per program, **not zero per construct**. As an absolute statement "no
> lemma" would have been overreach no. 4, in exactly the form `HISTORIE.md` tracks.
>
> **The consequence is architectural:** the **ghost-theory template becomes the most
> trust-critical component of the language** — that is where the structural induction lives, and
> it is checked by the **unverified** Gabbro core. It thereby stands beside the axiom layer, not
> below it.

**And a fourth item falls away that costs lines in the real code:** the branch "subtree is
not tree-shaped" becomes **unreachable**. `subtree(s)` is defined only if the invariant holds;
if it holds, the cycle does not exist. The two step limits, the `note_overrun`, the `break` —
all consequences of the invariant **not** being carried in the Rust code.

---

### The hole in attempt 3: the witness carries MEMBERSHIP, `delete_leaf` needs LEAFNESS

`it : linear Member(subtree(s))` says **"was in the subtree"**. But a slot may be deleted only
if it is **now** a leaf — otherwise its children are orphaned. And leafness **changes with
every deletion**.

**A linear witness that arises when the ghost theory is built cannot carry a mutating property
into the future.** The Rust code has its `descend_to_leaf` **inside** the loop for
exactly this reason; the sketch above silently dropped it. `{ delete_leaf(it); }`
does **not** type this way.

---

### P0.1b — the fourth attempt: where does the order come from, and who preserves it?

**Two ways out, and only one carries.**

#### (B) `delete_leaf` gets a leafness precondition — DISCARDED

Then a **second** witness is needed, and producing it is the descent — hence a
traversal **in the body**, over the same mutating structure. **The entanglement problem from
attempt 1 returns one level lower.**

#### (A) The witnesses come in POST-ORDER — carries, with a sharp condition

In the post-order of a forest it holds: **when the `k`-th witness is up, all its
descendants are the `k-1` previous ones — hence already consumed.** At that moment it *is* a leaf.

| | |
|---|---|
| **Condition** | the body may change the set **exclusively by consumption**. Any other write to `slots` destroys the order. `touches` must be able to express that — today it can only say "writes `slots`", which is too coarse |
| **Costs at runtime** | **none additional.** The post-order is ghost; the product still descends to the left leaf per round — **exactly the existing Rust code.** `by consuming` therefore lowers to `descend_to_leaf` + `delete_leaf` |
| **Costs in the proof** | the lemma *"in post-order the `k`-th element is a leaf after the first `k-1` have been removed"* — **structural induction over the tree** |

> **That puts the original prediction back, only in a different place.** `PLAN.md`
> said: the correctness condition of `revoke` is structural, hence induction. **It has not
> disappeared — it has migrated into the ghost-theory template**, where it arises once instead of
> per program. That is the (c) bargain, and it is real; it is just not magic.

- [ ] **`touches` is too coarse.** It needs a form for "changes the set **only** by
      consumption" — otherwise the order hangs on an assurance instead of on a condition. **That is
      a syntax item that comes from this test and must be decided before canonisation.**

---

### The result, in three sentences

1. **`revoke` is expressible — but not in the constructs `SYNTAX.md` names today.**
   Exactly one is missing: **the consuming traversal**, and it needs **post-order** plus
   a `touches` form that does not yet exist.
2. **With it T, N and I fall to zero per PROGRAM** — not to zero altogether. They arise
   **once in the generator**, as structural induction in the ghost-theory template.
3. **The price is trust, not runtime:** at runtime the construct lowers to the
   existing Rust algorithm. But the **template becomes the most trust-critical component
   of the language**, checked by the unverified core.

---

### The side finding is more important than the result: the COUNTING RULE is broken

The ghost theory has **no runtime effect**. By the counting rule from `PLAN.md` — *specification
is what the compiler deletes before code generation* — it thereby counts **into the numerator**.

> **Then the Gold mechanism worsens the metric the better it works.** Cut (c)
> generates more ghost code, hence more "specification", hence a worse ratio — while
> the work a human does falls.

That is the same class as "a counter that counts ATTEMPTS does not answer the question about
EFFECT". The rule must read:

> **Specification is what a HUMAN writes and what the compiler deletes before code generation.**
> Generated ghost code is neither specification nor code — it is **output**.

**The paper test found this, not the proofreading** — and it cost half a day
instead of the weeks a measurement on the compiler would have cost.

---

### What this does NOT show

* **One body is not a kernel.** `revoke` falls out because its postcondition is *"the set is
  empty"* — a statement about **membership**, and membership is exactly what a
  linear witness carries. The IPC fastpath has a postcondition about **values** (the message
  arrived, the reply obligation lies with the right thread). **Nothing here shows that that one
  falls too.**
* **The 10 % assumption remains unevidenced.** It carries the whole conditional yes and is the
  folder's least supported number — measured is **68,8 % algorithmic remainder**.
* **Cut (c) is thereby empirically supported for the first time**, not merely demanded by the
  goal: without a generated `delete_leaf` obligation **I** falls back to a hand proof.

---

### What follows from it

- [ ] **Admit `by consuming` into `SYNTAX.md`** — with the ghost theory it demands, and
      the open question of which `over` sets can deliver witnesses.
- [ ] **Correct the counting rule in `PLAN.md`** (human-written, not merely deleted).
- [ ] **P0.4 (new): the same test on the IPC fastpath.** It is the case about which `revoke` says
      nothing — and it decides the 10 % assumption, not this one here.


---

# P0.2 and P0.3 — device and space.rs

## P0.2 and P0.3 — both gates FALLEN

**Run on 2026-08-13** by an independent checker, against real Caprock code, on
paper only. Report and artefacts in the session scratchpad (`vtd.gabbro`, `delete_leaf.gabbro`,
`delete_leaf.beweis`). The numbers below I recounted where they carry.

---

### P0.2 — `vtd.rs` as a `device` block. **Fallen, and the reason is the denominator**

The block: **96 declaration lines** (15 registers, 5 `transition`, 2 `reason`, 3 `format`,
3 `assume`). `vtd.rs`: **1 448 lines** without blank lines, of them **577 prose** (recounted).

| Factor against … | Value | Gate ≥ 5 | answers the question … |
|---|---|---|---|
| the **whole file** (1 448) | **15,1** | passed | "how much smaller is a declaration than a file that is mostly something else" — **meaningless for the thesis** |
| what it **covers** (306) | **3,2** | **FALLEN** | the actual question |
| covered **code** without prose (191) | **2,0** | **FALLEN** | the same, sharper |

> **The factor 15 is exactly the artefact the gate was built against.** Whoever reports it measures
> the size of the uncovered remainder and calls it terseness.

**Uncovered: 1 141 of 1 448 lines = 78,9 %** (for the code 78,1 %). The checker split the file into
66 blocks and classified them without gaps, **counted in Gabbro's favour**: ~185 lines of
multi-instance logic, ~150 queued invalidation, ~168 second-level page tables, ~151 IRTE
allocation, ~145 fault bookkeeping, ~330 bring-up.

**An honest Gabbro version of the whole file: ≈ 1 353 lines — factor 1,07.**

**The terseness thesis is thereby refuted in the form in which it stood in the plan.** `device` is
on its own territory twice as terse as Rust, not five times — and its territory is a fifth of the
file. Register layout is the easy part; queues, invalidation and fault bookkeeping are code.

---

### P0.3 — `delete_leaf` twice. **Above the abort mark**

| | Lines |
|---|---|
| Gabbro code | 63 |
| Specification (by the rule: stands in the source, is deleted before code generation) | 71 |
| **Ratio** | **1,13 : 1** (narrow denominator: 1,69 : 1) |

**But the number is a lower bound, and that is the actual finding:** six proof items are
stubs (`{ ... }`). Written out, the ratio lies at **3,6–6 : 1** — **above the
abort mark of 3 : 1**. On top of that: **31 of 134 lines (23 %) are not writable at all today.**

---

### The aggregate — and it disposes of the 10 % assumption

Over **67,3 % of the tree (44 832 lines)**, three pots:

| | Share |
|---|---|
| **(a)** expressible, proof obligation falls out by construction | **15,1 %** |
| **(b)** expressible, needs hand-written specification | **65,1 %** |
| **(c)** not expressible today | **19,8 %** |

`PLAN.md` reckoned with **10 %** needing hand-written functional proofs. Measured it is
**65,1 %** — and the number lands next to the **68,8 %** algorithmic remainder that the same plan
carries itself. **The assumption that carried the whole conditional yes does not hold.**

At 65 % against 5 : 1 the mean does not lie at 0,8 : 1 but **beyond 3 : 1** — hence at the
abort mark.

---

### What that means, without embellishment

1. **Two of the three cheap paper gates have been run, both went against the folder.**
2. **The 0,5 : 1 thesis is dead in the justification it has had so far.** It rested on "10 % need
   a hand proof"; measured it is 65 %.
3. **What survives is smaller and nameable:** on the 15,1 % where the proof obligation falls out
   by construction, it does. That is a real gain — but it is a fifth of the
   kernel, not the kernel.

- [ ] **The abort condition is touched, not triggered** — it demands a measurement on two
      modules in phase P6, not an extrapolation. **But the extrapolation now stands there**, and
      whoever ignores it has chosen the mark after the fact.
- [ ] **P0.4 (IPC fastpath) is thereby no longer the decision but the confirmation.**


---

# P0.4 — the counter-probe

## P0.4 — the counter-probe: one design, one checker, and a hole in the MEASUREMENT PROCEDURE

**Run on 2026-08-13.** One agent designed a complete grammar (1 882 lines), a
second checks it against real Caprock code. Both on paper only. The load-bearing numbers I
re-checked.

---

### The most important find concerns not the language but the metric

> **A metric built from unchecked assurances rewards false assurances — they are short.**

Three pieces of evidence, all in the fragment that carries the designer's number:

| | Find | Site |
|---|---|---|
> **Renamed 2026-08-16: `G1`–`G3` are called `GP1`–`GP3` here now.** The identifiers
> collided with the grammar findings `G1`–`G11` from P2 (`SYNTAX.md`), which denote something
> completely different — there a missing EBNF line, here a wrong `ensures`.
> **Two labelling systems with the same names are the same error class as two
> prose orderings nobody checks against each other** — `GP` for *Gegenpruefung* (counter-check),
> `G` stays with the grammar.

| **GP1** | an `ensures` is **wrong**, not merely unproved: `e.caller is Some(cl) => cl == current_id(...)`. With an open rendezvous A and caller B it claims `A == B` — **re-checked**: the second caller goes into `senders` without touching `caller`. **And it is counted into the numerator** | `crates/caprock-ipc/src/lib.rs:652` |
| **GP2** | `msg_copied` — the **only** functional property of a fastpath — stands in **no** `ensures`. Counted and bound to nothing; `transfer()` has no postcondition at all | — |
| **GP3** | `effects` forgets `locks SCHEDS[owner_core(...)]` on the cross-core path — **by the author of the rule** | — |

**GP3 and the find F12 ("`effects` is fail-open") are the same hole from two sides:** an
omitted effect is **at once the strongest assurance and the shortest specification**. Whoever
measures is rewarded; whoever is complete, punished.

#### What follows from it for the measurement protocol

- [ ] **A metric without a validity check of its assurances is a lower bound with a NAMED
      error direction** — false and incomplete assurances are shorter than correct ones. That
      belongs beside every number, otherwise it reads like a measured value.
- [ ] **Three rules without which nothing is measured:** (1) every counted `ensures` is held
      against the real code; (2) a named property bound to no postcondition does **not**
      count — it is ornament; (3) `effects` is checked against the actual accesses,
      not read.

---

### The numbers

#### The anti-catalogue touchstone: **3 new words, not twelve — passed**

The designer set it himself: *"if twelve come up again at `vtd.rs`, it is a catalogue."*
Against the 14 named gaps of the `vtd` block his grammar needs **three** additional
words: RMW state bits, register bank at a runtime-computed base, conditional compilation
(**335 `cfg(feature)` sites** in the tree, recounted). Everything else falls to `tagged`,
`atomic`, `iasm`, `Queue(T,N)` or parametrisation.

> **The caveat is bigger than the number.** Four of the "0-word" rows are changes to
> `device` — the construct he **leaves unchanged**. Measured: `vtd|iommu|smmu` occurs in
> his 1 882 lines **twice**, `device` as a construct in **zero** of 14 code blocks.
> **Five vocabulary words and five killed traps, without a line of trial** — the finds
> F5 (only single bits), F6 (no runtime offsets) and F8 (`device` does not kill trap 4) survive
> untouched.

#### The ratio, written out instead of claimed

| Example | as a lower bound | **written out** |
|---|---|---|
| `delete_leaf` (checker) | 1,13 : 1 | **3,6–6 : 1** |
| `Endpoint::call` (designer) | 1,15 : 1 | **1,8–2,3 : 1** |

**The lower bounds are almost equal, the written-out ones are not — and the reason is the
finding:** `call`'s postconditions are **value statements over a FIFO**, `delete_leaf`'s are
**structural properties of a mutating tree**.

> **The (b) pot (65,1 %) is TWO-PEAKED, and the expensive peak is called *induction over a
> structure that changes under the proof*.** That is exactly what `by consuming` aims at — this is
> the first independent evidence that the construct hits the right place.

**Weighted over the expressible part: ≈ 2 : 1.** Below the abort mark (3 : 1), **four times
above the goal** (0,5 : 1).

---

### The three re-checks

1. **"M1 is a solver" — CONFIRMED**, and worse than reported. `crates/caprock-sched/src/lib.rs:1996`:
   `let p = (31 - self.bitmap.leading_zeros()) as usize;` needs a flow-sensitive inference —
   and the line **below it**, `self.queues[p]`, additionally needs the **data-structure invariant**.
   **P2's gate "S1a/S1b unformulable with 0 lines of annotation" has thereby turned from a
   decidability question into a heuristics question.**
2. **Quantifier boundary:** six expressions checked, **one** overreach — the self-reported one.
   Beside it an **unreported one of the same class**: `no_orphan_object` carries `runs online` and is
   a predicate **over** an aggregate, which its own rule does not permit.
3. **Lock nestings: number AND direction wrong.** It is **4 of 10** (`docs/invariants.md:36`),
   not 5 of 14 — and all four take a **larger** rank afterwards, hence are nestable by his
   own rule. **The real finding is better than the claimed one:** his
   `locks L { }` block makes nesting cheap and the intended copy-and-release expensive —
   **an incentive gradient against Caprock's explicit rule of thumb**, not an expressiveness gap.

**G5:** the CAS number measures the wrong quantity. Three loops instead of two, two of them in
`konsole.rs` instead of in `caprock-sync` — and the class is **unbounded waiting**, not CAS:
`caprock-sync` alone has **four** such loops, among them the ticket lock itself, and only one
contains a `compare_exchange`. **His verdict thereby becomes stronger, not weaker.**

**Self-correction by the checker:** `ObjectKind` has **13** variants, not 11 — the designer's
number was right, his own too small. **Recounted: 13.**

---

### Where the design fails on real code — reported by the designer himself

**CAS/wait loops: no solution.** `move_cap` is a node rename without a tree construct
(**new B3 candidate, stood on no list**). `install` needs **transactions**, otherwise
between `alloc_object` and `alloc_slot` there exists a state no construct describes.
`Finalized<'a>` needs lifetimes that do not exist. **And the central fastpath property
("may this thread write into this frame?") is a question of AUTHORITY, not of address space —
M1–M4 say nothing about it.**

**One positive find:** virtio `used`/`avail` ownership is phase-dependent and falls out of the
**same** mechanism as the boot phase — **second independent site** for the linear ghost witness.


---

# narrow — measured and withdrawn

## `narrow` measured — the most dangerous open item turns out well

**2026-08-14.** Open item 1 in [`SYNTAX.md`](SYNTAX.md) read: *`narrow` turns a
proof obligation into a runtime check. If it occurs frequently, the criterion is violated —
plumbing would stay with the programmer, only in a different form.* **Measured against 65 001
lines of Caprock.**

*(The three agents that were to check this more broadly failed at the session limit. This here is
the measurement by hand — narrower, but run.)*

---

### Where indices take their bound from — three files, 268 sites

| File | Sites | **bound from the type possible** (`index into …`) | Field | foreign/other |
|---|---|---|---|---|
| `caprock-cap/src/space.rs` (table) | 86 | **75,6 %** | 2,3 % | 22,1 % |
| `caprock-sched/src/lib.rs` (algorithmic) | 156 | **94,9 %** | 2,6 % | 2,6 % |
| `kernel/src/threads/mod.rs` | 25 | 0 % | — | 100 % (constant fields such as `FP_PATTERN[id]`) |

> **The selection bias I checked against did not occur.** I expected that
> `index into` carries only in table files and fails in **algorithmic** code. Measured it is
> the other way round: the scheduler lies at **94,9 %**, higher than the cap space.

---

### The hard class: **4 sites in 65 001 lines**

Flow-sensitive — the range follows from a **previously checked condition**, not from the type:

| | |
|---|---|
| `caprock-sched/src/lib.rs:1996` | `(31 - self.bitmap.leading_zeros())` |
| `crates/caprock-hal/src/cache_decode.rs:68` | `63 - n.leading_zeros()` |
| `kernel/src/colors.rs:864` | `u64::BITS - (n - 1).leading_zeros()` |
| `kernel/src/colors.rs:1052` | `n_lines.trailing_zeros()` |

**All four are the same idiom: a bit position out of a word.** And all four stand
behind a zero check — `dequeue_highest` has two lines above it
`if self.bitmap == 0 { return None; }`.

---

### That makes the statement about M1 more precise — and weaker than feared

The designer reported: *"M1 is called a range type and is a solver."* That is true, **but not in
the generality in which it sounds.** What M1 really needs:

> **Exactly one flow rule: a checked condition narrows the range of the checked quantity in the
> branch afterwards.** After `if x == 0 { return }`, `x : u64 in 1..`.

That is the cheapest form of flow sensitivity and state of the art in every range checker.
**What M1 does NOT need is general inference.** And with this one rule plus a
built-in `highest_bit(x: u64 in 1..) -> u32 in 0..63` the signature carries the range —
**all four sites are thereby writable without `narrow`.**

- [ ] **The most dangerous open item becomes a design decision:** M1 gets the
      narrowing at checked conditions, and the bit-counting intrinsics come with a contract
      instead of raw. **`narrow` stays in the design, but as an emergency exit for the individual
      case — not as the rule.**

---

### What this measurement does NOT show — otherwise it is overreach no. 15

* **The classifier is a heuristic over `x[y]` patterns.** It sees **no** indices that come from
  arithmetic or from a loop counter. The 1 398 variable indexings in the whole
  tree are therefore **not** classified, only 268 of them.
* **"Bound from the type possible" is a statement about the DECLARATION, not a proof.** It
  presupposes that the table carries its fields as `option index into slot`. That this works is
  design; that it carries is unchecked.
* **The second candidate class is unmeasured:** 25 `-=` and 69 `a - b` on potentially
  unsigned quantities. An underflow after a check is the same form as the four above —
  **how many of them are flow-sensitive I do not know.**
* **Three files are not a survey.** `programs/` is practically unmeasured (a single
  site in the checked userspace module).

- [ ] **Classify the 69 subtractions.** That is the next cheap measurement and the
      only one that can still tip the result.

---

# P2 — lexer and parser, run for the first time

## P2 RUN (part 1): the compiler reads, and the gate falls — **1 of 6 fragments**

**2026-08-14.** First line of Rust in this folder. Built for P2 out of the checker plan
([`SPRACHE.md`](SPRACHE.md) part III §6): **lexer, vocabulary, parser over the complete
EBNF**, plus three of the nine checking passes. The tree lies in `crates/`, the command is called
`gabbro`.

> **The ordering rule is violated, and that stands here instead of in a footnote.**
> `TODO.md` says: *"THE NEXT STEP IS NOT A LINE OF RUST"* — first the five
> scratchpad classes, then `19 → 0`. The compiler was begun anyway, on announcement.
> **What that costs is named:** P2 can no longer kill the thesis *before* the compiler is built,
> because the compiler build is already running. What it brings in stands below — the measurement
> was not runnable without a compiler, and it falls against the grammar.

### The gate, in advance and unchanged

> **P2** | lexer+parser over all fragments of the folder | *100 % of the fragments parse; three
> poison fragments fail with a named refusal*

**Result: 1 of 6.** The poison side stands: 26 speech tests, each in both directions; the
prohibition list (`while`, `for`, `goto`, `break`, `continue`, `switch`, `unsafe`, `_ =>`) falls
with a **named** refusal instead of with a follow-on error three tokens later.

| Fragment | Lines | Errors | Class |
|---|---|---|---|
| **F1** cap space | 212 | 1 | vocabulary (`slots`) |
| **F2** VT-d as a `device` | 134 | **0** | — |
| **F3** IPC fastpath | 126 | 1 | vocabulary (`ops`) |
| **F4** virtio transport | 117 | 5 | vocabulary (`next`, `slot`×2, `from`), outdated version |
| **F5** userspace service loop | 92 | 1 | vocabulary (`boot`) |
| **F6** test harness | 110 | 2 (+10 hints) | semicolon, `atomic … publishes` |

Over the whole folder (`FRAGMENTE.md` + the examples in `SYNTAX.md` and `SPRACHE.md`):
**8 of 32 translation units without errors, 1 030 lines of Gabbro.** Eight further blocks are
**excerpts** — they start in the middle of a form and do not count against the gate; the
compiler separates both classes itself, otherwise the percentage would be without a denominator.

### The finding, and it is NOT "the fragments are old"

**Seven of ten errors in `FRAGMENTE.md` are a single class: the closed vocabulary
collides with ordinary kernel naming.** Over the whole folder it is **nine words at
eleven sites**:

| Word | where it collides | Role in the vocabulary |
|---|---|---|
| **`slots`** | `lock CAPS protects { slots, cdt }` (F1, and the same example in `SYNTAX.md` §11) | quantifier domain |
| `ops` | parameter name (F3) | cost unit, `table ops` |
| `next` | register name in the virtio descriptor (F4) | `next <marke>;` |
| `slot` | `let slot = q.AVAIL_IDX % q.n;` (F4, twice) | `slotdecl` |
| `from` | parameter name (F4); `mirrors … from …` (`SYNTAX.md` §14) | `mirrors` |
| `boot` | parameter name (F5) | address space, `bootdecl` |
| `stack` | `step stack = boot_stack_top;` (`SPRACHE.md` §5, boot path) | `entryextra` |
| `check` | `linear ghost type Duty(check);` (`SYNTAX.md` §2, our own example) | `check` block |
| `u64` | `u64::max` (`SYNTAX.md` §2, `SPRACHE.md` §M1) | integer type |

**`slots` is the hardest, because the language generates the name itself.** `slots of c` is one
of the eight domains, `c.slots[s]` stands in every fragment — and the same character string is not
writable as a **place**. The parser admits it after `.` and `->` (no
keyword can stand there, so nothing can be confused) and rejects it everywhere else. **That is
a decision the grammar does not make, and it stands as a decision in the source text.**

**Two ways out, both cost something, neither is chosen here:** make the colliding words
contextual (then the vocabulary is no longer closed, and the table in
`SYNTAX.md` claims more than it holds) — or rename the fragments (then every
user carries the list in his head, and `slots` stays generated **and** forbidden anyway).

### Six holes in the grammar, found by the parser, not by reading

Each of them is a case in which **an example of the specification falls against the EBNF of the
same specification.** The same family as the three errors `pruefe-syntax.sh` found on
2026-08-13 — and the reason why a parser sees more than a guardian over rule names.

| | Site | what is missing |
|---|---|---|
| **G1** | `atomicdecl` (`SYNTAX.md` §11) | **no `publishes`** — the example two lines below uses it, `SPRACHE.md` §11.3 demands it, F6 writes it **eight times**. The parser accepts it and reports `P031` per site |
| **G2** | `axiom` (`SYNTAX.md` §12) | **no `-> typeexpr`, no `requires`** — `axiom rdtscp() -> u64 requires Has(RDTSCP) …` (`SPRACHE.md` part IV) is not writable. Concerns the axiom layer, the *"largest unproved item of the whole language"* |
| **G3** | `placeshift` against `placesuffix` | **ambiguous**: in `transition drv { ST: ACK -> ACK \| DRIVER }` `ACK -> ACK` is at once a transition and a field access. The parser resolves it in favour of the transition — **a decision that belongs in the grammar** |
| **G4** | `entrydecl` (`SYNTAX.md` §1) | `{ ident ":" ident "," }` demands the trailing comma **after every** entry; `regs in { nr: rax, …, a3: r10 }` (`SPRACHE.md` part II) has none |
| **G5** | `path` (`SYNTAX.md`, lexis) | `path = ident { "::" ident }` — **`u64::max` is not a `path`**, because `u64` and `max` are words. Stands in `SYNTAX.md` §2 and `SPRACHE.md` §M1 |
| **G6** | `costexpr`, `format` | **`O` and `version` are terminals no guardian sees**: `pruefe-wortschatz.py` reads only `"[a-z_]…"`, hence not `"O"` (capital) and not `"@version"` (leading `@`). Two words outside the closed table |

**G6 is a finding about the guardian, not about the grammar** — the same blind spot
`SYNTAX.md` already records twice above. The compiler now holds its word list
mechanically against the table (`tests/wortschatz.rs`, in **both** directions, 189/189).

### What is outdated about the fragments themselves — and that is not a grammar finding

* **F4**: `linear ghost type QueueSetup(q : Virtq);` writes `params` into the parentheses;
  `typedecl` demands `typelist` there. The comment «B3» in the fragment claims the opposite — it
  is written against the **second** version, the grammar is at the fourth. `Held(Lock)` is today
  correct.
* **F6**: `let g = f() else (e) { return false; };` — the grammar gives the forms with a block
  **no** closing semicolon. Two sites.

### What this run explicitly does NOT say

* **Six of nine passes are not built** — D1/D2, M1+V1–V3, M3, M2, pairing, costs. `gabbro
  paesse` prints the list together with what stays unchecked with each open pass, and every run
  repeats it beneath the result. **A green run is the absence of the findings three
  passes can see — no more.**
* **No generated C.** The lowering is not begun; the form table (40–60 entries)
  is still unwritten.
* **The parser checks the FORM.** That `effects { pure }` stands there does not mean it is true —
  that is decided by the effects pass, which does not yet exist.

### What is checked against the compiler itself

`forbid(unsafe_code)` stands in the workspace **and** is held by `tests/verfassung.rs`:
every crate must carry `[lints] workspace = true`, every dependency must stand on the named
list (today: **none except our own crates**), and no `.gab` in the compiler tree —
self-hosting is on the prohibition list. **Speech test run:** an `unsafe {}` in
`span.rs` breaks the compilation with `usage of an unsafe block`, then withdrawn.

**31 tests, all green; `pruefe-syntax.sh` and `pruefe-wortschatz.py` unchanged green.**

---

# P3 — M1 and the three flow rules, built and run

## P3 RUN: **the pass reproduces a finding the folder had found by hand**

**2026-08-14, same day as P2.** Built is pass 3 of the pass list: **range types (M1)
together with constant evaluation, V1, V2, V3**, plus an example corpus of **8 clean files
(871 lines)** and **15 poison files (128 lines)**, each with the code it must fall with.

### What the pass finds in our own fragment — and what that is worth

`FRAGMENTE.md` line 248 (fragment F1; the Rust original stands in
`crates/caprock-cap/src/space.rs:1067`): `o.slots[obj].refcount -= 1;`

```
Fehler: [M104] `o.slots[…].refcount` -= verlaesst den Bereich: `u32 in 0 .. 80255`
               gegen `u8 in 1 .. 1`
Fehler: [M101] die Zuweisung verlangt `u32 in 0 .. 80255`, der Wert hat `u32 in -1 .. 80254`
```

That is finding **«B29»**, entered by hand three lines above it, with the justification
*"M1 demands that the result stays in range; but `refcount == 0` falls out only via the
bookkeeping invariant, and that one is, per «B13», not writable at all."*

> **CORRECTED 2026-08-14, on the same day.** The first version of this section called
> it an **"independent rediscovery … without anyone having told it where to
> look"** and gave `space.rs:248` as the site. **Both were wrong:**
>
> * `space.rs:248` is a struct field; the 248 is a **`FRAGMENTE.md` line**, the
>   real Rust site lies at `:1067`. A line number with the wrong file name
>   in front of it is not a site.
> * **"Independent" does not carry.** Exactly this case is the declared motivation of the
>   pass and stands twice as a built-in touchstone: `beispiele/gift/01-unterlauf.gab`
>   names it in its header line, and `typen.rs` carries it as the unit test
>   `subtraktion_faellt_unter_null`. The **line** was not named to the pass, the
>   **form** was. That is a **passed regression test**, and that is worth something —
>   but it is not the evidence I passed it off as.
>
> The counter-check found this (see below), not I. The output block above moreover stood
> there **edited** (`gegen \`1\`` instead of `gegen \`u8 in 1 .. 1\``) — what had fallen away was
> exactly the part that shows the literal `1` being modelled as **u8**, and that is
> the root of a finding of its own.

Over the whole folder: **8 M1 findings under two codes** (4 × `M101`, 4 × `M104`), all in
`FRAGMENTE.md`, none in the examples.

### Two findings that must not be thrown together

| Code | Statement |
|---|---|
| **`M104`** | the value is **not representable on the machine** — the width is gone (`u32 * u32`, `0 - 1` on `u32`) |
| **`M101`** | the value does not fit into the **declared range of its target** (`a + 1` leaves `0 .. GRENZE`) |
| **`M102`** | the denominator does not exclude zero |
| **`M103`** | the index does not fit into the length of its array |

Whoever throws the first two together loses exactly the statement M1 makes: **the range
is an assurance of the declaration, the width a property of the machine.**

### The lesson the corpus forced — and it stood in no document

**A `u64` counter without an upper bound cannot be incremented.** `wert + 1` leaves `u64` if
`wert` may reach up to `2^64-1`; M1 says so at the line. The consequence is a rule that
concerns every kernel line:

> **Every counter needs two things: a bound in the declaration and a check before
> the computation.** `type Zaehlerwert = u64 in 0 .. GRENZE;` alone is not enough — `+ 1` then
> reaches up to `GRENZE + 1`. Only `if w < GRENZE { w = w + 1; }` carries, and V1 makes
> code without runtime cost out of it.

That struck at three sites of our own example corpus before it stood written down.

### A rule that was added — named, not smuggled in

**V1 also holds for the path AFTER a branch that always leaves.**

```gabbro
if a < b { return 0; }
return a - b;                    -- hier gilt a >= b, ohne dass es dasteht
```

The branch ends with `return`; what comes after it is exactly the case `a >= b` — **syntactically
decidable, without a fixed point** (the last statement is `return`/`leave`/`next` or a call
to `never`). Without this rule **every early return** needs a `narrow`, and the
yardstick *"`narrow` ≤ 24 sites"* falls on an idiom instead of on the language.
**It stands as a decision in the source text and here, not as quiet rule growth.**

### The coverage — the number without which a green run says nothing

`gabbro pruefe` prints per file **how many expressions M1 was able to type**:

```
beispiele/08-bereiche.gab: 23 Items, 0 Fehler, 0 Hinweise
  M1 sah 54 Ausdruecke, 0 davon ohne Typ (100 % Deckung)
```

Over the example corpus: **150 expressions, 13 without a type, 91 % coverage** — and **coverage
means "has a type", not "was checked"** (see the counter-check further below; it
found sixteen files with real overflows, fourteen of them with 100 % coverage). The 13 are
`sizeof`/`lenof` (they need the layout, hence the lowering), `old(…)` (ghost expression) and
calls to foreign functions. **Without this number "found nothing" and "looked at nothing"
look the same** — and that is the trap at which a checker becomes worthless.

### What P3 does NOT check

* **Predicates.** `requires`, `ensures`, `invariant` are ghost expressions; M1 sees bodies.
* **Call effects on non-locals.** Every call kills every fact about a place with a
  field or index access. Local quantities remain — Gabbro has **no address operator**,
  so a callee cannot change them. That is the only place at which the pass makes a
  statement about aliasing, and it makes the **conservative** one.
* **`index into T` has no upper bound** — see finding G8 below.

### Two further grammar findings, found while writing the examples

| | Site | what is missing |
|---|---|---|
| **G7** | `entrydecl` | `clobbers { }` is not writable: `identlist` demands at least one name. **An entry that destroys nothing cannot say so.** |
| **G8** | `table` | **a table does not name its slot count.** `index into T` therefore has no upper bound from the declaration; the bound hangs on an index type chosen suitably *by hand* (`type SlotIdx = u32 in 0 ..< NSLOTS`). **M4 — "no unchecked indexing" — rests at this site on a convention, not on the language.** The compiler therefore checks indices only against `[T; N]`, not against tables |

**48 tests, all green** (P2: 25, P3: +23), `pruefe-syntax.sh` and `pruefe-wortschatz.py`
unchanged green.

---

# MEASUREMENT PROTOCOL for the `narrow` full count — IN ADVANCE, before the first counted site

**These rules stand here before a single site had been looked at, and in a
separate commit BEFORE the commit of the count.** The reason is this folder's documented
weakness: **six of nine corrections in [`HISTORIE.md`](HISTORIE.md) were
reinterpretations at a boundary**, and this count has a built-in incentive gradient — every
site assigned to a V rule makes the result better. Whoever sharpens the rules during
the count sharpens them in the convenient direction.

## The bar, unchanged since [`SYNTAX.md`](SYNTAX.md)

> **`narrow` count on the tree: ≤ 24 sites.** If they grow beyond that, the rule set
> V1–V3 is too small — **and *that* is the refutation, not another quiet growth of rules.**

## What is counted — and what explicitly is not

**Counted are the sites at which M1 generates a range obligation and it does NOT fall out of the
operand types:**

| | Class | Reason |
|---|---|---|
| **yes** | subtraction on an unsigned quantity | underflow; the measured class (255 sites, 102 flow-sensitive) |
| **yes** | division and remainder | the denominator must exclude zero |
| **no** | addition and multiplication | in Rust without range types not separable from "fits anyway"; **a number from that would be guessed** |
| **no** | indexing | the bound hangs on `index into T`, and **`table` does not name its slot count** (finding G8). A count would be a statement about a convention, not about the language |

**The omissions are part of the result**, not its small print: the measured number
covers two of four obligation classes.

## The six columns — one sentence each, and no more

| Column | Decision rule |
|---|---|
| **K — by construction** | Both operands are literals or `const`, OR the operation is explicitly handled (`checked_sub`, `saturating_sub`, `wrapping_sub`, `checked_div`). **No obligation, no human.** |
| **V1** | In the same body there stands **before** the site a check of the **checked quantity against a constant** (`if n > 0`, `if n == 0 { return }`, `assert!(n >= 1)`, `while n > 0`), and between check and use there lies **no write** to the quantity. |
| **V2** | The same, but the check sets **the two places of the subtraction against each other** (`if a >= b`, `if a < b { return }`, `assert!(a >= b)`). |
| **V3** | The site stands in a `match` branch, and the value involved is the **binding of that branch**. |
| **F — function boundary** | No check in the body, and **at least one operand is a parameter**. The check therefore lies — if it exists — with the caller. **That is the class that decides whether `requires a >= b` suffices as a contract**, and it does NOT count against the bar. |
| **N — `narrow`** | Everything else: no check, and the operands arise in the body. **Only this column counts against the 24.** |

## The tipping rule — it ALWAYS tips toward N

1. **If a site fits two columns, the more expensive one holds** (N before F before V3 before V2 before V1 before K).
2. **If it is unclear whether there is a write between check and use, it is N.** A fact that
   may have died is not a fact.
3. **If a LOOP BOUNDARY lies between check and site, it is N** — the check stands
   before the loop, the site in its body. Loops carry no facts inward, and that
   is a rule of the language, not a weakness of the counter. **If both stand in the same
   loop body, the check holds normally.**
   > **Corrected 2026-08-14, BEFORE the first counted site and in a separate commit.** The
   > first version read *"if the check lies in a loop that encloses the site"* —
   > that would have tipped every check INSIDE a loop body to N and thereby rendered
   > a rule of the language wrongly. The error came to light while building the classifier,
   > not while counting; **it stands here because a silent correction would be exactly
   > the move this protocol is written against.**
4. **If the check stands AFTER the site, it does not count.**

## The classifier is a heuristic — and it has a speech test

The counter reads Rust **line by line**, not as a tree. It can cut macro bodies, closures and
multi-line conditions wrongly. **It therefore counts as a measuring instrument only if it finds
the sites this folder already knows:**

* `crates/caprock-sched/src/lib.rs:1996` — `31 - self.bitmap.leading_zeros()`, carried in
  [`TODO.md`](../TODO.md) as an open plumbing obligation;
* `kernel/src/colors.rs:864` and `crates/caprock-hal/src/cache_decode.rs:68` — the same
  idiom the earlier measurement found as "four sites, all the same form".

**If it does not find them, the number is invalid** — not imprecise, invalid.

## What makes the measurement INVALID (not merely unfavourable)

1. **The classifier does not find the three speech tests above.**
2. **A rule is changed during the count.** If it changes, counting starts over,
   and the protocol gets a new section with a date.
3. **A site is reclassified by hand without the rule for it standing here.**
4. **The number is reported without the column distribution.** A total without K/V1/V2/V3/F/N
   is not a measured value — it does not say whether the language carries or whether the counter
   is blind.

## The two outcomes, likewise in advance

| | |
|---|---|
| **N ≤ 24** | The rule set V1–V3 carries. `narrow` stays a named exception instead of a ritual. |
| **N > 24** | **Refutation at this point.** The rule set is chosen too small — and the answer is then NOT a fourth rule but the entry in [`HISTORIE.md`](HISTORIE.md). |

And separately from that, without a bar, because nobody could set one in advance:

| | |
|---|---|
| **F = 0** | V facts never die at the function boundary; `requires` as a contract is unnecessary. |
| **F > 0** | **Every one of these sites needs `requires a >= b` at the callee** — and thereby the question from [`TODO.md`](../TODO.md) is answered, not guessed. |

---

# The `narrow` full count — RUN and **INVALID**, with a reason

**2026-08-14.** The protocol stands above, in two commits before this line. The classifier
`zaehle-narrow.py` is built, calibrated and run. **Its result may not be
used**, and the reason is more important than any number it prints.

## What the counter prints — and why it is not a measurement

Over 114 files and 71 061 lines (`kernel/`, `crates/`, `programs/`) it finds
**513 range obligations** (subtraction, division, remainder) and classifies them:

| K | V1 | V2 | V3 | F | **N** |
|---|---|---|---|---|---|
| 269 | 20 | 16 | 0 | 40 | **168** |

**168 against a bar of 24 would be a refutation.** It is **not** reported here,
because a hand sample shows that the number measures the blindness of the counter, not the
language.

## The calibration — four named defects, all repaired BEFORE the count

| | Defect | Effect |
|---|---|---|
| **1** | `pd as usize - 1` — the cast cut the operand down to `usize` | every check on `pd` unfindable |
| **2** | closure parameters (`\|a: u64, b: u64\|`) did not count as parameters | every site in a closure wrongly N instead of F |
| **3** | saturating idioms (`len - frei.min(len)`) | safe by construction, counted as N |
| **4** | **`if c < 2 { return None; }` establishes `c >= 2` afterwards** | the most frequent form in the tree; **the same rule addition the compiler carries as `endet_immer`** — a counter that does not know it measures a DIFFERENT LANGUAGE than the checker |

After all four, N fell from 208 to 168. **Every repair moved the number in the convenient
direction** — and precisely for that reason each one stands here individually.

## The hand sample that kills the procedure

Five N sites outside the bring-up code, looked up by hand:

| Site | Counter | by hand | |
|---|---|---|---|
| `caprock-hal/src/x86_64/acpi.rs:101` | N | **N** | `(root.len() - 36) / entry_size` without a check — a real finding |
| `kernel/src/system.rs:446` | N | **N** | `base - PAGE` without a check |
| `caprock-mem/src/color.rs:131` | N | **K** | `(1u64 << per) - 1` cannot underflow; the counter does not compute the range of `1 << per` |
| `kernel/src/loader.rs:685` | N | **V1** | `(v != 0).then(\|\| … v - 1)` — the check stands in a boolean chain, not in an `if` |
| `kernel/src/system.rs:4088` | N | **F** | `n - aus_datei` with a documented precondition; in Gabbro a `requires`, not a `narrow` |

**Three of five wrong, all in the same direction: too much N.** An error rate of this
size makes 168 a number about the counter.

## The finding is METHODOLOGICAL, and it hits my own protocol

> **The protocol's speech test was too weak.** It demanded that the classifier
> **find three known sites** — that is a statement about **hit rate at three
> sites**, not about **accuracy at 513**. The counter passed it and was nevertheless
> wrong in 60 % of the sample.
>
> **A speech test over three cases cannot accept a classifier over 513.** That is
> the same error as the twice-paid-for blind spot in `pruefe-syntax.sh`: a checker
> that checks one direction and is silent about the other. **Whoever builds a
> measuring instrument next time puts the hand sample INTO THE PROTOCOL — with size and error
> bound, in advance.**

## What would make the count runnable

The three repairs that are still missing are no longer regexes: **range computation over
`1 << x`**, **boolean chains instead of `if`**, **documented preconditions as `F`**. Together
that is exactly **M1 with V1–V3, applied to Rust** — hence the pass that already stands in
`crates/gabbro-check/src/m1.rs`, only for the wrong language.

**From that follows the order, and it connects the two measurements of this day:**

> **The `narrow` count is only precisely runnable once Caprock ranges exist in Gabbro —
> then the compiler counts itself, with the same rule set it checks.** And for that
> the fragments must parse first (today **1 of 6**, gate P2).

## CORRECTION 2026-08-14 — **the bar is not open, it is missed**

The first version of this section closed with *"the bar ≤ 24 therefore stays open"*.
**That is the one place at which this report spared itself**, and the
counter-check found it.

It ran the classifier under **four** readings, among them the one most favourable to the
language that could be built:

| Reading | N |
|---|---|
| most favourable (generous K rule **plus** extended constant recognition) | **150** |
| as reported above | **168** |
| without the undeclared folder restriction | **177** |
| K rule **literally per protocol** (the denominator alone does not suffice there) | **317** |

**The bar is 24. Every reading misses it by a factor of 6 to 13.** The error rate of the
counter — put by three independent samples at 40–60 %, all one-sidedly too much
N — does not nearly suffice to explain that distance. And the opposite direction exonerates:
**0 of 19 drawn K/V1/V2/F sites were in truth N**, so 168 is a hard
**upper bound**, not an estimate around a mean.

> **So it stands:** the number is imprecise, the **verdict** is not. *"The bar
> stays open"* was wrong — correct is: **the bar is missed under every evidenceable
> reading, and by exactly how much is unknown.** Clearing away an uncomfortable number with a
> methodological argument is the same move the measurement protocol above
> is written against — it merely came back in one level higher.

**What that means for the language is not yet settled** and does not belong in this
measurement: whether V1–V3 are too small, whether `narrow` is thought too narrowly, or whether
Rust code checks systematically differently from how Gabbro code could — that is decided only by
the run of the compiler over Gabbro source. **What is settled: the bar does not hold today.**

**What is explicitly NOT measured:** the exact number of `narrow` sites. Whoever
quotes it quotes an uncalibrated counter — **but whoever says the bar is open quotes
nothing at all.**

### Two further protocol breaches, found by the counter-check

* **The script's largest classification rule does not stand in the protocol.** The protocol says
  K = *"**both** operands are literals or `const`"*; for `div`/`rem` the script lets
  the **denominator** suffice. **149 of the 513 obligations hang on it**, and the list of the four
  named calibration defects does not list it — the list that exists for transparency
  omits the largest item.
* **`V3 = 0` is an artefact.** The script's V3 rule fires not a single time over 513 sites;
  `entkerne` eats byte literals (`b'0'`) and leaves phantom operands behind.
  **The bar is set against V1–V3, what was measured is V1–V2.** That alone makes the number
  invalid, independently of any sample.

---

# The counter-check — **16 files that got through and had to fall**

**2026-08-14.** A second Opus-5 run proofread the compiler, the examples, the measurements
and this document, with the explicit brief to **find errors instead of
confirming them**. It set three subagents on it, ran 111 tool calls and
**touched no file in either tree**. What it found is the most valuable
single item of this day.

## The sentence that was wrong — and it stands in the specification, not only in the source text

> [`SPRACHE.md`](SPRACHE.md) §3.2: *"a **fact set** that grows only at the three named
> places and dies at **every write to a place involved**"*

**It was wrong in five independent ways.** The pass reported `0 Fehler` — and in
fourteen of the sixteen cases it added **"100 % coverage"**.

| | What got through | closed |
|---|---|---|
| **U1** | a write **in a sub-block** did not kill the fact of the surrounding block — every `if`, `match`, `locks`, every loop body | **yes** |
| **U2** | `let x = …` inherited the fact of the predecessor it shadowed | **yes** |
| **U3** | the fact about `buf[i]` survived `i = 0` — the place stayed, its index moved away beneath it | **yes** |
| **U4** | `ist_lokal` took `static mut g` for local; its fact died at no call | **yes** |
| **U5** | a call **inside an expression** (`let t = nuller(z);`) killed nothing at all — only the statement form did | **yes** |
| **U6** | `narrow … else { }` installed its range without the branch leaving | **yes** |
| **U7** | `let … else { }` without divergence — the rule from `SYNTAX.md` §7 was check**ed** by no pass | **yes** |
| **U8** | `schiebe_links` returned the **full** range for a possibly negative operand and thereby erased the overflow | **yes** |
| **U9** | **M4 check**ed the index only on **reading**, never on **writing** — the more dangerous direction | **yes** |
| **U10** | a declared `u8 in 200 .. 200` took on the width of the other side; whether a declaration happened to be a point decided whether M1 computes or is silent | **yes** |
| **U11/U12** | signatures and types are keyed by **bare name**: an identically named `fn` or `type` in another module erases the range check | **no — see below** |
| **Q** | the `effects` pass **never sees a body**: `effects { pure }` over a writing function gets through | **no — see below** |

**Ten of them are closed, with one poison file each** that pins them down
(`beispiele/gift/16-…` to `25-…`). Two stay open and now stand in the pass list,
where `gabbro paesse` prints them:

* **Pass 3 (M1) is `TEIL`** — names without module resolution.
* **Pass 8 (`effects`) is `TEIL`** — what is checked is the declaration, never the body.

> **The state `Teilgebaut` is new, and it is the actual yield of this finding.**
> Until today the pass list knew only *built* and *open* — and a pass that checks
> only half reported itself as built. **That was a false green at exactly the place at which
> this folder wants none.**

## Two parser errors, both run

* **`pfeil_ist_suffix` leaked**: a `?` jumped ahead of the restoration, and a typo
  in **one** `transition` made `->` a non-suffix in the **whole rest of the file** — three
  refusals, two of them phantoms on valid lines. Exactly the follow-on error rain the
  statement recovery is supposed to prevent. **Closed.**
* **`publishes`**: the parser accepted `publishes { … }` (which does **not** stand in the EBNF)
  and rejected `publishes place` (which **does**, §11). Doubly wrong, and at `atomic … publishes`
  it even reported the tear itself. **Closed**, both forms work, the brace form says `P032`.

## What the test suite could not do — and what follows from it

> *"There is no test whose failure means 'a real overflow was missed'."*

48 tests, both directions, all green — and sixteen overflows got through. The probes
check **presence of an expected refusal** and **absence of refusals under believed
good behaviour**; none checks whether a hole exists that nobody suspected. The
poison corpus has now grown from 15 to **25**, and the ten new ones are exactly the files
that once got through. **That does not replace the missing kind of test — it merely
collects what one counter-check finds, and the next one finds something else.**

## And the coverage number on which the most hangs

91 % coverage over the example corpus means **"has a type"**, not **"was checked"**.
Fourteen of the sixteen counter-examples reported **100 %**. The number stands in the report to
guarantee that *"found nothing" and "looked at nothing" do not look the same* — **exactly there
they looked the same.** It stays, because it measures something; **but it measures less than its
name promises**, and from now on that stands beside it.


---

# Mutation probe on the checker — **24 of 24**

**2026-08-14.** The counter-check had left behind a sentence that named the actual
gap: *"There is no test whose failure means 'a real overflow was missed'."*
48 probes in both directions were green while sixteen overflows
got through — because a probe checks **the presence of an expected refusal** and not
**whether a rule still bites at all**.

`./mutiere-pruefer.py` asks exactly that question: it damages **one rule at a time** of the
checker, runs the test suite and looks whether something falls.

| | |
|---|---|
| **survived** | **Finding.** This rule could fail without a probe falling — it is unguarded today |
| **caught** | the rule is under observation |
| **invalid** | the mutation does not compile; it does not count |

The source is changed only during a run and afterwards **restored byte-wise against a
hash**, including on abort. The harness has its own speech test: a
**null mutation must survive** (otherwise it measures the file instead of the rule) and a dead
range check **must fall**.

## First run: 21 of 24 — and the three that got through are the interesting ones

| Mutation | Rule |
|---|---|
| `literal-immer` | **U10** — a point range again takes on foreign width |
| `schieben-ohne-vorzeichen` | **U8** — `schiebe_links` forgets the negative operand |
| `v3-tot` | **V3** — the `match` binder no longer carries its payload |

**All three were rules that had been repaired on the same day** — and none had
a test that pins them down. The repairs stood in the source text, the assurance nowhere.
Especially clear at U8: `beispiele/gift/24-schieben-mit-vorzeichen.gab` already falls at the
**upper** corner, so the corpus could not tell "half a rule" from "a whole rule".

Three new probes (`gift/26`, `gift/27`, two unit tests in `typen.rs`) close that —
and the last of them needed two attempts: the rule stands **symmetrically** in the source text,
and a test that touches only one side lets a mutation of the other survive.

**Second run: 24 of 24.**

## What the number does NOT say

**The 24 mutations are written by hand**, one per rule. A generator that systematically
twists all operators and conditions of the checker would find more. **100 % is a
statement about these 24, not about the checker** — exactly as a speech test over three
sites does not accept a classifier over 513. *The same lesson, twice on the same day.*

And the probe covers the **checker**, not the **emission**. The item `README.md`
carries — *mutation probe on the annotation emission* — stays open, because nothing is
emitted yet.


---

# The two partial passes closed — and what the mutation probe found doing it

**2026-08-14.** After the counter-check two passes stood as `Teilgebaut` in the list.
Both are now closed, and the mutation probe catches both repairs.

## Pass 3 — module resolution

Signatures, types and constants were keyed by **bare name**. The
resolution now goes from the own module outwards, then over the `use` lines.

**It catches both directions, and that is the evidence that it is right:**

| Case | before | after |
|---|---|---|
| `zwei::nimm(x)` with `x + 1000` on a full `u32`, beside it a foreign `eins::Eng = u32 in 0..10` | **0 errors** — the foreign narrow type won, M1 stayed silent about a real overflow | 2 errors |
| `eins::nimm(x)` with `x + 1000` on `0 .. 10`, beside it a foreign `zwei::Eng = u32` | **2 errors** — false finding, the path ran at its last segment into a foreign module | 0 errors |

A silent hole **and** a false finding, both out of the same line.

## Pass 8 — `effects` against the body

Up to here the pass checked only the **declaration**: presence, `pure` alone,
`diverges`. The assurance *"`effects` is not fail-open"* thereby enforced a **list, not
its truth** — `effects { pure }` over a writing function got through.

Now **every write** and **every `locks`** must be covered by a declared effect
(`E005`, `E006`); covered means: the declared place is a prefix of the
written one, `writes c.slots` covers `c.slots[s].benutzt`.

**The pass stays `Teilgebaut`, and with a reason** — not out of unfinishedness:

* **Reading is not checked.** `FRAGMENTE.md` reads in every function places that no
  `reads` line names. Whether that is a finding about the fragments or the intended meaning
  of `effects` **is decided by the folder and not by the pass**. A checker that builds an
  unsettled question into its refusals decides it silently.
* **Call effects likewise not.** For that the effects of the callee would have to be mapped
  onto the arguments of the caller. **That is the item that first makes `effects`
  compositional.**

## What the mutation probe said about it

Three new mutations (`rumpf-egal`, `sperre-egal`, `modul-egal`). The third **survived** —
the counter-examples to the module collision lay in the scratchpad, not in the poison corpus. Two
files later: **27 of 27.**

*The same pattern as in the first run: the repair stood in the source text, the assurance
nowhere. Without the mutation probe it would have stayed unnoticed both times.*

**State afterwards: 3 of 9 passes fully built, 1 partial, 5 open.** 50 tests, 32
poison files, five guardians green.


---

# A1 to A4 run — four gates, and three turned out differently from plan

**2026-08-14.** The plan (`PLAN.md` §A) set four items with two-sided gates. All four
have been run.

## A1 — `own` linear: **GREEN on the mechanism question**

Paper test on F1, as the gate demanded, **without a line of checker code beforehand**.

**The place at which it had to fail carries:** `revoke`'s `traverse` body calls
`blatt_loeschen` with two `own` pointers. A linear value would be consumed after the first
pass — **it is borrowed**, because the effect list does not name it under `consumes`.
And that distinction needs **no new word**: `eff` already carries `consumes`, and
`boot_end(t) effects { consumes t }` against `raw fn … requires BootPhase` already makes it.

> **No fifth mechanism.** Separation falls out of M2, as the derivation table in §3b has
> always claimed — the grammar merely has to say so.

**But the second half uncovers something sharper than the gate asked for.** The borrow carries
the *chain*; it has no **origin**. `lock KAPPEN protects { eintraege }` names
**places**, not a linear value; `lockstmt = "locks" place block` has **no binder**;
`static mut` is not linear; and **Gabbro has no address operator**, so nobody can form
a pointer to global state. A `device` has a creation form
(`device Vtd(basis : Pa) at mmio`), a `table` **has none**.

> **The chain therefore stands on a parameter that comes out of nowhere** — and that is a
> finding none of the 31 names. It belongs before every line of the M2 pass.

## A2 — dynamic calls: **the gate falls on "forbid"**

67 `dyn` sites in the core. But the breakdown decides:

| Trait | dynamic sites | **implementations** |
|---|---|---|
| `SchedOps` | 10 | **1** (`KernelSched`) |
| `Park` | 9 | **1** (`Sicht<'_>`) |
| `DmaEnforcer` | 0 | 2 (already uses static dispatch) |
| `FnMut`/`Fn` | ~~89~~ **64** | — (**closures**, see below) · *the 89 has no search path, corrected 2026-08-16, see RESULT* |

**The two traits that are used dynamically have ONE implementation each.** That is
not polymorphism but a layer boundary — the call is statically known, and in
Gabbro the trait object disappears.

> **`fnptr` needs no contract.** The item from «B9» falls away, and the prohibition list
> grows instead of the grammar.

**The rest is a question the plan did not foresee: 64 closures** (*89 stood here; the number had no search path*)**.** Gabbro has
none at all — neither `dyn FnMut` nor `impl FnMut`. What becomes of them (inline, pointer plus
context, or prohibition) is **undecided and new**.

## A3 — `table … count N`: **built, and a finding out of itself**

The index type is now **generated**: `index into T` inherits the bound from `T`'s `count`, and
M4 gets its number for the first time out of the language instead of out of the convention that
somebody writes `type SlotIdx = u32 in 0 ..< NSLOTS` suitably beside it.

**While building it became apparent that half the change would have been worth nothing:**
`index into` was only `slottype`, not `typeexpr` — the generated type could be **named in no
signature**, so a hand-written type would have stood beside it after all. That too is
closed (`indexty` as `typeexpr`; `slottype` becomes shorter rather than longer by it).

## A4 — the cost model: **the gate fell TWICE, in both directions**

**First the implementation was wrong.** It counted `if`, `return` and the loading of
constants in — but §7 names exactly **four** primitives. After the correction the
declared numbers of `08-bereiche.gab` (4, 8, 8) held **exactly**. *The declarations were
right, the calculator was not.*

**Then the declarations were wrong**, at three other places:

| | declared | computed | why |
|---|---|---|---|
| `einsammeln` | 4 096 | **831 488** | traversal over the whole table: NSLOTS × (200 + 3) |
| `scharfschalten` | 64 | **1 032** | contains a `retry … bounded 1024 ops` |
| `faellige_wecken` | 4 096 | **5 120** | NFAEDEN × 5 |

All three I had guessed. **That is the sort of number this folder wrote its
measurement protocol against** — it looked plausible and was never computed.

**The most valuable finding is `K002`:** `04-schleifen.gab` held `PLANER` over a full
traversal — **3 072 ops against `held <= 300`**. And the answer is *not* to raise `held`:
**the lock belongs INSIDE the pass.** On this number hangs the latency statement of
every waiting site (§9.3), and without pass 9 it was a claim.

## What A1–A4 moved together

| | before | after |
|---|---|---|
| passes fully built | 3 of 9 | **4 of 9** (+ costs), 1 partial |
| poison files | 32 | **36** |
| mutations caught | 27 of 27 | **32 of 32** |
| guardians | 5 | 5 |

**And three findings that did not exist before A1–A4:** the missing **origin** of the ownership
chain (A1), the **64 closures** without a form in the language (A2) — *89 stood here, a number without a search path* —, and `costs` on a **recursive**
function, which stays an assumption instead of a computation (A4, named in the pass header).


---

# The origin — and it dissolved instead of being closed

**2026-08-14.** A1 had left behind a finding that stood before every line of the M2 pass: the
ownership chain has no beginning. `lock L protects { … }` names places instead of a linear
value, `locks` has no binder, `static mut` is not linear, and **Gabbro has no
address operator** — nobody can form a pointer to global state.

**The answer is not a new construct but a question nobody had asked
before: does kernel state need a pointer at all?**

## Looked up, not guessed

`kernel/src/system.rs` writes `CAPS.write().cspace` — **one** CapSpace instance, behind
a lock. The `&mut CapSpace` that runs through all Caprock signatures is **Rust's
borrow form**, not the structure of the thing. F1 translated it along because the original had it.

## Two statements, and both cost no word

| | |
|---|---|
| **A `table` IS memory.** Its name is its place: `Kappenraum.slots[s]` is a `place`, `Held(KAPPEN)` the evidence | **one** instance, hence no pointer pair, hence **no aliasing question** |
| **The parameter list of a `device` IS its constructor.** `device Vtd(basis : Pa)` says what a Vtd arises from | the address comes from data (ACPI DMAR), not out of nowhere |

**F1 and F2 are both written out without a single pointer** and go through all five
built passes (`beispiele/09-ohne-zeiger.gab`, 19 items, 0 errors).

## What remains — and only there was separation ever a question

**DMA buffers, allocated regions, foreign memory.** There a function gives ownership away:

```gabbro
extern fn belegen(bytes : u64) -> ptr<normal, rw+own> Region effects { allocs halde };
extern fn freigeben(r : ptr<normal, rw+own> Region)          effects { consumes r };
```

`own` makes the pointer linear; **consumed if `effects` names it under `consumes`,
otherwise borrowed.** No fifth mechanism, no new word, no grammar change.

> **The lesson is not the answer but the question.** The finding read *"the chain
> lacks its beginning"* — and the chain was the problem. It stood there only because a
> Rust original had it. **A fragment that translates its original along brings that
> original's constraints with it, and those then look like requirements of the new language.**
> That hits the other five fragments just as much, and it is one more reason to bring them up
> to date.

**With that the last design item before the M2 pass is gone.** What is missing is only the pass.


---

# The 200 000 counted out — the number on which Gabbro's whole thesis rests

**2026-08-14, measured instead of estimated.** `l4v` at `f4940273` (2026-08-08), shallow clone,
lines in `*.thy`. **One architecture (ARM)**, so that the numbers are comparable: the tree
carries five today, and a total count over `proof/` (861 309) measures the number of
architectures along instead of the proof effort.

| Item | Directory | Lines | Share |
|---|---|---|---|
| **Invariant preservation** over the abstract model | `proof/invariant-abstract` (neutral + ARM) | **76 873** | **32,1 %** |
| **Refinement** abstract → executable | `proof/refine` | **95 915** | **40,1 %** |
| **Refinement** executable → C | `proof/crefine` | **66 670** | **27,8 %** |
| **functional correctness, ARM** | | **239 458** | 100 % |

In addition, **on top and separate**:

| | | |
|---|---|---|
| security theorems (item 5) | `proof/infoflow` + `proof/access-control` | **56 323** = **+23,5 %** |
| C semantics (item 2) | `tools/c-parser` | 86 891 |
| binary verification (item 4) | `tools/asmrefine` | 10 651 |
| abstract specification | `spec/abstract` (neutral + ARM) | 10 280 |
| executable specification | `spec/design` | 7 695 |

> **The confirmed number holds.** `TODO.md` carries "proofs in the `l4v` repo ~200 000" as
> re-checked; measured it is **239 458 for the functional correctness of one
> architecture**. Order of magnitude and cut are right — the number was correct, it was merely
> **unbroken-down**, and the breakdown is what Gabbro's thesis hangs on.

## What the breakdown says for Gabbro — and it says three different things

**Gabbro's argument reads: the refinement falls away because specification and implementation
are the same language.** That is **67,9 %**. But the three thirds behave differently:

| | Share | what Gabbro does with it |
|---|---|---|
| **abstract → executable** | **40,1 %** | **falls away structurally.** One layer instead of two — that is the Low\* arrangement and the most load-bearing part of the thesis |
| **executable → C** | **27,8 %** | **is not proved away but trusted away.** The flat lowering is an assurance; `BEWEIS.md` books `restrict` and `volatile` as trust. Recoverable only via item 4 — and **the tool for it is small** (10 651 lines), the proof is not |
| **invariant preservation** | **32,1 %** | **does NOT fall with the layers.** Amortisable over `table … ops`, but **only where all mutations are generated** — the K condition of the measurement protocol. How many carriers satisfy that has **never been counted** |
| **security theorems** | **+23,5 %** | **not addressed at all** (item 5) |

> **That brings "Gabbro takes the 19,5 : 1 away" into a checkable form:**
> **40 % structurally, 28 % shifted into trust, 32 % remain as invariant work** —
> and the 32 % are exactly the item whose amortisation hangs on a condition
> nobody has measured.

**The metric prediction does not change by this, its justification does:** whoever expects 0,5 : 1
expects the 32 % to amortise completely **and** the 28 % to be trustworthy.
Both are unevidenced today.


---

# The search for further B13-like misjudgements — four found, three classes

**2026-08-14.** The B13 lesson reads: *a verdict "not formulable" can be wrong because it
presupposes the **hand-written** form — the generated one does not need the statement at all.*
All absolute verdicts of the folder have accordingly been gone through and, where possible,
**run against the compiler** instead of judged.

## Class 1 — B13-like: the verdict presupposes handwriting

| | Verdict | the third way out |
|---|---|---|
| **«B7»** | *"`return Completion { id: …, len: … }` is not writable"* — no compound literal in `expr` | **The parameter list of a declaration IS its constructor.** Exactly that was built on 2026-08-14 for `device` (`Vtd(basis)`); a `type Completion = { id, len }` would get `Completion(id, len)` out of **the same mechanism**. The verdict presupposed that a literal must be a **syntactic form** |
| **«B10»** | *"`traverse` returns no value, there is no `break`; the search for the FIRST hit becomes the emptying of the whole set, an operation counter cannot be raised"* | **Two thirds dissolve.** A **generated** search operation (`ops finde`) returns the first hit without `break`; the counter is `accumulates` — **and `accumulates` was itself the third way out for «B21»**. What remains is only that a hand-written search body still does not work |
| **«B26»** | *"`transition reset { DEVICE_STATUS: any -> 0 }` is not writable: there is no placeholder for the prior state"* | A **generated** `reset` operation above the `state` declaration needs no `any` — it is the transition into the initial state, and the declaration already names that |

## Class 2 — plainly wrong: run against the compiler

| | Verdict | run |
|---|---|---|
| **«B12»** | *"`forall i in 0 ..< MSG_WORDS` is not writable: the seven domains do not cover it"* | **`elems of` IS one of the eight domains.** `forall w in elems of msg : w == 0` **parses and goes through all passes.** A numeric-range domain is still missing — but the statement about the message words is writable, and that was exactly the occasion |
| **«B14»** (half) | *"`option` exists only as a `slottype`, not as a `typeexpr`"* | **Came along with A3**, without my noticing: `impl fn f(o : option index into T)` works. *The second half — `let … else` demands a `call` on the right — remains open* |

## Class 3 — real, and explicitly NOT pushed into the third way out

* **«B15» genericity.** `Queue(T, const N)` needs **monomorphisation**, and that is
  [`PLAN.md`](PLAN.md)'s own candidate for *"two demanded properties contradict
  each other"* — it is the first non-flat lowering and attacks M-Gold-2. **Here there is
  no third way out, and to claim one would be the same error as B13, only the other way round.**
* **«B23»/«B20» granularity.** One class per *register* instead of per *field*; `wrapping` at the
  slot type instead of at the register type. That is **missing fineness of the notation**, not a
  generatable form. Honestly open.
* **«B27»** `prim fn` without an `abi` block: a missing construct, not a misjudgement.

## And two stale verdicts

* [`FRAGMENTE.md`](FRAGMENTE.md):62 still says *"`forever` has no exit"* — `leaves`
  has existed since the third version.
* [`BEWEIS.md`](BEWEIS.md):376 says *"W^X remains unformulable"* — `walk` + `mappings of` +
  `embeds` have existed since the specification.

**Both stay standing**, because the folder keeps its refuted versions; the refutation
stands here, not there.

## The lesson, in the form in which it bites next time

> **A verdict "not formulable" is only complete once it says WHICH FORM it
> presupposes.** B13, B7, B10 and B26 all presupposed handwriting and did not say so.
> The check line for it is cheap and mechanical: *would the statement be necessary if the
> operation were generated?* — **and it belongs in the fragment prescription**, next to the four
> check steps that already stand there.
>
> **And it has a second half-clause, without which it lists to one side:**
> *…**and what does the generated form cost the template surface?***
>
> **The third way out is not free — it shifts proof burden onto ONE recipient.**
> `by consuming`, `table ops`, `transset`, `exchange`, `accumulates`, and now the four
> candidates of this re-check: everything falls *"once in the template"*, and the template
> is the most trust-critical unproved surface. **Without a count it grows monotonically and
> unquantified — exactly like the axiom layer before it was counted out.**
>
> **That is why since 2026-08-14 there is the third counting column:** `gabbro schablonen`,
> **16 templates, 16 of them unproved**, each with the sentence saying what exactly has to be
> shown once. An entry without that sentence is a name and not a booking, and a test enforces
> it. **The one Isabelle item is thereby not a number 1 but a list with a length.**

### The limit of this re-check — and it belongs at the measuring point, not in a footnote

**At «B12» and «B14» the evidence given is "parses and goes through all passes".** That is a
legitimate oracle for **writable** — the compiler decides exactly that. **It is no
oracle for "carries".** The built passes check grammar, names, ranges, loop labels,
effects and costs; they do **not check the semantics behind it** — whether `elems of msg` really
quantifies over the message words is decided by no pass but by the meaning of the
domain.

> **Both statements cleanly separated:** «B12» claimed the statement was **not writable** —
> that is refuted. Whether it **carries** is thereby not shown, and **whoever later reads this
> line as evidence for the second inherits a circle:** a young checker would then pass off its
> own incompleteness as confirmation.


---

# The checker as a measuring instrument for the measurements that ought to stand before it

**2026-08-14.** [`HISTORIE.md`](HISTORIE.md) carries the breach of the ordering rule. **A
recorded breach is no licence for the gap to keep widening** — and the more
checker comes into being before the count of 17, the more expensive its unfavourable outcome
becomes and the greater the pressure to reinterpret it.

**The way out is not to stop the tool but to make it serve the queue.**
The K condition of the measurement protocol is mechanically checkable with the existing pass
infrastructure:

> *"Per obligation that is one mechanical question: **are all write sites of the carrier
> generated?**"*

`gabbro k-bedingung <datei>` answers it per carrier — and **delivers the
`breaking` list along the way, hence item L3 of the remainder list**, exactly as the protocol
predicts. The same rule now also exists as a refusal: **`D001`**, since `SPRACHE.md` §10.2 says
anyway *"a hand-written mutation on a `table` with `ops` is a compile error"*.

## The first run, on our own example corpus

```
Traeger      ops    Handschrift  breaking  K
Kappenraum   NEIN   9            0         FAELLT
Objekte      NEIN   2            0         FAELLT
-- 2 Traeger: 0 mal haelt K, 2 mal faellt sie.
```

**Zero of two.** Both tables name no `ops`, both are mutated by hand — **exactly
the situation `FRAGMENTE.md` F1 stands in**, and exactly the reason why «B29» and «B13» looked
lethal there. *The number is thereby not a finding against the language but the first
mechanical entrance into measurement 2* — the column K/A/W per obligation starts here.

**With that the gap closes from the other side**, and the entry in `HISTORIE.md`
gets a yield after the fact instead of only a price.

---

## Two sharpenings on the new registers

**1. The fall direction of the template ratchet now stands written down, and a test holds it:**

> **An entry leaves the list only PROVED or TOGETHER WITH ITS CONSTRUCT** — not
> by rewording, not by merging two entries into one, not by the obligation
> "actually already sitting inside another one". **A surface shrunk by rewriting
> has not become smaller.**

**2. `32 of 32` had the wrong reference quantity.** The honest one is **mutations per
emission surface**:

| Surface | Mutations | |
|---|---|---|
| **checker** (refusals) | **32** | built, mutable |
| **annotation emission** — the wished-for-form channel | **0** | **not built, hence not damageable** |
| **C emission** | **0** | not built |
| **generator templates** | **0** | 16 entries, mostly designed — what is not code catches no mutation |

> **A surface with 0 mutations is not covered but undamageable.** `32 of 32`
> measures the **code half of the checker**; about annotation and emission it says nothing — and
> `README.md` carries the annotation emission explicitly as the place at which a
> consistently weakened generator is caught **by no proof**.


---

# PAPER TEST — group and locks at the CapSpace/CDT pair

**Run 2026-08-14** against `arch/x86_64`. Three questions per protocol, three answers, one
verdict about a candidate construct — and two gaps that were not in the brief.

> **Re-checked, not adopted.** Every site of this protocol has been held against the tree;
> what came up doing so stands marked as *added later*.

## Answer 1 — the connection invariants: three real, four structural, and they are **already formalised**

`audit_cdt` carries the list as anomaly codes 1–7. **K1** (occupied slot → occupied object),
**K2** (`refcount(o)` == number of slots pointing at it — *that is «B13» literally*) and **K3**
(occupied ⟺ `refcount > 0`) are **connection** invariants; K4–K7 are structural.

**The find that changes the template question:**
`Verification/capability-system/proofs/cap_space.rs` (**832 lines, re-checked**) carries exactly
this list as **one** `spec fn cap_inv` (line 56, conjunction of clauses 1–7, in Verus).
The head of the file says the thing itself:

> *"Every capability operation is proved to PRESERVE `cap_inv` — i.e. one operation
> preserves ALL invariants at once (unlike the separate pilot models)."*

**That is the group template, and it already exists by hand.** The entry
`gruppe.ops` thereby has a **model instead of a blank sheet**: the "once per operation" proofs
would be **generated** from the template instead of invented. And the direction of transfer is
evidenced in the tree — at two places the audit oracle was **weaker** than the Verus invariant
and was brought up to it. *The formal version is the source, the audit the projection.*

## Answer 2 — the group already exists as a structure; `by ops` sharpens an existing boundary

**The CDT is not a second table:** `Mdb` (parent/first_child/next_sibling/prev_sibling)
lies **in the slot**. The pair is `{slots, objects}` — both slabs in **one** `CapSpace`, all
mutations methods over `&mut self`, hence over both carriers at once. **Gabbro's
group `ops` gives an existing architecture a grammar, not a new one.**

**The write sites of the critical field, re-checked individually:**

| Site | what | confirmed |
|---|---|---|
| `space.rs:1018` | `refcount: 1` in the compound literal (install) | yes |
| `space.rs:543` | `+= 1` (copy, also used by mint) | yes |
| `space.rs:1067` | `-= 1`, **zero check in :1068 afterwards** | yes — *that is «B29»* |
| *added later* | `object.rs:191` `refcount: 0` in the `EMPTY` default value | no mutation of a living object |

`object.rs:182` carries the field as `pub(crate)`. **Rust's visibility is thereby today's
`by ops` at crate level — the grammar line narrows crate to construct, it does not invent the
boundary.**

> **B13 verdict confirmed on paper:** with group `ops` K2 falls per operation; with `ops` per
> single table it does not. **The group proof rule holds.**

## Answer 3 — the lock imprint: ONE lock, and of a kind the language does not know

`static CAPS: RwSpinLock<Caps>` (`system.rs:732`, rank R0, outermost). Mutations take
`write()` exclusively, **the hot cap resolution takes only `read()`**. The lock imprint of the
group operations is uniform; the question *"one shared or two with an order"* is
answered: **one, by architecture.**

*Added later, because it quantifies L-A:* **33 `CAPS.read()` sites against 44 `CAPS.write()`.**

### The verdict: **`locks ordered` dies**

The check line was whether every repeated acquisition of the same class stands lexically
together. **The answer is stronger: there is not a single repeated acquisition of the same
class.** `system.rs:15` carries it as an invariant — *"no path takes two different `SCHEDS[*]`
at once"* — and migration, the expected test case, works differently:
`SCHEDS[src].lock().migration_candidate()`
(`system.rs:2804`) — **take, select, release**, then the target side with revalidation.

> **Zero test cases — the word does not go into the grammar.** No construct without measured
> need; the same rule that stopped `abi { … }`. **And the paper test has thereby done exactly
> what it was built for: it killed its own candidate instead of confirming it.**

## Two real gaps the test found instead

**L-A — the language knows no shared lock acquisition.** `lock`/`locks` and the `Held` witness
are thought of as **exclusive**. The hottest lock in the tree is a **reader-writer** lock, and
the hot path is the shared side: **33 sites**. Without `locks shared` — *held shared:
reads the protected places, does not write them, **mechanically checkable against the effect set
of the block*** — cap resolution, **the most-travelled path of the kernel, is not
writable.** A first-order construct gap, on no list.

**L-B — handover with revalidation.** The pattern that **replaces** double acquisition: select
under lock A, release, continue under B, **re-check the finding**. The honest version is no
promise of atomicity but a **constraint**: a value that crosses a lock boundary
loses its facts (*the language already does that* — V rules die) **and** the continuation
must re-check the load-bearing condition. Sketch: the selection delivers `ghost Stale(T)`, which
only a fresh check under the new lock turns into a usable `T`.
**Candidate, not a decision.**

## Side findings — and N1 goes to Caprock, not to Gabbro

**N1 — the two documented lock orders contradict each other, and more sharply than
described.** Re-checked:

* `system.rs:11–13`: *"`CAPS` (R0) → `EPS`/… (R1) → `SCHEDS[*]` (R2) → `Heap.inner` (R3) →
  `MEM` (R4, **innermost**)"* — and with it **"`MEM` never holds a further lock"**.
* `system.rs:723`: *"outer→inner: `CAPS` < {`EPS[i]`, `NTFNS[i]`, **`MEM`**} < `SCHEDS[*]` <
  `FP_STATES`"* — **MEM in the middle of a chain that continues**.

Both at once does not work: either MEM is a leaf (header) or it has SCHEDS below it (:723).
**Exactly this error class — two prose orderings nobody checks against each other — makes a
declared `rank` line structurally impossible.** *To be settled with Caprock.*

**N2 — `FP_OWNER` as the "atomic dinghy" of the lock order.** The reschedule path holds
`SCHEDS[core]` "+ atomic `FP_OWNER`" — an atomic that is **explicitly part of the
deadlock derivation**. The boundary drawing *"which atomics are participants in the order"*
belongs in the ordering full count as **a column of its own**.

**N3 — the RwSpinLock observation sharpens the `held` computation.** `held <= K ops` was meant
for **exclusive** holders; on the shared side the quantity to compute is not the hold time
of a reader but the **writer waiting time under reader pressure**. **The latency formula from
§9.3 needs a branch of its own for reader-writer locks** — and the cost pass today computes
only the exclusive case.

## The speech test the test demanded — run

`beispiele/gift/37-b29-unter-ops.gab` writes `zaehler -= 1` by hand on a `table` with
`ops`. **The same line falls twice:**

```
Fehler: [D001] `von_hand_senken` schreibt `Objekte` von Hand, obwohl die Tabelle `ops` nennt
Fehler: [M104] `o.slots[…].zaehler` -= verlaesst den Bereich: `u32 in 0 .. 65535` gegen `1`
```

**The language form and the measurement form at the same site** — `D001` says "the K condition
falls", `M104` is the underflow that made «B13» look lethal. The K-condition report for it:
*1 Traeger, 0 mal haelt K.*

## What became of the paper test — on the same day

`locks ordered` is **struck** (obituary in [HISTORIE.md](HISTORIE.md)). **L-A is
built**, because the assurance is exactly one and falls mechanically: *to hold shared means to
read the protected places and not to write them* — `protects` names them, the body names
its targets, the comparison is the same as at `E006`.

| | |
|---|---|
| Grammar | `locks [shared] place block`, `lock … [shared held <= K ops]`, `effects { locks shared N }` |
| Refusals | `H001` `H002` `H003` `H004` `E007` `K004` |
| Probes | example `10-geteilte-sperre.gab`; poison `38`–`41` |
| Mutations | **+5, all caught** — 37 of 37 on the surface *pruefer* |

**Two numbers instead of one** (side finding N3 is thereby closed): `held` applied to
**exclusive** holders, and the cost pass computed only that one. `shared held` is an assurance
of its own with a check of its own, because the load-bearing quantity on the shared side is a
different one — the **writer waiting time under reader pressure**.

**The dangerous direction has got a code of its own.** `E007` falls when a body takes
exclusively and declares `locks shared`; the reverse is admissible. Whoever holds more than
he promises errs on the safe side — whoever holds less lets the caller build a
latency computation on a concurrency that does not exist.

> **What stays open is the witness at the call boundary** — `requires Held(N)` out of a shared
> block. That is the same asymmetry one level higher and needs the **call graph**:
> exactly the hole on which the call effects already hang in pass 8. *One hole, not two.*

## Correction to the speech-test justification — 2026-08-15

I had reported the B29 cut as standing in **two independently written kernels**.
**Wrong.** `git log --follow` shows `R099` — a rename with 99 % similarity from
`crates/sel4lake-cap/src/space.rs` to `crates/caprock-cap/src/space.rs`, the same
authorship line. The second copy lay outside git, an older snapshot of the same
descent. **Two paths are no evidence of two origins** (`HISTORIE.md`).

**The load-bearing justification is measured instead of inferred.** `git log -L 1060,1075` over
the delete-path region:

| | |
|---|---|
| Origin | `2111f30`, **2026-06-23** — there line 341/342, literally the same order |
| Rebuilds of the region since | **5**, up to `b026c83` (2026-07-29) |
| of them on the release semantics itself | **2** — `Reply-Cap mit Revocation`, `DMA-Teardown-Token` |

The line sequence — `-= 1`, zero check **afterwards** — has survived all five, plus a
package rename and the duplication of the file.

> **B29 is not a slip but an attractor.** Whoever writes the delete path writes
> it this way — even at the fifth rebuild, even after the trap had been paid for once. That
> carries the speech-test obligation better than the refuted independence claim, because it says
> something about **recurrence**, not about spread.

---

# VORAB — Messprotokoll: systematisch erzeugte Mutationen gegen den Pruefer

**Separate commit, BEFORE the run.** After the run nothing in this section is changed;
the result comes below it.

> **Note on the form:** The brief demands the advance protocol in a separate commit
> *and* a git-ignored workshop folder. Both at once does not work — a commit over
> an ignored file is empty. The advance protocol therefore stands **here**, where the advance
> protocols of this folder have always stood (as already at measurement 2), and the workshop
> version points to it. *The rule is the immutability after the run, not the folder.*

## What is measured

A generator **systematically** twists one site at a time in `crates/gabbro-check/src/*.rs` —
in contrast to the 38 mutations chosen **by hand**, each of which hits a rule
I had in my head while writing. *That is exactly the suspicion: `38 of 38` is a statement
about the 38 sites that occurred to me.*

| Class | Twist |
|---|---|
| `VERGL` | flip a comparison operator (`>` ↔ `>=`, `<` ↔ `<=`, `==` ↔ `!=`) |
| `BOOL` | `&&` ↔ `\|\|` |
| `NEG` | negate a condition |
| `KONST` | shift an integer literal by 1 |
| `LEER` | skip a loop body |

## Counting rule

* **A mutant counts only if it COMPILES.** If `cargo build` breaks, it is **invalid**
  and falls out of numerator **and** denominator. *A coverage number counts evidence, not
  attempts* (`WERKZEUGKASTEN.md` W1).
* **Caught** = `cargo test` falls **or** a poison probe loses its code **or** a
  clean example gets a refusal.
* **Escaped** = all probes stay green.
* The 38 hand mutations are carried **separately** and not counted in.

## Tipping rule

If the probe hangs or breaks (time limit 120 s), the mutant counts as **invalid**, not
as caught. **Borderline cases tip into the more expensive column, are never split.**

## The two-sided gate

| | |
|---|---|
| **passed** | **at least one escaped mutant** that the 38 hand mutations do not find — then `38 of 38` is unmasked as a statement about 38 sites |
| **fallen** | **not a single one escapes** — then the checker is as tight at the generated sites as at the chosen ones. **That is a result, not a failure.** |
| **invalid** | **fewer than 30 mutants compile** — then the run measures the generator, not the checker |

## What the run explicitly does NOT say

Nothing about the emission surfaces. Annotation, code and template still have **0
mutations** — and what has 0 mutations is not covered but **undamageable**.

## RESULT of the run — 2026-08-15, sample 40 of 377 sites

**The gate is PASSED, and clearly.** The number fixed in advance:

| | |
|---|---|
| mutable sites found | **377** in 13 files |
| drawn (deterministic, fixed seed) | **40** |
| **caught** | **7** |
| **escaped** | **32** |
| invalid (does not compile) | **1** — out of numerator **and** denominator |
| **rate** | **7 of 39 = 18 %** |

Against `38 of 38 = 100 %` of the hand mutations. **`38 of 38` was a statement about 38
sites that occurred to me while writing — not about the checker.** That stood
exactly as a suspicion in the TODO, and it is now quantified.

### The breakdown of the 32 — AFTER THE FACT, and therefore carried separately

**The 18 % above stand and are not touched** (R2). What follows here is a
*classification afterwards*, not a recomputation — it says **what** escaped, not how many.

| | Class | what it means |
|---:|---|---|
| **15** | **RULE** | real gap: the site could fail without a probe falling |
| 4 | message text / documentation | a twisted site reference is not a rule violation |
| 3 | test body | measures the probe, not the rule — **filter gap of the generator** |

**The three test bodies and the four message texts are a finding about the generator**, not
about the checker: its `BLIND` filter recognises comments and long strings, but not
`#[cfg(test)]` regions and not multi-line messages. *That too belongs reported — a
measuring instrument whose rejects one does not know delivers not a number but an impression.*

### The fifteen real gaps

```
typen.rs:277  [VERGL]  if a.min >= 0 && b.min > 0 {
typen.rs:317  [BOOL]   if a.min < 0 || b.min < 0 {
typen.rs:343  [KONST]  if bits >= 127 {
typen.rs:346  [KONST]  (1i128 << bits) - 1
typen.rs:352  [VERGL]  if b.min < 0 || b.max >= a.breite as i128 {
typen.rs:257  [KONST]  let min = ecken.iter().copied().min().unwrap_or(0);
umgebung.rs:121 [VERGL] if z.rsplit("::").next() == Some(kurz) {
umgebung.rs:438 [BOOL]  BinOp::Und => i128::from(x != 0 && y != 0),
umgebung.rs:439 [BOOL]  BinOp::Oder => i128::from(x != 0 || y != 0),
umgebung.rs:439 [KONST] (dieselbe Zeile, andere Verdrehung)
umgebung.rs:543 [KONST] .unwrap_or_else(|| IntBereich::voll(32, false));
kosten.rs:244 [KONST]   XForm::Update { rumpf, .. } => Kosten::Zahl(1).plus(…)
kosten.rs:248 [KONST]   Kosten::Zahl(1).plus(self.ruf(&l.ruf)).plus(self.block(&l.sonst))
kbedingung.rs:194 [KONST] let (mut haelt, mut faellt) = (0, 0);
schablonen.rs:270 [KONST] n + 1,
```

**The pattern is readable, and it is not accidental:** the gaps cluster in
`typen.rs` (**6**) and `umgebung.rs` (**5**) — the **range arithmetic** and the
**constant evaluation**. Both are layers no example addresses directly: the
examples check whether a refusal falls, not whether a bound is **exactly** right. An example
with `u8 in 0 .. 200` falls out the same way for every wrong upper bound between 200 and 255.

> **The actual finding is therefore not "82 % escaped" but WHERE they escape:** the
> checker is tight at the places at which it **generates refusals**, and thin at those at
> which it **computes**. The hand mutations aimed at the refusals, because refusals are
> what one has in one's head while writing.

**What follows from it and what does NOT.** It follows: the range arithmetic needs probes that
hit **bounds** instead of classes — value tables, not example files. It does **not** follow
that the checker is worse at the 38 measured rules than reported; that number stands
unchanged and continues to measure what it measures.

---

# GATE P2 IS REACHED — 6 of 6, on 2026-08-15

**For the first time the entire fragment corpus parses against today's grammar** — 791 lines
of Gabbro in six translation units, zero refusals.

| State | units clean |
|---|---|
| 2026-08-14 (run 1, before all repairs) | **1 of 6** (17 %) |
| after wave 0/1 | 1 of 6 |
| after `M-woerter` (provisional, R12) | 2 of 6 |
| after the semantic follow-ups | **6 of 6 (100 %)** |

## What the gate cost — and who had the errors

**Four of them were errors in the CHECKER, not in the corpus.** That is the actual yield:

| | Finding | Class |
|---|---|---|
| `E005` | took **local names** for effects — a function that only counts could not be `pure` | too strict |
| `S002` | `endet_immer` knew **no calls** — a block ending on `exit();` counted as falling through, although `exit` diverges | too strict |
| `queue` domain | had **no bound**, although it is unambiguously derivable: the compound of a queue carries **exactly one** field array | gap |
| `Some`/`None` | `option index into T` had **no constructor**. The stock has always written `Some(x)` — in `match` patterns, in expressions, **and in `SPRACHE.md`:381 itself**; the grammar knew it at none of the three places | gap |

In addition two dead words of the same class: **`Self` stood in the vocabulary table and in no
production** — the guardian never saw it, because its terminal regex read only lower-case letters.
*Third find of this kind in one day.*

## And two findings about the CORPUS that carry an order of magnitude

**«B34» — `revoke` promised `<= 200 ops`; the body costs 16 452 480.** Five
orders of magnitude. The 200 were no typo but the **typical** case; `costs` is
however a **bound**. It became visible only once `CapSpace` named its slot count
(`count NSLOTS`) — before that the pass could not bound the domain and said so
(`K003`), instead of estimating. **Second occurrence of the same confusion** (A4: 4 096
promised, 831 488 computed).

> **What the kernel really does is thereby not in the line:** Caprock bounds `revoke`
> over the **CDT depth**, not over the table size. That bound is today **not expressible**
> in Gabbro — `descendants of` inherits the table. *That is the finding, not the
> number.*

**«B32» — `wrapping` stands at the slot, not at the register.** virtio's `AVAIL_IDX` wraps
**by design**; `slottype = intty "wrapping"` (SYNTAX.md:500) can say that, `regdecl`
cannot. **The most frequent case in a device driver cannot state its intent.**

**«B33»** — the V rules do not narrow the type of a **register place** after
`if … == N { return; }`; only `narrow` carries the fact. Whether that is intent (a register can
change between check and computation!) or a gap is decided by the folder. **If it is
intent, the justification belongs written down — it would be a strong argument.**

## «B29» is resolved, and at the language

The original wrote `refcount -= 1;` and checked for zero **afterwards**, with the argument that
the bookkeeping invariant was, per «B13», not writable. **Both are true and neither
helped** — for `narrow … else` demands no invariant but a **check**:

```gabbro
narrow o.slots[obj].refcount to 1 .. 80255 else {
    return Fehler::Buchfuehrung;
}
o.slots[obj].refcount -= 1;
```

**That is the difference between one net and two:** the invariant remains the reason
why the `else` branch is never taken; the type remains the reason why it **must stand there**.

## The methodological lesson, and it is expensively paid for

> **A refusal list behind a parser error is not a measurement but a LOWER
> BOUND.**

The vocabulary collisions were first 6, then 7, after the renaming **14** — every closed
site lets the parser run further and find more. `memos/M-woerter.md` named 6; the number
stood behind two desynchronisations. **And I walked into the same trap after having
noted it down:** line 873 was not a collision but a follow-on error — I renamed a real
keyword and had to withdraw it.

---

# VORAB — Messprotokoll: die `narrow`-Zaehlung ueber GABBRO-Quelltext

**Separate commit, BEFORE the count.** After the run nothing in this section is changed.

## Prior history, in one sentence
The count over **Rust** was **invalid** on 2026-08-14 (classifier error 40–60 %), and
the verdict read: *the number is imprecise, the verdict is not* — N = 150…317 against a bar
of 24. The count became runnable only with gate P2 (6 of 6, 2026-08-15).

## What is counted

**The range obligations that need an EXPLICIT discharge** — hence exactly the places at
which the writer has to write down `narrow … to … else { … }`, because neither the type nor the
V rules carry the proof.

**Mechanically, without a classifier:**

1. **Remove** all `narrow` statements from the fragment corpus.
2. Run `gabbro pruefe` and count the refusals `M101`/`M104`.
3. **That number is N** — every such refusal is a site that does not compile without
   `narrow`.

*The classifier the first count died on thereby falls away without replacement: it is not a
script that decides what a range obligation is but the pass that checks it.*

## Counting rule

* What is counted are **sites**, not refusals: `M101` and `M104` at the same line are
  **one** obligation (the pass reports range and width separately).
* A site in a **comment** or in a removed `narrow` line itself does not
  count.
* **R16:** if the parser aborts anywhere, the number is a **lower bound** and is carried as
  "≥ n, abort at X", not as n. Gate P2 stands at 6 of 6 — it may **not** fall when the
  `narrow` are removed; if it falls, the run is invalid.

## Hand sample — size and error bound IN ADVANCE

* **n = 20** sites, stratified over the six units (at least one per unit,
  the rest proportional to the line count). If there are fewer than 20 sites, **every** one is
  checked and the size reported.
* Decided by hand: *is a proof really needed at this site, or does the value
  demonstrably lie in range?*
* **Error bound: at most 1 error in the sample.** At 2 or more the count is
  **invalid** — carried separately from "missed".

## Extrapolation, and its limit

The corpus is **791 lines of Gabbro** against **75 294 lines of Rust** in the core (`a1bf707`,
139 files). An extrapolation over that factor **is reported but not carried as a measured
value** — the six fragments are chosen by their difficulty, not at random, and
are thereby **no representative cut**. The density stands there as a density.

## The two-sided gate

| | |
|---|---|
| **passed** | the measured density carries an extrapolation **≤ 24** for the whole core |
| **missed** | it carries an extrapolation **> 24** |
| **invalid** | ≥ 2 errors in the hand sample · **or** gate P2 falls when the `narrow` are removed · **or** the parser aborts (then: lower bound, R16) |

**The bar is not moved.** It stood at 24 and stands at 24.

## R14 — the harness first proves that it can measure

Before the first number:
1. **A build abort is distinguishable from a hit.** The counting tool aborts visibly
   if `gabbro pruefe` does not run at all — it does **not** then count zero.
2. **The number demonstrably hangs on the subject.** Probe: put **one** `narrow` back in;
   N must **fall by exactly one**. If it does not, the run measures something else.

## RESULT of the `narrow` count — 2026-08-15

**N = 2** range obligations in 791 lines of Gabbro, six translation units.

| | |
|---|---|
| removed `narrow` statements | 2 |
| gate P2 without them | **4 of 6** — it falls, so the run measures something |
| **N (sites)** | **2** |
| density | **2,5 per 1000 lines** |
| R14 self-probe | **passed** — 2 removed `narrow` → exactly 2 additional obligations |

## Hand check — n = 2, hence EVERY one (advance protocol: "fewer than 20 ⇒ every one, report the size")

| Site | Verdict |
|---|---|
| `space.rs` fragment, `refcount -= 1` | **real obligation.** `u32 in 0 .. 80255`, and the underflow is «B29» itself |
| `kstackmark` fragment, `i += 1` | **NOT a real obligation** — the traversal runs over `s.worte` and bounds `i`; **M1 does not see that.** A checker limit, not a language obligation |

**1 error in the sample.** The bound fixed in advance was "at most 1" — the
count is thereby **valid**, and **narrowly** so.

> **The finding behind the finding:** half of the measured obligations are a
> **checker limitation**, not a language obligation. At n = 2 that is not a rate but
> a hint — but it is **the same hint the invalid Rust count gave**
> (classifier error 40–60 %, all in the same direction). *Twice in a row the hand
> probe points in the same direction: the raw number is too HIGH.*

## The gate — **missed by the letter, and the protocol was contradictory**

Extrapolated to 75 294 lines of core: **2 / 791 × 75 294 ≈ 190**. Against a bar of 24
that is missed by a factor of **eight**; subtracting the checker limitation leaves
**≈ 95**, hence factor **four**.

**And here a finding about my own advance protocol arises.** It says both:

> *"passed: the measured density carries an extrapolation ≤ 24"*
>
> *"The extrapolation is reported but **not carried as a measured value** — the six
> fragments are chosen by their difficulty, not at random."*

**I hung the gate on a quantity that the same protocol declares to be non-measuring.**
By **R2** a gate is not adjusted after the run — so it stands: **missed**,
together with the finding that the basis for the decision is, by our own protocol, none.
*A gate that rests on a declared non-measurement is a construction error of the
protocol, and it belongs reported rather than repaired.*

**What is settled nevertheless and is worth more than the gate:**

* The count has been **run for the first time without a classifier** — it is not a script
  that decides what a range obligation is but the pass that checks it. *That is exactly what
  the first count had died of.*
* **N = 2 over 791 lines is something completely different from the 150…317 of the Rust
  count** — and the difference is no measurement error but the **thing itself**: the Rust count
  counted *all* range obligations; Gabbro's types and V rules carry most of them **without**
  a `narrow` line. What is counted here is only what needs the **emergency exit**.
* **The next count needs n, not care.** With two sites every single hand probe
  decides 50 % of the result. The four missing area fragments
  (scheduler, MMU, loader, parser) are the measurement basis, not a side point.

---

# BASISRATE — "How many formats does Caprock really have, how often do they change, how many errors of this class per year?" (TODO.md:480)

**Run 2026-08-15** against `../caprock-messbasis` @ `a1bf707`.
The TODO entry names the most honest possible result itself: *"If it comes out small,
the most honest result is 'the trap is too rare for a language'."*

## The numbers

| Quantity | Search path | Result |
|---|---|---|
| formats in the tree | `grep -rn "#\[repr(C)\]" --include=*.rs` | **5** |
| of them named | `MemRegion`, `HandoverInfo`, `TrapFrame` (+2) | 3 readable |
| commits that touch a `repr(C)` struct | `git log --all -S"repr(C)" -- '*.rs'` | **5** |
| observation period | `git log` first/last commit | **2026-06-23 to 2026-08-14 — 53 days** |
| entries in `done.md` | `grep -cE "^#{2,3} "` | 234 |
| **errors of this class in `done.md`** | patterns for wrong offsets, field order, swapped byte order, layout errors | **0 as an occurred error** |

## The only near miss, and it is instructive

`done.md:1745-1750` describes the virtio header size: **12 bytes** under `VIRTIO_F_VERSION_1`,
10 in the legacy version.

> *"Whoever inserts it shifts every received frame by two bytes and finds the
> ethertype in the wrong place — an error that looks like 'the other side does not
> answer'."*

**That is the trap in pure form** — and it stands there as **avoided**, not as paid for.
The text is a warning, not an obituary.

## Verdict — and it goes against the folder

**Extrapolated: 5 format changes in 53 days ≈ 34 a year; errors of this class: 0.**

> **The base rate does not carry `format`.** Five formats, zero occurred errors of the
> class, one documented near miss that an attentive comment caught.

**What that does NOT mean.** It does not mean that `format` is useless — the near miss shows
that the class is real and that its detection today hangs on **attention**. It means:
**this measurement does not justify `format`**, and whoever wants to justify it needs an
argument other than the error frequency in this tree.

**And the honest limitation to it:** 53 days are a short period, and `done.md` is
a **curated** document — it carries what the author thought worth reporting. An error
found and fixed in five minutes does not stand there. **The zero is a zero in
`done.md`, not a zero in the tree.**

## Check path
```
cd ../caprock-messbasis
grep -rn "#\[repr(C)\]" --include=*.rs . | wc -l          # 5
git log --oneline --all -S"repr(C)" -- '*.rs' | wc -l      # 5
git log --format=%ad --date=short | tail -1                # 2026-06-23
sed -n '1745,1750p' done.md                                # der Beinahe-Fall
```

---

# `programs/` — the repetition, 2026-08-15

> *"`programs/` broke 4 of 4 — but the measurement is **older than the constructs** that
> concern it (`leaves`, `transition publishes`). Unchecked whether it carries today."*
> (`TODO.md`:56)

Measured against `../caprock-messbasis` @ `a1bf707`: **9 Rust files, 1 778 lines** in four
groups.

## What broke the old measurement — and whether it still breaks today

The break was **`loop { … break … }`**: the grammar of the second version had neither
`leave` nor `break`, and a service loop was thereby **not writable**. Exactly that is what
`forever … leaves`/`leave` closed.

| Program | Lines | endless loops | `break` | `dyn`/`Box` |
|---|---:|---:|---:|---:|
| `hardware/virtio-blk` | 426 | 2 | **2** | 0 |
| `trusted/fs` | 365 | 3 | **5** | 0 |
| `trusted/init` | 119 | 1 | 0 | 0 |
| `userland/hello` | 25 | 0 | 0 | 0 |
| **total** | **935** (4 of 9 files) | **6** | **7** | **0** |

**All seven `break` sit in a named loop** and are thereby `leave <marke>` —
the construct that has stood since the third version. **The measured break is closed.**

**And the second candidate falls away as well:** *zero* `dyn Fn`/`Box` in the four
programs. The 47 closure sites of the tree (`memos/M-verschluesse.md`) lie
**entirely in the core**, not in the programs.

## Verdict — **partly lifted, not lifted**

> **The measured reason for the break no longer carries.** Whether `programs/` *gets through*
> today this measurement does **not** say — for that the four programs would have to be
> written out in Gabbro, and that is a fragment brief, not a counting brief.

**What this measurement achieves:** it takes the basis away from the entry "4 of 4 broken" and
says **what takes its place** — an open question instead of a measured no.
*A finding whose reason has fallen away is no longer a finding; it is an unasked
question.*

## Check path
```
cd ../caprock-messbasis
find programs -name "*.rs" | wc -l                                  # 9
grep -rcE "\bbreak\b" programs/hardware/virtio-blk/src/*.rs        # 2
grep -rn "dyn Fn|Box<" programs/ --include=*.rs | wc -l             # 0
```

---

# Die aarch64-Luecke — why a number is missing and not merely unmeasured

**Entered 2026-08-15.** Several items of the folder demand a **second architecture**:
the axiom layer ("how many axioms does an x86 **and** an aarch64 kernel need"), the
eager-FP decision, and implicitly every statement about transferability.

## What is there

| Tree | what it is |
|---|---|
| `SEL4Lake/SEL4Lake` @ `arch/x86_64` | the measured core. **139 files, 75 294 lines.** In git, commit `a1bf707` |
| `SEL4Lake/ARMTest/stm32mp25-kernel` | **not a second kernel** |

## The proof

```
$ git log --follow --name-status -- crates/caprock-cap/src/space.rs
R099   crates/sel4lake-cap/src/space.rs -> crates/caprock-cap/src/space.rs
```

**`R099` — a rename with 99 % similarity.** The ARM tree carries the package names from
**before** that rename (`sel4lake-cap`), lies outside git and is thereby an
**older snapshot of the same descent**. The same authorship line, the same file.

## Why that does not merely make the number imprecise but wrong

An axiom table from both trees would show **agreement** — and that
agreement would be no finding about architectures but about **copying**. It
would answer exactly the question nobody asked.

> **And it erred in the flattering direction.** "The axiom layer carries across
> architectures" is the statement the folder would like to have. *Precisely for that reason it
> is the one at which one has to look twice* — and precisely this move (inferring
> origin from surface similarity) has stood since 2026-08-15 in
> [`HISTORIE.md`](HISTORIE.md) as a paid-for error.

## The honest version, until a second tree exists

> *"Measured for x86. For aarch64 no number stands, and the existing tree cannot
> deliver one — it is the same kernel in an older version."*

**What unblocks the item:** an aarch64 kernel with a descent of its own. Nothing else — no
tool, no care, no second attempt on the same tree.

## Check path
```
cd ../caprock-messbasis
git log --follow --name-status -- crates/caprock-cap/src/space.rs | grep '^R'
ls ../SEL4Lake/ARMTest/stm32mp25-kernel/crates/     # traegt die Namen VOR der Umbenennung
cd ../SEL4Lake/ARMTest/stm32mp25-kernel && git rev-parse --show-toplevel   # scheitert: kein git
```

---

# IN ADVANCE — Neuerhebung of the plumbing classes against x86

**Separate commit, BEFORE the survey.** After the run nothing here is changed.
Measurement base: `../caprock-messbasis` = `SEL4Lake/SEL4Lake` @ `arch/x86_64`, `a1bf707`.
**Explicitly x86 only** — the aarch64 side is blocked, see *Die aarch64-Luecke*.

## Why fresh and not reconstructed

Five of the eleven classes lay only in the scratchpad and are **not reconstructible** — not even
their **names**: the six documented ones are named, the five remaining ones only as "the
remaining five". **A measurement whose subject can no longer be named is
not half present but not present at all.**

Therefore **all eleven** are surveyed afresh. The result is called **N_neu** and is with the 19
**not comparable** — it replaces them, it does not continue them.

> **Marking that must run along in every later citation:
> "newly surveyed 2026-08-15, not reconstructed; x86 only."**

## The eleven classes — the stock names them (`README.md`:13)

Index · Overflow · Alias · Frame · Lock · Race · Termination · Phase · Leafness ·
Publication · Refinement

## What is counted, per class

**Two numbers, strictly separated:**

1. **Sites** — mechanically, with the search path beside it. That is the **size** of the class.
2. **Does the class hang?** — does a *present-day* construct carry it **by construction**, or
   does human work remain? The answer is **a construct name or a named gap**, never
   "presumably".

**N_neu = the number of classes that hang.** Not the number of sites — a class with
40 000 index accesses and a carrying construct does **not** hang.

## Tipping rule

* If a construct carries a class **only partly**, the class counts as **hanging** and
  the covered part is named. *Borderline cases into the more expensive column.*
* If a class is **not findable** in the x86 tree (zero sites), it counts **not as
  covered** but as **not measured** — carried separately.
* **R16:** if a search path aborts, its number is a lower bound and is called so.

## The two-sided gate

| | |
|---|---|
| **passed** | **N_neu = 0** — every one of the eleven classes is carried by a named construct |
| **missed** | **N_neu > 0**, with class, site and named gap per item |
| **invalid** | a class cannot be sought mechanically **and** cannot be decided by hand — then the criterion is missing, not the answer |

**The gate is NOT "19 → 0".** The 19 are not reconstructible; a gate on a number
that nobody can evidence any more would be trap 80 in pure form. **The new gate is `N_neu → 0`,
and N_neu is determined for the first time in this run.**

## R14 — the harness first

Before the first number: every search path is **run once against a site I know
exists** (e.g. `refcount -= 1` for overflow, `CAPS.write()` for lock).
If it does not find it, it does not measure what it claims.

## RESULT of the Neuerhebung — 2026-08-15, **x86 only**

**Marking that has to run along: newly surveyed, not reconstructed.**
The 19 from the old count are **replaced, not continued** — their subject was
no longer nameable.

### R14 — the search paths find their known sites

`refcount -= 1` → 1 · `CAPS.write()` → 45 · `self.slots[slot]` → 15 · atomics → 704 ·
loops → 276. **All five probes hit.**

### The eleven classes

| # | Class | Sites | does a construct carry it? |
|---:|---|---:|---|
| 1 | **Index** | 2 143 | **yes** — `index into T` inherits the bound from `count N` (A3), `M103` checks |
| 2 | **Overflow** | 1 758 | **yes** — M1 range types, `M101`/`M104`; the intended wraparound has been sayable at the slot **and** at the register since «B32» |
| 3 | **Alias** | 628 | **yes** — dissolved instead of closed: kernel state needs no pointer (A1); where it does, `own` makes it linear |
| 4 | **Frame** | 296 | **HANGS — half.** `effects` checks **writes** and `locks` (`E005`/`E006`/`E007`), **not reads and not call effects** |
| 5 | **Lock** | 419 | **yes** — `lock … rank … held`, `locks`/`locks shared`, `K002`/`K004`, `H001`–`H005` |
| 6 | **Race** | 2 276 | **HANGS.** The pairing pass (P6) is **not built**; `publishes`/`awaits` are not set against each other |
| 7 | **Termination** | 276 | **yes** — three loop forms, `bounded`/`on_exceeded`/`progress`, `M4`; `forever` is permitted and named |
| 8 | **Phase** | **1** | **HANGS — and the class is almost empty in the tree** (see below) |
| 9 | **Leafness** | 180 | **yes** — `descendants of` + `by consuming` with a witness ordering (§9.2) |
| 10 | **Publication** | 824 | **HANGS.** `publishstmt` stands in the grammar, the **pairing pass is missing** — the same gap as 6 |
| 11 | **Refinement** | 792 (168 `asm!`) | **HANGS.** The lowering is a trust basis, not a construct; the C form table is unwritten |

### **N_neu = 5** — gate **MISSED**

Hanging: **Frame · Race · Phase · Publication · Refinement.**

And **Race and Publication are the same gap** — both wait for the pairing pass.
If one counts gaps instead of classes, it is **four**. *The tipping rule says: count classes, and
borderline cases into the more expensive column.* **N_neu = 5.**

### The side finding on the class Phase, and it is the most interesting one

**A single site in the whole tree:**

```
crates/caprock-slab/src/lib.rs:173
    /// Wie [`Slab::attach`]. Zusätzlich: **nur beim Boot** aufrufen, bevor andere Kerne
```

**The kernel carries no boot phase as a value.** The obligation exists — it stands as a
**comment**, and nothing enforces it. That is exactly the situation Gabbro's
`BootPhase` as a linear value is written against.

> **Two readings, and the difference is large.** Either: *the class is so rare in the tree
> that a construct for it does not carry* (the same logic `locks ordered`
> died on). Or: *it is rarely VISIBLE because there is no notation* — a comment
> is cheap, a linear value is not, and what one cannot write nobody counts.
>
> **This measurement cannot separate the two**, and that belongs said. What would separate
> them: a search for functions that are **in fact** called only in bring-up — a
> call graph, the same one `H005` and the call effects hang on. **Third item at the
> same missing tool.**

### What the number does NOT say

The site counts are **sizes of the classes**, not obligations. 2 143 index accesses
do not mean 2 143 proofs — they mean that a carrying construct bites there 2 143 times.
*Precisely for that reason `N_neu` counts classes and not sites.*

### Comparison with the 19 — **there is none**

The old number counted **obligations**, this one counts **classes**. Both are legitimate, neither
is convertible into the other, and the old one can no longer be evidenced. *Whoever puts both
side by side compares two sets that were never the same.*

---

# The count of 17 — **INVALID, and by its own condition at that**

**Set up 2026-08-15**, per the committed protocol, **applied unchanged**.

## Step 1 of the protocol decides, and it falls

> *"1. locate the 17 obligations with `file:line` (otherwise invalid, see below);"*
>
> *"If fewer than 17 obligations can be found again with `file:line`, the **source**
> is not reproducible — the same protocol class as the five scratchpad classes, and then
> there is no counting, the basis is established first."*

**Found: ONE.** The whole section *The logic/plumbing split* (`MESSUNGEN.md`:268–300)
carries exactly **one** site with file and line — `kernel/src/system.rs:1215` —, and that one
belongs to the eager-FP question, not to the 17.

The source says: *"Ten hand-translated fragments from eight areas, 74 proof obligations
assigned individually."* **The assignment itself is not in the folder.** What stands there is the
**aggregate** — 74 / 17 / 57 / 19 / 1 — and a breakdown by area without sites.

## Verdict: **invalid, not unfavourable**

**The count is not run.** By the protocol the **basis is now to be established**,
not the result estimated.

> **And that is the same finding as with the five scratchpad classes, for the second time in
> one day:** a number stands in the folder, its subject does not. **Both times the aggregate
> is handed down and the assignment lost.**

## What that says about the bookkeeping — the actual yield

Three measurements of this folder rest on assignments that do not lie in the folder:

| Number | Aggregate present | Assignment present |
|---|---|---|
| 74 proof obligations (17 L / 57 P) | yes | **no** |
| 19 hanging obligations, eleven classes | yes | **only 6 of 11** |
| `delete_leaf` 3,6–6 : 1 | yes | **no** (which is why it tipped to 1,75 : 1 on the re-split) |

**That is a pattern, not a single case.** And it is mechanically preventable: *a number without
a source list does not belong in the document.* **That is a guardian rule, not a
question of style** — the same class as "`[x]` in a file that claims exclusively open
items".

## What is to be done now, in this order

1. **Reassign the 74** — on the ten fragments, with `file:line` per obligation. That is
   hand work and the reason it got lost the first time.
2. **Only then** the split of the 17 by K/A/W, with the line extent **before** the
   classification (that is how it stands in the protocol, and the order is the point).
3. Carry the marking along: **newly assigned, not reconstructed.**

**Not done, because it does not fit into this run** — the reassignment of 74 obligations on
ten fragments is a brief of its own, not a side point. *An honest "blocked, because"
beats a number with residual doubt.*

---

# The class *Frame* — reassessed, 2026-08-15 (addendum to the Neuerhebung)

The Neuerhebung booked **Frame** as hanging, with the reason: *"`effects` checks writes
and `locks`, **not reads and not call effects**."* The second half has been closed since the
call graph.

| | before | now |
|---|---|---|
| writes | `E005` | `E005` |
| `locks`, with strength | `E006`/`E007` | `E006`/`E007` |
| **call effects** | **was missing** | **`E008` — transitive, over the call graph** |
| **reads** | missing | **still missing** — `memos/M-effects-lesen.md`, and the decision lies with the folder (R5) |

## Verdict: **Frame still hangs — on ONE half instead of two**

**N_neu stays at 5.** The tipping rule is unambiguous: *if a construct carries a class only
partly, it counts as hanging, and the covered part is named.* What has changed
is not the number but **what it hangs on** — and that is the difference between
an item and a building site.

**And the rest is no longer building work but a judgement.** The read half is measured
(reading A: 10 of 32 functions, reading C: 3 of 32 — factor three), the memo is there, and
**what is missing is the folder's decision, not a tool.**

## What the call graph changed about the other classes: nothing

* **Race** and **Publication** still wait for the pairing pass — the same gap.
* **Refinement** waits for the C form table.
* **Phase** waits for the loader fragment, not for a tool (R18: a class with one
  site whose notation is missing is decided **at the fragment**, not by a count).

> **The call graph solved three blockers and cleared away no class.** That is no
> contradiction: it was a precondition, not a cause. *R17 says what one starts with, not what
> comes out of it.*

---

# W7 SWEEP — numbers without a source list, 2026-08-15

**Search path, mechanical:** per paragraph in `MESSUNGEN.md`, `BEWEIS.md`, `README.md`,
`SPRACHE.md` collect all bolded or tabulated numbers ≥ 10 and ask whether **in the same
paragraph** a piece of evidence stands — `file:line`, a `grep`/`git log`/`wc` call, or a
reference to a list.

```
MESSUNGEN.md   20 Absaetze mit Zahl ohne Beleg im Absatz
BEWEIS.md       5
SPRACHE.md      4
README.md       0
```

**The raw number is an upper bound, not a finding** — table headers count in whose body
carries the evidence. Individually checked were the three known aggregates and the four
largest remaining ones.

## Result per case

| Number | State | Finding |
|---|---|---|
| **2 231** `Ordering::` sites | **evidenced** | `grep -rhoE "Ordering::" --include=*.rs . \| wc -l` yields **exactly 2231**. *The search path was not beside it; now it is.* |
| **74** proof obligations (17/57/19/1) | **unevidenced — marked** | aggregate handed down, assignment missing. The count of 17 became invalid by it |
| **19** hanging obligations, eleven classes | **unevidenced — replaced** | by `N_neu = 5` with sites (Neuerhebung 2026-08-15) |
| **3,6–6 : 1** (`delete_leaf`) | **unevidenced — replaced** | by **1,75 : 1** with a line table |
| **106** axioms (→ 65, 30, ~130 names) | **unevidenced — marked** | no list per axiom, no search path. **And the aarch64 half (58) additionally rests on the sealed tree** |
| **1 398** range checks | **unevidenced — marked** | a recount yields **2 143**; which search path led to 1 398 stands nowhere |

## What the sweep says about the folder

**Five of six checked large numbers were unevidenced, one was exactly reproducible.**
And the one reproducible one is the one where somebody had the search path in his head — not in
the document. *The difference between 2 231 and 106 is not care but whether the
count was mechanical.*

> **The rule that follows from it already stands** (`WERKZEUGKASTEN.md` W7). What this sweep
> adds: **a number that comes from a `grep` carries the `grep`** — then it is
> re-runnable at any time, even if nobody maintains a list. *For mechanically collectable
> quantities the search path is the list.*

**Nothing deleted.** Five markings stand in the text where the numbers stand.

---

# BASIS N_L — the logic obligations, newly derived with sites

**2026-08-15, x86 only.** Marking that must run along: **newly surveyed, not
reconstructed.** The 17 are **replaced**, not continued — their assignment was not
in the folder (W7 sweep).

> **Every obligation carries its `file:line` from the first draft on.** An intermediate state
> without a site would be an aggregate on the way to the list — exactly what
> arose the first time. This list is therefore **first** the list and **then** a number.

## Where logic obligations stand in the tree — the search path

By the criterion (`BEWEIS.md`: *"logic if the statement mentions the THING"*) these are the
places at which the tree carries an **invariant over its subject** and claims its
**preservation**:

```
grep -rn "spec fn [a-z_]*inv\b" Verification/ --include=*.rs     # die Invarianten
grep -rc "proof fn "             Verification/ --include=*.rs     # die Erhaltungssaetze
```

*Not counted:* auxiliary definitions (`slot_live`, `contrib`, `refs_to`, `unlink`) — they are
vocabulary of the invariant, not themselves an obligation. **Borderline cases by the tipping
rule into the more expensive class:** where it was unclear whether a `spec fn` is a definition
or a statement, it counts as a statement.

## The eight invariants, individually

| # | Invariant | Site | Subject |
|---:|---|---|---|
| 1 | `pool_inv` | `Verification/region-runtime/proofs/conservation.rs:42` | memory regions |
| 2 | `dma_inv` | `Verification/dma-lifetime/proofs/dma_revoke.rs:33` | DMA lifetime |
| 3 | `ntfn_inv` | `Verification/notifications/proofs/notification.rs:32` | notifications |
| 4 | `ep_inv` | `Verification/ipc/proofs/endpoint.rs:199` | endpoints |
| 5 | `token_inv` | `Verification/ipc/proofs/endpoint.rs:206` | reply tokens |
| 6 | `budget_inv` | `Verification/scheduler/proofs/runqueue.rs:116` | time budgets |
| 7 | `sched_inv` | `Verification/scheduler/proofs/runqueue.rs:130` | run queue |
| 8 | `cap_inv` | `Verification/capability-system/proofs/cap_space.rs:56` | **CapSpace + CDT, clauses 1–7 in ONE spec fn** |

## The preservation theorems per area

| Area | File | Theorems |
|---|---|---:|
| capability system | `capability-system/proofs/cap_space.rs` | **16** |
| IPC | `ipc/proofs/endpoint.rs` | **29** |
| scheduler | `scheduler/proofs/runqueue.rs` | **12** |
| notifications | `notifications/proofs/notification.rs` | 7 |
| DMA lifetime | `dma-lifetime/proofs/dma_revoke.rs` | 6 |
| loader | `loader/proofs/load_gate.rs` | 6 |
| regions | `region-runtime/proofs/conservation.rs` | 5 |
| **total** | | **81** |

## **N_L = 8 invariants with 81 preservation theorems**

**The number that goes into the K/A/W computation is 81** — *formulating* an invariant is one
obligation, *preserving it per operation* is as many as there are operations, and **the
preservation is the work.**

> **And that is something other than the 17.** The old number counted obligations on
> **hand-translated fragments**; this one counts them on the **Verus proofs that exist**.
> Both are legitimate, neither is convertible into the other — *and only this one here has a
> list.*

**What this basis does NOT cover:** areas without a Verus proof (MMU/page tables, parser,
bring-up) have **zero** obligations standing here — not because they have none but because
nobody has written them down. **That is a lower bound and is called so** (R16).

---

# IN ADVANCE — the K/A/W count over N_L = 81, newly registered

**Separate commit, BEFORE the first classification.** Afterwards nothing here is changed (R2).

## Why it is newly registered — and why that is NOT a moving of the gate

> **The old population was unevidenced (W7), not the old result uncomfortable (R2).**

That is the whole reason, and it is checkable: the 17 had **one** `file:line` in the
whole folder, and that one belonged to the eager-FP question. The new population has **89
sites** (8 invariants + 81 preservation theorems), all in the text above.

*Were I to move the bar here, it would be visible at this place — which is why it stands
here and not in the result.*

## The three columns — **taken over unchanged**

| Column | Decision rule (literally from the old protocol) |
|---|---|
| **K — by construction** | The statement mentions **only the machine**, OR it is a **declared invariant** whose preservation the generator shows **once above the declaration**. A human writes nothing. |
| **A — descent statement** | Writable as *"for all x in ⟨declared domain⟩: P(x)"*, and P(x) follows from P on the **strictly smaller** elements **plus exactly one declared step assurance**. |
| **W — value statement** | Everything else: the argument concerns **values a body computes** and that no declaration fixes. |

## The K condition, mechanically per obligation

**K holds only if ALL write sites of the carrier are generated or method-bound.**
Checked by a site search in the tree: if anything outside the carrier's methods writes to its
fields, K falls.

```
grep -rn "<traeger>\.<feld>\s*[-+]\?=" --include=*.rs .     # je Pflicht
```

*The compiler carries the same check for Gabbro source as `gabbro k-bedingung`.*

## The four tipping rules — **always toward W**

1. If it is unclear whether the domain is **declared**, A tips to **W**.
2. If it is unclear whether the generator shows the preservation **once**, K tips to **W**.
3. If the obligation needs **more than one** step assurance, it is **W**.
4. If a justification needs **more than one sentence**, it is a tipping case and hence **W**.
   *A long justification is a tipping case defending itself.*

## Outcomes — as a MAJORITY RULE over N_L, not as an absolute number

| | |
|---|---|
| **W > N_L/2** (hence **> 40,5**, i.e. from 41) | the value statements are the majority — **the ceiling of step assurances does not carry**, and the generated induction scheme does not solve the bulk |
| **W ≤ 40** | the majority falls under K or A — **the ceiling carries**, and the rest is nameable |

**Both outcomes are, in advance, good results.** The first kills an assurance, the second
evidences it; neither is a failure.

## Invalid (separate from unfavourable)

* If **fewer than 81** preservation theorems can be located with `file:line` → **invalid**,
  establish the basis. *(They are located, see the list — this condition is already
  satisfied.)*
* If **more than a third** of the obligations need a justification of over one sentence →
  **invalid**: then the columns do not separate, and the criterion is the problem, not the
  distribution.

## The weight formula — written down for good, order binding

**First** measure per obligation the line extent of the proof body concerned, **then**
classify. *If the shares are determined after the count, the temptation to weigh
W obligations small is structural.*

```
F        = Zeilen aller 81 Beweisruempfe
W_zeilen = Zeilen der Ruempfe, deren Pflicht als W gebucht ist
w        = W_zeilen / F
Ueberschlag = w * 5,0  +  (1 - w) * 0,3
```

**The caveat in the same line:** the 81 are **no random cut** through the kernel —
they are the areas for which **somebody has written a Verus proof**, hence the
**well understood** ones. The extrapolation carries that bias, and **its direction is
known**: well understood areas have *fewer* value statements. **The estimate is thereby
a lower bound for w, not a guess.**

## «B34» is a W candidate and is not forgotten

The `revoke` bound (16 452 480 against a promised 200) is a **value statement about a
computed quantity** — it stands in the list and is not silently booked under K.

## RESULT of the K/A/W count — 2026-08-15

**Order observed:** line extent per obligation **first** (F = 1 389 lines over 81
obligations), **then** classified.

| | | |
|---|---:|---|
| **K — by construction** | **28** | the assurance names `requires <inv> … ensures <inv>` — preservation of a declared invariant |
| **A — descent statement** | **13** | auxiliary theorems over a declared domain (all `lemma_*`) |
| **W — value statement** | **40** | everything else |
| **N_L** | **81** | |

```
F = 1389   W_zeilen = 474   w = 0,341
Ueberschlag = 0,341 · 5,0 + 0,659 · 0,3 = 1,90
```

## BUCHUNG (2026-08-16): **MISSED** — and the reason lies in the POPULATION

> **The eight tool artefacts never belonged in `N_L`, and that is justifiable ex ante.**
>
> `lemma_refs_push`, `lemma_live_update` and their kind quantify over raw `Seq<…>`
> and claim something about `push`/`update`/`len`. **Those are library lemmas of a
> prover Gabbro does not use.** In Gabbro's world they do not exist at all — the
> manifest exports `ensures` obligations, not the auxiliary theorems an SMT solver needs
> in order to compute over a sequence. **The question is never asked there.**
>
> **So: `N_L = 73`, K = 28, A = 7, W = 38 against 36,5 — the value statements are the majority,
> the ceiling of step assurances covers a MINORITY.**

### Why that does not violate R2

**R2 forbids moving a gate after the run. Here the population is corrected, and for a
reason independent of the result** — it would have held just as much had it
pointed in the other direction.

**The probe for it is the direction:** the correction moves the result **against the
flattering reading**. *To err in the uncomfortable direction is, under the rules of this
folder, never a reinterpretation; only the opposite direction would have been one.* Were
`N_L = 73` the more comfortable result, the 81 would stand here.

### The borderline position is itself a finding

**One obligation of margin in the one population, two in the other.**

> **A gate that tips on the definition of the population measures the definition along with it.**

That is no subordinate clause: the number answers not only *"how much remains for the human"*
but also *"what did we count as an obligation"* — and the second question was unanswered up to
this booking.

### What `W = 38 of 73` is NOT yet

**Not the estimate.** The weight formula needs the **line shares**, and those come
only with the **B3 quantification from wave 4** (which bodies are not traversals, with a
line share). *The 1,90 resp. 1,98 are substitutions with the lines of the Verus bodies — not
with the lines of the kernel.* Until wave 4 the metric stands as **open**, not as 1,98.

### EINSETZUNG (2026-08-16): **B3 is measured — and does NOT close the metric**

**The number stands** (B3 section further below): `p_B3 = 0,0096` — 584 non-empty lines in
22 bodies out of 60 756, gate passed with a factor of 5 margin, to be carried **as a lower
bound**.

```
Aufschlag_B3 = p_B3 · 5,0  =  +0,048   ->   >= +0,05
```

**And the paragraph above expected too much of it. That is a correction, not a
footnote:**

> **B3 does not deliver the line shares of the weight formula, because it measures a
> different quantity.** The formula weights **proof obligations** (what share of the proof
> lines belongs to a value statement). B3 counts **code form** (what share of the kernel lines
> cannot be written as a traversal). **A body can be traversal-shaped and
> still cost 5 : 1** — because of `effects`, `locks`, linearity or the
> nesting limit. The two numbers are **summands, not replacements.**

**The trap lies in the substitution itself**, hence written out:

| substituted from | share | estimate by the same formula |
|---|---:|---:|
| **obligation side** (Verus bodies, `w = W_zeilen/F`) | 0,341 | **1,90** |
| **code side** (B3, `p_B3`) | 0,0096 | **0,345** |

**Whoever reads B3 as the kernel-side `w` gets 0,345 — and thereby a metric BELOW the
seL4 anchor 0,56, hence a triumph.** That would be wrong: the 0,345 says only that the
*loop repertoire* carries almost the whole kernel. It says nothing about `effects`, `locks`,
linearity — and nothing about the 38 value statements that remain standing beside it.

**Both numbers are lower bounds. The binding one is the larger:**

```
Kennzahl  >=  1,90        (Pflichtseite, Population 81; 1,98 mit N_L = 73)

Aufschlag aus B3  =  >= +0,05  UNTER GETRAGENER INDEX-BUCHUNG
                     +1,03     FAELLT SIE
```

> **The surcharge is substituted CONDITIONALLY, not absolutely** — and the condition stands in
> the formula, not three paragraphs above it. *A substitution that does not carry its condition
> along is the next number to run parallel to the truth as soon as somebody touches the
> booking.*

**The condition is stable, and that belongs with it, otherwise the line reads more threatening
than it is:** the class *Index* rests on **2 143 sites** and on **pure M1 mechanics**
(`index into T` inherits the bound from `count N`, A3, checked by `M103`) — **it is the
best-evidenced class of the Neuerhebung** (rank 1 of the eleven, see above). *Conditional does
not mean shaky; it means named.*

**The caveat of the measurement stands here verbatim, because it is needed exactly at this
place and nowhere else:**

> **"The surcharge from B3 is not the design's distance to the floor but a summand
> in it."**

**And the back-computation belongs substituted with it, otherwise the +0,05 is read too
calmly:** if the booking of the class *Index* falls, the summand becomes **+1,03** — factor 21.
*The substitution thereby carries the same condition as the measurement: it stands on
`index into T` inherits `count N`.*

**With that B3 is settled as a cost item and the metric remains open.** What would
close it is named and stands in `TODO.md`: the line shares of the **Gabbro side**
— hence what a proof in Gabbro actually costs for the same 73 obligations. *That is
no longer a measurement on Caprock; for it the obligations have to be written in Gabbro.*

### And what the pre-registered text provided for this outcome

> *"both outcomes are, in advance, good results. The first kills an assurance, the second
> evidences it; neither is a failure."*

**That is no mood-dampener.** The missed outcome is the number that **quantifies k** —
the share that needs functional correctness — and **only with it does the seL4 comparison
become honest**: seL4 carries 0,32 invariants / 0,40 refinement / 0,28 crefine, and Gabbro's
thesis reads that the last two fall away. **Whether the first falls is decided by exactly this
majority.**

---

## The gate, as first computed: **passed by ONE obligation** (population 81)

**W = 40 against N_L/2 = 40,5.** The majority falls under K or A; the ceiling of the
step assurances carries.

> **And that is the most uncomfortable number of the whole folder, because it hangs on a
> single item.** A rebooking in either direction tips the gate. **That stands here instead of
> being quoted as "passed"** — whoever uses this number further has to take the one with it.

**All 13 A obligations are tipping candidates** and stand individually in the list; likewise
the 28 K. *The protocol's tipping rule says: in doubt toward W* — and in doubt the
gate falls.

## The classification is mechanical, and the first attempt was NOT

**First pass: K=22, A=12, W=47 → gate missed.** It classified by **names**
(`*_preserves` → K). The hand probe on the four largest W showed: `copy`, `mint`, `install`
and `delete` stand as

```
requires cap_inv(cs), slot_live(cs, src)
ensures  cap_inv(cs2)
```

there — **that is preservation of a declared invariant, hence K by the advance protocol.**
The name classifier had them wrong, because their names name the operation and not the
assurance.

**Second pass: from the `ensures` clause** — `K` exactly when the same `*_inv` stands in
`requires` **and** `ensures`. Result K=28, A=13, W=40.

> **I nearly reported `W = 47` and a fallen gate, on a name basis.** That is
> the same error the first `narrow` count died of — a classifier that looks at the
> surface. *The difference is that this time the hand probe came BEFORE the report.*

## The K condition, mechanically checked

The protocol demands it per obligation: *K holds only if all write sites of the carrier are
generated or method-bound.*

| Field of the carrier | write sites | outside the carrier methods? |
|---|---:|---|
| `refcount` | 2 | no — both in `caprock-cap/src/space.rs` |
| `used` | 14 in 3 files | **checked:** the sites in `kernel/src/system.rs` write `VSPACES` and `DmaCtx`, **not** `CapSpace.slots` |
| `first_child` | 10 | no |
| `next`, `prev`, `rank`, `parent` | 2 / 0 / 0 / 3 | `pcie.rs:463` writes a **PCIe topology**, not the CDT |
| | | **The K condition holds for `cap_inv`.** |

*Two of the hits were false alarms of the same search pattern — same field names, different
carriers. Without the individual check the K condition would have fallen wrongly, and the gate
with it.*

## The estimate and its caveat

**1,90** — and the reference for it is to be corrected.

> **A W7 violation by me, in the same commit as the measurement — and the correction found a
> second violation inside it.**
>
> I wrote "against the target mark the folder carries as 0,56 (seL4)". **The 0,56 stands
> nowhere in the folder except in that sentence of mine.** Then I corrected with *"against
> seL4's C core of about 10 klines"* — **and that number too stands nowhere except in my
> sentence.** *A correction that replaces one unevidenced number with another is none.*
>
> **And the two quantities are not the same.** That belongs separated:
>
> | | Numerator | Denominator | Value |
> |---|---|---|---|
> | **proof to C** | 239 458 (`proof/`, ARM) — **measured** | seL4's C core — **not counted** | "beyond 20 : 1" is an estimate |
> | **specification to C** | **10 280** (`spec/abstract`, neutral + ARM) — **measured**, `f4940273` | seL4's C core — **not counted** | **open** |
>
> **The language's 0,5 : 1 floor is derived from the SECOND ratio, not from the
> first** — a language that takes over refinement and plumbing carries in the end the
> specification. *My "beyond 20 : 1" therefore does not replace the 0,56 anchor; it
> answers a different question.*
>
> **What is missing is exactly one `wc -l`:** seL4's C core at a point matching the l4v state.
> The numerator (10 280) lies there measured, the l4v repo is pinned (`f4940273`), **and the
> seL4 tree does not lie in this folder** — which is why the number stands here as **blocked
> with a named search path**, not as estimated.
>
> > **As long as it is missing, the language's metric goal hangs on one sentence of mine.**
> > That is the most expensive open W7 item, and it costs a single command.

The evidenced reference quantities are those from `PLAN.md`:341 — the folder reckoned with
**0,8 : 1** under the assumption that a tenth of the kernel needs the 5 : 1 effort.
**Measured it is 34 % of the proof lines, not 10 %** — hence 1,90 instead of 0,8.

**And the caveat stands in the advance protocol, not invented here:** the 81 are **no
random cut** but the areas with a Verus proof — the **well understood** ones. Their
direction is known: well understood areas have **fewer** value statements. **w = 0,341 is
thereby a lower bound and 1,90 likewise.** The true value lies higher, not lower.

## «B34», as promised in advance

`revoke`'s cost assurance stands as **W** — a statement about a computed quantity. It has
not been booked under K.

---

# Sensitivity probe: **is Verus fit as a population at all?**

**The question came from outside, and it is to be answered with numbers.** Carried after the
fact and separately — **the reported number (W = 40, gate passed) is not touched** (R2).

## What sits in the 81 that is not a logic obligation

**Eight of the 81 are tool artefacts**: they quantify over raw `Seq<…>` and claim
something about `push`/`update`/`len` — *that is the data structure of the PROVER, not the
subject.*

```
region-runtime/lemma_live_push:47        ensures live_bytes(regions.push(r)) == …
capability-system/lemma_refs_push:90     ensures refs_to(slots.push(sl), o) == …
capability-system/lemma_refs_update:117  requires 0 <= i < slots.len(), …
…  (8 Stueck, 122 Zeilen)
```

A folding lemma over `Seq::push` says nothing about capabilities. **It exists because the
SMT solver needed a hint.** In Gabbro this obligation would not exist — not because the
language is cleverer but because the question would never be asked.

## And their removal TIPS the gate

| | N_L | K | A | W | Gate |
|---|---:|---:|---:|---:|---|
| as reported | 81 | 28 | 13 | **40** | **passed** (40 ≤ 40,5) |
| without the 8 tool artefacts | 73 | 28 | 7 | **38** | **MISSED** (38 > 36,5) |

`w` rises from 0,341 to 0,358, the estimate from 1,90 to **1,98**.

> **The gate result hangs on whether Verus's sequence lemmas count as logic obligations.**
> They should not. **The gate is thereby not robust**, and that is a bigger finding
> than the direction in which it falls.

## The answer to the question

**Verus is a good AVAILABILITY basis and a bad SEMANTIC one.**

| for | against |
|---|---|
| The 81 are **written down and machine-checked** — unlike any hand count that needs a classifier (and that is exactly what the first `narrow` count died of) | A `proof fn` arises **when the solver needs a hint** — not when the thing has an obligation. That is a statement about the tool |
| They carry `file:line`, hence W7-fit | They prove over a **MODEL** (`cap_space.rs`), not over the code (`space.rs`). **The refinement — 27,8 % of the effort at seL4 — does not occur at all** |
| They are the only basis that exists in the tree | Areas without a Verus proof count **zero**: MMU, parser, bring-up. The well understood ones are over-represented, and the direction of the bias is known |

**The heaviest point is the refinement.** Gabbro's assurance reads *"lowering is near 0"*,
and the Verus population **cannot check** that assurance, because it has the same gap:
it proves over a model. **A measurement that does not contain the largest item of the
comparison at all cannot refute it either.**

## What a better basis would be

None that is available today — and that is the honest conclusion. What it would have to have:

1. Obligations **at the code**, not at the model (hence with refinement).
2. An origin that **does not hang on the degree of automation of a solver**.
3. Sites (W7).

**Conditions 1 and 2 exclude each other today:** what proves at the code does so with a
solver, and its hints land in the count. *That is no defect of this measurement
but the reason why the number 1,90 must be quoted with its basis and not
alone.*

---

# Race and Publication — reassessed, 2026-08-16

The Neuerhebung booked both as hanging, **with the same reason**: *the pairing pass is
not built.* It is built.

## What the pass covers, with sites (W7)

| | Refusal | Site in the checker | Probe |
|---|---|---|---|
| orphaned `publishes` | `V001` | `crates/gabbro-check/src/paarung.rs:123` | `beispiele/gift/51-verwaistes-publishes.gab` |
| orphaned `awaits` | `V002` | `paarung.rs:139` | `gift/50-verwaistes-awaits.gab` |
| undecidable (cycle) | `V003` | `paarung.rs:108` | — (W10, third state) |
| `relaxed` with a payload | `V004` | `paarung.rs:153` | `gift/52-relaxed-mit-nutzlast.gab` |
| **pairing across an intermediate function** | — | `paarung.rs:94-101` (unified set) | `beispiele/14-paarung-ueber-zwischenfunktion.gab` |

Mutations: `paarung-je-funktion`, `verwaistes-awaits-egal`, `relaxed-darf-tragen` —
**all three caught**, 44 of 44 on the surface *pruefer*.

## Verdict per class

**Publication — CARRIED.** `publishstmt` names the payload at the store, the pass holds both
halves against each other, and `relaxed` can carry none. *The class falls.*

**Race — STILL HANGS, and the reason is now a different one.**

> The pass checks that the **declarations** pair. It does **not** check that
> `release`/`acquire` on the target machine establish the visibility the pairing
> claims — that is a statement about the **memory model**, and it falls into the
> **axiom layer**, not into the pass.

**That is no defect of the pass but the limit of what a pass can achieve here.**
And it moves the class from *"unbuilt"* to *"built, rests on named axioms"* —
the same place `Refinement` stands in.

*The axiom layer is marked in the W7 sweep as unevidenced (106 without a list). **Race thereby
hangs on a number that is itself open.***

## N_neu: **5 → 4**

| | State |
|---|---|
| Index, Overflow, Alias, Lock, Termination, Leafness | carried |
| **Publication** | **carried (new)** |
| Frame | hangs on ONE half (reads) — a decision, not work |
| **Race** | hangs on the **axiom layer**, no longer on the pass |
| Phase | undecided — is decided at the loader fragment (R18) |
| Refinement | rests on the lowering; translation validation per build is the way |

**Seven of eleven carried.** And the four remaining are four **different** kinds of
distance — a decision, an axiom count, a fragment, a sub-project.

---

# IN ADVANCE — the loader fragment decides the class *Phase*

**Separate commit, BEFORE writing the fragment.** Afterwards nothing here is changed.
Measurement base: `../caprock-messbasis` @ `a1bf707`, `kernel/src/arch/x86_64/bringup.rs`
(**6 706 lines, 36 functions**).

## Why at the fragment and not by a count (R18)

The Neuerhebung found for *Phase* **a single site in the whole tree**, and that one is a
**comment**: `caprock-slab/src/lib.rs:173` — *"call only at boot, before other cores"*.

> **A class with one site whose notation is missing is not decided by a
> count.** What one cannot write nobody counts: a comment is cheap, a
> linear value is not. **At the fragment it shows whether the form carries or is missing.**

*`locks ordered` remains validly dead — double acquisition was writable and still did not
occur. Here it is the other way round.*

## What is counted

**Sites at which `BootPhase` as a linear value carries an obligation that nothing
carries today.** A site counts if **one** of the three conditions holds:

1. **single-core assumption** — the operation is correct only as long as the further cores
   stand still (no lock, because nobody is concurrent yet).
2. **ordering constraint** — it must run after a named boot step and before
   another, and only prose says so.
3. **once-only** — it may run exactly once, and nothing enforces it.

**Every site is evidenced with `file:line`** — from the first draft on, not in the final state
(W7).

## The two-sided gate — **k = 5**

| | |
|---|---|
| **construct-worthy** | the token carries at **≥ 5** sites |
| **dies like `locks ordered`** | it carries at **≤ 4** — then today's comment is the appropriate form, and `BootPhase` comes out of the language |
| **invalid** | the three conditions cannot be decided on `bringup.rs` — then the criterion is missing, not the answer |

**Why 5 and not 1:** a construct that carries a single site is a special rule.
Five is the threshold from which a form pays off — the same order of magnitude at which the
`Sonderform` class becomes a pattern.

**And the number stands here because afterwards it can no longer be chosen.** If the
measurement comes out at 4, that is a result; if it comes out at 6, likewise. *Both are, in
advance, a good result — the one outcome saves a construct, the other justifies one.*

## RESULT of the loader fragment — the class *Phase* is **construct-worthy**

**Measured: 7 sites against a gate of k = 5.** Each with `file:line` in `FRAGMENTE.md`
(F7). *Conservatively counted* — `main.rs:144` and `:151` describe the **same** boundary from
two sides and are booked as **one** site, not as two.

| | |
|---|---|
| candidates raw | 8 |
| after merging the MMU boundary | **7** |
| gate | **5** |
| **verdict** | **carries — the class does not come out of the language** |

## The evidence that weighs more than the number

`main.rs:251`, literally:

> *"D5: first report the authority document, then start the root task. **Exactly this line
> was missing on ARM** — there the manifest path ran along unchecked."*

**A paid-for error of exactly this class.** The order stood as a comment in one
architecture and **was missing in the other**; no tool could say so. *That is the
difference between "rare" and "rarely visible" that R18 demanded — and it falls
in favour of visibility.*

## And the yield is not the number but «B37»

**The token carries "before the MMU" against "after the MMU"** — there lies a consumption, and
linearity makes the two sides distinguishable.

**The four ordering constraints WITHIN a phase it does not carry.** `cap_tabellen` before
`ipc_tabellen` stands in the fragment only because I wrote it that way: the compiler sees
a chain of consumptions and says **nothing about their order**.

> **«B37»: linearity enforces *exactly once*, not *in this order*.**
>
> For the order one would need **a token of its own** per step — then the
> vocabulary grows with every boot step, and that is the move `abi { … }` and
> `locks ordered` died against — or an **order on tokens**, and that does not exist.

**The class *Phase* is thereby half carried**, and the tipping rule says where that falls:
*if a construct carries a class only partly, it counts as hanging, and the covered
part is named.* **Phase stays in N_neu.**

## Convergence metric — the first data point from an area fragment

| Fragment / occasion | new constructs | cumulative |
|---|---:|---:|
| F1–F6 (stock) | — | base |
| «B32» virtio ring counter | 1 (`wrapping` at the `regdecl`) | 1 |
| «B34» revoke bound | 0 — the premise fell | 1 |
| «B29» refcount underflow | 0 — `narrow` sufficed | 1 |
| `heldpred` (from H005) | 1 | 2 |
| «B35» `Some`/`None` | 1 | 3 |
| **F7 loader/bring-up** | **0** | **3** |

**The loader fragment cost no new construct** — it *justified* one
(`BootPhase`, which already existed) and found a **limit** («B37»).

> **One data point is not a curve.** Three further area fragments are outstanding, and only
> with them does the metric say something about convergence. *But it is no longer empty.*

---

# CONVERGENCE METRIC — complete, 2026-08-16

**The probe on the folder's strongest product argument:** *new constructs per
written-out area fragment must fall.* Until today it had **zero data points from
area fragments**; now it has **four**.

> **Two columns, not one — and that is the honest frame around the number.**
> **Zero new words is not zero language movement.** The vocabulary convergence measures only
> *one* of the two maintenance quantities; the other is the **template and axiom surface**,
> and it keeps growing. Without the second column the second movement becomes invisible as soon
> as the first shines.

| Fragment / occasion | **new constructs** | **changed meaning of existing ones** | cumul. words |
|---|---:|---|---:|
| F1–F6 (stock, 2nd version) | — | — | base |
| «B32» virtio ring counter | 1 — `wrapping` at the `regdecl` | — | 1 |
| «B34» revoke bound | 0 — the premise fell | — | 1 |
| «B29» refcount underflow | 0 — `narrow` sufficed | — | 1 |
| `heldpred` (from `H005`) | 1 | `Held` now carries its **strength** | 2 |
| «B35» `Some`/`None` | 1 | — | 3 |
| **F7 loader/bring-up** | **0** | **«B37»:** `BootPhase` carries *exactly once*, **not** *in this order* — a named **limit** | 3 |
| **F8 scheduler** | **0** | **«B38»:** a lock boundary demands revalidation **or a named carrier** — semantics extended | 3 |
| **F9 MMU/page tables** | **0** | **«B39»:** the axiom layer becomes **longer** (`A`/`D` as hardware writers) | 3 |
| **F10 parser/checkpoint** | **0** | — | 3 |
| **B3 (whole kernel, no fragment line)** | **1** — `ancestors of` | **«B41»:** two further gaps, **none of them a construct** (an open question resp. a prediction) | 3 |

## **Four area fragments, zero new constructs — and three changed meanings.**

**That is the first real piece of evidence for the convergence bet** — and it is stronger than
the number looks: the four areas were **never written out** and counted as the hardest ones
(scheduler, MMU, loader, parser). *Each of them could have demanded a construct.*

## What they demanded INSTEAD — and that is the honest part

**No new construct, but four findings and two checker gaps:**

| | Finding | Kind |
|---|---|---|
| «B37» | `BootPhase` carries *exactly once*, not *in this order* | **limit of an existing construct** |
| «B38» | `Stale(T)` in the constraint version is **refuted** — 2 of 5 transitions rest on `masks IRQ`, not on revalidation | **candidate died** |
| «B39» | the MMU writes `A`/`D` itself — a writer no `effects` line names | **belongs in the axiom layer** |
| «B40» | the DTB parser checks 145 lines without error and without a tool — `format` wins **brevity, not safety** | **goes against the folder** |
| «B41» | **three domains are missing, and measured at that** (B3): `ancestors of` (the device topology is walked upwards), union-find (`find` writes the chain it walks), a chain over an **edge function** (`kante: impl Fn(u16) -> Option<u16>`) | **first measured construct demand** |

In addition **two gaps in the checker**, both found at the MMU fragment and both closed:

1. The domain `mappings of` had **no bound**, although `levels × node length` stands in the
   `walk` declaration — the same class as the `queue` domain.
2. **A `walk` was not known to the type system at all.** `ptr<normal, r> Seitenabstieg` was
   simply `Unbekannt`; the chain knew formats, devices and tables — and no walks.
   *The bound already stood there and still did not bite.*

> **The bet holds at four points, and the price stands beside it.** The fragments cost
> no construct — they cost **two checker repairs, one dead candidate and one
> finding against our own product argument.** *That is a better result than a smooth
> zero, because one can recompute it.*

## And the second column is the one that keeps growing

**The vocabulary converges (column 1). The trust surface does not (column 2).**
«B39» lengthens the axiom layer, «B38» extends a semantics, «B37» draws a limit into
an existing construct. **None of these three movements appears in the word count**, and
all three raise what a reader has to believe.

> *Whoever quotes the convergence bet quotes column 1. The upkeep stands in column 2.*

## ADDENDUM (2026-08-16): **«B41» stands beside the zero in column 1, not below it**

**The zero in column 1 holds for the four area fragments F7–F10. B3 measures a different
population — the whole kernel — and finds there a demand for three domains.**

| | Population | new constructs |
|---|---|---:|
| convergence metric F7–F10 | four written-out area fragments | **0** |
| **B3** | **`kernel/` + `crates/`, 2 186 bodies** | **1** (`ancestors of`) |

**The one is ranked, not rounded.** Of the three gaps **only `ancestors of`** counts
here — a domain line with the same generation logic as `descendants of`, hence a
construct in the sense of the metric. The **edge function** is an open question about the line
(the general case of `chain(a,b)`), and **union-find will presumably get no
traversal form at all** — it is the disguised entanglement from P0.1 attempt 1, not a missing
repertoire. *Whoever counts all three as constructs counts a prediction and an open question
along.*

> **`ancestors of` is thereby the first construct need MEASURED by the convergence metric:
> zero out of four fragments, one out of a measurement.**

**The numbers do not contradict each other — they answer different questions**, and precisely
for that reason the second stands here: **whoever quotes "zero new constructs" has to take
«B41» with it.** One writes a fragment in the language one has; a kernel contains what it
contains. *The convergence evidence becomes weaker if one changes the population — and that is
the more honest sentence than the zero alone.*

> **And the demand is not yet a build.** W3 demands a **measured need** for a
> construct — that lies there now, with `file:line`. It does not demand following it: three
> domains more are three domains more that every reader has to believe (column 2). *The
> decision stands in `TODO.md`, not here.*

---

# B3 quantified: which bodies are NOT writable as a traversal

> ## **This measurement did NOT observe R1, and that stands before the result.**
>
> **The marker rule was sharpened with the numbers visible.** The sequence in the protocol of
> the run: tool built and run (versions 1–4), *afterwards* the advance text written.
> There is **no pre-registration commit**; the "IN ADVANCE" below is written down after
> the fact. Exactly the temptation R1 stands against — four versions, four numbers,
> each in knowledge of the previous one.
>
> **What holds nevertheless, and why the number does not go in the bin:**
>
> 1. **The gate was pre-registered, the rule was not.** The 5 % bar stands in
>    `TODO.md` @ `642e4c0`:112–118, entry "B3 beziffern" — there since `75c9841`
>    (2026-08-13), hence **three days before this run**. The entry has migrated with this
>    booking to `DONE.md`; the site therefore names the commit, not only the line. **R2 is
>    observed** — nothing was moved.
> 2. **The gate verdict is rule-invariant.** The four versions yielded 0,03 % · 4,36 % ·
>    0,74 % · 0,95 %. **All four pass the 5 % bar** — including the deliberately too coarse
>    version 2. *The number hangs on the choice of rule, the verdict does not.*
> 3. **Every sharpening went into the more expensive column.** 19 → 26 bodies: every step
>    added, none removed. Whoever sharpens a rule while the gate reads "≤ 5 %"
>    sharpens **against** his own passing.
>
> **What is not curable:** a repetition "per protocol" does not restore the pre-registration,
> because the rule is now known. **R1 is a one-shot rule, and it is missed here.**
> The number counts as a *lower bound with a passed, rule-invariant gate* —
> not as a pre-registered measurement.
>
> ---
>
> ## **The sentence the whole measurement comes down to:**
>
> ## **The gate is rule-invariant but booking-variant.**
>
> | | Spread | Effect on the gate |
> |---|---|---|
> | **rule versions** (0,03 % … 4,36 %) | **factor 130** | **none** — all four pass |
> | **one single booking decision** (class *Index*) | **factor 21** | **the gate tips** |
>
> **The rule invariance carries more as a rescue than it sounds:** a result that stays stable
> over a factor-130 spread of **deliberately too coarse** rules is well defended against
> rule fitting. **And its limit stands in the same sentence:** it holds only within the
> **tried** versions. Four versions are no sample from the rule space; they are
> four points I chose. *Precisely for that reason R1 stays booked as missed, instead of
> being lifted by the invariance.*

## IN ADVANCE — written down after the fact (see box), wording as used during the run

**Measurement base:** `../caprock-messbasis` = `SEL4Lake/SEL4Lake` @ `arch/x86_64`, `a1bf707`.
Read only; `git status --porcelain` there is empty after the run.
**Population:** `kernel/` + `crates/`, 105 `.rs` files.

### What "writable as a traversal" means mechanically

Gabbro has **three** loop forms (`dokumente/SYNTAX.md`:459–478) and **eight** domains
(`dokumente/SPRACHE.md`:778–783):

```
traverse … over <domäne> by (unvisited | consuming | decreasing e)
retry   … until <pred> bounded N ops on_exceeded <name>
forever … per_pass bounded N ops on_exceeded <name> effects { … }

Domänen: slots of · chain(a,b) in · descendants of · queue · fields of
         elems of · threads · mappings of
```

A body is **not** writable as a traversal if it carries at least one of the three
markers. The markers are syntactic and are collected by `zaehle-b3.py`.

| Marker | Condition |
|---|---|
| **Na — chain walk without a domain** | In a `while`/`loop` the per-round progress is a chain step: `x = …x….<feld>` (pointer chain), `x = A[x]` (index chain, an array whose elements hold indices into the same array), or `let Some(n) = f(x)` followed by `x = n` (edge chain, a chain that only arises through a call). **Excepted**, because covered by a domain: `first_child`/`next_sibling` (`chain(first_child,next_sibling) in slots`, `descendants of`) and `qnext`/`qprev` (`queue`). |
| **Nb1 — pointer surgery without a domain** | The body **writes** a linking field — element selection (`[…]`, `*` deref, `&mut` binding) **and** a field that names another element of the same collection — on a structure for which none of the eight domains is declarable. |
| **Nb2 — pointer surgery with a domain** | The same write on a structure that **has** a domain. |

**Why Nb2 counts at all, and that is the only evaluative decision in the protocol:**
a domain gives the **reading** of a linkage, not the **relinking**. `by consuming`
covers exactly the removal of the *currently visited* element, hence **one** write site per
round. Whoever bends three neighbours in one move is not traversing. That is a borderline case —
and borderline cases tip by rule into the **more expensive** column.

**Both numbers are reported separately:** *letter* = Na + Nb1 (the wording of the
definition), *reported* = Na + Nb1 + Nb2 (with the tipping rule). Whoever does not share the
tipping decision can read off the other number without recomputing.

### Counting rule

* **The unit is the function body**, not the loop. A body with five loops, one of
  which tips, counts once — with **all** its lines.
* **Lines per body = non-empty lines between the body braces**, comments
  included. The reference quantity is formed with the same rule.
* **Bodies without a loop count in.** The second half of the definition knows no
  loop condition: pointer surgery is pointer surgery, whether straight ahead or in a
  loop. *This stipulation was necessary because the scheduler's queue surgery, expected by
  name, has no loop at all (see below).*
* **Nested `fn` do not count twice** — only the outermost body.
* **Reference quantity:** non-empty lines of `kernel/` + `crates/`. In addition the
  quantity is carried **without `#[cfg(test)]` modules**; what is reported is the pairing with
  the **larger** ratio (the more expensive column).

### Tipping rule

1. If it is unclear whether a field is a **linking field**, it counts as one.
2. If it is unclear whether a structure has a **domain**, it counts as Nb2 — hence it counts in.
3. If it is unclear whether a loop walks a **chain** or merely looks up, it counts as a chain.
4. Percentages are **rounded up**, never rounded benevolently.

### The two-sided gate

The gate is **not newly set** but taken over from `TODO.md` @ `642e4c0`:112–118
(there since `75c9841`, 2026-08-13; today in `DONE.md`): *"5 % of the kernel is +0,25 on the
metric, 10 % is +0,5"*, hence surcharge = share · 5.

| | |
|---|---|
| **passed** | **p ≤ 5 %** — the remainder costs at most **+0,25**, the loop forms carry the kernel |
| **fallen** | **p > 5 %** — the three loop forms cover too little, and the repertoire is to be extended or the surcharge borne |

**Invalid — separate from unfavourable, and none of these conditions says anything about the height of p:**

* **U1** The brace matching aborts in more than 2 % of the files → the body inventory
  is incomplete, the number is not a measurement (R16).
* **U2** R14(b) fails: a change to the subject does not change the number → the
  tool does not hang on the subject.
* **U3** The hand sample (**n = 13**: every 4th of the N list sorted by `file:line`,
  plus 6 equidistant ones from the set of bodies with a loop and no marker)
  shows **more than 1** misclassification.
* **U4** More than a third of the markers can only be justified with running text instead of
  with a site → then the criterion does not separate.

### R14 — the harness first

* **(a) An abort must be distinguishable from a hit.** An unbalanced brace
  is put into the *copy* of a subject; the tool must report `Abbrueche: 1` and
  must not silently deliver a number.
* **(b) The number must hang on the subject.** Three mutations on the copy: **remove** an
  N body, **insert** an artificial N body, **rewrite** an N body **into a
  traversal**. Each must move the number in the predicted direction,
  the withdrawal must restore the initial value.
* **(c) Full count instead of trust in the rule at the `for` heads.** The domain recognition in
  the `for` head is a pattern list and thereby attackable. Therefore **all** distinct
  `for … in` expressions are enumerated and those without a pattern hit are decided
  **individually** by hand.

---

## RESULT — 2026-08-16, x86 only, against `a1bf707`

### The population

```
./zaehle-b3.py ../caprock-messbasis
find kernel crates -name '*.rs' -exec cat {} + | wc -l              # 69 283 roh
find kernel crates -name '*.rs' -exec cat {} + | grep -c '[^[:space:]]'   # 65 168 nicht leer
```

| | |
|---|---:|
| files | 105 |
| lines raw / non-empty | 69 283 / **65 168** |
| of them `#[cfg(test)]` modules (non-empty) | 4 412 |
| reference quantity without test modules | **60 756** |
| function bodies | 2 536 (of them 2 186 outside the test modules) |
| bodies with a loop | 462 |
| loops: `for` / `while` / `loop` | 571 / 146 / 117 |

### R14 — all three probes passed

**(a) Abort.** Unbalanced brace in `dmar.rs` → `Abbrueche: 1`. More important than the
reporting is **what happened beside it**: the reported number thereby fell silently from 26 to
24, because two bodies dropped out of the inventory. **Without the abort counter the
measurement would have delivered a number two too low and looked healthy doing it.**

**(b) The number hangs on the subject.**

| Mutation on the *copy* | expected | measured |
|---|---|---|
| `dmar::union` (6 L) gutted | −1 body | 26 → **25**, 621 → 615 L |
| artificial chain walk over an edge function appended | +1 body | 26 → **27**, 621 → 631 L |
| withdrawal of both | initial value | **26 / 621 L** |

**(c) The `for` heads, in full.** 347 distinct `for … in` expressions. 331 hit a
domain pattern. The **16 remaining ones were decided individually** and are **all** domains:
eleven bare places (`segs`, `endow`, `caps`, `regions`, `runs`, `w`, `holes`, `bytes`,
`entries`, `data`, `paare` → `elems of`), two array literals (`&[true,false]`,
`&[0u32,1,4242]`), one path (`system::ERLAUBTE_SPAETBINDUNGEN`) and two iterators of our own,
both domain-backed: `img.segments()` = `(0..self.phnum).filter_map(…)`
(`elf.rs`:166 → `slots of`) and `self.ops()` = `&[Op]` (`irte.rs`:1023 → `elems of`).

> **Finding, and it goes against expectation:** **not a single one of the 571 `for` loops in
> the core runs over something that is not a domain.** The non-traversability sits
> entirely in `while`, `loop` and in loopless bodies.

### The number

| | Bodies | Lines | Share | Surcharge |
|---|---:|---:|---:|---:|
| **letter** (Na + Nb1) — without test modules | 12 | 387 | 0,637 % | +0,032 |
| **reported** (+ Nb2, tipping rule) — whole tree | 26 | 621 | 0,953 % | +0,048 |
| **reported** — without test modules | 22 | 584 | **0,961 %** | **+0,048** |
| for information, against the TODO denominator 75 294 (raw, whole tree) | 26 | 621 | 0,825 % | +0,041 |

**What is reported is the most expensive pairing: p = 0,961 %, rounded up p = 1,0 %.**

#### **Gate PASSED** — p = 1,0 % against a bar of 5 %, with a factor of 5 margin.

Aborts: **0**. U1–U4 none triggered. The hand sample (n = 13) yielded
**0 misclassifications** at a tolerance of 1 — checked were `move_cap`,
`abstieg_terminiert_auf_einem_zyklus`, `scope_covers`, `build_groups`,
`handler_kante_loesen`, `remove_from_ready`, `alloc` from the N list and `classify_all`,
`exception::init`, `arbitrary_mutations_never_panic`, `ring3_worker`, `loader::probe`,
`run_certfuzz` from the complement.

### **And the yield is not in the number. It is in the suspect list, which was wrong.**

> **All three candidates expected by name were wrongly guessed, and the largest item
> stood in no suspect area.** DMAR/PCIe supplies **226 of the 584 lines (38,7 %)** —
> more than scheduler and CDT individually.

**That is R18 from the other side.** The rule stands as a *visibility bias*: what
is loud gets counted. Here it was the reverse — **the suspect list came from what is
*famously* hard** (IPC fastpath, `revoke`, scheduler queue), **not from what is
*measurably* hard** (device topology, union-find, handler chains). *A suspicion from the
reputation of a thing is no measurement; it is the memory of other people's kernels.*

**And `revoke` delivers along the way the finest evidence `by consuming` will ever get.**
The body for which the construct was **designed on paper** already exists in the real kernel
in exactly this form — `space.rs`:619–657, word for word `descendants of s by
consuming`, including a hand-written `bounded N ops` discipline. **Not a construct that fits
a body, but a body that found the same form without the language.**

### The 26 bodies, each with `file:line` (W7)

| `file:line` | Body | Marker | L |
|---|---|---|---:|
| `crates/caprock-cap/src/space.rs:557` | `move_cap` | Nb2 | 34 |
| `crates/caprock-cap/src/space.rs:783` | `audit_cdt` | Na | 100 |
| `crates/caprock-cap/src/space.rs:1032` | `link_child` | Nb2 | 10 |
| `crates/caprock-cap/src/space.rs:1044` | `unlink` | Nb2 | 15 |
| `crates/caprock-cap/src/space.rs:1138` | `abstieg_terminiert_auf_einem_zyklus` *(test module)* | Nb2 | 10 |
| `crates/caprock-cap/src/space.rs:1152` | `abstieg_weist_index_ausserhalb_der_tabelle_ab` *(test module)* | Nb2 | 7 |
| `crates/caprock-cap/src/space.rs:1163` | `kinderliste_zaehlt_und_bricht_ab` *(test module)* | Nb2 | 14 |
| `crates/caprock-cap/src/space.rs:1182` | `kinderliste_weist_index_ausserhalb_der_tabelle_ab` *(test module)* | Nb2 | 6 |
| `crates/caprock-hal/src/x86_64/dmar.rs:374` | `scope_covers` | Na | 24 |
| `crates/caprock-hal/src/x86_64/dmar.rs:519` | `find` | Na, Nb1 | 7 |
| `crates/caprock-hal/src/x86_64/dmar.rs:526` | `union` | Nb1 | 6 |
| `crates/caprock-hal/src/x86_64/dmar.rs:538` | `alias_rid` | Na | 13 |
| `crates/caprock-hal/src/x86_64/dmar.rs:553` | `build_groups` | Na | 106 |
| `crates/caprock-hal/src/x86_64/dmar.rs:689` | `is_below` | Na | 12 |
| `crates/caprock-hal/src/x86_64/pcie.rs:406` | `read_topology` | Nb1 | 58 |
| `crates/caprock-microkit/src/lib.rs:779` | `handler_kante_setzen` | Nb1 | 8 |
| `crates/caprock-microkit/src/lib.rs:793` | `handler_kante_loesen` | Nb1 | 10 |
| `crates/caprock-sched/src/lib.rs:926` | `switch_to` | Nb2 | 21 |
| `crates/caprock-sched/src/lib.rs:1700` | `end_donation` | Nb2 | 10 |
| `crates/caprock-sched/src/lib.rs:1873` | `enqueue_ready` | Nb2 | 18 |
| `crates/caprock-sched/src/lib.rs:1893` | `remove_from_ready` | Nb2 | 25 |
| `crates/caprock-sched/src/lib.rs:1922` | `record_zombie` | Nb2 | 46 |
| `crates/caprock-sched/src/redirect.rs:577` | `pruefe_bindung` | Na | 31 |
| `crates/caprock-sched/src/redirect.rs:625` | `kettenlaenge` | Na | 12 |
| `crates/caprock-slab/src/lib.rs:258` | `alloc` | Nb2 | 10 |
| `crates/caprock-slab/src/lib.rs:271` | `free` | Nb2 | 8 |

Distribution of the 584 lines outside the test modules: **DMAR/PCIe 226 L (38,7 %) ·
scheduler 163 L (27,9 %) · CDT 159 L (27,2 %) · Microkit 18 L · Slab 18 L.**

---

### What speaks against our own thesis

#### 1. All three candidates expected by name were wrongly guessed — two entirely, one half.

**`revoke` is the cleanest traversal in the whole tree.**
`crates/caprock-cap/src/space.rs`:619–657 is word for word
`traverse it of s over descendants of s by consuming { delete_leaf(it) }` — and already
carries the `bounded N ops` form by hand: `limit = self.cdt_step_limit()`, `ops > limit`,
`note_overrun()`. The body stands **not** in the list, and not by a
benevolent rule but because `descendants of` covers it. *The TODO entry
suspected the opposite here.*

**An IPC fastpath exists — but not where it was sought, and it costs for a
different reason.** `grep -rniE 'fastpath|fast_path' kernel crates` → 12 sites; the
path is `Scheduler::switch_to` (`crates/caprock-sched/src/lib.rs`:926). The
message copying one would have suspected is `for i in 0..MSG_WORDS`
(`crates/caprock-ipc/src/lib.rs`:171–177) = `slots of`, and the endpoint queue is
a ring buffer over an array (`head`/`tail` mod `QCAP`, ibid. 68–95) = `queue`. **What
makes `switch_to` expensive is the surgery on the donation edges** `sc_donor`/`sc_donee` —
two mutual references between TCBs for which none of the eight domains is declarable,
because **nobody ever walks them** (no `for`/`while`/`loop` in the tree follows them).
21 lines, not the message path.

**The scheduler's queue surgery is real — but has no loop at all.**
`enqueue_ready` (18 L) and `remove_from_ready` (25 L) are straight ahead, O(1). And the
ready list **has** a domain (`queue`); its walkers — `migration_candidate`:1415 and
`audit`:1743, both `while i != NIL { i = t.qnext }` — are clean traversals and
stand **not** in the list. The surgery lands in the expensive column only via the
**tipping rule**, not by the wording of the definition. *Had I not written the tipping
rule down in advance, the item expected by name would have dropped out entirely with its
43 lines.*

#### 2. The largest item stands in none of the three suspect areas.

**DMAR/PCIe supplies 226 of the 584 lines — 38,7 %, more than scheduler and CDT
individually.** And it names a **concrete language gap** that no count had before:

* **Gabbro has `descendants of` but no `ancestors of`.** Four of the five DMAR bodies
  (`scope_covers`, `alias_rid`, `build_groups`, `is_below`) walk the device topology
  **upwards**: `cur = topo[cur].parent`. Downwards it would be a domain; upwards it is none.
* **Union-find is accessible to none of the eight domains** — `dmar.rs`:519 `find` writes the
  chain it is currently walking (`parent[x] = parent[parent[x]]`). That is traversal and
  surgery in the same statement.
* **A chain that only arises through a call** is not declarable:
  `pruefe_bindung`/`kettenlaenge` (`redirect.rs`:577, 625) walk the handler edge over
  a parameter `kante: impl Fn(u16) -> Option<u16>`.

**These three gaps are the actual yield of the measurement, and they weigh more than the number.**

##### **But they are NOT of equal rank — and the ranking belongs beside them, otherwise somebody proposes a `union_find` domain**

| | Gap | Verdict |
|---|---|---|
| **cheap** | **`ancestors of`** | **a domain line with the same generation logic as `descendants of`** — the same edge, the other direction. The convergence metric can take it as a *measured* need. |
| **medium, open** | **chain over an edge function** | the **general case of `chain(a,b)`**. The question is not whether it works but **where the line lies**: does a *declared* edge function hold — pure, M1-typed, like the `update` body of `exchange` — or is it **quantifier repertoire through the back door**? |
| **not at all** | **union-find** | **different in principle. Will presumably get no traversal form at all.** |

> **Union-find is not a missing domain but a disguised entanglement.**
> `find` with path compression **mutates the structure it runs over** — that is not
> *"no domain present"*, that is **the entanglement from P0.1 attempt 1, dressed up as a
> read operation.** Whoever makes it a domain brings back exactly the case on which
> the first attempt failed.
>
> **The honest prediction, so that it is later refutable:** union-find stays
> **either a 5 : 1 item** or becomes **group `ops` material** — the compression as a
> *generated operation* with preservation of the representative invariant, not as a loop form.
> *That is a prediction, not a measurement. It stands here so that the next proposal has to
> beat it first.*

#### 3. The tool would have ruined the measurement twice — not the subject.

Four rule versions, four numbers: **2 → 27 → 19 → 26 bodies**, corresponding to
**0,03 % → 4,36 % → 0,74 % → 0,95 %.** (The fourth version is the reported one; the
correction of the `==` error lowered it further from 27 to 26.)

* Version 1 (0,03 %) saw only bodies **with** a loop — loopless surgery was invisible.
* Version 2 (4,36 %) read `for x in segs` as a non-domain; a single wrongly marked
  body (`demo_report_then_idle`, 1 360 L) made up 2 % on its own.
* Version 3 missed index chains (`find`/`union`), edge chains (`pruefe_bindung`,
  `kettenlaenge`) and the donation edges (`switch_to`, `record_zombie`).
* Version 4 read `==` as an assignment and marked `migration_candidate` (18 L) wrongly.

**The two discarded versions span a factor of 130 and bracket the right
answer.** Both could have been presented with the same list of sites. The
difference between them and the final version is **exclusively R14** — the
full count of the `for` heads and the three mutation probes. **A number from this
class of tool without R14 is worthless, and that is no subordinate clause: three of four
versions were wrong.**

#### 4. The number is a LOWER BOUND — with four named reasons.

Not because of R16 (0 aborts) but from the build of the tool:

1. **The series does not visibly converge from above.** Every sharpening after version 2
   added **real** bodies, removed none (19 → 26). There is no reason
   to assume that a fifth version would find nothing more.
2. **`unsafe`/`asm!` blocks are not measured.** The cleaner replaces string literals
   with spaces; the 168 `asm!` sites are empty for this tool.
3. **Surgery behind a call counts at the helper, not at the caller.** That is the
   right unit, but it means: `revoke` stays clean although it calls `delete_leaf`, which
   calls `unlink`, which relinks. Whoever charges the 5 : 1 surcharge to the callers too
   comes out higher.
4. **B3 asks only about the loop repertoire.** A body can be traversal-shaped and
   still cost 5 : 1 — because of `effects`, `locks`, linearity or the
   nesting limit of two (`arbitrary_mutations_never_panic`, `manifest.rs`:867, nests
   three deep and stands as **T** in the count). **The surcharge from B3 is not the
   design's distance to the floor but a summand in it.**

#### 5. An assumption that works in favour of the thesis and stands here so that it does not go under.

The count reads every Rust slice/array iteration as `elems of` resp. `slots of`. In
Gabbro that presupposes that the place is a **declared** collection with `count N`.
That obligation is not new and not booked here — it hangs on the class *Index*, which
the Neuerhebung of 2026-08-15 booked as **carried** (`index into T` inherits the
bound from `count N`, A3/`M103`). **If that booking falls, this number falls with it** — and
not by a few lines but by the 449 bodies with a loop that count here as
traversable.

##### **The back-computation, so that the later rebooking becomes a SUBSTITUTION and not a re-measurement**

A caveat that couples a number to an **open decision** must quantify the affected
subset — otherwise it is a warning without a price tag. **The tool has reported it
since this booking** (`./zaehle-b3.py … ` → section *RUECKRECHNUNG*):

| | Bodies | Lines | Share | Surcharge | Gate (bar 5 %) |
|---|---:|---:|---:|---:|---|
| **today** — class *Index* carried | 22 | 584 | **0,96 %** | +0,05 | **passed** |
| **hanging on it** (every body with a `for`) | +268 | +11 974 | | | |
| **were the Index booking to fall** | **290** | **12 558** | **20,67 %** | **+1,03** | **FALLEN** |

**The counter-computation is exact and not estimated:** the full count from R14(c) yielded
that **all** 347 distinct `for … in` expressions hit a domain and that **all
hit domains are `elems of`/`slots of`** — the chain domains (`descendants of`,
`queue`) run in `while`, not in `for`. *The affected set is therefore exactly: every
body with at least one `for`.*

> **Factor 21. The gate tips, and it does not tip narrowly.**
>
> **B3 thereby measures not primarily the loop repertoire but the Index booking.**
> The 0,96 % say: *"if `index into T` inherits its bound from `count N`, the
> repertoire carries the kernel."* They do **not** say that the repertoire carries it
> unconditionally. **The load-bearing item of this measurement is a booking of 2026-08-15,
> not a loop form.**
>
> *And the direction of the residual risk is thereby named: **the only thing that can
> overturn this measurement is not a recount on itself but a rebooking elsewhere.***

#### 6. What stands out and what this measurement CANNOT evidence.

Four of the largest N bodies are **checkers**: `audit_cdt` (100 L) searches cycles in the CDT,
`pruefe_bindung` (31 L) searches cycles in the handler chain, `is_below`/`scope_covers`
(36 L) check topology membership — together **167 of the 584 lines, 29 %**. It is
tempting to say that these bodies would not exist at all in Gabbro, because the invariant
stands in the type instead of in an auditor. **That is a conjecture, and this measurement
does not support it.** It counts bodies in the stock, not bodies in a counter-design. Noted,
not offset.

---

### The number for the K/A/W weight formula

```
p_B3        = 0,0096   (584 nicht-leere Zeilen von 60 756; aufgerundet 0,010)
Aufschlag   = p_B3 · 5,0  =  +0,048   ->  gerundet  +0,05
```

**To be substituted into the formula: `p_B3 = 0,010`, surcharge `+0,05`.**

**It is a LOWER BOUND** — for the four reasons under point 4, not because of an
abort. It is to be carried as `≥ +0,05` and **not** as an estimate.

**And the soberest finding at the end:** the surcharge lies **below the resolution of the
metric**. Even the wrong version 2 with 4,36 % would have yielded only +0,22. **B3 is
thereby settled as a cost item — and open as a list of sites for three missing domains
(`ancestors of`, union-find, chain-over-edge-function).** The second part is the
more valuable one.

### Check path

```
./zaehle-b3.py ../caprock-messbasis                 # 26 Ruempfe, 621 Z, 0,953 % / 0,961 %
./zaehle-b3.py ../caprock-messbasis --json=b3.json  # Marken + Belege je Rumpf
cd ../caprock-messbasis
grep -rniE 'fastpath|fast_path' --include=*.rs kernel crates              # 12
grep -rnE '\.(next|prev|first_child|next_sibling|prev_sibling|head|tail|link|sibling|parent|qnext|qprev)\s*=[^=]' \
     --include=*.rs kernel crates | wc -l                                 # 45
find kernel crates -name '*.rs' -exec cat {} + | grep -c '[^[:space:]]'   # 65 168
git status --porcelain | wc -l                                            # 0 — nur gelesen
```

Tool: [`zaehle-b3.py`](../zaehle-b3.py), markers and exceptions in the header comment and
in the regexes `KETTE`/`IDXKETTE`/`KANTENKETTE`/`CHIR`/`DOM_LINK_ABSTIEG`.

---

# SWEEP — die anderen Verbindungs-Invarianten, 2026-08-16

**What is NOT repeated here:** the paper pass at the CapSpace/CDT pair. That has been
run (K1–K3 plus four structural ones, the group exists as a `CapSpace` structure with
exactly three `refcount` write sites, lock imprint one `CAPS` RW lock), and E1–E3 in the
`TODO.md` cite it. **What was open was not the pass but the quantifier of the
proof rule** — *"**every** connection invariant occurring in the tree has a group whose
`ops` close it"* —, and for that the sweep for the **others** was missing.

**And B3 had already delivered the second test case**, without it having been booked as such:
the donation edges `sc_donor`/`sc_donee`, the measurably expensive part of `switch_to`, are
literally a connection invariant — reciprocity over **two TCBs**, the same form as the
Mdb siblings.

## The four found, each with carrier and lock imprint

| | Connection invariant | Carrier | Lock imprint of the group `ops` |
|---|---|---|---|
| **V1** | `refcount_matches` — counter in A against references in B | **one** structure (`CapSpace`) | **one** lock: `CAPS`, two-level |
| **V2** | **reciprocity of the donation edges** — `tcbs[t].sc_donor == Some(a)` ⟺ `tcbs[a].sc_donee == Some(t)` | **one** structure (`Scheduler.tcbs`) | **one** lock: `SCHEDS[core]` |
| **V3** | queue marker against the ready list — `tcbs[t].queued` against the actual linkage | **one** structure (`Scheduler`) | **one** lock: `SCHEDS[core]` |
| **V4** | **endpoint queue against thread state** — `t ∈ ep.receivers` ⟺ `IPC ∈ tcbs[t].reasons` | **TWO structures, two crates** (`caprock-ipc::Endpoint` / `caprock-sched::Scheduler`) | **TWO locks, two classes, declared order `EPS[i] < SCHEDS[core]`** |

**Sites (W7):** V2 — `crates/caprock-sched/src/lib.rs`:958–959 (setting), 1704–1705,
1937–1938, 1947–1948 (clearing), 1537/1596 (reading). V3 — ibid. 1881, 1912, 1823. V4 —
`crates/caprock-ipc/src/lib.rs`:513, 625, 652, 675, 692 against
`crates/caprock-sched/src/lib.rs`:930, 935, 1004, 1008; order in
`kernel/src/system.rs`:724 and :881.

## **V4 is the first imprint that is not a single lock — and thereby the first real test for the `locks` line of the group grammar**

> A group `ops` over V4 would have to **hold `EPS[i]` and `SCHEDS[core]`**, in that
> order, across two crates. **That answers the `locks ordered` question
> empirically: it is two locks with an order, not one shared one.**

**And the kernel says so itself, in the same line in which it hedges:** the
fault hook in `crates/caprock-microkit/src/lib.rs`:1303–1305 stands where it stands **because
it would otherwise take `EPS` under `SCHEDS` and invert the order.** *A group whose `ops`
declare the order would have made this comment superfluous — it is a hand-carried
connection invariant between two locks.*

## What the sweep did NOT find, and that is a finding of its own

**No double acquisition of the same lock class.** `kernel/src/system.rs`:15 says it
explicitly: *"no path takes two different `SCHEDS[*]` at once"* — migration runs via a
handover, not via two held instances.

> **The expected test case for `locks ordered` thereby falls away, and the one found is a
> different one:** not *"two locks of the same class"* but **two classes with an order across
> two crates.** *The grammar line must carry the second case; the first does not exist in the
> tree.*

## W12 — this is a filled map, no evidence of a complete one

**The quantifier of the proof rule is thereby NOT proved.** Four found means four found.
The search paths were: reciprocal field writes (`sc_donor`/`sc_donee`),
marker-against-structure (`queued`), queue-against-state (`receivers`/`reasons`),
counter-like quantities outside the caps. **What they systematically miss:** invariants whose
two halves do not share **the same name** and are **not** connected by an index field — for
instance a sum condition over two tables. *Whoever wants to close the proof rule needs a
mechanical sweep, not a search path; this one here is a candidate list with
sites.*

---

# Lesart A gebaut — and the predicted price did NOT occur

**The decision** (`TODO.md`, slot `M-effects-lesen`): reading is declared just as
completely as writing. **The pre-registered price was a factor of three** —
*"A drops 10 of 32 functions, C drops three"*.

## Measured after the pass was built

| | |
|---|---:|
| fragment functions that fall at `E010` | **0 of 32** |
| my own examples that fell | **2 files, 5 sites** |
| errors in `E010` itself that the first run uncovered | **4** |

> **The predicted price was an estimate, and it was too high.** `FRAGMENTE.md`
> already declares its reads — the ten expected dropouts do not exist. **What
> fell were my own examples**, and that is not a property of the reading
> but of my care in writing.

## What the first run found in `E010` itself — four things, two of them foreign

1. **The binder of a `match` branch counted as world state.** `Some(p) => …` reported `p`.
   **And that was an error of the WRITE half**: `lokale()` did not collect binders, so
   `E005` would have done the same for a `Some(p) => { p.feld = … }`. *The read half found an
   error that had lain in `E005` since 2026-08-14.*
2. **The binder of `update(v)`** — the old value of an `exchange` — likewise.
3. **A constant is not world state.** `v1_erhoehen liest GRENZE, erklaert aber pure`
   was right in wording and wrong in substance. Without this exception `pure` would be
   practically unreachable.
4. **A variant is not a place.** `IpcResult::Ok` and `Fehler::Buchfuehrung` were reported as
   unnamed reads.

## The restriction that follows from it — and what it costs

**`E010` speaks only about known world state**: `static`, `atomic`, `table`, `device`,
`state`. *In a complete translation unit nothing is lost by that* — an
unknown name already falls in the name pass. **In an excerpt it costs the whole bite**,
and that is the honest sentence about it:

> **On the fragment corpus `E010` has ZERO bite today** — not because everything is declared
> there but because excerpts do not declare their state. **The evidence that the rule bites
> therefore does not come from the corpus** but from three other places: two of our own
> examples fell (`09`, `14`), `beispiele/gift/62-lesen-ohne-reads.gab` falls with exactly
> one refusal, and **two mutations** in `mutiere-pruefer.py` damage the rule — one
> switches it off, the second *loosens* it (every `reads` line covers every site).

*The second mutation is the more important one, and the poison is built specially for it:
`pruefe_grenze` declares `reads Protokoll.slots` truthfully and reads `Objekte.slots` beside
it. **An effect list that names one read site looks complete.***

---

# The carrier group built — pass 10, and the pass list has grown

**R7 first, and this time without a shortcut:** the template entry stood before the grammar.
`S16 gruppe.ops` already existed (from «B13»); the sweep demanded a **second** one, because it
found a case the first does not cover:

| | Template | covers |
|---|---|---|
| S16 | `gruppe.ops` | groups over carriers under **one** lock (V1–V3) |
| **S17** | **`gruppe.sperrabdruck`** | groups over carriers with **different** locks (V4) |

> **A template that carries both cases as one hides the difference at which it
> can fail:** under one lock the preservation is a sequential argument, under
> two it hangs on the **order** and on no foreign writer coming in between the two
> acquisitions.

## The grammar line — and what it does NOT declare

```gabbro
group Zustellung over { Endpunkte, Faeden };
```

**The lock order does not stand at the group.** Every carrier lies under a
`lock … rank N`, and the ranks give the order. *A second declaration would be a second
truth about the same thing* — the same error class as two labelling systems with the same
names.

## Five refusals, and `U003` is the one V4 would have needed

| | |
|---|---|
| `U001` | the group names something that is **declared and not a carrier** |
| `U002` | a carrier of the group stands **under no lock** |
| `U003` | **a function writes two carriers of the group and does not hold all their locks** |
| `U004` | a group with **one** member — that is a table |
| `U005` | two locks of the group carry **the same rank** — there is no order |

> **`U003` makes a comment superfluous.** `caprock-microkit/src/lib.rs`:1303 explains
> why a function stands where it stands — were it to take `EPS` under `SCHEDS`, it would
> invert the order. **That is a hand-carried connection invariant between two
> locks**, and it is the measured need, not a design wish.

## Two guardians struck along the way, and both rightly

1. **The vocabulary ratchet** stopped `group` before it was allowed to be in the lexer — the
   word first had to stand in `SYNTAX.md`.
2. **The pass-list test** stopped the tenth pass: `assert_eq!(liste.len(), 9, "die
   Reihenfolge steht in SPRACHE.md Teil III §6")`.

> **The second is the more important one, and it did exactly what it is built for.**
> *"The specification is the pass list"* means, conversely: **a new pass is a change
> to the specification.** Without the test the tenth pass would have been one module more, and
> `SPRACHE.md` would have gone on claiming nine. **It is now booked in `SPRACHE.md`
> part III §6, with its reason.**

## And the coverage, as small as it is

**What is built is the lock imprint, not the invariant.** The group today names its carriers,
not its connection statement. `U003` says that not everything that is touched is held —
**not that the invariant holds.** *That stands here so that nobody reads the coverage
bigger than it is.*

**Evidence:** `beispiele/17-gruppe-ueber-zwei-sperren.gab` (the correct version),
`beispiele/gift/63-gruppe-halb-gesperrt.gab` (falls with exactly `U003`), and **two mutations**
— one switches `U003` off, the second *loosens* it: one held lock covers the whole
group. **58 of 58 caught.**

---

# `U006` — the third S17 obligation, and a surviving mutation

**Of the three obligations S17 places on a group operation, two now stand:**

| | Obligation | State |
|---|---|---|
| (a) | locks in rank order | **`U003`/`U005`** |
| (b) | invariant at the beginning **and** at the end | **open** — needs the clause |
| (c) | **no intermediate exit** | **`U006`** |

**(c) was checkable without any generation**, and that was not foreseeable: the obligation
sounds like a statement about a generated move but is one about the **control flow between the
first and the last write access**. *Whoever has written carrier A and leaves the body
before he has written B leaves the group in the intermediate state — and the
error path is exactly the place where that happens, because nobody looks there.*

## The surviving mutation is the yield, not the mishap

After poison 64 (`return` between the write accesses) the probe stood at **59 of 60**:

```
!! UEBERLEBT  gruppe-austritt-nur-return   U006 -- `let … else` ist kein Austritt
```

**63 poison probes did not notice that the checker had lost one of its three doors.** Poison
64 would never have caught it — it takes `return`.

> **A rule with three ways needs three probes, not one.**

**And the second attempt was not enough either.** Poison 65 first took
`let g = … else (fehler) { return false; }` — the else branch contained a `return`, so
the **`return` rule** caught the case, and the mutation went on surviving. Only an else branch
that **diverges** instead of returning (`aufgeben()`) isolates the `let … else` door.

> **Twice on the same day the same construction:** a probe that triggers the intended case
> but via a **different** rule. At `E010` it was the write half, here the
> `return` half. *A poison probe evidences a rule only if it would get through
> without that rule — and no refusal says that, only the mutation does.*

**State: 60 of 60.** `beispiele/gift/64-gruppe-zwischenaustritt.gab` (`return`),
`beispiele/gift/65-gruppe-austritt-durch-else.gab` (`let … else`, diverging else branch),
and the counter-probe: the same function with the check **before** the first write access goes
through cleanly.

## The coarseness has a direction (W9)

The order is the **source order** of the recursive descent, not the control flow.
An exit in a branch that cannot reach the second write access at all is
reported nevertheless. **Reporting too much is the safe side here** — the refusal says *"here
a way leaves the move"*, and whoever knows that this way does not exist has to write the proof
for it, not the pass.

---

# `U007` — the connection statement, and where the checker stops

**The third S17 obligation is now built as FORM, not as a proof.** The difference is
the whole statement of this section:

| | Question | who answers it |
|---|---|---|
| **form** | *Does this invariant name more than one carrier of the group?* | **`U007`, mechanically** |
| **preservation** | *Does it hold under every operation?* | **S16/S17 — a matter for the prover** |

> **`U007` is the same refusal as `U004`, one level lower:** there the **declaration**
> is a singleton, here the **statement**. And the reason is the same: *without this check
> `group` would be a more convenient notation for `table … invariant` — and a construct that
> is only more convenient has, by W3, no evidence.*

## The line as it now looks

```gabbro
group Zustellung over { Endpunkte, Faeden } {
    invariant wartende_haben_grund cost O(n) runs offline :
        forall e in slots of Endpunkte :
            Faeden.slots[Endpunkte.slots[e].wartet].gruende > 0;
}
```

**The body is optional.** Without it the lock imprint (`U003`/`U005`) and the move
(`U006`) bite — the group is therefore useful even before its invariant. *That was not planned
and is the second finding of this build: the two mechanical obligations from S17 do not hang
on the statement at all but on the control flow and on the ranks.*

## State of the carrier group

| | | |
|---|---|---|
| `U001`–`U002` | carrier exists, carrier is locked | |
| `U003`, `U005` | **(a)** locks, rank order | S17 |
| `U006` | **(c)** no intermediate exit | S17 |
| `U007` | **(b)** the statement connects | S17, **form** |
| — | **(b)** the statement **holds** | **open, a matter for the prover** |

**61 of 61 mutations.** Evidence: `beispiele/17-gruppe-ueber-zwei-sperren.gab` (group with an
invariant, clean), poison 63 (`U003`), 64 (`U006` via `return`), 65 (`U006` via `let … else`
with a diverging else branch), 66 (`U007`).

---

# REBOOKING: **Frame** is carried — `N_neu = 3`

**The class hung on one half and on one word.** The Neuerhebung booked it as hanging
with the reason *"`effects` checks writes, not reads"*, and the verdict of 2026-08-15 said:
*"the rest is no longer building work but a judgement"*.

**Both fell on 2026-08-16:** the reading is settled (**A**), and it is built
(`E010`). `effects` thereby holds all four parts — writes (`E005`), `locks` (`E006`/`E007`),
**reads** (`E010`) and the **call effects** (`E008` over the call graph).

## The limit is booked along, otherwise the booking is embellished

> **`E010` speaks only about declared world state** (`static`, `atomic`, `table`, `device`,
> `state`). On the fragment corpus the rule therefore has **zero bite** — excerpts
> do not declare their state.

**In a complete translation unit nothing is lost by that**, because an
unknown name already falls in the name pass. *The class thereby counts as carried for
translation units and not for excerpts — and because Gabbro compiles programs and
not excerpts, that is the right population.*

## State of the eleven classes

| | |
|---|---|
| **carried (8)** | Index · Overflow · Alias · Lock · Termination · Leafness · Publication · **Frame** |
| **hanging (3)** | **Race** · **Phase** · **Refinement** |

**And the three no longer hang on missing passes but each on something different** — that
is the actual progress over `N_neu = 5`:

* **Race** hangs on the **axiom layer**, not on a pass: the pairing pass stands
  (`V001`–`V004`), but that `release`/`acquire` *establish* the visibility the
  pairing claims is a statement about the memory model.
* **Phase** hangs on «B37» — `BootPhase` carries *exactly once*, not *in this order*.
* **Refinement** hangs on the **emission**, which does not exist.

> *Three classes, three different reasons, no common build.* Whoever wants to lower `N_neu`
> has from here on three projects ahead of him and no longer one building site.

---

# CORRECTION: what "0 of 571" says — and what it does not

**The number stays, the sentence beside it changes.** Until now it stood as *"99,04 % of the
kernel lines are writable as a traversal"*. That is the overreach form as a
statistic, and the B3 chain delivered the right frame itself.

> **`for` heads hit domains — the CHAINS run in `while`.**

Union-find, edge functions, the three «B41» gaps: they lie **by construction
outside the population of this count.** The 571 are the `for` loops; the hard
minority has no `for` form at all, so it could never appear in this number.

**The two sentences belong side by side, and both are strong:**

1. **The domain repertoire is COMPLETE for the counting-loop-shaped majority** — 0 of 571,
   and that went against expectation.
2. **About the hard minority the number says NOTHING**, because its loop form was not
   counted in.

*The first alone would be a statistic that conceals its own population — the same
construction as a filter that shrinks the population and appears as a success (W11).*

---

# IN ADVANCE — the 89 closures by kind of use, 2026-08-16

**R1 observed this time: this section is committed BEFORE the counting.** At B3 it
was not, and the booking there says so explicitly. *A rule that has once been missed
is visibly observed the next time or it is none.*

## The question

`dyn FnMut`/`Fn` — **89 sites**, and Gabbro has **no form** for it. The item counted
as the heaviest of the five necessary ones, because with it the question reads *whether*
instead of *how*.

> **The thesis being checked: the question is more decidable than it looks, because the 89
> sites break apart by kind of use — and every class already has an answer.**

## The three predicted classes, with their answer

| | Class | expected answer |
|---|---|---|
| **V-a** | **callback with ONE implementation** | becomes an ordinary call — **the Gabbro answer already exists: A2** |
| **V-b** | **stored handler in a table** | pointer plus context, **designable as a declared dispatch table** — the same medicine as `entry … dispatch`, only on the user side |
| **V-c** | **real combinator case** (iterator adapters, `map`/`filter` chains) | **prohibition** — in a language without genericity they would not be typeable anyway |

**If the count turns out this way, "whether" is a threefold "how / how / no", and the item
loses its special status.**

## The two-sided gate, written down before the run

| | |
|---|---|
| **passed** | **every one of the 89 sites falls into V-a, V-b or V-c**, and no class is the majority *through* the residual category |
| **fallen** | **more than 10 %** of the sites fit into none of the three → there is a fourth kind of use, and *that* is the design item |

**Invalid** (separate from unfavourable): the number of sites deviates by more than 10 % from
89 → then the count measures something other than the source of the 89, and the classes are
formed over a foreign population.

## The tipping rule

1. If it is unclear whether a callback has **one** implementation, it counts as **V-b** (more expensive).
2. If it is unclear whether a chain is a combinator, it counts as **V-b**, not as V-c —
   *prohibition is the cheapest answer and may therefore never be the answer in doubt.*
3. What falls into no class is **listed individually**, not rounded into one.

# ERGEBNIS — die Verschlüsse, 2026-08-16: **the gate is VOID, and the reason is the number itself**

## First the invalidity, because it comes before the result

**The pre-registered invalidity condition is triggered.** It read: *"the
number of sites deviates by more than 10 % from 89 → then the count measures something other
than the source of the 89."*

```
grep -rnoE "(dyn|impl|&|Box<)\s*(dyn\s*)?(FnMut|FnOnce|Fn)\s*\(" kernel crates   ->  64
grep -rnE  "\bdyn\b"                                              kernel crates   ->  67
```

**The 67 `dyn` sites reproduce exactly** — it is the same tree. **The 89 do not: the
reproducible value is 64, a deviation of −28 %.** And no plausible search path hits
89: closure literals `|…|` yield **441**, `move` closures **16**, `Box<dyn Fn*>` **0**.

> **The 89 is a number without a search path** — exactly the class W7 stands against, and it
> survived the W7 sweep of 2026-08-15 because it stood in a *table* and not in
> a sentence. **Whoever checks only sentences does not find it.**

**The gate is thereby void. A new one is NOT set now** — that would be R2. What follows is
a **descriptive count without a gate**, and it is marked as such.

## The descriptive count over the reproducible population (64)

| Class | predicted | **measured** |
|---|---|---|
| **V-a** callback, passed as a parameter | majority | **practically all** — 39 directly in parameter lists, the rest in multi-line signatures |
| **V-b** stored handler in a table | a class of its own | **ZERO.** `Box<dyn Fn*>` = 0, struct fields with an Fn type = 0 (all 20 hits are multi-line *parameters*) |
| **V-c** combinator (iterator adapter) | a class of its own | **not in this population** — it lives in the 441 closure literals, of them **270** in `.map`/`.filter`/… |

## **The actual finding: there are TWO populations, and "89" names neither of them**

| | Population | Number |
|---|---|---:|
| **P1** | mentions of the `Fn` traits as a **type** | **64** |
| **P2** | **closure literals** `\|…\|` | **441**, of them 270 in iterator adapters |

**The prediction mixes them:** V-a and V-b are statements about P1, V-c is one about P2. *A
classification over a population that means two things at once cannot pass
or fall — it can only look as if it did.*

## What the prediction nevertheless had right, and it is the expensive half

**V-b is EMPTY, and that is the cheapest refutation that was possible.** The class was the
only one that would have demanded a **new construct** (declared dispatch table,
user-side `entry … dispatch`). *It does not occur in the tree.*

**And the dominant use is ONE:**

```
&mut dyn FnMut() -> Option<u64>      25 Fundstellen   (mmu, smmu, vtd)
```

**The page-table allocator, the same callback passed through 25 times.** That is not a
closure in the sense of the question — it is **a callback with one implementation**, hence
literally A2, and Gabbro's answer has stood since 2026-08-14.

**The second largest is an old acquaintance:**

```
impl Fn(u16) -> Option<u16>           3 Fundstellen   (sched/redirect.rs)
```

**That is the edge function from «B41».** The closure item and the third
domain gap are **the same subject**, and neither of the two investigations noticed that
until both numbers lay side by side.

## Verdict

> **The closure item loses its special status — but not because the prediction came
> out, but because the population was wrong.**

* **P1 (64)** breaks apart into *"callback with one implementation"* (A2, decided) and
  *"edge function"* (the line question from «B41»). **No new construct, one open line.**
* **P2 (441)** is a different question and is properly called *"does Gabbro need iterator
  adapters?"* — and it hangs on **genericity**, not on closures.

**What was booked as "the heaviest of the five necessary ones, because the question reads
*whether*" is, after this count, two questions, one of which is already answered and the other
of which is called genericity.** *The item was not hard, it was blurred.*

## Addendum to the closure count: **the error form has a predecessor in the same folder**

**A classification over a double set cannot pass or fall — it can only look as if
it did.** The prediction treated *"89 closures"* as **one** set that was **two**:
type mentions (P1) against literals (P2).

> **That is the same error form as the two generator rates over different samples
> — only in the DESIGN instead of in the measurement.**

*There it was two rates over two populations that were read as one; here it
is a prediction over two populations that was written as one.* The rule
that follows from it already stands (W11: every ratio names its N) — **it holds for
predictions too, not only for measurements.**

## And the convergence nobody looked for

**The heaviest "whether" item and the last «B41» gap were the same subject.**

| | | |
|---|---|---|
| **25×** | `&mut dyn FnMut() -> Option<u64>` | the allocator callback — **literally A2, answered since 2026-08-14** |
| **3×** | `impl Fn(u16) -> Option<u16>` | the **edge function** — the domain line whose line has stood since the cut |

**The list of five necessary ones is thereby really a LIST OF FOUR**, and the item that was
the only one called *"whether"* has broken apart into **two already decided "how"s**.

> **Neither of the two investigations saw it until the numbers lay SIDE BY SIDE.**

*That is a quiet argument that this document will at some point need a cross-reference
column — which measurements share sites. Bookkeeping for later, not an item for now.*

---

# IN ADVANCE — `table.induktion` into Isabelle, the first template

**Pre-registered on 2026-08-16, before a line of Isabelle is written.** The same
discipline as with the closures, and for the same reason: *at B3 it was missing, and the
booking there says so explicitly.*

## Why this item gets the head of the critical path

**Not because of the effort — because of a curve.** The amortisation argument of the whole
design reads: *a template falls **once**, not per program.* It is the only
difference between the template list and seL4's mountain of proof.

> **And it holds only from the first PROVED template on.** Until then it is an assurance
> about a surface nobody has set foot on. **One proved of eighteen is qualitatively something
> other than zero of seventeen:** the register changes from *"list with a length"* to *"list
> with a fall direction"*.

## **The expected outcome — and it is NOT "confirmed"**

**The prediction, so that the result is not read over:** the formalisation will almost
certainly **not simply confirm** the template. The likely outcome is that it
**flushes out the side conditions** the prose version silently carries. Four stand there
by name as candidates, so that nobody can say afterwards that he had meant them:

| | expected silent assumption |
|---|---|
| **N-1** | **finiteness of the domain** — the prose says "well-founded", not "finite"; for `slots of` it falls out of `count N`, for `descendants of` not without further ado |
| **N-2** | **stability of the witness ordering** under **exactly the generated mutations** — not under arbitrary ones |
| **N-3** | **the empty-set clause** — it once stood there as a mere **implication** instead of as an obligation of its own (`consuming.leermenge`) |
| **N-4** | **completeness of the scheme** — that the generated induction principle covers **all** cases, not only the occurring ones |

## How the result is booked — fixed in advance so that the direction does not wander

> **Every flushed-out side condition is a GAIN and is booked as such** — as a
> **sharpening of the template entry**, not as a setback.

*That is exactly why one climbs the first slope: not to write "proved" into the register
but to learn **what the register has concealed so far**.*

## The gate, two-sided — and the suspicious result is the smooth one

| | |
|---|---|
| **good** | the template goes through, **and at least one silent assumption is flushed out** and stands afterwards in the entry |
| **also good** | the template does **not** go through — then an assurance of the folder is refuted, and the cheapest of them all at that |
| **SUSPICIOUS** | the template goes through **smoothly**, **without flushing out a single silent assumption** |

> **The third outcome is the only one that triggers a counter-check.** A prose template
> that loses nothing on formalisation was either already written formally — or the
> formalisation silently took over the same assumptions. *For an entry that
> has counted for days as "the smallest one" and never came up, the second explanation is the
> more likely one.*

**Invalid** (separate from unfavourable): the Isabelle version formalises **a different
statement** from the template text — then the run measures the translation, not the template.
The probe for it is mechanical: **every sentence of the entry `table.induktion` must be
assignable to a line of the formalisation, and vice versa.**

# RESULT — `table.induktion`: **four assumptions flushed out, NOT proved**

## First the blocker, because it comes before the result

```
isabelle  coqc  lean  lean4  agda  z3  cvc5  why3  alt-ergo   ->  keiner vorhanden
```

**On this machine no prover is installed.** The template is thereby **not
proved**, its `Stand` stays `Entworfen`, and the ratchet mark stays, torn as it is, at
17 of 18.

> **A `.thy` file nobody has checked is a prose template in a different script.**
> To book it as a proof would be exactly the grip this register stands against — and it would
> be more expensive than with any other number, because the register is the **only** surface
> whose purpose is the shrinking of the trust basis.

**What was run nevertheless** is the part whose pre-registered yield does not hang on the
machine check: *not to write "proved" into the register but to learn
what the register has concealed so far.* The formalisation stands as
[`beweise/Table_Induktion.thy`](../beweise/Table_Induktion.thy), marked in its header as
**unchecked**.

## The predicted outcome occurred — **all four**

| | predicted | **found** |
|---|---|---|
| **N-1** | finiteness of the domain | **yes — and sharper:** it falls **not out of this declaration** but out of `table.indexschranke`. A linking field without a range bound points out of the table |
| **N-2** | stability of the witness ordering under the generated mutations | **yes — as a LIMIT:** the principle holds for **one** state and says **nothing** about a mutating traversal. That is `consuming.ordnung`, a different template |
| **N-3** | the empty-set clause | **yes — but in the other direction** (see below) |
| **N-4** | completeness of the scheme | **yes:** `vollständig` was ambiguous, and for `chain(a,b) in` the scheme needs **two premises**, not one |

**The suspicious result — gone through smoothly without a single flushed-out assumption — did
NOT occur.** The counter-check falls away.

## The most uncomfortable of the four is N-3, and precisely because it pointed in the wrong direction

**What was expected was a MISSING clause. What was found was a WRONGLY ASSIGNED one.**

The base case is **absorbed** in the induction principle — for a leaf the premise is
vacuously satisfied. No empty-set clause is needed here at all. What `consuming.leermenge`
claims is something else: that the **generated witness set is complete**.

> **A missing clause one adds. A wrongly assigned one has until then reassured at the
> wrong place.**

## And the structural find nobody predicted

**N-1 uncovered a dependency between templates.** `table.induktion` rests on
`table.indexschranke` — and the entry did not name that.

> **A template list without dependencies looks like 17 independent items — and is
> not.** Whoever fells one possibly fells it **underneath** one that is still standing.

**Built:** `Schablone::haengt_an`, with a test that falls on missing targets (*a
dependency on a missing name is worse than none — it looks like a booked
relation*). Two edges stand: `table.induktion → {table.indexschranke,
consuming.ordnung}` and `consuming.ordnung → table.induktion`. **The second is a cycle,
and it is real:** the ordering needs the scheme, the scheme needs the ordering for the
mutating case. *That is no bookkeeping mishap but the thing itself — and it means
that the first proved template cannot separate these two.*

## What the entry now says instead of two words

The old version read, in full length: *"The induction scheme generated from the `table`
declaration is well-founded and complete."* **Two words, four gaps.** The new one
names N-1 to N-4 individually and says explicitly: **well-foundedness is a hypothesis, not a
result** — the declaration must name the load-bearing invariant.

> **The slope has been climbed, the summit not. What it threw off is worth more than what
> would have stood at the top:** a "proved" in the register would have changed one line; the
> four flushed-out conditions change what the template claims at all.

---

# RESULT II — `table.induktion` is **machine-checked**, 2026-08-16

**Isabelle2025-2 is installed and the theory goes through.**

```
Session Unsorted/Gabbro
Gabbro: theory Gabbro.Table_Induktion 100% (0.293s cumulated time)
Finished Gabbro (0:00:01 elapsed time)
```

`sorry`/`oops`: **0.** Five lemmas, two definitions.

## R14 holds for the prover too: it must be able to reject

**Before the result was booked, a false claim was inserted** —
`kante_bleibt_im_bereich` with `shows "d < N ∧ False"`:

```
*** ⟹ False
*** At command "by" (line 143 of "…/Table_Induktion.thy")
Unfinished session(s): Gabbro
```

**The checker rejects.** *A green run whose tool can never go red is no
result — the same rule every measurement of this folder starts with.*

## The invalidity probe: sentence against line, in both directions

| Sentence of the entry | Line of the formalisation |
|---|---|
| **N-1** finiteness | `im_bereich`, `kante_bleibt_im_bereich`, `traeger_endlich` |
| **N-2** one state | `kante :: tabelle ⇒ (idx × idx) set` — the state is a **parameter** |
| **N-3** base case absorbed | `blatt_ohne_eigene_klausel` |
| **N-4** two premises | `kante` as a union, `table_induktion_zwei_kanten` |
| well-foundedness is a hypothesis | `assumes wf` in `table_induktion` |

**Conversely: no line of the formalisation without a sentence in the entry.** The probe is
passed.

## **Two limits, and the second is the uncomfortable one**

**First: what is proved is the MATHEMATICS, not the delivery.** That a *generator* emits this
scheme is not formalised — there is no generator, `mutiere-pruefer.py` reports
the emission surfaces with **0 mutations**.

**Second, and that is the limit one easily conceals:**

> **The four side conditions were flushed out by HAND WORK, not by the machine.**
>
> The first attempt should have failed at the checker — a forward reference to a never
> defined function. **I corrected it beforehand.** The machine thereby *confirmed*,
> it did not *discover*.

*A formalisation that only writes down what its author believed anyway cannot flush out more
than he saw. Only an independent one would find that.*

## What changes by it — and it is not the number

**`17, of them 16 unproved`.** The number has fallen by one, and that is the smaller part.

> **For the first time the amortisation argument holds not as an assurance but on a case.**
> Until today the difference between the template list and seL4's mountain of proof read: *"a
> template falls once, not per program"* — a claim about a surface nobody
> had set foot on. **Now one has been set foot on.**

**And the test enforced the bookkeeping**, as it should: `ungedeckt() == SCHABLONEN.len()`
fell until the number here **and** in `BEWEIS.md` had been brought up to date. It now stands
at **16** — *whoever proves the next one falls again; a number that quietly moves along is no
ratchet.*

---

# IN ADVANCE — three further templates, and the yield is MEASURED ALONG (2026-08-16)

**Committed before the first line of Isabelle.** What is run is **S12**, then **S1 + S2
together** — separately it does not work, `consuming.ordnung` and `table.induktion` form the
cycle from the same day.

## Why exactly these three, and not all sixteen

**S12 first, because the proof of S4 rests on it.** `traeger_endlich` assumes `im_bereich N σ`
— and that is literally what `table.indexschranke` owes.

> **A proved template that rests on an unproved one has not shrunk the trust basis
> but shifted it.**

*Of the sixteen, four are not provable at all (the construct does not exist — a proof
about it proves a wish and afterwards looks like coverage), two wait for another
surface (generator, memory model), ten would be formalisable. **Sixteen in one go, by the same
author, would be the largest green surface of this folder and the least measured one.***

## **The actual measurement: the YIELD, not the ticks**

The yield of a formalisation is not the word *proved* but **what it flushes out**.
There is exactly **one** data point: `table.induktion` released **4** silent assumptions.

**Predicted, per template:**

| | Prediction | Justification |
|---|---|---|
| **S12** | **1–2** | the entry is concrete (*"covers exactly the occupied slots"*), but *"the lowering lays out N slots"* is a statement about the **emission**, which does not exist — that one I expect as a limit |
| **S1** | **2–4** | *"the ordering is preserved under the generated mutation"* — **under WHICH mutations** does not stand there |
| **S2** | **0–1** | the sentence is already sharp (*"if it is empty, the domain is empty"*) — here I expect the least |

**Sum predicted: 3–7.**

## The two-sided gate for the yield

| | |
|---|---|
| **the register was more honest than feared** | **≤ 2** flushed out over all three → the remaining twelve are diligence without insight, and *that is a good result* |
| **the register has systematically concealed** | **≥ 8** → then the question is not *"prove all 16"* but **why the entries are written so imprecisely** — and that is a finding about the procedure, not about the templates |

*Between 3 and 7 lies the prediction; hitting it is the most boring outcome and
says the least.*

## What makes it invalid

* **U-a** One of the three formalises a different statement from its entry (sentence against
  line in both directions, as at S4).
* **U-b** The prover runs without a negative control — **every** theory gets an
  inserted false claim, and it must fall.
* **U-c** A "flushed-out side condition" is counted that already stood in the entry. *Only
  what did NOT stand there before counts.*

## And the limit that remains from S4

**The machine confirms, it does not discover** — the conditions are flushed out by hand work.
That holds here too, and it is the reason why the yield number **is a statement about my
care in writing, not about Isabelle.**

---

# RESULT III — three templates, and the yield has a category nobody provided for

**All three have been run, all three go through, all three with a negative control.**

```
Gabbro: theory Gabbro.Table_Induktion    100% (0.359s)
Gabbro: theory Gabbro.Table_Indexschranke 100% (0.100s)
Gabbro: theory Gabbro.Consuming          100% (0.159s)
```

`sorry`/`oops`: **0** in all three files. **U-b satisfied:** into every theory a
false claim was inserted, and every one fell (`Failed to finish proof`, line 35 resp. 40 resp. 45).

## The predicted number is right — **and it is the less important half**

| | predicted | flushed out | **refuted** |
|---|---|---:|---:|
| **S12** `table.indexschranke` | 1–2 | **2** | **1** |
| **S1** `consuming.ordnung` | 2–4 | **2** | **1** |
| **S2** `consuming.leermenge` | 0–1 | **1** | 0 |
| | **3–7** | **5** | **2** |

**5 flushed out — in the middle of the prediction, hence the most boring outcome.** The gate
says neither *"the register was honest"* (≤2) nor *"systematically concealed"* (≥8).

> **But the pre-registration did not know the right-hand column.** It asked for *silent
> assumptions*. What was found were **two sentences that are plainly FALSE** — and that is a
> different class from a missing condition.

## The two refuted sentences

**M-1 — `table.indexschranke`:** *"The generated index type `0 ..< N` covers **exactly** the
occupied slots."* **False.** A table with `count 80256` and three occupied slots has an index
type with 80256 values. Counter-example: `indextyp_deckt_nicht_nur_belegte`.

**K-2 — `consuming.ordnung`:** *"the ordering is preserved under the generated mutation."*
**False for the relinking.** `umhaengen_kann_zyklus_erzeugen` constructs a
well-founded state out of which **one** relinking makes a loop.

> **And that is no edge case:** the stock does both in **one** move — `delete_leaf` calls
> `unlink`, and `unlink` rewrites the sibling pointers of the **neighbours**. **B3 counted
> exactly that as marker Nb2** (`space.rs:1044`), without anybody seeing the connection.

## The third find, and it destroys the ordering of the list

**K-3:** *"From it leafness at the moment of consumption falls out."* — **It does not fall out
of it.** `wf` says that minimal elements **exist**, not that the traversal
**takes** one. The missing condition is called `waehlt_minimal` and is an **additional
obligation on the generation**, not a consequence.

*A "falls out of it" in a proof obligation is the most expensive formulation of all: it
promises that at this place nothing more is to be done.*

## **The booking, and it is uncomfortable**

| | before | after |
|---|---:|---:|
| entries | 17 | **19** |
| proved | 1 | **4** |
| **unproved** | **16** | **15** |

> **Three formalisations — and the number of the unproved fell by ONE.**

The reason: two entries had to be **split**, because they were half provable and half over
a nothing. `table.indexschranke` → `+ table.absenkung` (talks about the emission, which
does not exist). `consuming.ordnung` → `+ consuming.umhaengen` (the blanket version is
**refuted**, not open).

> **The trust surface has not shrunk. It has for the first time been SURVEYED** —
> and became larger in the process, because the measuring makes visible the half-measures a
> prose line could hold together.

## What that means for "all sixteen"

**Of three checked entries two contained a false sentence.** That is the answer to
the question whether one should push the rest through — and it reads differently from before:

> **The register is not a list of proof obligations. It is a list of drafts**, and
> every third sentence in it does not withstand a formalisation.

*The work is thereby not "sixteen proofs" but "edit nineteen entries" — and
that is cheaper, but it also means that the number `17 unproved` was never a number about
proofs but one about unfinished sentences.*

---

# IN ADVANCE — editing all 19 template entries (2026-08-17)

**Committed before the first entry was read.** No proving — **reading**, against the three
error forms the formalisation of S4/S12/S1/S2 **measured**.

## The three markers

| | Marker | Example from the measurement |
|---|---|---|
| **F-1** | **"exactly" / "all" / "only"** — a claim that is too strong and thereby false | S12: *"covers **exactly** the occupied slots"* |
| **F-2** | **a singular where several cases stand** — and at least one of them does not hold | S1: *"under **the** generated mutation"* |
| **F-3** | **"falls out of it" / "thereby holds"** — promises that at this place nothing more is to be done | S1: *"**from it falls out** leafness"* |

**In addition a fourth one that comes from S12/M-3 and is not a linguistic form:**

| **F-4** | **two halves in one entry**, one of which talks about a subject that does not exist |

## The expected value, so that the result is not read over

**Out of 3 checked entries 2 came with a false sentence.** Naively extrapolated: **about 12 of 19**.
*That extrapolation is the worst sort of number* — n = 3, and the three were not chosen at
random but were the most formalisable ones. **It stands here as a prediction, not as an
estimate**, so that one can beat it.

**Predicted: 8–14 entries with at least one marker.**

## The two-sided gate

| | |
|---|---|
| **the two out of three were an outlier** | **≤ 5** marked → the register is better written than the sample suggested, and the editing is an afternoon |
| **the rule, not the exception** | **≥ 12** marked → *"17 unproved" was never a number about proofs*, and the register needs a writing rule before another entry is added |

**Invalid:** a marker is awarded without quoting the sentence that carries it. *Every marker
names its wording — otherwise the editing is an opinion with a counter.*

# RESULT — editing all 19 entries: **11 marked**

**Predicted were 8–14. Measured: 11.** The gate says neither *"outlier"* (≤5) nor
*"the rule"* (≥12) — **and it misses the second threshold by ONE entry.**

> *A gate that tips on one item measures the definition along with it* — the same sentence
> as at the K/A/W borderline, and it holds here just as much.

## The eleven, each with its wording (U condition of the pre-registration)

| Entry | Marker | the sentence that carries it |
|---|---|---|
| `table.ops.erhaltung` | **F-1** | *"**every** `online` invariant is preserved"* — a **connection** invariant is preserved by no single-carrier operation; that is exactly what `gruppe.ops` exists for |
| `transition.transset` | **F-1** | *"**no** intermediate state is observable"* — observable **by whom**? On a multicore machine empty |
| `exchange.rmw` | **F-4** | *"is atomic **and** the body pure"* — atomicity is the axiom layer, purity is pass 8 |
| `accumulates.monoid` | **F-1 + F-4** | *"yields **the same value** as an atomic RMW"* — only at a quiescent point, not concurrently |
| `walk.mappings` | **F-1** | *"hits **exactly** the reachable leaf entries"* — a large page maps **above** the full depth |
| `format.roundtrip` | **F-1 + F-4** | *"checks the buffer length **exactly once** at entry"* — false for **variable** lengths, and those are open |
| `entry.abdruck` | **F-4** | *"and the stack switch is **correct**"* — correct **against what**? An indeterminate predicate is no obligation |
| `device.konstruktor` | **F-4** | *"the register layouts hit the **hardware** layouts"* — showable in no prover; axiom layer |
| `ops.suche` | **F-2** | *"in **the** ordering of the domain"* — `chain(a,b)` has two kinds of edge, hence none |
| `state.reset` | **F-1** | *"holds from **EVERY** state"* — from one with a held linear value it would be a leak; M2 forbids it |
| `gruppe.ops` | **F-4** | carries the **lock imprint** a second time, which `gruppe.sperrabdruck` has carried since 2026-08-16 |

## The distribution is sharper than the number — and it is an AFTER-THE-FACT split

**The gate stood over the 19. This column did not stand in the pre-registration** and is
therefore carried as a finding, not as a gate result:

| | Entries | marked |
|---|---:|---:|
| **written or edited today** | 7 | **0** |
| **older** | 12 | **11** |

> **Eleven of twelve older entries carry a marker. The twelfth is
> `verbund.konstruktor`** — *"sets every field exactly once and leaves none uninitialised"*,
> a sentence that defines its own condition instead of claiming it.

**That is the answer to the question whether 2 of 3 were an outlier: they were not.**

## What follows from it, and it is not proof work

**The four markers are writing errors, not thinking errors** — and three of them have a rule
that can be written down:

> **F-1:** *"exactly", "all", "every", "no"* in a proof obligation needs evidence
> **in the same sentence**, otherwise it is a claim about an edge nobody has checked.
> **F-2:** a singular over a domain with several kinds of edge is none.
> **F-3:** *"falls out of it"* promises that nothing more is to be done — and was wrong both times.
> **F-4:** two obligations in one sentence cannot fall individually.

**None of these rules needs Isabelle.** *The most expensive insight of the day is that the
formalisation achieved above all one thing: it forced me to read the sentences I had
written myself.*

---

# `ancestors of` built — «B41», and the build uncovered an older gap

**The first construct need MEASURED by the convergence metric is built.** A domain line,
the same generation logic as `descendants of`, the same edge — the other direction. It
inherits the bound, and for the same reason: *an ascending chain cannot, without a cycle, be
longer than the table has slots.*

## And doing so something came to light that has nothing to do with `ancestors of`

The first example fell with `K003` — **no bound**. The counter-probe with `descendants of`
at the same site fell **just the same**:

> **`traverse … over descendants of g` with `g : index into T` had never had a bound.**
> The table name came **unqualified** out of the index type, the capacity table keys
> **qualified** — the resolution silently fell out, and `K003` made a refusal about
> the *declaration* out of it instead of about the *resolution*.

**No example had ever triggered the site.** The corpus carries `descendants of`
exclusively in **predicates** (`ensures !exists k in descendants of s: …`), and there
no cost pass runs.

> *A bound that was never triggered is not covered but undamageable —
> the same class as an emission surface with 0 mutations.*

**Two mutations secure both**: `vorfahren-ohne-schranke` (the new domain loses its
inheritance) and `indextyp-nennt-seine-tabelle-nicht` (the uncovered gap). **65 of 65.**

## What «B41» thereby still has open

| | Gap | State |
|---|---|---|
| 1 | `ancestors of` | **built** |
| 2 | chain over an edge function | **the line stands** (`SPRACHE.md`, the cut) — design line open |
| 3 | union-find | **prediction: gets no traversal form** |

*Of three measured gaps one is built, one decided and one predicted.*

---

# THE FIRST YES-STATEMENT — one fragment, all the way through (2026-08-17)

**Until today the emission surface did not exist.** `mutiere-pruefer.py` reported it with
**0 mutations**, and *what has 0 mutations is not covered, it is undamageable*. It was the
largest such surface in the folder, and three things hung on it: the plumbing class
**refinement**, the templates `table.absenkung` and `table.ops.erhaltung`, and the **licence
notice** that `LIZENZ-ZUSATZ.md` demands in generated C while nothing wrote it.

## The chain, and every link had to hold

```
.gab  →  gabbro emit  →  C  →  cc -std=c11 -Wall -Wextra -Werror  →  run  →  compare
```

| | |
|---|---|
| 1. emit | ok — 29 lines of C from `beispiele/16-by-ops-am-feld.gab` |
| 2. licence | ok — `Generated by Gabbro` in the header |
| 3. `cc -Werror` | ok — **no warning** |
| 4. **result** | ok — **`42 1 8 0`** |
| 5. speech test | ok — a falsified artefact falls |

**What the four numbers say, one by one:** `stand()` returns what was written · `belegen()`
sets `benutzt` · the array has the **8 slots from `count N`** · and slot 0 is untouched, so the
operation hits **one** slot.

> **Stage 4 is the one that turns the other three into a statement.** A generator that produces
> compilable C computing something else is worse than one that produces nothing — *it looks
> like a result.*

## R14 applies to the emitter too

Before booking, the emitter was made to lie: `return x` became `return 0*(x)`. The guardian
fell at stage 4 with `0 1 8 0`. **A differential test that cannot go red measures nothing.**

## What the emitter refuses — and that it refuses at all

`C001` is the whole design: **for every form this one fragment does not need, the emitter
refuses by name instead of emitting something plausible.** It found its own first two errors
that way during construction — `bool` was not a path, and `Zaehler` was a named type — and
both times it stopped instead of guessing.

**One of those stops was a real design error, not a gap:** the first version lowered a path
naming a table to `uint32_t` and called that *a coarsening in the safe direction*.

> **It was not coarse, it was wrong.** `ptr<normal, r> Objekte` became `const uint32_t *`, and
> the generated C would have compiled while pointing at the wrong thing. *W9 asks for the
> direction of a coarsening; it does not license one where the exact answer is available.*

## What this is NOT

**One fragment, not ten.** Nine further fragments are unchecked. The emitter covers exactly the
forms this file uses: `table` with `count`, range types, `bool`, `index into T`, pointer
parameters, field and index access, assignment, `return`. **Loops, `match`, `locks`, `publish`,
`exchange`, every generated operation — none of it is lowered**, and `C001` says so at each.

**And the plumbing class *refinement* is not carried by this.** What has been shown is that
*one* lowering produces what it promises for *one* file, checked by execution. Refinement is a
statement about **every** lowering.

> **The surface is no longer undamageable, and that is the whole of today's gain.** Two
> mutations now bite in it (`67 of 67`): one turns the table pointer back into `uint32_t`, the
> other drops the licence notice. Before today neither could have failed.


---

# VORAB — NEUZUWEISUNG: the 74 proof obligations, with `file:line`

**Separate commit, BEFORE the count. After the run nothing in this section is changed.**

## Prior history, in one sentence

The aggregate **74 / 17 / 57 / 19 / 1** was assigned on 2026-08-14 over ten hand-translated
fragments; on 2026-08-15 the W7 sweep found that the whole section carries **exactly one**
`file:line`, and that one belongs to the eager-FP question. Verdict then: **invalid, not
unfavourable** — *the count is not run, the basis is established first.* The folder wrote down
the order itself (`MESSUNGEN.md`, *What is to be done now*): reassign · then the K/A/W split ·
and carry the marking **newly assigned, not reconstructed**.

## Population, and it is frozen

`dokumente/FRAGMENTE.md` @ commit `708beed`, the ten ```gabbro blocks:

```
F1  92-349 (258)   F2  397-530 (134)   F3  554-704 (151)   F4  753-896 (144)
F5 919-1018 (100)  F6 1047-1163 (117)  F7 1280-1333 (54)   F8 1409-1461 (53)
F9 1503-1550 (48)  F10 1624-1668 (45)                      = 1 104 lines of Gabbro
```

The file carries its own freeze sentence (*"a record of 2026-08-14 and stays untouched"*), so
the line numbers are stable. **The anchor of every obligation is `FRAGMENTE.md:NNN`**; the
Caprock origin stands per fragment in its header and is not repeated per line.

## What is counted

**An obligation is a statement that must be true for the fragment to be correct**, at a named
line. It arises from exactly one of eight events — **one obligation per (line, event)**, and
repeated occurrences of the SAME statement at the SAME line collapse to one:

| | Event | recognised at |
|---|---|---|
| **A** | **declared clause** | `requires` · `ensures` · `maintains` · `invariant` · `axiom` · `progress` · `variant` |
| **B** | **index** | an expression indexes a `table`, an array or a slot |
| **C** | **bounded arithmetic** | `+` `-` `*` on a range type or a `wrapping` type |
| **D** | **ownership move** | `own` · `consume` · `by consuming` · a linear value handed on |
| **E** | **lock** | an acquisition · `locks` · `locks shared` · `held` |
| **F** | **ordering** | `publishes` · `awaits` · `exchange` · atomic access · barrier · `mirrors` |
| **G** | **loop** | **one per loop head** — its termination argument |
| **H** | **lowering** | **one per fragment** — the refinement of this fragment to C |

## The three columns, and the third is the yield

1. **The statement**, in words.
2. **K or L**, by the criterion of `BEWEIS.md`: *mentions only the MACHINE → K (plumbing);
   mentions the SUBJECT → L (logic).*
3. **Who discharges it** — a **refusal code of a present-day pass** (`M103`, `E005`, `U003`, …)
   or a **named gap**. Never "presumably".

> **The interesting cell is K with a gap.** `BEWEIS.md` fixes the abort condition as *"a named
> plumbing obligation remains that the programmer has to discharge by hand"* — so **every K
> without a code is a breach of the thesis at that site**, and it is the number this run exists
> to produce. Call it **H** (hanging).

## The two-sided gate

| | |
|---|---|
| **passed** | **H = 0** — no plumbing obligation on the ten fragments stays on the human |
| **missed** | **H > 0**, each with fragment, `FRAGMENTE.md:line`, statement and named gap |
| **invalid** | the R14 calibration fails and cannot be repaired · **or** more than 10 % of obligations are **disputed** (the criterion does not decide them) · **or** the enumeration aborts — then R16: the number is a **lower bound** and is called one |

**The bar is not moved.** `BEWEIS.md` set it at "no hanging plumbing obligation", and it stays
there. *The old aggregate itself named 19 hanging ones — a gate at 19 would be a gate on a
number nobody can evidence any more.*

## R14 — the harness first, and it has a published answer to hit

**`delete_leaf` is part of F1 and was already broken down on 2026-08-15:** 11 obligations,
**4 K / 7 L** (`BEWEIS.md`:1078–1092). The generation rule above is applied to `delete_leaf`
**first**, before anything else is touched.

* **Hits 11 with 4 K / 7 L** → the rule measures what the folder has already measured, and the
  new count is **commensurable** with the 1,75 : 1.
* **Comes out different** → the rule is **corrected before the other nine fragments are
  read**, and the correction is booked with its reason. *A rule tuned after seeing the result is
  an R2 breach; a rule calibrated against a published result before the run is R14.*

## The search path is mechanical, the classification is not

`zaehle-pflichten.py` enumerates the **candidate lines** per event class over the ten blocks and
prints `FRAGMENTE.md:NNN` for each. It guarantees that no line is missed; it cannot decide
what a statement says. **Both numbers are reported** — candidates from the tool and obligations
after the hand pass — so every correction is visible instead of absorbed.

## The prediction, written down before the run — R11

The old aggregate says 17 L against 57 P: **0,3 : 1**. The `delete_leaf` re-count says
**1,75 : 1** — and `delete_leaf` is one of these ten fragments. **Both cannot be right.** If the
old 17 held, `delete_leaf` alone would carry **7 of them** and the remaining nine fragments
**10 between them**.

**Predicted:** the fresh count lands **far above 74 in total and far above 17 in L**, because
the old count was at the coarse granularity the `delete_leaf` re-count already refuted
(proof steps instead of obligations, `BEWEIS.md`:1098).

> **If it lands near 74 / 17, that is the suspicious outcome, not the confirming one** (R11).
> Two countings at different granularities do not agree by accident.

## What the number will NOT say

* **The ten fragments were chosen by their difficulty, not at random.** No extrapolation to the
  core is carried as a measured value. A density stands there as a density.
* **Newly assigned, not reconstructed.** The 74 is **replaced**, not continued — the same
  marking the Neuerhebung of the eleven classes carries.
* An obligation count is not a proof-step count. *Both are legitimate, they answer different
  questions, and the folder's question — what is left for the human? — is answered by the
  obligation count.*


---

# RESULT — NEUZUWEISUNG: **238 obligations, gate MISSED at H = 36**

**Newly assigned 2026-08-17, not reconstructed.** The full list with `file:line` per obligation
stands in [`PFLICHTEN.md`](PFLICHTEN.md) — *this section carries the protocol, the gate and the
findings; the list is the source list W7 demands.*

| | | |
|---|---:|---|
| Obligations in total | **238** | 228 anchored at a line + 10 lowering |
| **Plumbing (K)** | **173** | 73 % |
| **Logic (L)** | **65** | 27 % |
| **hanging** | **50** | of which **36 K** |
| disputed | **1** | 0,4 % — the gate allowed up to 10 % |

## Gate: **MISSED.** `H = 36` against a bar of 0

`BEWEIS.md` fixes the abort condition as *"a **named** plumbing obligation remains that the
programmer has to discharge by hand"*. **Thirty-six of them are now named**, each with fragment,
line, statement and gap ([`PFLICHTEN.md`](PFLICHTEN.md), *The 36 hanging plumbing obligations*).

**The run is valid:** the enumeration did not abort, one row of 238 is disputed, and the R14
calibration was repaired before the count (below). *Missed is not invalid — the number is
usable.*

## R14 — the calibration failed as pre-registered, and the repair is booked

The rule of the VORAB was applied to `delete_leaf` first. **It did not find the published
eleven.** Three gaps, all in the rule, none in the answer:

| | what was missing | why it is principled |
|---|---|---|
| 1 | `costs`, `effects`, `touches`, `where`, `bounded`, `on_exceeded`, `floor`, `claim` were not in event **A** | they are declared clauses. A plain bug |
| 2 | **the call** — `unlink(c, s)` triggers the callee's precondition | published obligations 2 and 3 sit exactly there → new event **I** |
| 3 | **the branch** — `Memory(m) => { free_region(a, m); }` | published obligations 6–9 and 11 sit exactly there → new event **J** |

After the repair the aid finds **11 of 11** published statements at their Gabbro anchor.

> **A rule pulled into shape after seeing the result would be an R2 breach; a rule calibrated
> against a published result before the run is R14.** All three additions are general — a
> precondition at a call site and a state-changing branch generate obligations in any program
> logic, not only in this one.

## The prediction: **right on the counts, wrong on the ratio**

| predicted | measured | |
|---|---|---|
| far above 74 in total | **238** | 3,2 × — holds |
| far above 17 in L | **65** | 3,8 × — holds |
| — | **L : K = 0,38 : 1** | against the old **0,30 : 1** — **near** |

**The ratio nearly reproduced across a threefold change of granularity**, and that was not
predicted. The plausible cause is dull rather than deep: the same dividing line over the same
corpus scales both columns roughly together. *It is booked because it was not predicted, not
because it is proved.*

## THE FINDING — the same function, the same criterion, and the ratio flips

`delete_leaf` was broken down on 2026-08-15 over the **Rust** original: **4 K / 7 L = 1,75 : 1**,
and the folder booked that as *"the plumbing is the minority"*. Over the **Gabbro** fragment the
same criterion gives:

```
Rust original    4 K  /  7 L   =  1,75 : 1
Gabbro fragment 13 K  /  8 L   =  0,62 : 1
```

**All eleven Rust obligations are still there.** What changed is that the Gabbro version carries
**nine more plumbing obligations** — `Held(CAPS)`, `Held(MEM)`, `<= 200 ops`, the `effects` line,
the `own` threading, the second index, two call preconditions.

> **Gabbro does not create those obligations. It writes them down.** They were true of the Rust
> function too — unwritten, unchecked and therefore uncounted. **R18 in its purest form, and it
> is hitting the folder's own headline metric:** the language makes plumbing visible, and the
> metric punishes it for that.

## What follows: the ratio is the wrong statistic

`BEWEIS.md` says *"2 : 1 of pure logic is a success. 0,5 : 1 with hand-written range checks is
not."* **The ratio cannot tell those two apart** — `Held(CAPS)` and a hand-written `narrow` both
count as one K.

**The third column can.** *Who discharges it* separates a plumbing obligation with a refusal code
beside it from one the human has to write out:

| | | |
|---|---:|---|
| K, carried by construction | **137** | 79 % of all plumbing |
| **K, hanging — H** | **36** | 21 % |

> **H is the measurand, not L : K.** A language that carries more plumbing explicitly gets a
> *worse* ratio and a *better* H — and only the second is the direction the thesis claims. *The
> number turns from the goal into the diagnosis, and this run says which number.*

## The `narrow` count and H are the same quantity

Three of the 36 are hand-written `narrow … else`. The folder counts those separately
(`zaehle-bereichspflichten.py`, bar of 24) **under a different name and against a different
bar.** They are the overflow class of H.

**And the three are not equal, which neither measurement sees today:**

| Site | else branch | |
|---|---|---|
| `FRAGMENTE.md`:1660 (F10) | **reachable** — a hostile DTB takes it | a real check |
| `FRAGMENTE.md`:1100 (F6) | **cannot be taken**, and must stand there anyway | a ritual — the bound falls out of the domain, M1 does not see it |
| `FRAGMENTE.md`:268 (F1) | reachable only if the bookkeeping invariant is already broken | the second net, deliberately |

*A `narrow` whose else branch is unreachable is a different finding from one that catches an
attack. The bar of 24 counts them the same.*

## The largest single cause is the lowering — 10 of 36

**One per fragment, and all ten hang.** The emitter of 2026-08-17 lowers
`beispiele/16-by-ops-am-feld.gab` — **an example, not a fragment** — and `C001` refuses for every
form these ten need. *That is the honest connection to yesterday's work: the differential test
showed one lowering holds for one file; refinement is a statement about every lowering, and
against this corpus it stands at zero of ten.*

## Two further findings from the assignment

**The old "1 logic obligation not formulable at all" is now two, and both are in F1's `table`
body:** «B13» `refcount == count(s in slots : s.object == o)` — no aggregation, no cross-table
domain — and «B14» the mutuality of the sibling chain — `pred` cannot resolve an
`option index into`. **Both are L, not K**, so they do not enter H; they are the human's work
that the language cannot even let him write down.

**F6 is the worst-carried fragment and F3 the most logic-heavy.** The test scaffold has 21 K
against 5 L with **7 hanging K** — measuring apparatus is almost pure plumbing, and Gabbro
carries the least of it. F3 is the only fragment with L ≥ K (13/13), and it is one of the two
that *do not fit*. *The fragment that says most about the subject is the one the grammar
serves worst.*

## What this number does NOT say

* **The ten fragments were chosen by their difficulty, not at random.** No extrapolation to the
  core is carried as a measured value.
* **238 obligations are not 238 proofs.** 137 of them have a refusal code beside them and cost
  the human a declaration, not an argument.
* **Newly assigned, not reconstructed.** The 74 is replaced. The old count and this one are not
  convertible, and the old one can no longer be evidenced.


---

# The escalation of 2026-08-14, settled — eleven classes, each with its construct

**The decision of 2026-08-14 read:** *"that is not an abort but an escalation: for each of the
eleven classes the construct that takes it over is to be designed."* Seven items were written
down. **They are now checked against today's grammar and today's passes, not against the design
verdict of Part 1** — that verdict said *"falls"* six times, and *falls* was a statement about a
drawing.

## The seven items

| | demanded 2026-08-14 | state today | evidence |
|---:|---|---|---|
| 1a | **`forever` needs `on_exceeded`** like `retry` | **built** | `SYNTAX.md`:489–491 — `forever` carries `per_pass bounded … ops` **and** `on_exceeded ident` |
| 1b | **whether lock time counts in `per_pass`** | **decided, and written down** | `SPRACHE.md`:924 — *"lock waiting time does not count into `per_pass` — and must nevertheless not be unbounded"*; `held` carries the second half |
| 2 | **`per_pass` in a quantity other than `cycles`** | **built** | `SYNTAX.md`:490 — the unit is `ops`. *"There are no cycles in the language"* (`SPRACHE.md`:820) |
| 3a | **`publishes` at the STORE** | **built** | `publishstmt = place "=" expr "publishes" nutzlast ";"` (:652), reachable from `stmt` (:444) |
| 3b | **a form for "nothing"** | **built** | `[ "publishes" ( placelist \| "nothing" ) ]` (:450) |
| 3c | **a form for volatile stores to a device** | **NOT built** | `publishes` sits at `atomicdecl`, not at a device register — «B19», `PFLICHTEN.md` F4:796 |
| 4 | **a construct for "pointer AND bitfield"** (PTE) | **built and evidenced** | `embeds` (:233), `walkdecl` (:530), `mappings of` (:355) — F9 uses all three, **0 new constructs needed** |
| 5 | **a form for relational preconditions** — *"the big item"* | **built** | **V2** (`SPRACHE.md`:662): under `a >= b`, `a - b` has type `0 .. a.max − b.min`. Pass 3, `M101`–`M105` |
| 6 | **`break`/`continue`: admit or forbid** | **admitted, with a name** | `leavestmt = "leave" ident ";"`, `nextstmt = "next" ident ";"` (:446–447) — **the exit carries a name, which is what D0 cost ten days for** |
| 7 | **the remaining five classes from the scratchpad** | **permanently lost** | not even their names were recorded. Replaced twice over: by `N_neu` for classes, by the 238 for obligations |

**Six of seven built, one open** (3c), one unrecoverable (7).

> **And item 5 carries a number discrepancy that nobody has reconciled.** Part 1 says *"54
> relational preconditions"*, `SPRACHE.md`:662 and :1222 say *"the **102** sites"*. **Two
> numbers for the same population, neither with a search path** — a W7 item, entered here rather
> than resolved, because resolving it means a count against `../caprock-messbasis`, not a
> decision.

## The eleven classes, each with the construct that takes it over

**And now for the first time against evidence instead of against a design**: the 36 hanging
plumbing obligations of [`PFLICHTEN.md`](PFLICHTEN.md) are sorted onto the classes.

| Class | taking-over construct | booked | hanging obligations found |
|---|---|---|---:|
| **Index** | `index into T` inherits `count N` · `M103` | carried | **0** — confirmed |
| **Overflow** | M1 range types · `M101`/`M104` · `wrapping` | carried | **5** — three `narrow`, «B33», the V rules do no arithmetic |
| **Alias** | dissolved: no pointer needed; where one is, `own` · `L101`–`L105` | carried | **0** — confirmed |
| **Frame** | `effects` with writes, `locks`, reads (`E010`), call effects (`E008`) | carried | **1 — «B39»** |
| **Lock** | `lock … rank … held` · `H001`–`H006` · `K002`/`K004` | carried | **0** — confirmed |
| **Race** | *(hangs on the axiom layer)* | hanging | **2** — «B21», «B38» |
| **Termination** | three loop forms · `bounded`/`progress`/`on_exceeded` · `S001`/`S002` | carried | **0** — confirmed |
| **Phase** | `linear ghost type` · `L101` | hanging | **3** — «B37» ×2, «B18» |
| **Leafness** | `descendants of` + `by consuming` · `kosten.rs` | carried | **0** — confirmed |
| **Publication** | `publishstmt` · pairing pass · `V001`–`V004` | carried | **1 — «B19»** |
| **Refinement** | *(the emission)* | hanging | **11** — ten lowerings + «B27» |
| **— no class —** | | | **13** — device, `format` and expression notation |

## Two classes booked as carried are refuted by name

**Frame — «B39».** `FRAGMENTE.md`:1558 says it literally: **the MMU sets `A` and `D` itself, and
the frame statement *"only what stands there changes"* is FALSE at this site.** The rebooking of
2026-08-16 named its limit as *"`E010` speaks only about declared world state; in a complete
translation unit nothing is lost, because an unknown name already falls in the name pass."*

> **That limit does not cover this case.** The MMU is not an unknown name — it is a **writer that
> is not a program**. The honest form is `assume … falsifier …`, which moves the case into the
> axiom layer, *where Race already sits.*

**Publication — «B19».** Booked carried on `publishstmt` + pairing pass. But the store the
class exists for is not an atomic: the virtio `avail` index is a **volatile store into a DMA
region, to a device**, and `publishes` sits at `atomicdecl`. **The class is carried for atomics
and not for device registers** — and item 3c above is the same gap, arriving from the other side.

**Overflow is a different case, and it is definitional, not factual.** Its five sites are
`narrow … else` and the two V-rule limits. A `narrow` is a **named, checked, bounded** residue
with its own bar (≤ 24) — not an unnamed gap. *Whether a named residue tips a class is a
question for the folder (R5), and it is not decided here.*

## What replaces the 19

| | |
|---|---|
| **2026-08-14** | 19 hanging obligations in eleven classes — **aggregate only, six classes named, five lost** |
| **2026-08-15** | `N_neu = 5` hanging **classes**, with sites — *replaces, does not continue* |
| **2026-08-16** | `N_neu = 3` after the Frame rebooking |
| **2026-08-17** | **36 hanging plumbing obligations**, each with fragment, line, statement and gap |

**The 36 are the evidenced successor of the 19** — not comparable as a number (the old one
counted differently and can no longer be evidenced), but the same question, answered with a
source list.

> **And they say something the class count cannot: thirteen of the 36 belong to no class at
> all.** Device notation, `format`, the missing struct literal, the missing return-value binding.
> **The eleven-class taxonomy was built for what a kernel gets wrong; a third of the measured
> gaps are about what the language cannot SAY.** *That is a different axis, and the folder has
> been counting on one axis only.*


---

# The mutation density as a diagnostic — 2026-08-17

**The question was not "how many mutations are caught" but "which lines can be damaged at
all".** `87 of 87` is a ratio over the surface that can be damaged; where nothing can be
damaged, a total reads like coverage.

## The search path

```
Mutationen je Zieldatei  =  grep -oE '^\s*"[a-z0-9_]+\.rs",' mutiere-pruefer.py | sort | uniq -c
Zeilen je Datei          =  wc -l crates/gabbro-check/src/*.rs
```

| | before | after |
|---|---:|---:|
| checker lines | 6 823 | 8 163 |
| **lines with zero mutations** | **1 310** (19 %) | **0** |
| mutations | 67 | **87** |
| tests | 79 | **91** |

## What the undamageable lines were hiding

**Four findings, and none of them came from reading the code for its own sake** — each came
from asking *what would a mutation here break?*

### 1. The template ratchet's second tooth had been dead for a day

```rust
SCHABLONEN.iter().all(|s| s.stand != Stand::Bewiesen) && SCHABLONEN.len() > MARKE_OHNE_BEWEIS
```

**With the first proved template the left half became false forever.** From then on the
register could grow without limit — and it grew **17 → 19 on that same day**.

> **The mechanism failed on exactly the day the event it was waiting for occurred.** *A ratchet
> with a single detent is a stop, not a ratchet.*

Repaired as the literal generalisation of the sentence already standing beside it (*"whoever
needs the nineteenth must prove the first"*): **base mark plus one slot per proved template**,
so every further entry costs a proof. **The three slots of air today are booked as air** — two
of the four proofs arose from *splitting* entries and thereby created entries of their own.

**And both teeth only ever read the real list, which is healthy.** They therefore said nothing
about whether the mechanism bites. Both now take a list as an argument and have a speech test
with deliberately broken registers.

### 2. A pass could silently not run

`SPRACHE.md` part III fixes *"the specification is the pass list"*. 241 lines of `lib.rs`
carried no mutation, so nothing enforced the sentence. Two mutations now remove a pass from the
list; `U001`–`U007` and `V001`–`V004` fall silent, and the poison probes catch it.

### 3. The call graph's collection side had never been looked at

`huelle` was probed seven times; `sammle_rufe` not once — **all seven probes called on the top
statement level only.** A call in a `match` arm, under `locks` or in a loop body could have
gone missing, and then `effects` covers exactly the calls nobody hid.

> **The corpus has precisely that shape.** `delete_leaf` calls three times inside `match` arms
> (`FRAGMENTE.md`:277–279), `revoke` calls `delete_leaf` inside a `traverse` body (:337).

Three new probes, **all green on the first run — R11**, and eight mutations are the answer to
that: each shows that its probe hangs on the subject.

### 4. `gabbro annahmen` reported 15 assumptions where there are 14

**The file the folder cites as the ratchet that already exists had neither test nor mutation.**
`schablonen.rs` names the axiom layer as *the* example (*"the axiom layer has its own"*);
`manifest.rs` was the least guarded file in the crate.

`beispiele/06` and `beispiele/07` both declare `axiom write_cr3` — same probe, same effects,
only the parameter name differs, and the manifest does not carry parameter names. The command
**concatenated per file instead of uniting**, though `SYNTAX.md` §12 demands a **set of names
with class**.

> *A promise "proved under A1…An" with a duplicated A claims a larger assumption set than it
> has.*

**The dangerous case is the other one, and the repair is built for it:** two files declaring the
same NAME with different content — other probe, other effects, or falsifiable in one place and
not in the other — are a **contradiction in the assumption set**, not a duplicate. The old
version would have printed both lines without a word; the command now refuses by name.

## And one mutation survived, which is the point of the harness

`eine-einheit-faengt-mit-irgendwas-an` made `ist_uebersetzungseinheit` blind to what a block
begins with — **and nothing fell.** The rule *"a translation unit begins with an item"* stood
unguarded although **gate P2 rests on it**: it decides what gets counted at all.

> *A denominator nobody checks is the cheapest way to improve a ratio.*

The probe it demanded takes five excerpt forms and both borderline cases of the ellipsis —
allowed in a comment, not in code.


---

# NACHTRAG zur Neuzuweisung: `H = 36 → 35`, und die Absenkung ist bei 1 von 10

**Same day, and the run is not re-opened** — the measurement booked `H = 36` and that number
stands as measured. What changed is the world, not the count: **F7's lowering obligation is
carried since 2026-08-17**, and the ledger in [`PFLICHTEN.md`](PFLICHTEN.md) carries the
correction with its date.

```
.gab (aus FRAGMENTE.md geschnitten)  →  C  →  cc -Werror  →  ausgefuehrt  →  123456
```

**Six boot steps, in order, each exactly once.** The generator does not read a copy — the
guardian cuts the block out of the frozen corpus and refuses if the cut misses.

## What F7 buys, and it is the folder's first statement about COST

`BootPhase` is a `linear ghost type`. It carries the entire safety argument of the fragment —
*the token arises once, travels the stretch and is consumed; a path that drops it is a boot that
never finishes, one that duplicates it is two cores each believing they boot alone* — and it
lowers to **nothing**.

> **The obligation is discharged at compile time. At run time the six calls stand there and the
> token does not.** *That is the first sentence this folder can make about what Gabbro costs,
> and the answer at this site is: nothing.*

## The erasure holds at three places, and two failure forms are silent

| place | right | wrong |
|---|---|---|
| signature | `void mmu_an(void)` | `void mmu_an(BootPhase)` — needs a representation that does not exist |
| call site | `mmu_an()` | `mmu_an(p)` — passes a value that is not there |
| **`let` binding** | **`mmu_an();`** | `void p1 = mmu_an();` *(does not compile)* — **or the whole statement drops** |

**The third right-hand cell is the dangerous one, and it was measured rather than assumed.**
Made to fail that way, the C **compiles without a warning** and prints `6`:

```
erwartet:   123456
bekommen:   6
```

**Five of six boot steps gone, silently.** Only `root_task_starten()` survived — it is a plain
call statement, not a `let`. *That is exactly why stage 4 of the guardian exists: a generator
that produces compilable C computing something else is worse than one that produces nothing.*

## One decision inside it deserves naming: the foreign type

`extern fn melde_roh(text : ptr<code, r> Text)` names `Text` and nowhere declares it — the
fragment is an excerpt of a larger program. The emitter lowers it to an **incomplete** C type
(`struct Text;` forward, `const struct Text *` at the parameter).

> **That is not a guess.** C already carries the rule the emitter would otherwise have to
> invent: behind a pointer an incomplete type is legal, and **any use that needs the layout is a
> compile error.** *The refusal is delegated, not dropped — and delegated to the one tool that
> can decide it.*

**And C11 has a second requirement the first version missed:** the tag must stand **before** the
parameter list, otherwise its visibility ends at the semicolon. `-Wall` said so, `-Werror` made
it a finding, and the test now asserts the ordering rather than the presence.


---

# Der Erzeuger fiel an drei Stellen OFFEN aus — 2026-08-17

**Found by the same method as the day before: run the emitter against the corpus and read what
it does.** The emitter's entire design is one sentence — *refuse by name instead of emitting
something plausible* — and it had **three exceptions**. All three compile. Two compute something
else.

| Site | old output | why it is wrong |
|---|---|---|
| `option index into T` | `uint32_t` | **every value 0..<N is a valid index** — no bit pattern is left to mean *absent*. The C is structurally incapable of holding what the type says |
| unknown expression form | `/* NOT LOWERED */ 0` | it compiles **and yields zero**. *A comment nobody reads is not a refusal* |
| `Some` / `None` | `None()` | an implicit declaration. That `-Werror` catches it is **luck, not refusal** |

## The `option` case is a decision the folder has not taken

Lowering it to a plain index is not a coarsening — it is a **loss of information the type
promises**. An option needs a representation: a sentinel value (which costs a slot of the index
range and has to be checked), or a tagged struct (which costs a word per field).

> **Choosing one is a template obligation, not a translation** — and the register has no entry
> for it. *The refusal is therefore the honest state: `C001` says the emitter cannot lower this
> until the folder decides how.*

**And it is load-bearing in the corpus:** F1's `CapSpace` carries four `option index into
CapSpace` fields (parent, first_child, next_sibling, prev_sibling) — the whole CDT. F8's
`aufloesen` returns one, and that return is the revalidation the fragment exists for.

## The expression fallback is the one that scares me most

`"/* NOT LOWERED */ 0"` predates the ghost work. **Any expression form the emitter did not know
became the literal zero**, in a component every other pass hands its result to.

> *It never fired in the two units the guardian runs* — which is exactly why it survived: a
> fail-open path is invisible until something walks into it. **The mutation `ausdruck-faellt-
> offen-auf-null` now makes it visible**, and the probe that catches it uses a unary `!`, a form
> the emitter still does not lower.

**95 of 95 mutations, and one had to be re-anchored:** the signature change threaded `Absagen`
through the expression path and broke the anchor of `geist-let-verschwindet-ganz` — the most
important emission mutation there is. *The harness reported `ANKER FEHLT` and excluded it from
the count instead of quietly passing 94 of 94.*
