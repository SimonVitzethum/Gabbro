# Gabbro — the corrections

This file records **what was already wrong about this design**. It stands apart because the
`README` would otherwise grow as sediment from layers of corrections — at 658 lines it already
had, and the location note "this correction is in line 3" had rotted before anyone read it.

**The documentary value is the point.** A design folder that deletes its refuted versions ends
up looking as if it had been right from the start.


---

## A falsifier without a threshold, cleared by a judgement *(2026-09-03)*

**`G1` of `GABBROV.md` §11 never had a number, and on 2026-09-02 it was reported as not
firing.** The condition reads *"a **noteworthy** part of the 66 L obligations is not sayable in
the fragment"*. 56 of 66 stood as a `Prop`, and three documents wrote down ~~*"`G1` does not
fire"*~~ — `GABBROV.md` in three places, `messung/GABBROV-V1.md` in its own answer-up-front,
and `TODO.md` in a parenthesis.

**No count can clear a gate that has no number, and none can trip it either.** What was
written was a judgement, and it was written in the tone reserved here for measurements — in a
report whose entire subject is that difference. *The count itself was right and is untouched;
only the verdict over it is gone.*

**The repair that was NOT made is the point of the entry.** The obvious fix is to supply the
missing threshold. It was refused, and for a reason that has a name in this folder: a
threshold chosen while 56 of 66 is already on the table is chosen to clear it — `R2`, a rule
pulled to fit a result. *A gate set after the run is not a gate, it is a caption.*

So the withdrawal stands without a replacement number, and the criteria that take over —
`E1` (every obligation gets a verdict; a line count against a line count) and `E2` (decided
against undecided, against a **named** exception list in `dokumente/AUSNAHMEN.md`) — get their
force from something a threshold cannot supply: **they were written down before the runs they
judge.**

> **The class, and it is older than this entry.** `G5` sits in the same table and cannot fire
> either — *"the assumption set has no model"* is a question about formulas, and the eight
> assumptions of the ten fragments are German prose sentences (`messung/GABBROV-V1.md` §6).
> **Two of five falsifiers cannot be evaluated, and both looked evaluable from the outside.**
> *A falsifier list is a promise that something could go red; a row that cannot go red is an
> ornament in the exact sense of `R11`.*

---

## The most expensive faults sit in what nobody read *(2026-08-20)*

> **The most expensive faults of this project do not sit in what was thought wrongly, but in
> what nobody read** — and the last three guardians are answers to that sentence.

On one day, five faults fell out of the first driver that did not come from the design, and
three more out of the two instruments built in response. **Not one of them was a wrong idea.**
Every one was a sentence the folder had already written down and that no reader held:

| what was written | who did not read it |
|---|---|
| `SPRACHE.md`:355 — *„Generates: reader, **writer**"* | the emitter built only the reader |
| the ghost erasure, specified in three places | the fourth, `return`, was never built |
| *„**M2**: the waker consumes **exactly its** reason"* | no pass compared the names |
| `PFLICHTEN.md` F10 — the `where` clause carries the length promise | no pass read the clause |
| «B37» — the order on a linear mark | the `boot` construct did not check its own order |
| `beispiele/06`, a file that DEMONSTRATES probes | its `can_fail` body had no type pass |

**And the reason they were invisible is one sentence, measured twice and then a third time:**
the corpus is written from the language outward, one file per construct, and the faults sit at
the **combinations**. The same as at the hand-written mutations — *dense near the refusals,
thin at the arithmetic*. What someone has in mind while writing covers the axes, not the
surface.

The three answers are instruments, not rules:

```
mutiere-pruefer.py       what has 0 mutations is not covered but UNDAMAGEABLE
gabbro blindstellen      what has 0 sites is not checked but UNREACHABLE
pruefe-reichweite.py     what 0 passes read is not in order but UNREAD
```

*Each of the three carries its own limit in its own output.* The one that matters most is not
a number: **an occupied cell says only that a pass CAN see the form** — that is the sentence
which keeps `151 → 0` from ever being quoted as coverage.

### And a third class, found the same week: **the half-reading tool**

> **A tool that reads half its subject looks plausible and measures its own reach.**

| | what it read | what it therefore reported |
|---|---|---|
| the call-effect hull | top-level statements only | a call in a `match` arm was invisible — and the corpus has exactly that shape |
| `enthaelt_schritt` | the outermost level of a loop body | one `locks { }` around the step made `O006` silent |
| `pruefe-gruende.py` | up to the first `\`-continuation of a Rust string | it reported **`N011`** as a suspect — the one rule whose note names the load-bearing reason verbatim |

The third is the sharpest because it inverts the answer instead of losing it. *R16 in text form:*
a lower bound that does not say it is one reads as a result.

**All three share one structural signature: a tool without a descent step** — the hull did not
descend into callees, `enthaelt_schritt` not into nested bodies, the reason counter not past
the truncated line. That makes the class detectable in advance, and the question is now
**W16**: *is the subject recursive or multi-line — and does the tool descend?*

> **A lost answer is missing. An inverted one stands there and looks complete.** The inversion
> arises exactly where the truncated material carries the EXONERATING evidence — a tool that
> reads only the charge and never the defence finds culprits reliably.

**And the same week produced its mirror image:** a measuring apparatus that produces the
scatter rather than the subject. `pruefe-gruende.py` first reported thirteen suspects; eleven
were the substring `word` matching rules that speak about the *vocabulary* — the language of
the comment, not its subject. **13 → 2 by tightening a word list**, and the number that
mattered was neither: **44 refusal texts state their reason in neither language at all.**

*A refusal without an articulated reason is not wrongly justified — it is unverifiable for
reach.* Nobody, not even its author, can tell whether it grips too narrowly or too widely.
That was the mechanism in all four known instances of the previous class; there a WRONG reason
stood where here none stands. **The cure is incremental and cheap: every refusal that is
touched once gets its reason in one of the two languages.** Not a project — a maintenance
principle.

---

## The two overreaches — same class, two weeks apart

Both stood in **line 3**, both were the strongest word at the place with the weakest coverage,
and the second arose while **correcting the first**.

| | Version | what was wrong with it |
|---|---|---|
| **Ü1** | "**provable** by construction" | Gabbro proves nothing. It generates by rules; correctness hangs on an **unverified compiler**. EverParse actually proves its parsers, in F\*. Gabbro delivers "correct given trust in the generator, plus a differential test" |
| **Ü2** | "programs whose **GOLD** proof is cheap" | Gold means functional correctness. The seven constructs explicitly deliver **no** general postconditions — what follows is a **safety hull plus declared invariants**. Only for `format` is the descriptor the complete functional specification |

**Ü2 is the more instructive one.** It arose as a *correction* of Ü1 and was one notch quieter
— no longer "Gabbro proves" but "Gabbro's output is cheap to prove". The error moved from the
verb to the object. That is the form in which an overreach survives a correction: it gets
worded weaker without **becoming** weaker.

> The sentence "a proof that proves the wished-for form is worse than none" also applies to
> words in headings — and apparently to words in corrections of headings.

---

## The broken ordering rule — 2026-08-14, announced, and booked here

**The rule stood twice and in capitals:** *"No checker line before the result of measurement
2"* and *"THE NEXT STEP IS NOT A LINE OF RUST"*.

> **Both citations were checked on 2026-08-17, and one of them no longer resolves.**
> [`TODO.md`](../TODO.md) still carries the sentence (struck through, dated).
> [`PLAN.md`](PLAN.md) carries only two weaker descendants of it. *A file that records broken
> rules and cites a site that has since moved does the same thing it accuses others of — so
> the citation now says which of the two holds.*

**Measurement 2 has still not been run** — it is blocked because five of the eleven plumbing
classes exist only in the scratchpad.

**On 2026-08-14 a compiler came into being anyway:** lexer, parser over the complete EBNF, five
of nine checking passes, plus example and poison corpora. **That is real checker code, not a
tool layer** — the guardians (`pruefe-syntax.sh`, `pruefe-wortschatz.py`, `zaehle-fallen.sh`)
were never barred; the compiler was.

| | |
|---|---|
| **What it was** | a **breach**, not a change. The rule stands unchanged |
| **How** | on explicit announcement, not silently |
| **Where it is recorded** | [`MESSUNGEN.md`](MESSUNGEN.md) P2, first paragraph; [`TODO.md`](../TODO.md); and from now on here |
| **What it cost** | **P2 and P3 can no longer kill the thesis *before* the compiler is built.** The order was built so that each stage consumes the result of the previous one — that chain is severed at one point |
| **What it earned** | the measurements in [`MESSUNGEN.md`](MESSUNGEN.md) from P2 on: 1 of 6 fragments, eleven grammar findings, the vocabulary collision, 16 unsoundness holes found, the cost figures |

**The lesson is not "the breach was wrong"** — it was a decision with a yield, and the yield is
recorded as measured. **The lesson is where it was booked:** it stood as a paragraph *inside
the measurement that profited from it*, and nowhere else. A broken rule belongs where you look
for it when you distrust the folder — and that is this file.

> **And the form in which it nearly disappeared:** [`BEWEIS.md`](BEWEIS.md) still said *"Gabbro
> has no line of compiler"*. That sentence became false, and **pulling it up to the new state**
> would have been the convenient move — smoothing the claim instead of surveying the tree. That
> is literally the class from commit `5904cae` ("the previous commit message described three
> changes that were not carried out"). The passage now carries **the rule status, not just the
> fact**.

## The first construct killed by our own paper test — `locks ordered`, 2026-08-14

`locks ordered` had been on the candidate list since the multicore push: a grammar line
requiring that every repeated acquisition of the same lock class stand lexically together. It
was not a fantasy — it was the answer to a real deadlock case in other kernels.

**The paper test against `arch/x86_64` found zero test cases. Not few. Zero.**

And the answer was stronger than the question: in the whole tree there is **not a single
repeated acquisition of the same lock class.** `system.rs:15` states it as an invariant, and
migration — the test case I had expected — works the other way round:
`SCHEDS[src].lock().migration_candidate()` takes, selects, **releases**, and revalidates the
target side.

**Why this is here and not a tick in the TODO:** striking a construct is not a completed item.
It is the finding that I had designed a grammar around a *presumed* need without having counted
the need. That it was cheap is luck: `locks ordered` was never implemented, it stood on a list.
The rule that kills it is the same one that stopped `abi { … }` — **no construct without
measured need** — and this time it worked, because I applied it before building rather than
after.

**The yield is larger than the loss.** The same test found two gaps that were on no list: the
language knows **no shared lock acquisition** (`locks shared`) — and the most-travelled path of
the kernel, capability resolution, takes exactly that way, **33 sites**. I had designed a
construct for a rare case and missed the common one.

> **The form:** I measure only once I already like the construct. Here it was the other way
> round, and the result was one deletion plus two real finds. **The test is worth exactly as
> much as its licence to kill its own candidates.**

## Two sites from one inheritance — 2026-08-15, and `git log` would have said so

I had reported that the B29 pattern (`refcount -= 1`, null check afterwards) stood **twice**, in
"two independently written kernels of the same tree", and concluded: *the form does not come
from one author's habit*. A finding pointing exactly the way I needed.

**It is wrong, and the refutation costs one command:**

```
R099   crates/sel4lake-cap/src/space.rs -> crates/caprock-cap/src/space.rs
```

99 % similarity, a rename, the same authorship line. The second copy lay outside git, in an
older snapshot — **I had seen two paths and made two origins out of them.**

**The error class:** a statement about **origin** formed from **surface similarity**, instead of
from the evidence lying right next to it. It is the same move as in `5904cae` — smoothing a
claim about the tree instead of surveying it — only this time about history rather than code.
**And it was convenient**: the wrong reading was the stronger one.

**What remains is better than what fell.** The line sequence has stood since the original
commit (`2111f30`, 2026-06-23) and has survived **five rebuilds of exactly this region**, two of
which rewrote the release semantics themselves. B29 is not a slip but an **attractor** — and
*that* is measured rather than inferred.

> **The lesson, mechanically:** a statement about the origin of files is backed by
> `git log --follow` or not made at all. Two paths are no evidence of two origins.

## The rest, shorter

| What | Version that fell | what holds instead |
|---|---|---|
| **`format` = `table`** | the first version treated both alike | a format is a **pure function**, a table is **mutated state**. The difference decides the value of the whole folder, and the (a)/(b)/(c) cut follows from it |
| **The comparison opponent** | the kernel branch was measured against **Low\*** | the cheaper opponents stand closer: **Rust-today** and **Verus**. Low\* is the one after next |
| **`Parked` as an argument** | was cited as evidence **for** the branch | it counts **against**: Rust-today found the fifth site **without Gabbro existing**. Whoever cites the success of the baseline cites a reason **not** to replace it |
| **"63 of 63 measured"** | the `Depends` measurement counted as evidence for Gabbro's `touches` | the measurement is real, the **transferability** is assumed — SPARK checks existing code, Gabbro generates it. Half a notch too strong |
| **`restrict`** | the table row sounded general | it carries **only at the parameter boundaries** of generated functions; inside a traversal body in (c) it says nothing |
| **The line breaks at `insert`** | so it first stood | it breaks at **`revoke`** — whose correctness condition is structural (tree shape, induction), i.e. exactly the excluded quantifiers |
| **The SPARK finding** | "SPARK found two errors Verus did not ⇒ a language of one's own buys something" | the gain came from a **default setting**, not from Ada's expressive power. `refcount` sits in the Verus model as `nat` and **cannot even ask** the question. What remains is the checkable version: *defaults beat capability* |
| **"deliberately in line 3"** | a location note in running text | stale at the first insertion above it. Statements about **order** hold, line numbers do not |
| **"neither SPARK nor Rust"** | "the caller holds the lock" counted as the **largest single item** and as an expressive gap in all existing tools | **measured 2026-08-13: Verus can do it**, as a `tracked` witness, `no_std`, without a byte in the artefact. The sentence was true for SPARK and Rust and was silently extended to "all" — and **Verus stood in the relatives table dismissed with "proves what someone modelled".** Whoever devalues the nearest relative instead of running it keeps their justification longer than it holds |
| **Twenty constructs** | the first version of the plan file had one keyword per error class — `device`, `lock`, `atomic`, `barrier`, `bitfield`, `unit`, `set`, `right`, `placement`, … | **that is a catalogue, not a language**, and it grows with every finding. The obvious derivation from a list of traps is the wrong conclusion. There are **four mechanisms** (range types · linear, also ghost values · address spaces with rights · no unchecked index) and **two declaration rules**; the twenty fall out of them as a library. The prettiest derivation is `check`: a **linear obligation**, not a checking keyword |
| **Ü2 has RETURNED** | "make Gold cheap" stood as refuted in this file | **and has been back in the `README` since 2026-08-13** — that belongs here, otherwise a silently withdrawn correction looks like one never made. The difference from the refuted version is twofold: there is now a **mechanism** (invariants on the structure · syntax-directed lowering · `spec`/`impl` in one language, plan file §3c) and a **lowered target** (5 : 1 for kernel code instead of 1 : 1). **A claim may return — but only with a mechanism and with a number** |
| **"not a general-purpose language"** | stood as a promise in the `README` and the roadmap | **abandoned on 2026-08-13**, on request and explicitly. The replacement is the five abort conditions in the plan file — an abandoned promise without a replacement would be merely a forgotten sentence |
| **The wrong denominator** | the metric measured specification lines against the **hand-written Rust reference** | the denominator is **Gabbro code** — the question is whether a kernel *written in Gabbro* is cheap to verify; Rust does not appear in it. The wrong version gave "for Caprock as a whole: no", the right one "conditionally yes". **A denominator is a question, not a formality** — with the wrong one you answer cleanly the question nobody asked |
| **5 : 1 as the floor** | counted as a derived lower bound for kernel code | seL4's 20 : 1 is **not a single item**: about 0,5 : 1 abstract specification, about 19,5 : 1 proof. Only the first is untouchable. **The floor is ≈ 0,5 : 1**, and the 5 : 1 came from treating proof effort as indivisible |
| **Two paths in the folder** | a narrow format generator as a "fallback cut" **and** the kernel as the main direction, with two plans side by side | **struck on 2026-08-13.** A folder with a fallback has no gate — you fall back instead of stopping. The format generator is the **library layer** of the language, not a path of its own; there is one plan and one goal |
| **Goal confused with threshold** | 0,5 : 1 stood as a **trigger** ("above this the thesis is refuted") | it is the **goal** — the theoretical floor. A threshold says "passed", a goal at the floor says **what is still missing**: every tenth above it is a nameable, still hand-written proof item. The abort is at **> 3 : 1**, where proof dominates again |
| **0,8 : 1 as a prediction** | assumed 10 % of the kernel at 5 : 1 | **incompatible with the goal 0,5 : 1**, which is the floor. 0,5 : 1 means **no hand-written proof** — even 5 % at 5 : 1 would be +0,25 |
| **B2: "the solver gets the invariant for free"** | stood as the condition for 0,5 : 1 | **overreach no. 3.** What is free is the **safety hull**; functional loop invariants are still written by someone. True for the hull, silently extended to Gold — **exactly the form this file tracks as a pattern**, and this time it carried the metric goal |
| **"no variant, no lemma"** | stood in the result of P0.1 for obligation **T**, while the same thing under **I** was correctly phrased as "the generator shows it once" | **would have been overreach no. 4 — caught before it propagated.** It is **amortisation, not elimination**: zero per program, not zero per construct. "Falls out" everywhere means "falls once, in the generator" |
| **The counting rule, second version** | "what a **human** writes" | leaves a gap with an AI co-author — and **a detour: have a macro layer generate source that then counts as written.** What holds up is **source versus derived**: decidable at the artefact, with no claim about who typed |
| **The counting rule, first version** | "specification is what has no runtime effect" | generated ghost code has none — it would have counted **into the numerator**, and the Gold mechanism would have worsened the metric the better it worked. Correct: **what a HUMAN writes** and gets deleted |
| **0,5 : 1 as the goal** | the number was the goal everything hung on | **it is a proxy.** The criterion is a **kind**, not a quantity: prove logic only, nothing else. Even 2 : 1 is good if the lines are logic; 0,5 : 1 would be a failure with hand-written range checks. Same class as "a checker that reads a single byte" — **the size was measurable, the property was not** |
| **"M1 needs exactly one flow rule"** | derived from 4 measured `leading_zeros` sites | **the sample structurally excluded the hard form.** All four are **unary**; the counter-measurement found **54 relational** cases (`if a >= b { a - b }`) that an interval type cannot carry. **The house pattern, applied to me** — a sentence that would be true had I not extended its scope |
| **"program-specific induction is excluded forever"** | stood as the ceiling of the whole design, with the conclusion "Gold is unreachable this way" | **it is not impossible but FORBIDDEN** — by three lines in the list "what deliberately does not exist". **The difference between "impossible" and "forbidden by us" is exactly the house pattern.** And the equation *template at the construct ⟹ nothing program-specific* is missing its middle step: an induction scheme can be **generated from the user's declaration** — the way Isabelle derives one from a datatype |

---

## The trajectory — the pattern above the individual errors

**This folder has survived every fallen gate by refounding**, and the hard gate has migrated
behind the compiler in the process:

| Gate | Outcome | Answer |
|---|---|---|
| EverParse | covers only the `format` half | **bypassed** |
| base rate / coverage | ≤ 9 % measured | not "too small" but **a plan for the other 91 %** |
| Verus × 2 | **both fell** | not an ending but **a merge into one language** |
| fallback cut | was the cheap, defensible version | **struck**, so that the expensive one is the only one |

The argument for it — *"a folder with a fallback has no gate"* — is sharp and **cuts both
ways**. The old sentence "the path on which a format generator quietly becomes a language
family" has come true: **not quietly, but noticed, documented — and anyway.**

The hard mark is now `> 3 : 1`, **chosen rather than derived**, and measurable only once a
compiler exists. The three cheap gates before it were named through three rebuilds and **never
run**, while about 2000 lines of design text appeared in a single day. **The correction loop ran
faster than the measurement loop** — "measure before building", inverted at the meta level.

**Countermeasure, since 2026-08-13:** P0.1 has been run ([`MESSUNGEN.md`](MESSUNGEN.md)) and
immediately found an error in the counting rule that three rebuilds of proofreading had not.
**No further design text before P0.2 and P0.3.**

---

## The form that repeats

Six of the nine entries are the same move: **a sentence that would be true if its scope were
not silently widened.** `format` → everything; parameter boundary → everywhere; one measurement
of the mechanism → its transfer; Silver → Gold.

That is not carelessness but what a design text does by itself as long as nobody **writes the
scope down**. Which is why every claim in the `README` and in [`SPRACHE.md`](SPRACHE.md) now
carries one — and where none stands, that is a finding.
