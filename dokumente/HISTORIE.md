# Gabbro — the history and the corrections

This file records **what happened to this design and what was already wrong about it.** It
stands apart because the `README` would otherwise grow as sediment from layers of corrections —
at 658 lines it already had, and the location note "this correction is in line 3" had rotted
before anyone read it.

**The documentary value is the point.** A design folder that deletes its refuted versions ends
up looking as if it had been right from the start. The git history is the protocol: a deleted
file is not lost, and the commits named below say where to find it. *(Tidied 2026-10-17: a
dated timeline first, then the corrections that teach, then what the deleted reports recorded.
The corrections themselves are not rewritten; their dates and wording stay.)*

---

## 1. Timeline

One line per event, newest last. A hash is the commit that carries it; a file name is where the
decision is written. Dates are commit or decision dates, not measurement dates.

| Date | Event | Evidence |
|---|---|---|
| 2026-08-13 | A narrow language for formats and tables, target C, is drafted as *Basalt* and renamed **Gabbro** the same day; the first overreach (`provable`) and its correction follow | `f3a7ec0c`, `155cbdf0` |
| 2026-08-13 | The kernel branch gets a number: the seven constructs cover at most 9 % of Caprock; the plan for the other 91 % is written | `b5763f25`, `d106f2d4` |
| 2026-08-14 | A compiler (lexer, parser over the whole EBNF, five of nine passes) is written although the ordering rule said no checker line before measurement 2: **a breach, booked** | §2 below |
| 2026-08-14 | `locks ordered` is struck by its own paper test (zero test cases in the whole kernel tree) | §2 below |
| 2026-08-15 | Two copies of the B29 pattern turn out to be one inheritance (`R099` rename) | §2 below |
| 2026-08-20 | Five faults fall out of the first driver, none a wrong idea: each was a sentence the folder had written and no reader held | §2 below |
| 2026-08-31 | First full acceptance over 49 guardians: three times the guardian was the finding. Twelve emitter wildcards counted: eight fire, and `breite_von` 146 times | `bb11bdd3`, `7be80aed` |
| 2026-09-01 | `gabbro` prints `Hallo` without a hand-written C driver; tag `0.0.1`; twelve subcommand/flag pairs get English first names; the audit of the whole tree; the hardware plan is written and retracted in part within three days | `aecd27fe`, `2f2ded1b`, `27681e08` |
| 2026-09-02 | GabbroV measured: 56 of 66 logic obligations are sayable as a `Prop`, and `lean` took them without looking in | `86054b06` |
| 2026-09-03 | Four obligations the shared semantics cannot state; the `G1` falsifier without a threshold is withdrawn | §2 below |
| 2026-09-04 | The four `K100` gates audited adversarially; `H = 0` shown buyable | `ff3dc75c` |
| 2026-09-10 | A goal assessment says the goal is not reached | its report, last present at `4bb5e944` |
| 2026-09-14 | `theorem gabbro_ziel : GabbroZiel` proved (tag `milestone-2026-09-15-gabbro-ziel`) | tag |
| 2026-09-15 | Rounds 5 and 6 of the independent review (`G1` repaired, `W1` closed in Lean and Rust); both reviewers find "the goal with named gaps — no unnamed gap found"; stage (a) of the C chain closes generically; the Isabelle theories are ported to Lean (lanes 168/169) | tag `milestone-2026-09-15-zielsatz-bestaetigt`, `92b75c60`, `944001ff` |
| 2026-09-15 to 27 | The session runs on a server; everything computes there and on a second machine | `CLAUDE.md` |
| 2026-09-26 | Opus lanes O25, O25b, O25c: the goal statement carries the **atomic rely** (`PrueferX`, `NutzerPflichtA`, `ZielFX`/`ZielX` over GX); agents A–L extend runtime threads, weak memory, invariants, linking, handlers, bare metal | `AGENTS.md` §2 |
| 2026-09-27 | Everything runs locally again | `CLAUDE.md` |
| 2026-09-28 | Milestone: a Gabbro Linux kernel module with a real bounded heap, no OS call hard-wired in any runtime; dynamic data structures come into scope | tag `milestone-2026-09-28-kernelmodul-heap` |
| 2026-09-29 | GabbroV bridge milestone | tag `milestone-2026-09-29-gabbrov-bruecke` |
| 2026-09-30 | Generic parser chain: sieve (a) re-measured at 5 of 148; the C-free lane removes handwritten C from the runtimes | tag `milestone-2026-09-30-parser-generic-chain5` |
| 2026-10-01 | Simon selects a **direct x86-64 backend with final-byte validation** (C11 validation becomes legacy evidence); up to 15 Muse agents run in parallel | header of the old validation plan |
| 2026-10-05 | Lean layout rule: at most 20 entries per folder; mechanical move guardian | `AGENTS.md` §3 |
| 2026-10-07 | **Direction change: AArch64 (Armv9-A) on the Sail Arm model instead of x86-64**; the C emitter is archived (tag `archiv/c-emitter-2026-10-07`) and deprecated; performance target 80 % min / 110 % of GCC `-O3` | `ARM-PLAN.md`, `4e098dcb`, `2b3c54d6` |
| 2026-10-08 | Mathlib is allowed everywhere, pinned to Lean v4.33.1 | `c852c3f6` |
| 2026-10-10 | The x86-64 model (357 Lean files, about 265 000 lines, 48 documents, an unwired Rust foundation) is moved to the branch `archive` | `7c693cb7` |
| 2026-10-14/15 | **LLVM backend**: Gabbro lowers directly to LLVM IR for x86-64 and AArch64, no C, no libc, static binaries; untrusted, refuses by name (`Y101`–`Y106`) | `a6a6c622` |
| 2026-10-15 | Simon: the C emitter is outdated and no guide for language, checker or compiler work; repository cleanup removes 998 Muse reports, 83 lane tasks, about 240 measurement files and the state documents (§3); `TODO.md` replaces `OFFEN.md`; the unbounded heap with pressure sampling is built | `014b4d93`, `f6eb0ac2`, `b62a25a2` |
| 2026-10-16 | The sampling clause is written in English: `pb P blw B` | `60e71603` |
| 2026-10-17 | Real threads for `start`; recursion lowered to loops with growable continuation storage; the LLVM backend measured against the Lean constructor register | `dbda971d`, `9a2b9986`, `158047cc` |
| 2026-10-17 | **`own`, aliasing and `noalias`**: `R014` refuses two pointer arguments with one root, an untraceable pointer is *unknown* and equals every root (a soundness gap closed), `R015` names the boundary assumption; Lean model of objects below a table (`ParamGetrennt`, `ObjGetrennt`) with a bridge to `R014`; `noalias` on writable pointer parameters of internal functions | `704719db`, `74d7c90d`, `bf760447`, `be9320a4`, `a6a2e2d6`, `4bb5e944` |
| 2026-10-17 | The emission check stops being a push gate (the C backend is deprecated) | `acb9b5dd` |
| 2026-10-17 | **Documentation consolidation**: 163 Markdown files become 30 (README, `AGENTS.md`, `CLAUDE.md`, `TODO.md`, `ARM-PLAN.md`, 21 documents, three machine-read ledgers; the ledgers went in the four-guardian cut below) | this commit series |
| 2026-10-17 | **Exactly four guardians** (Simon): Lean model, LLVM compiler, checker, GabbroV. 81 guardians, counters and tools (the 54 `pruefe-*`, 22 `zaehle-*`, the mutation run, the C-emitter stages) and the ledgers they read (`KENNZAHLEN`, `PASSREGISTER`, `RUECKLAUFWERTE` and ten `.txt` registers) are deleted; the Markdown set is 27 files. Also the same day: the `u32 + u32 -> u64` hole closed by reverting `94e526fd` (gifts 1445-1447, example 1164), `gabbro llvm-cert` printing valid Lean, port-space devices refused by name (`Y102`, gift 1470), `annahmen --per-file` | `git show 414feafc:instrumente/` holds the retired scripts |

---

## 2. The corrections that teach (newest first)

### Found during the 2026-10-17 consolidation: documents and a printer nobody ran

Three findings, all of one class: *a statement about an artifact that nobody ran through its
consumer.*

- **The x86-64 direction lived six days as the selected target** (decision 2026-10-01, reversed
  2026-10-07) and the archive move came three days after that (2026-10-10). The validation plan
  and the optimiser specification kept naming x86-64 as the target, and the optimiser
  specification still linked to `Grammatik/X86/*.lean`, files no longer on master, until this
  consolidation. *A decision that reverses must reach every document that
  states the old one.* The optimiser specification and the hardware plan were rewritten as
  target-neutral with the archive named (`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §8,
  `PLAN-HARDWARE.md` §2.3).
- **`gabbro llvm-cert` prints Lean that does not elaborate.** `LLVM-BACKEND.md` said the file
  "elaborates with plain `lean`". Run through `lean`, every definition fails (`unexpected token
  ':='`: the printer writes a second `:=` after comment lines, `llvm.rs:444–452`); the tests
  check substrings, and nothing in `grammatik/` reads the definitions. *Open.*
- **The LLVM backend lowers a `device … at port` register as a volatile memory access** (`gabbro
  llvm beispiele/65-port-space.gab` prints `load volatile` at `base + offset`). That is the
  2026-09-02 defect of the C emitter ("the generated code reads RAM"), reborn in a new producer
  and against the rule "refuse by name, never guess". *Open; written down at `PLAN-HARDWARE.md`
  §3.1.*

### The hardware plan, retracted in parts within three days *(2026-09-01 to 2026-09-04)*

The 3 078-line hardware plan was written on 2026-09-01 and corrected in place until 2026-09-04.
Each retraction below was found by running something, not by rereading. The plan's lasting
content is in `PLAN-HARDWARE.md`; what fell:

| Claim | What happened |
|---|---|
| "twelve wildcards, seven fire" | **eight** fire; the pass was run by four commands and the hits fell into one pot; the line named as the root (`breite_von`) was booked "silent" and fired 146 times. *A counter that aborts at its first hit counts "at least one", not "which"* |
| "the vocabulary is 234 words" | **222**: a `grep` over the file counted 15 words from comments and lost three; the denominator is the `wortschatz!` macro call |
| "string output is unreachable" | retracted within the hour; strings went on the day. The *question* was then mis-framed too (a length is not a terminator) |
| "462 bookkeeping entries" | not reconstructible; **359** comparable entries over `beispiele/` (80 more are bodiless `extern`/`prim`, trust surface that cannot reach zero) |
| "59 of 359 carry nothing" | **withdrawn, not corrected**: the hull inherits the callee's padding, so the measurement hides the very error it should find |
| "effects form a finite lattice, so the fixpoint converges" | false: crossing a call edge creates new places, `k.wert → k.kind.wert → …`; the derivation widens at depth four. The conclusion survived, the argument did not |
| `phase` as one generalised word | calculated and rejected: one word falls, not four; two of four sites already had it |
| "exactly one item remains" (ownership transfer) | the remainder after an enumeration with no written denominator; there were two |
| "75 % → 87 % → 90 %" | not comparable; the denominator was written down only at the third pass |

*The general rule this paid for:* before a rule over a word belongs a count of its uses, and
whether they go wrong in the same direction.

### The big step — four obligations the shared semantics cannot state *(2026-09-03)*

**`L24`, `L34`, `L50` and `L52` are the first four rows of the list of obligations the semantics
could not state**, and the entry stands here because burying them under *"ten rows are not
sayable"* was the mistake.

They are one missing means seen four times. `L24` says two places are never half set — *no
third state exists between the pre and the post*. `L34` says the opposite about the same
object — *one does exist, and the invariant fails in it*. `L50` and `L52` order two effects of
one step: the flush before the reply, the reply before the service ends.
The semantics' `exec` is **big-step**. It hands out a start state and an end state, and
nothing in between.

**Why this is not a gap in the specification fragment**, which is the reading that would send
the repair to the one place it cannot be made: a fragment is a language of predicates over the
objects the semantics provides. A new construct would have nothing to range over. It would
denote nothing — or, worse and far more likely, denote something weaker while wearing the
obligation's name: `flush ∧ reply` type-checks and reads right.

**And the sharp end.** One site is where GabbroV would earn its keep beyond convenience: `D013`
checks that the invariant `I` *exists* and expressly not that the block restores it, so *"a
`breaking` on the wrong-but-existing invariant still passes."* The statement that site needs
**is `L34`**.

> So the four are not four leftovers at the edge of a good count. **They are the centre of the
> case for building the tool**, and they are the part of it the semantics could not express.
> *An exception list whose members are the most valuable rows is a finding, not an appendix.*

The repair is not a wider fragment but a small-step or trace semantics. *Later:* the goal
statement carries the order leg `folge` for `L50`/`L52` and the invariant legs for `L24`; `L34`
stands as an existence with a witness (`TODO.md` O1-Rest).

### A falsifier without a threshold, cleared by a judgement *(2026-09-03)*

**`G1` of the GabbroV plan never had a number, and on 2026-09-02 it was reported as not
firing.** The condition reads *"a **noteworthy** part of the 66 L obligations is not sayable in
the fragment"*. 56 of 66 stood as a `Prop`, and three documents wrote down ~~*"`G1` does not
fire"*~~ — the plan in three places, its own measurement report in its answer-up-front,
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
against undecided, against a **named** exception list) — get their force from something a
threshold cannot supply: **they were written down before the runs they judge.**

> **The class, and it is older than this entry.** `G5` sits in the same table and cannot fire
> either — *"the assumption set has no model"* is a question about formulas, and the eight
> assumptions of the ten fragments are German prose sentences.
> **Two of five falsifiers cannot be evaluated, and both looked evaluable from the outside.**
> *A falsifier list is a promise that something could go red; a row that cannot go red is an
> ornament in the exact sense of `R11`.*

### The most expensive faults sit in what nobody read *(2026-08-20)*

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
| `PFLICHTEN.txt` F10 — the `where` clause carries the length promise | no pass read the clause |
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
were the substring `word` matching rules that speak about the *vocabulary*. **13 → 2 by
tightening a word list**, and the number that mattered was neither: **44 refusal texts state
their reason in neither language at all.** *A refusal without an articulated reason is not
wrongly justified — it is unverifiable for reach.* The cure is incremental and cheap: every
refusal that is touched once gets its reason in one of the two languages. Not a project — a
maintenance principle.

### The two overreaches — same class, two weeks apart

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

### The broken ordering rule — 2026-08-14, announced, and booked here

**The rule stood twice and in capitals:** *"No checker line before the result of measurement
2"* and *"THE NEXT STEP IS NOT A LINE OF RUST"*.

> **Both citations were checked on 2026-08-17, and one of them no longer resolved.** A file
> that records broken rules and cites a site that has since moved does the same thing it
> accuses others of — so the citation said which of the two held.

**Measurement 2 was not run** — it was blocked because five of the eleven plumbing classes
existed only in the scratchpad.

**On 2026-08-14 a compiler came into being anyway:** lexer, parser over the complete EBNF, five
of nine checking passes, plus example and poison corpora. **That is real checker code, not a
tool layer** — the guardians (`pruefe-syntax.sh`, `pruefe-wortschatz.py`, `zaehle-fallen.sh`)
were never barred; the compiler was.

| | |
|---|---|
| **What it was** | a **breach**, not a change. The rule stands unchanged |
| **How** | on explicit announcement, not silently |
| **Where it is recorded** | `MESSUNGEN.md` P2, first paragraph; and from now on here |
| **What it cost** | **P2 and P3 can no longer kill the thesis *before* the compiler is built.** The order was built so that each stage consumes the result of the previous one — that chain is severed at one point |
| **What it earned** | the measurements from P2 on: 1 of 6 fragments, eleven grammar findings, the vocabulary collision, 16 unsoundness holes found, the cost figures |

**The lesson is not "the breach was wrong"** — it was a decision with a yield, and the yield is
recorded as measured. **The lesson is where it was booked:** it stood as a paragraph *inside
the measurement that profited from it*, and nowhere else. A broken rule belongs where you look
for it when you distrust the folder — and that is this file.

> **And the form in which it nearly disappeared:** `BEWEIS.md` still said *"Gabbro has no line
> of compiler"*. That sentence became false, and **pulling it up to the new state** would have
> been the convenient move — smoothing the claim instead of surveying the tree. That is
> literally the class from commit `5904cae` ("the previous commit message described three
> changes that were not carried out"). The passage now carries **the rule status, not just the
> fact**.

### The first construct killed by our own paper test — `locks ordered`, 2026-08-14

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

### Two sites from one inheritance — 2026-08-15, and `git log` would have said so

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

### The rest, shorter

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
| **Twenty constructs** | the first version of the plan file had one keyword per error class — `device`, `lock`, `atomic`, `barrier`, `bitfield`, `unit`, `set`, `right`, `placement`, … | **that is a catalogue, not a language**, and it grows with every finding. There are **four mechanisms** (range types · linear, also ghost values · address spaces with rights · no unchecked index) and **two declaration rules**; the twenty fall out of them as a library. The prettiest derivation is `check`: a **linear obligation**, not a checking keyword |
| **Ü2 has RETURNED** | "make Gold cheap" stood as refuted in this file | **and has been back in the `README` since 2026-08-13** — that belongs here, otherwise a silently withdrawn correction looks like one never made. The difference from the refuted version is twofold: there is now a **mechanism** (invariants on the structure · syntax-directed lowering · `spec`/`impl` in one language) and a **lowered target** (5 : 1 for kernel code instead of 1 : 1). **A claim may return — but only with a mechanism and with a number** |
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

## 3. What the deleted reports recorded

The 2026-10-15 cleanup (`014b4d93`, parent `7c693cb7`) and this consolidation removed reports,
verdicts and working notes. Their *lasting facts* went into the documents named in the last
column; the rest is git history. "Last present" is the commit whose tree still holds the file
(`7c693cb7` for the 2026-10-15 deletions; files still present on 2026-10-17 were last present
at `4bb5e944`, the base of this consolidation; read one with `git show <commit>:<path>`).

| Files | What they recorded | Last present | Facts now in |
|---|---|---|---|
| `messung/muse/MUSE-REPORT-NNN.md` (975 files, lanes 02 to 1398) | one report per Muse contributor lane: what was built, `CUTS`, build results, findings for the reviewer | `7c693cb7` | `git log`; `AGENTS.md` §5 for the process |
| `messung/muse/OPUS-BERICHT-*.md` (25) | the 2026-09-15 Opus lane reports: `STUFE-A`/`-B` (closing theorem stages), `KORROK`, `BLOCK`, `STAERKER`, `KONGRUENZ`, `RAHMEN`, `GERAET`, `AGGREGAT`, `CPARSER`, `TICKET`, `EXPORT`, `LINEAR`, `PFLICHT`, `O13` … | `7c693cb7` | `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§6–7 |
| `messung/muse-audit/` (58 Lean files) | audit probes of the Muse waves | `7c693cb7` | — |
| `messung/URTEIL-{MUSE,OPUS}-2026-09-13…15d.md` (12) | six rounds of two independent verdicts "is the goal reached": rounds 1 and 2 (2026-09-13/14): Muse "reached for the Lean model, not yet for the implementation", Opus **"not reached"** (two defects of substance); round 3 Opus "not the goal yet" (`P1` unsatisfiable lock invariant, `P2` free parameters, `P3` payload races); round 4 "the goal with named gaps", but `F1` (out-of-range float stop) was not named yet, and `F2` (global deadlock leg) and `F3` (stop classes) were repaired; round 5 unnamed gap `G1` (an axiom answer or register read whose declared type `einpassen` cannot hold); round 6 **both: the goal with named gaps — no unnamed gap found** (`W1` closed) | `4bb5e944` | `BEWEIS.md`, `AGENTS.md` §2 |
| `messung/URTEIL-SPECDIFF-*.md` (8) | independent adversarial reviews of each `Spec.lean` diff: fix lanes F9–F11 (2026-09-23), Opus agents A (runtime threads), B (weak memory `schwach`), D (invariants), E (linking `N501`–`N505`), G (`folge`), H (`KernHaltE`), O25c (atomic rely) | `4bb5e944` | `BEWEIS.md`, header of `Spec.lean` |
| `messung/review-2026-09-21/G01…G13, FIX-F1…F11, dokumente/BEWEIS.md` (25) | the static review of 2026-09-21 over the Muse lanes while the second machine was unreachable (13 groups), and the eleven fix lanes that repaired it: integer `match` coverage (`N411`–`N414`), dynamic arenas, the `child` block as a thread, thread starts, fd carrier and gates, bounded strings, smaller Rust findings, Lean witnesses "no claim bigger than its proof", the clone hand-off, worker pools in the goal, same-core interrupt preemption | `4bb5e944` | `AGENTS.md` §7 ledger, `BEWEIS.md` |
| `messung/OPUS-{A…L,O25,O25B,O25C}-*.md` (14) | the 2026-09-26 Opus agent reports: runtime threads, weak memory beyond DRF-SC, **how far a green `lake build` reaches** (the reach audit behind `REGISTER.txt`), invariants, linking, link races, `OFFEN O1` order leg, handlers and cores, bare metal, freestanding, target-bound gates, the atomic rely | `7c693cb7` (`dokumente/BEWEIS.md`: `4bb5e944`) | `BEWEIS.md`, header of `Spec.lean` |
| `messung/GABBROV-*.md`, `GABBROV-V1/V2`, `SPRACHLUECKEN*`, `PARSER-LANE-REPORT`, `SERVER-0E-*` | GabbroV: the 56 of 66 measurement and its audit, the bridge report, the proof-lines-per-user-line ratio, the server and parser lane reports; the language-gap reports and the server lane's phase-1 measurements | `7c693cb7` | `GABBROV.md`, `FRAGMENTE.md`, `PLAN-DYNAMISCH.md` |
| `messung/ARM-KOMPATIBILITAET-A…G.md`, `ARM-NATIV-ABI.md` | AArch64 readiness of the C emitter, the language model, the checker and the Lean ABI model; what the native compiler needs from Lean | `7c693cb7` | `ARM-PLAN.md`, `PLAN-HARDWARE.md` §2.3 |
| `messung/arm/REPORT-06…12.md` | the AArch64 hardware-model agents: executions, the axiomatic model, litmus bench, atomics, barriers, sequential integer ISA, loads/stores | `4bb5e944` | `PLAN-HARDWARE.md` §2.3 |
| `messung/CFORM-REGEL-*.md` (22), `CFORM-ABARBEITUNG.md` | one ruling per emitted C form (`&`, `->`, `sizeof`, `~`, `inline`, …): which are admitted as lemma or assumption | `7c693cb7` | `C-SPEICHERMODELL.md`, `pruefe-cformen.py` |
| `messung/ABSENKUNG*.md`, `ABSAGEFORMEN`, `EMISSIONSZWEIGE`, `WILDCARD-ZWEIGE`, `ERZEUGER*`, `DREI-ERZEUGERFEHLER`, `STILLE-KOLLISIONEN`, `C-NAMEN`, `ERZEUGERSWEEP` | the C emitter under measurement: per-primitive statement budgets, 139 refusal sites in 130 forms, the twelve wildcards, six emitter defects repaired one by one, names C had already taken, a sweep that broke the promise 342 times in 5 889 cases | `7c693cb7` | `C-SPEICHERMODELL.md`, `PLAN-HARDWARE.md` §5 |
| `messung/TEARING-*.md`, `TOCTOU-*.md`, `RACE.md`, `ADRESSRAEUME`, `ADRESSRAUM-REGELN`, `DEVICE-DMA-NOTIZ`, `CPU-DEVICE-NAHT` | tearing inventory and ruling, TOCTOU as a class (check, window, use), the race classes by form, the six address spaces and which the emitter reads, DMA memory-model note | `7c693cb7` | `C-SPEICHERMODELL.md`, `PLAN-HARDWARE.md` §3 |
| `messung/AUDIT-*.md`, `K100-*.md`, `K3-*.md`, `GEGENPROBE-F03`, `KLASSEN-F03`, `BERICHT-H0`, `BERICHT-B10/SUCHE/O3-RATSCHE/ERZEUGERHALT/UEBERSETZERFAMILIE`, `W24-FRAGMENTE` | the 2026-09-01..05 audits, the four `K100` gates, the three readings of `K3` ("0 of 8"), the standing adversary of `F03`, the fragment break-throughs (`H = 0`) | `7c693cb7` (`AUDIT-2026-09-02`, `AUDIT-K100`, `BERICHT-H0`, `GEGENPROBE-F03`, `K3-BEFUND`, `KLASSEN-F03`: `4bb5e944`) | `FRAGMENTE.md`, `PRUEFER.md`, this file |
| `messung/DOMAENEN*`, `PREDICATE-NAMES`, `EINHEITENSICHT`, `ERSTNAMEN`, `K001*`, `K003-TOR`, `SCHLEIFEN*`, `TORREICHWEITE`, `UNTERE-GRENZE`, `AUSSETZUNG`, `RUMPFKANAL-*`, `ZEREMONIE`, `VIER-LUECKEN` | the checker's rule studies: quantifier domains, names a predicate may write, the unit view, the English first names, the `K001` bound, the loop invariant, the lower bound `2 of 94`, `leave`/`breaking`, the body channel's 66 refusals | `4bb5e944` for those still in the tree on 2026-10-17 | `PRUEFER.md` |
| `messung/{ABNAHME-*,VOLLER-LAUF-GELESEN,AUFRAEUMEN-2026-09-12,VORRICHTUNGEN,TODO-TREUE-2026-09-04,KETTE-2026-09-13,WARTESCHRANKEN-2026-09-15}.md` | the full acceptance runs read line by line (49 guardians, "100 % over a guardian that stood after 2.8 seconds"), the guardian fixtures, the TODO staleness rate, the chain count of 2026-09-13, the waiting-bound census | `7c693cb7` | `WERKZEUGKASTEN.md`, `MESSUNGEN.md` |
| `dokumente/{DONE,PROJECT-STATUS,STAND-2026-09-03}.md` | the finished list, the provenance behind the README snapshot, the handover of 2026-09-03 | `7c693cb7` | this file, `README.md` |
| `dokumente/AUFTRAG-*.md` (3), `dokumente/GLEITKOMMA.md` | the GabbroV, GabbroV-verification and translation-validation assignments; the float memo ("the price is a second fact logic, and the demand is zero") | `7c693cb7` | `GABBROV.md`, `GLEITKOMMA.md` |
| `lanes/*.md` (83 task files) | finished lane assignments; the templates stay | `7c693cb7` | `git log` |
| `dokumente/x86/` (48), `Grammatik/X86/` (357 Lean files), `DIRECT-COMPILER*.md`, `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | the x86-64 hardware model, its optimiser rule library, the direct-compiler record and design | branch `archive` | `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §8, `PLAN-HARDWARE.md` §2.3 |

---

## 4. The trajectory — the pattern above the individual errors

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

**Countermeasure, since 2026-08-13:** P0.1 has been run (`MESSUNGEN.md`) and immediately found
an error in the counting rule that three rebuilds of proofreading had not. **No further design
text before P0.2 and P0.3.**

**The same pattern one level up, 2026-10:** the selected target of the validation
plan changed twice in a week (C11 → direct x86-64 bytes, 2026-10-01 → AArch64 on Sail Arm,
2026-10-07) and the working backend changed to LLVM IR within another week (2026-10-14); each
switch left documents naming the target before it. The goal theorem did
not move: it is about the model, and the model was never the backend.

## 5. The form that repeats

Six of the nine entries of the early list are the same move: **a sentence that would be true if
its scope were not silently widened.** `format` → everything; parameter boundary → everywhere;
one measurement of the mechanism → its transfer; Silver → Gold.

That is not carelessness but what a design text does by itself as long as nobody **writes the
scope down**. Which is why every claim in the `README` and in `SPRACHE.md` now carries one —
and where none stands, that is a finding. The 2026-10 entries add two shapes of the same move:
*a claim about an artifact that nobody ran through its consumer* (the certificate that does not
elaborate), and *a decision that reversed without reaching the documents that stated it* (x86-64).
