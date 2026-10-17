# Toolbox — the instruments, and the working rules they were built from

**What this is.** The inventory of the measuring instruments in `instrumente/` (95 entries: 54
`pruefe-*` guardians, 22 `zaehle-*` counters, `mutiere-pruefer.py`, `abnahme.py`, helpers and
data files), the probe corpora that stand beside them, and the working rules (**W1–W29**) the
folder earned. **Admission condition for a rule:** it comes from a *mistake in this folder* and
the mistake is named. No good intentions, no borrowed wisdom — whoever reads a rule can see the
damage it was paid for. The rule ids are cited from source comments and other documents and are
never renumbered.

> The trap numbering (`Falle 80` …) lives in `messung/fallen-klassifikation.tsv` — 100 paid-for
> Caprock traps, a measured inventory with a named source; nothing is added to it after the fact.
> **W1 and W2 are both children of trap 80** (*a number a human runs parallel to the truth*) —
> once in the instrument, once in the declaration.

---

## 1. Running the instruments

```bash
./instrumente/abnahme.py            # every guardian, one verdict each (the acceptance run)
./instrumente/abnahme.py --voll     # additionally the heavy ones: the mutation run over the whole checker, the Lean/Isabelle proof guardians
./instrumente/pruefe-waechter.py [--lauf]   # are the guardians themselves fit instruments?
```

**Exit codes, the same in every instrument** (`messung/RUECKLAUFWERTE.md`): `0` measured, no
finding · `1` measured, and something stands open · `2` **nothing was measured** (a missing
precondition, a failed speech test, an empty population, a timeout, a crash). The line between
1 and 2 answers one question — *who has to change, the tree or the set-up?* `abnahme.py` prints
five verdicts: green · **ROT** (everything measured, something open) · **TEILMESSUNG** (it left
before its last measurement and says where: something was measured, not everything, and the
finding count beside it is a lower bound) · **ABBRUCH** (nothing measured) · **NICHT FAHRBAR**
(its subject is not here, e.g. a foreign corpus). It reads the cast from the directory
(`pruefe-*`, `mutiere-*`, `zaehle-*`), not from a list in the script, so a new guardian is in the
acceptance run on the day it appears; what stays outside is named with its reason in
`pruefe-waechter.py` (`OHNE_URTEIL`, `SCHWER`, `FREMDER_KORPUS`).

**After the mutation run the next acceptance run is red, and that is not a finding.** The
mutation run rewrites checker sources and restores them byte for byte — with a new mtime, so
every source is younger than the built binary and `pruefe-saetze.py` aborts with *binary is
OLDER than N source files*. The cure is a build (`cargo build`), never a `touch` on the binary:
forging the timestamp hides exactly the mixture the guard stands against.

**Every instrument carries five requirements**, held statically by `pruefe-waechter.py` (the
fifth only by `--lauf`): a **deadline** on everything it executes (a hang looks like "still
running", not like a finding) · a **speech test** in both directions (what should fall falls,
what should not does not: *a guardian that cannot go red measures nothing*) · **red on abort**
(`set -e` with `timeout` is the trap: the deadline ended the guardian silently with exit 0) ·
the **work quantity** beside the verdict (W17) · a **pinned locale** (`LC_ALL=C`: under
`de_DE.UTF-8` the linker says *Mehrfachdefinition von*, a tool searching for the English
words reported a failure that did not exist).

**Heavy runs — one at a time, with `free -g` beside them.** `cargo build` and `cargo test
--no-fail-fast`, the whole mutation run, `pruefe-emission.sh`, `pruefe-luecken.py`, Isabelle
and Lean builds; never two in one tree (`cargo test` rebuilds the model with `lake` and
replaces the `.olean` files the running `lean` processes read — measured as 52 phantom Lean
errors). An agent gets its own working directory and its own scratch directory.

---

## 2. The working rules

### W1 — A coverage number counts evidence, not attempts
*Damage (2026-08-14):* five new rules, five new mutations, summary `37 of 37` — formed from
`len(MUTATIONEN)`, while an older mutation had lost its anchor and did not run at all. **A dead
mutation counted as coverage**, devaluing every other number, because it is the number the
others are checked with.
*Rule:* every coverage, completeness or progress number is formed from verified evidence, never
from attempts, entries or lines; a dropout must **lower** the number. *Handle:*
`mutiere-pruefer.py` counts `caught` out of `valid`; a lost anchor appears as `ANKER FEHLT` and
falls out of the denominator, not into the numerator.

### W2 — The zero promise: the checker is the instrument for the numbers it checks
*Damage:* `costs` lines for a new example were first guessed; then pushed down to `1 ops` so the
checker named the true numbers (`4`, `2`, `2`). Right procedure, manual handle — and manual
work on a number is where numbers start running parallel to the truth.
*Rule:* where a pass **checks** a declared number it must also be able to **name** it; a promise
is copied down, not guessed. *Handle:* `gabbro costs file.gab` prints, per function, the
computed body figure beside the promised one, and per `locks` block the hold time beside `held`.
The `slack` column is a difference, not a verdict (for `held` it is almost always wrong, because
the latency statement computes with the promise).

### W3 — No construct without measured need
*Paid twice:* `abi { … }` was stopped before it was written; `locks ordered` died at the paper
test with **zero** test cases — in the whole tree there was no repeated acquisition of one lock
class. *Rule:* a construct needs **counted** sites in real code before the first grammar line —
not plausible, not remembered ones. The test must be allowed to kill its own candidate (that
paper test found two gaps on no list instead).

### W4 — A loud overstatement is cheaper than a silent exception
*Case:* `locks shared` stood, but the witness at the call boundary needed a call graph that did
not exist; without a rule the boundary was permeable (the callee writes exclusively, the caller
holds shared). *Rule:* where a load-bearing rule has a hole that can only be closed later, the
coarse, too-strict version goes in front — not nothing — and is **named** as interim. Somebody
goes looking after a loud overstatement; nobody goes looking after a silent exception, because
it looks like a green. *Handle:* `H005` — a shared block calls no function with `requires
Held(…)`, full stop.

### W5 — An interim rule carries three parts, otherwise it becomes permanent
A too-strict rule without an expiry note is taken for the right one after three months. The
refusal itself names (1) the rule — what it forbids, (2) the price — what it forbids too much,
concretely, (3) the replacement — which check will replace it and what that check must do. In
the refusal and not in a ticket: the refusal is read by the person paying the price, who is the
one who can report it. *Handle:* `H005`.

### W6 — Omitting a runtime check is justified by M1 alone, never by an invariant
*Damage (booked one level up, `5904cae`):* smoothing a claim about the tree instead of surveying
it; one level down it would be striking a range check from the generated C because *the proof
says it cannot go negative*. M1 hangs on the **type** (`u32 in 0 ..= NSLOTS`) and is recomputed
per program; an invariant hangs on a **template** and lives in the trust surface once. A
`refcount : nat` proved `oldrc >= 1` from the invariant is exactly one net; the typed range is
a second one that holds without it. *Rule, at every emission decision that cites a proof:* **the
cited fact must be derivable from M1 alone, otherwise the check stays in the C.** One line in
the emission pass instead of one per construct.

### W7 — A number without a source list does not belong in a document
*Paid three times in one day:* 74 proof obligations (list lost), 19 hanging obligations in
eleven classes (attribution lost for 6 of 11), `delete_leaf` 3.6–6 : 1 (lost; recounted 1.75 :
1). The damage is not vagueness but **irrefutability**: a number with no attribution cannot be
checked by anyone, is quoted, carries decisions and is immune to correction.
*Rule:* a reported number carries the list it came from — per item `file:line` or a re-runnable
command; if it does not fit in the document it goes in a file beside it. *A number with a list
is allowed to be wrong: it is checkably wrong.*
*Addition (2026-08-16):* the sweep reads **table cells** as claims, not only sentences — the
89 closures sat in a table cell and survived the first sweep.
*The number pair, measured on one tree:* **67** `dyn` sites (search path stated) reproduced
**exactly**; **89** closures (path stated nowhere) reproduced as **64**, off by 28 % — and
nobody would have noticed, because it looked plausible. *Handles:* `pruefe-luecken.py`,
`zaehle-bereichspflichten.py`, `gabbro costs`, `gabbro k-condition` print their sites;
`pruefe-zahlen.py` is the register (§3).

### W8 — A compositional check is probed over two levels, not one
`E008` includes the effects of callees. The obvious probe (caller declares `writes`, callee
declares `writes`) is already green if the pass sees only the first level. A probe for a
transitive property puts an **intermediate function that does not itself have the property**
between them (`masks IRQ` only at the bottom, `pure` in the middle and at the top): if the pass
falls back to one level the effect vanishes and the probe tips. Every analysis that says
"includes …" needs it (the pairing pass: a `publishes`/`awaits` pairing across an intermediate
function).

### W9 — If an analysis coarsens, the direction is checked, not the convenience
`E008` computes over **sets**, not paths — right, because here the coarseness errs in the safe
direction (more effects than there are, never fewer). The same coarseness is inadmissible for
`diverges`, which does *not* travel upward (it holds only if a callee diverges on **every**
path): over sets it would force `diverges` onto functions that return — the unsafe direction.
Before an analysis coarsens, ask per property which way the coarse version errs, and write the
answer in the pass comment.

### W10 — The third state: not refused does not mean confirmed
`E008` rightly does not refuse from a lower bound (R16), but the first version then let the
function pass **silently**: a `pure` promise behind a cycle was green — the escape-hatch
assurance of R15 one level down. Where an analysis may not refuse out of incompleteness it may
also not confirm; the honest third state is **undecidable**, with a code of its own, visible.
*Handle:* `E009` names the reason and says the promise is *not checked* here. Two of its first
three firings were gaps in the graph, not in the program.

### W11 — Every gate ratio names its N, and a jump in N is itself a test case
*Near miss:* sharpening *excerpt / unit* with a search for `…` in raw text threw out five of six
fragments (the `…` sat in comments) and gate P2 would have read `1 of 1 without error (100 %)`
— also 100 %. A filter that shrinks the population masquerades as success. The right report is
*"N fell from 6 to 1"*. The flip side of W1: when the denominator shrinks, that must be louder
than the rising numerator. *Confirmed one day later (B3, 2026-08-16):* a broken brace in a copy
of the subject made the reported number fall silently from 26 to 24 (two bodies dropped out of
the inventory); only the abort counter showed it.
*The number pair for R14:* the spread between the **discarded** rule versions of the B3 tool
was **factor 130** (0.03 % — saw only bodies with a loop; 4.36 % — read `for x in segs` as a
non-domain; 0.74 % — missed three chain kinds; 0.95 % reported); the distance between tool and
truth after the three R14 probes was **factor 1**. A number from this class of tool without R14
is not imprecise, it is worthless — three of four versions were wrong and none looked wrong.

### W12 — A filled map is no evidence of a complete map
The domain bound for `mappings of` was there and demonstrated — and did not bite, because type
resolution knew formats, devices and tables and **no walks**: `ptr<normal, r> Seitenabstieg`
was `Unbekannt`, which ran along as an empty entry; half an hour was lost searching at the wrong
end. *A resolution with a catch-all branch claims a completeness it does not have.* *Rule:* at
every resolution site match **exhaustively over the declaration kinds, without a `_` branch**,
so a new kind is a compile error at every chain that does not handle it. *Handle:*
`Traegerart::ALLE` (`umgebung.rs`). `Typ::Unbekannt` stays admissible as a *result*; what is no
longer possible is being unknown because nobody looked.

### W13 — Touching is not checking
A pass that touches a construct does not check it: `schleifen.rs` read `ItemArt::Check` only to
walk into `can_fail`; `kbedingung.rs` read `ops` as `!ops.is_empty()`, a boolean, never a set.
Both counted as "read", and no promise of either ever fell. The field level had the distinction
(`pruefe-klauseln.py`: ZUSAGE versus ABSENKUNG); the construct level lost it and reported 21 of
23 read. *Rule:* a coverage question is not *"does a pass access it"* but **"has something ever
fallen on it"** — is there a poison probe that makes it fall (7 of 19 had none)? Derive the new
question anew instead of stretching the old measure.

### W14 — Your own coverage is systematically overestimated by an order of magnitude
Expected → measured: field clauses without a reader **4 → 48**; German message texts **41 →
151**; constructs without a probe **2 → 7**. Intuition about one's *own* coverage runs about a
factor ten optimistic, because one counts what one remembers and one remembers what one built —
what was never built leaves no memory, which is the class these tools measure. *Rule:* write the
expectation down before measuring (R11) and compute with the factor: an estimate of four means
"probably a few dozen". It does not license estimating high instead of measuring.

### W15 — A catch-all branch is a silent promise, not a reservation
The checker had **78 `_ => {}` branches** over `StmtArt`; every pass descended by itself, every
one ended in a catch-all and each forgot a different arm (`observes` invisible to six passes,
`exchange` to five, `narrow … else` to two). A call *inside* an `observes` block did not reach
the call graph, so two `E008` vanished. A catch-all reads like a reservation and acts like a
promise, and nobody re-checks it when a statement kind is added. The difference between a
catch-all and a refusal is the difference between a gap and an entry (`emit.rs` closes with
`_ => weigere(…)` naming every form it cannot do: `C001`). *Rule:* whatever descends a tree
matches exhaustively, without `_`, in **one** place (`lib.rs::unterbloecke`,
`lib.rs::endet_immer`) that all others use — `endet_immer` had stood three times, each
incomplete and different. `pruefe-abstieg.py` measures it (at file level it said 7 gaps, at
function level 15 — W14, fourth time).

### W16 — A measuring tool without a descent step measures its own reading width
*Three tools in one week looked plausible and measured something other than their subject:* the
call envelope (did not descend into callees: a call in a `match` arm was invisible),
`enthaelt_schritt` (nested bodies: a `locks { }` around a step silenced `O006`),
`pruefe-gruende.py` (did not read past the cut-off line, and flagged `N011` — the one rule whose
note names the carrying reason). *Pre-run question:* **is the subject recursive or multi-line —
and does the tool descend?** With W8 this is a mechanical pre-check for every new tool. The
worst case is not loss but **inversion**: when the cut-off material is the *exculpatory* one the
tool finds the guilty reliably — a lost answer lacks something, an inverted one shows the
opposite and looks complete. *The family reaches past tools:* `rsync -a` keeps mtimes and
`cargo` decides freshness by mtime, so a transferred file with an old mtime is "current" and the
build is a mixture of new source and old object (a test red on the server, green locally, with
**byte-identical** sources). *The mirror image (2026-08-20):* the cure `-rlpgoD` (fresh mtimes)
breaks `pruefe-beweise.sh`, which wants *evidence* that Isabelle really built and the second way
to that evidence is a timestamp (*no build log younger than every source*): `isabelle build`
decides freshness by **content**, `cargo` by **time**; two transfers, not two habits. The guard
says in its refusal which of the two causes is the likelier.

### W17 — Success without work: a positive verdict about nothing
*Three different tools the same day:* `isabelle build -D .` selected **nothing** and said
*Finished*; `zaehle-b3.py` printed `! ABBRUCH` and exited 0; a `pruefe-todo.py` pattern hit
nothing and said *table agrees with the subject*. A false verdict has a subject and errs about
it; this one has none and says yes. *Rule:* **beside the verdict stands the work quantity** —
files, sites, hits — otherwise a green run is indistinguishable from an empty one (kin of W11,
one level up). `pruefe-waechter.py` demands it as its fourth requirement; `--lauf` prints the
wall time per guardian and the sum (19 of 25 in 4.4 s on 2026-08-20).
*One level higher: the exception list whose reason nobody recomputes.* `pruefe-waechter.py`
excluded five instruments as "too heavy for one run", each with a reason; **four reasons were
wrong** (`pruefe-emission.sh` "~25 min" — measured 13.7 s; `pruefe-notation.py` "fourteen
`cargo run`" — 0.56 s and no `cargo run`; …). The 25 minutes came from the morning the guard hung
on `baum41` — the deadline removed the hang and the number stayed as the reason never to measure
it again. *Rule:* an exception from measurement carries its reason **as a measurement**, with
date and place; where the reason is a time, the time the run itself measured stands beside it.

### W18 — A register that contains its own output has a fixed point instead of a measurement
`pruefe-zahlen.py` holds figures against the command that derives them. On its first day the two
figures it prints *about itself* (guarded and unguarded figures) went into its own register: the
entry calls the tool, the tool checks the entry — cancelled after two minutes. A fixed point
that *terminates* would be worse: the number is then right always, independent of whether
anything was measured (R15 above the tool). *Rule:* no register entry may name a command that is
the register-keeping tool itself — checked by code. **The first guard was one step deep** (it
looked for the tool's name in the command): `pruefe-zahlen.py → pruefe-waechter.py --lauf →
every light guardian → pruefe-zahlen.py` closes a ring of length two. The version that works at
any depth hangs on **child processes** (an environment mark inherited by every register command;
whoever finds it at start was called by itself), measured on a real child. *A guard against a
cycle must hang on the edge that really closes it: a name comparison closes a cycle over names;
a process closes one over processes.*

### W19 — A judgement that reads as a measurement acquires the authority of a measurement
`N_ritus` was booked as a gate *"`zaehle-bereichspflichten.py` distinguishes the three cases"* —
the tool did not; the distinction stood in `PFLICHTEN.txt`, in judgement, and the number read as
coming from a run. Two parts of the resolution, the second more important: build the half that
needs no judgement (`N_folgenlos`: a `narrow` whose removal changes nothing is decoration;
two-level probe, W8; **0**), and **name it differently** — `N_ritus` is defined by the
reachability of the `else` branch, and an unreachable site still carries a duty because M1 does
not see the bound. *A name is not a label, it is a declaration of responsibility.* The same cut
recurs in `gabbro ceremony`: *derivable* versus *load-bearing*.

### W20 — A figure that can become a target carries its calibration in the tool
A usability measure instantly becomes an optimisation target; uncalibrated, the cheapest thing
falls first — `effects`, `costs`, the pairing clauses, the very subject of the language. A
calibration in a footnote is not read when the number is quoted. Form: **two axes in the same
output.** Axis 1, measured: does this fact stand a second time in the unit (derivable /
redundant / load-bearing). Axis 2, declared: may the figure fall — per rule a yes/no **with a
reason** (a no without a sentence is an edict, a yes without one an invitation). `gabbro ceremony
--tafel` prints both; a guardian reads the table from the tool (W7). The separation allows the
case that matters: *derivable and must not fall* (`A4`, an effect line a callee explains anyway —
striking it would undo `E008`). The speech test moves from patterns to rules: a rule of the table
with no hit anywhere is itself a finding, and what the corpus does not trigger a deliberately
badly written probe does (the first run reported **zero** redundant sites — a clean corpus and a
blind tool look alike).

### W21 — A guardian whose subject lies elsewhere measures the machine
`pruefe-waechter.py --lauf` was green on the workstation and red on the build server, with
byte-identical sources: `zaehle-narrow.py` measures the second corpus and `zaehle-b3.py` the
Caprock base, and **both exist only on the workstation**. A missing subject appears either as
**red without a finding** (the call fails) or as **green without a measurement** (the tool counts
zero and says "no findings") — the second is W17, the first its mirror image, equally worthless.
*Family reach into the working tree:* `../caprock-messbasis` is a *relative* path and in a git
worktree it points beside the worktree, not beside the main checkout. *Rule:* a guardian whose
subject lies outside the tree **declares the path and what stands there** (`FREMDER_KORPUS`); if
it is missing the result is neither red nor green but **not measured**, with its number beside
the verdict ("18 of 19 that ran name their work quantity, 1 more not measured: foreign corpus
missing" — a hole that can be counted is an item). *Pre-step:* ask whether the subject can be
**brought along** — `mutiere-pruefer.py --anker` was red on the server because the transferred
tree is no git repository and its speech test demanded `clean`/`dirty` of the surrounding tree
(`SPRECHPROBE GESCHEITERT`, a false sentence). The cure was a throwaway repository of its own
(`git init`, one file, one commit: all three states reachable anywhere). A probe with a single
reachable outcome measures nothing; that is a missing precondition and ends with `2`.
*The family was three:* `pruefe-luecken.py` asked the same question in its own copy and read
only `stdout` (empty means clean) — so it ran on and **wrote into sources** with no evidence that
the tree was clean; `erzeuge-mutationen.py` read exit 128 as "crates/ is not clean" — right
refusal, wrong reason, which sends the reader to repair a clean tree. *Whoever calls `git`
looks at its return code: an empty output from a failed command is not an answer.*

### W22 — A false refusal is reported by nobody, so it is measured by the corpus asymmetry
The error classes of this folder nearly all ran one way (a rule stayed silent, a note claimed,
a clause had no reader). The other direction — the checker **refuses a correct program** — had
occurred exactly zero times in 492 commits and then three times in two days (`U005` rank not
resolving in an empty module path; `M2` consumed on both paths reported as on none; `M108` a
`pure` call killing a narrowing). Too strict is harmless to the promise and expensive for usability
— and nobody reports it, *because the programmer rewrites the program instead of suspecting the
checker*. The structural cause is measurable: on 2026-08-25 **275 poison files (6 937 lines)**
against **50 examples (4 564 lines)** — 5.5 : 1; today (2026-10-17) `ls beispiele/gift/*.gab | wc
-l` gives **898** against **170** in `beispiele/` (5.3 : 1 in files). A poison probe can in
principle not find a false refusal; it checks that something falls. *Consequences, in order:*
goal 3 gets a second axis (how often is correct code refused — ceremony in its most expensive
form: not a line but a rebuild, leaving a language description that carries the workaround as an
idiom); the **positive corpus is the only probe of this class** (every repair of a false
refusal brings its probe as a *correct* program, not as a poison); whoever rewrites a refused
program instead of questioning the rule has discarded the finding.

### W23 — A measurement whose population contains its own probes measures itself
*Case (2026-08-28):* to evidence the need for `V009` (how often does a plain read from an
`atomic` gate a branch?) the first run reported **26 bindings, 0 plain** over `beispiele/` **and**
`beispiele/gift/` summed; the second split the pots, and the **only** plain atomic read in the
tree was the poison probe written for `V009`. W18 in the measurement direction: a fixed point
is noticed because the number never moves; a self-measurement delivers a plausible, non-trivial
number nobody can trace. *Pre-run question:* **does the set I count over contain files written for
the subject of this count?** `beispiele/gift/` belongs in hit counts (*does the rule fall?*) and
nowhere else; where both pots are needed they are reported separately. And a corrected
measurement keeps the replaced number beside the right one — *a corrected measurement without the
replaced number is a claim about a correction.*

### W24 — Before a new word is considered: does the obvious form already parse?
*Four cases, the fourth the most expensive (a wrong row answered the question for eleven days):*
`transition` (*"a gap in the graph, not in the program"*), «B35» (same), the **`ops` call form**
(2026-08-28; a proposed statement `insert v.slots[n] under p;` with a new word `under` — but
`Verzeichnis::insert(v, i)` has always parsed: `parse.rs::erwarte_feldname` accepts any
vocabulary word after `::`; the EBNF did not say so), and **«B17»** (a multi-place form for
`transition` — but `transset = placeshift { "," placeshift }` stands in `SYNTAX.md` and is *used*
in `beispiele/02-geraet.gab`; of seven probes exactly one fell at the parser, at one token; what
really lacked was that `breaking I { … }` never resolved its name). Through the unchanged
checker the real answers were `E009` (callee unknown to the graph) and `K003` — not a single
`P00x`: the missing thing was the **callee**, not the call form. *Rule, asked before the
weighing:* **write the obvious form and run it through the unchanged checker — does it parse?
and if not, does it fall at the parser or at something behind it?** The rejected statement kind
would have forced the effect, cost, lock and phase question to be re-answered at thirty
`StmtArt::Ruf` sites. Sister of W22 (measure the *false refusal* by the corpus asymmetry; here
the *supposed unwritability* by one run).

### W25 — A number evidences its denominator, not its label
`pruefe-grammatiktafel.py` reported `UNGEDECKT = 4` and wrote *"the generator refuses, the
checker does not"* beside three of the four words. The number was right (`chain`, `queue`,
`threads`, `state` are uncovered); the sentence was wrong — the generator does not refuse three of
them (`0 errors, 0 C001`, measured per smallest program). `absage` was the set of words that
**occur in a refusal text**, not the set of forms whose refusal anyone measured: the guardian took
a mention for a measurement. *A wrong sentence beside a right number is the most durable form of
an error, because every check that points at the number confirms it.* Unlike W16 (the *number* is
wrong) here the number stands and the label carries a second, unmeasured claim — the
consequence was a wrong **class**: three corpus gaps looked like a language decision for four
days. *Precaution:* a label that gives a reason needs the same measurement as the number beside
it; where it is derived it says so (*"contains the word"*).

### W26 — A truncated population looks like a verdict over everything
`pruefe-emission.sh` died at `F06`'s `N043` in **stage 4 of 10** with exit 1; stages 9 and 10 never
ran and no line said so — behind the cut stood two findings nobody saw for two weeks (six files
whose generated C does not compile; a counter seven too low). W17 is the *empty* population (a
green verdict about nothing); W26 is the *truncated* one, and worse: it looks like a verdict over
**everything**. The exit code cannot say it — the three classes (`0`, `1`, `2`) know "nothing
measured", not **"half measured"**; a `1` in mid-run means *a finding here* and *an abort for
everything behind* at once. The method that found the earlier holes (each guardian once over an
empty tree) catches a precondition missing from the *start*, not one that breaks *mid-run* (the
empty tree measures the start; this measures the middle). Measured over 50 instruments
(`messung/RUECKLAUFWERTE.md`): **251** exit sites behind the first (the surface), **248** really
end the run, **104** end with `1` *reachably without anything being broken*, **92** carry output
on both sides — the danger; a surface nobody can shrink stops being read, hence the sieve.
*Precaution, not a cure:* **whoever leaves before the end says WHERE** (`instrumente/abschnitt.py`
and `abschnitt.sh`; `abnahme.py` reads them and prints `TEILMESSUNG`, with the finding count a
lower bound). The WHERE comes from the tool's own output (it remembers the last printed `== … ==`
line; a mark per stage would be a second register over one thing, W7). The one line that needs
judgement is `fertig()`: a guardian that ends with `1` at its **last** exit has measured
everything, one that ends with `1` at the second-to-last has not, and from outside both look
alike — it belongs *before the verdict chain*. A covered site cuts the run just as much; it only
says so (what is measured is whether the cut is announced, never whether it is right: W10).

### W27 — A missing handle, read as a missing capability
*Booked 2026-09-01 after three instances in one lane:* `--with` did not reach `--compare`, so
*"does it see the derivation across the boundary?"* was **not askable**, and the absence of an
answer read like a negative; `emit --unit` did not exist — the capability lay in `bau.rs` with no
name on the command line (7 refusals without the flag, 0 with it, byte-identical C); `assume`
at a unit boundary was **not impossible but unbuilt**, and nothing at the boundary says the
decision was taken. Not W16 (there the instrument measures something else; the countermeasure is
to check the instrument): here it **cannot accept the question**. *Ask whether the answer is
"no" or "not asked".* The most expensive form stood in `N041`: the rule held every named item
except `module` and `use`, `extern fn` included — the construct whose purpose is the deliberate
binding to a C name — so a Gabbro program could not print and **eight attempts at "add two
numbers"** had an explanation that was not the language. Redeemed 2026-09-01 as a **change**,
not an exception: `beispiele/63-druckt.gab` prints `Hallo` (checked, emitted, compiled under
`-Wall -Wextra -Werror`, run), and `N046` asks the right question — *does the signature match
the one C already knows?* The handle for that was missing too: `./instrumente/miss-c-signaturen.py`
(not in the tree today; the measurement stood at 138 of 558 names bindable, 420 not).

### W28 — A figure that triggers a lane carries its HANDLE and its DENOMINATOR
*Booked 2026-09-01 after the sixth instance of W16 — this time hitting a prioritisation.* The
vocabulary-ratchet lane was justified by *"226 → 234 words in one day"*; the handle behind it
(`grep -oE '"[a-z_][a-z0-9_]*"' kw.rs | sort -u | wc -l → 234`) takes every lowercase string of
the file — fifteen too many from comments, the three capitalised too few. Counted properly it was
never 234 and never 226: 219 · 220 · 222 over eight days. For **result** figures the tree has
long kept the denominator (W7, the counter-probe in the guardian); for **justification** figures
not — and the damage is larger there: a wrong result figure turns red next run, a wrong
justification figure *steers a lane and disappears*. The conclusion held here (221 words and a
lowering sentence are a disproportion whatever the slope) — **luck, not merit.** *Second line,
after the eighth instance:* two of the six W16 cases share a special reason: **`gift/` in the
denominator** (the domain computation: 17 words fall → measured 3; §42: 14/31/6/102 → 3/12/3/52 in
the ratchet corpus, eleven of fourteen `order` being poison probes). A corpus whose purpose is
refusal inside a count of *use*. The rule: **a figure that triggers a lane carries its handle and
its denominator; every frequency measurement runs without `gift/` unless somebody writes the
opposite.** Seen live the same hour: `zaehle-formate.py` reported *"523 files, 46 format
declarations"*; recounted **39**, 13 of them in `gift/` — a third. Of 21 tools counting over
`.gab`, four did not name `gift/` (two of them select a subset that excludes it anyway).

### W29 — Before a rule over a WORD: count its uses, and their DIRECTION
*Booked 2026-09-01 after the third instance.* A rule over a keyword hits **all** its uses, and the
distribution behind it is rarely uniform:

| Word | the rule wanted | the distribution was |
|---|---|---|
| `runs online` | *"without a generated check → `C001`"* | **three classes**: `table … ops` (3) carries it through a machine-checked template · `table` without `ops` (5) as an `E` duty · **`walk` (3) through nothing** |
| `narrow … else` | add a terminator | **three constructs of one build**: `narrow … else`, `let … else`, the `exchange`-`update` body |
| `_ =>` | strike the wildcards | **three categories**: dead defence (4) · load-bearing default (6) · real finding (1) |

Three times the same move — a rule over the **surface** instead of the **thing**: a rule over the
word `online` would have hit two working registers to reach the one that does not. The count is
cheaper than the rule, with three outcomes (uniform → the rule is right, now measured instead of
assumed; several → it hits too broad, it belongs to the class, not the word; one class → the
rule is a refusal over one case). *Addendum:* a count over **the own corpus** is self-confirming
(a construct not sensibly writable today is not there, so rule A refuses, so it never arises —
a circle, not a finding); where an external witness exists (`../caprock-messbasis`, 139 files,
75 294 lines) it is stronger than the corpus. *Second half: not only how many, but whether they go
wrong in the same direction.* For `_ =>` the three categories were ordered **by danger** (silent
memory error · wrong type · wrong value) and the repair order hung on that, not on frequency; the
case first caught is in the Caprock base: of five sites that change a mapping (`mmu.rs`), three
**add**, one **changes rights**, one **switches the address space** — a rule *"every PTE write
invalidates"* would be wrong for three of five (a not-present → present transition needs no
invalidation on x86). *The rule belongs to the KIND of change, not to the write* — and whether the
add case needs an invalidation is an architecture question, so an `assume … arch` with a
falsifier, not a decision in the lowering. **Two uses that MASK each other are worse than ten
that do the same.**

### The R-rules that these entries cite
The measurement protocols of the folder cite rules `R1`–`R18`; the wording was never collected in
one place, and what follows is *reconstructed from use* in the entries above and the
measurements (`MESSUNGEN.md`), not quoted: **R1** the protocol is committed before the first
counted site · **R2** a gate is not moved after the run (a population may be corrected only for a
reason independent of the result — and the correction that moves *against* the flattering
reading is never a reinterpretation) · **R7** the template entry stands before the grammar ·
**R8** overstate only in the safe direction · **R11** a measurement that delivers the hoped-for
result at the first try is suspect (for a comparison "hoped for" means *winning by a mile*) —
write an expectation down before measuring · **R14** a measuring tool first proves that it can
measure: (a) a deliberate abort must be counted, (b) the number must hang on the subject (mutate
a copy, the number moves), (c) the search paths find their known sites / full count of the
enumerated heads · **R15** an assurance that is satisfied because nothing happened is no
assurance · **R16** a number from a search path that aborted is a lower bound and is called one ·
**R17** says what one starts with, not what one ends with · **R18** a class with one instance is
not designed before its decisive fragment.

---

## 3. The instrument inventory (checked against `ls instrumente/`, 2026-10-17)

Each row: the command, and what it measures. The *docstring of the tool* is the contract and
wins over this table; `abnahme.py` runs everything marked **A**.

### 3.1 Acceptance and meta-guardians
| Tool | Measures |
|---|---|
| `abnahme.py` **A** | the whole cast, one verdict per guardian (§1); `--voll` adds the heavy ones; `--probe` is its speech test |
| `pruefe-waechter.py` | the five requirements of §1 for every instrument; `--lauf` executes the light ones and reads the exit class they promise |
| `abschnitt.py`, `abschnitt.sh` | the shared form of *whoever leaves mid-run says where* (W26) |
| `binaer.sh` | the single rule for *which* `gabbro` binary an instrument measures (never a stale or a different-profile one: an instrument that takes `target/release/gabbro` because it exists measures whatever was built last) |
| `korpus.py` | "is this file one `git` knows about?" — the check a dozen tree walks lacked |
| `zaehle-probenzweige.py` | how many instruments have a branch only the speech test ever reached |

### 3.2 Numbers and documents
| Tool | Measures |
|---|---|
| `pruefe-zahlen.py` **A** | every figure in the guarded documents against the command that derives it; `UNBEWACHBAR` is the register of figures with a written reason why no command can exist (a record, a foreign tree, an ordinal, a judgement) and a reason that no longer points at anything falls (W18, W7) |
| `pruefe-todo.py` **A** | `TODO.md` against itself and against the folder; reads `messung/KENNZAHLEN.md` together with it |
| `pruefe-widerruf.py` **A** | retracted sentences: no document may still say what a measurement refuted (exempt blocks: `<!-- widerruf:aus --> … <!-- widerruf:an -->`) |
| `pruefe-englisch.py` **A** | the surface language is English: German diagnostic texts, source comments, ratchets per layer |
| `pruefe-kennungen.py`, `pruefe-vergabe.py` | no code twice; one code, one rule (not only one code, one file) |
| `pruefe-saetze.py` **A** | the second tooth of the pass register: no new refusal code without its sentence (`crates/gabbro-check/src/saetze.rs`) |
| `pruefe-syntax.sh` **A** | the examples in the documents against `SYNTAX.md` (forbidden forms, retired German keywords in code blocks *and* prose), the EBNF closed and every rule reachable, the vocabulary table covers the terminals |
| `pruefe-wortschatz.py`, `zaehle-wortschatz.py` | the vocabulary table against the grammar; the vocabulary ratchet (two marks) |
| `pruefe-grammatiktafel.py` | form × responsibility from the grammar; `UNGEDECKT` must be empty (W25: labels are measured too) |
| `pruefe-zitate.py` | a note that claims a check its rule does not perform |
| `pruefe-gruende.py` | does a rule stand on the technical or on the load-bearing reason (W16: reads past the continuation line) |
| `pruefe-notation.py` | the notation gaps of §2 of `FRAGMENTE.md` against *today's* grammar (smallest program per gap), plus the emitter gaps |
| `pruefe-manifest.py` | the obligation manifest against its correspondence table |

### 3.3 Checker coverage (what a rule, a clause, a pass really reads)
| Tool | Measures |
|---|---|
| `mutiere-pruefer.py` | **mutation run on the checker itself**: damage one rule, see whether any probe falls (survived = the rule is unguarded; caught; invalid = does not build and does not count). `--anker` counts anchors without a build (measured today: **388 of 422** anchors bite, 34 measure nothing, because the checker moved under them — a dead anchor is W1's case); `--schnell` runs only the speech test. Needs `crates/` clean; writes into sources and restores them byte for byte |
| `pruefe-luecken.py` | the named gaps of the generator run, one by one (re-builds thirteen times: heavy) |
| `pruefe-klauseln.py` | clauses declared, carried, never read (ZUSAGE versus ABSENKUNG; homonym table); `ZUSAGE 0` as of 2026-09-12 |
| `pruefe-konstrukte.py`, `pruefe-abstieg.py` | a construct without a poison probe (W13); does every pass descend into every statement kind with a sub-block (W15, W16) |
| `pruefe-reichweite.py`, `pruefe-aufloesung.py`, `zaehle-karten.py` | a body no pass *reads*; a qualified map queried with a bare name; two looks at one map of which only one was module-aware |
| `pruefe-schablonen.py` | tooth 3: every proved template binds its premises to a pass (a ratchet, not a target) |
| `pruefe-sondendeckung.py`, `pruefe-unfalsifizierbar.py`, `pruefe-sonden.sh` | `A_p` (falsifiable hardware assumptions whose probe stands as a program, floor 1/8); the `unfalsifiable` category latched twice; the probe runner (§4.3) |
| `pruefe-umwandlungen.py` | the checker does in Rust what `M104` forbids in its object language: casts with `as` |
| `zaehle-gifttreffer.py`, `zaehle-absagen.py`, `zaehle-verdrahtung.py`, `zaehle-fremdverengung.py`, `zaehle-traversierungen.py` | every poison probe against its own promise (does the expected code fall *alone*); the forms of generator refusal; two parts correct and unconnected; how often a foreign body's promise decides; duplicated traversal bodies (the number before the generic-bodies decision) |
| `vergleiche-binaerprogramme.py` | two `gabbro` binaries over the whole corpus byte for byte — the counter-direction for a change that is meant to be additive |

### 3.4 Fragments, obligations and corpus counters
| Tool | Measures |
|---|---|
| `zaehle-fragmente.py [--je-datei]` | the completed fragment corpus: clean / lowers / pierced (§4.2) |
| `zaehle-pflichten.py [--haengend\|--spalten\|--gabbrov\|--zeilen]` | candidate lines of the obligation search path; the K/L columns derived from the rows; what hangs per fragment; GabbroV's population |
| `zaehle-bereichspflichten.py` | the `narrow` count over Gabbro source without a classifier: remove every `narrow`, run the checker, count `M101`/`M104` sites; `N_folgenlos` |
| `zaehle-b3.py`, `zaehle-narrow.py` | foreign-corpus counters (B3 traversability; `narrow` over Rust). `zaehle-narrow.py` is **not a measuring instrument** (its classifier failed the protocol's hand sample) |
| `zaehle-formate.py`, `zaehle-netz.py`, `zaehle-zeremonie.py`, `zaehle-theorien.py`, `zaehle-fallen.sh` | format versions (0 formats with a second version); the network stack against published vectors; ceremony of the corpus (goal 3's first figure); proof prose versus proof steps; the trap inventory |
| `zaehle-c.py`, `zaehle-c-formen.py`, `zaehle-kette.py`, `zaehle-p6.py` | handwritten C per target; the C forms really emitted; the validation-chain count; how many obligations a prover can read |

### 3.5 Back ends and run-time evidence
| Tool | Measures |
|---|---|
| `pruefe-emission.sh` | the differential test — the *yes* statements: emit, compile under `-Wall -Wextra -Werror` at `-O0`/`-O2`, **run**, compare with a hand-written expectation, plus a poison edit per run. 22+ stages, among them UBSan/ASan, the five `lauf "fragmentN"` runs, freestanding link (stage 12), bare-metal QEMU (11), the concurrent twin (22b), atomic accesses (22c). **Legacy check since 2026-10-17: not a push gate**; run it when `emit.rs` or the C runtime changes |
| `pruefe-cformen.py`, `pruefe-ctext.py`, `pruefe-genlean.py` | no emitted C form without its semantics (three states: lemma / assumption / uncovered); the pinned C text is what the emitter writes; a committed generated Lean file is what the generator writes |
| `pruefe-freistehend.sh`, `pruefe-metall.sh`, `pruefe-kernelmodul.sh`, `pruefe-os-bindung.sh`, `pruefe-seiten-zurueck.sh`, `pruefe-nebenlaeufig-zwilling.sh`, `pruefe-atomar-zugriffe.py`, `pruefe-osfrei.py`, `pruefe-uebersetzerfamilie.py`, `miss-arena-decke.sh`, `vergifte-leeren.py` | every emitting unit linked without an OS; threads on bare metal (QEMU); a unit as a Linux kernel module (QEMU); what the runtime takes from the OS as a number that has to reach zero; reset gives pages back; a concurrent driver against a handwritten twin; every atomic access through a C11 atomic operation; no OS memory call outside the runtime; two translators of one family are one translator; the ceiling costs nothing; the poison twin of a runtime helper |
| `baue-llvm.sh` | pure Gabbro through the LLVM pipeline (checker → LLVM IR text → `llc` → `ld.lld`), no `clang`, no `cc`, no libc; the current back end |
| `pruefe-llvm-modelldeckung.py`, `erzeuge-abi-tabelle.py` | the LLVM coverage register against the Lean constructors; the ABI table generated from the Lean records (one source) |
| `sonde-fma.c` | the FMA probe: no fused multiply-add hides in the generated arithmetic |

### 3.6 Lean and Isabelle
| Tool | Measures |
|---|---|
| `pruefe-beweise.sh` **A (--voll)** | the Isabelle guardian, with a watchdog (a proof step that searches without a bound is a loop without `bounded`; paid twice); needs `~/Isabelle2025-2` or it reports `OHNE NACHWEIS` — no finding |
| `pruefe-lean-beweis.sh`, `pruefe-lean-pflichten.sh`, `pruefe-lean-programm.sh`, `pruefe-p6-beweis.sh`, `pruefe-vorlagen.sh`, `pruefe-beweis-tor.sh`, `pruefe-sperre-beweis.sh`, `pruefe-sicherheit.sh` | rule A for the body channel / the duty channel / the program export / the generated refinement obligation; every owed unit's template compiles to goals; the gates of `gabbro prove` each with its poison probe; the lock invariant in the duty channel; the safety theorem's three files |
| `pruefe-akzeptiert-diff.py`, `pruefe-deckung.py`, `pruefe-gestalt.py`, `pruefe-kein-sorry.py`, `pruefe-lean-layout.py` | the Rust checker computes the whole Lean checker Bool of the goal theorem (differential test); the coverage theorem talks about *this* language; sentences against definitions per file; no `sorry`/`admit`/`native_decide`/`sorryAx`/`unsafe`/unrecorded `axiom` (allowlist `kein-sorry-allowlist.txt`); at most 20 entries per Lean folder (`lean-layout.py --check`, `--apply`; rules in `lean-layout-rules.py`, map in `lean-layout-map.json`) |
| `zaehle-theorien.py` | Isabelle theories: lines, sentences, frozen proof searches |
| `arm-bau`, `arm-probe` | queued build / check of the separate Lake project `arm/` |

### 3.7 What the instruments do **not** do
Counters (`zaehle-*`) measure, they do not guard; a counter that is red over an empty tree is
what `abnahme.py` reports as ABBRUCH, never as a finding. A static reading (`pruefe-waechter.py`
without `--lauf`) says a `timeout` stands in the text, not that it stands in the right place.
A covered site cuts a run just as much as an uncovered one; what is measured is whether the cut
is announced.

---

## 4. Probe corpora

### 4.1 `messung/proben/` — the smallest programs that decide a question
*The W24 pre-run as a directory.* Before a refusal of the generator is decided, the smallest
program that contains the form is written and run through the **unchanged** checker and
generator. *A comment that says "the checker already catches that" is not a measurement.* They
live here and not in `messung/fragmente/`: there stand the ten frozen excerpts, a corpus with its
own count. A probe is not a fragment — an argument in program form — and not an example
(`beispiele/` shows what the language can do, a probe what it *does* at one place; several are
programs the generator refuses on purpose). Some of the answers, measured when the probe was
written (several have since been repaired; the file stays so the measurement can be re-run):

| Probe | Question → answer |
|---|---|
| `probe-elems.gab` | type of the loop variable of `elems of` → the generator lowered it as `uint32_t`, a narrowing that failed `-Werror=type-limits` (cause in the generator) |
| `probe-vergleich.gab` | does the checker say anything on a comparison its own range makes constant → **no**: 0 errors at 100 % type coverage |
| `probe-unbekannter-ruf.gab`, `probe-vier-zellen.gab` | does the checker accept a call nobody declared → without a cost promise yes (only `E009`, a hint); with one `K003` falls. `state`, `queue`, `chain in`, `threads`: 0 errors, four `C001` — same root: `K003` hangs on a promise that a `divergent fn` does not make |
| `probe-f32-literal.gab` | width of a float literal in the generated C → **`double`**: `x * 0.1` computes in double on `x : f32` (39 974 of 200 000 values differ) |
| `probe-erzeugernamen-frei.gab` | does `N042` refuse six words that *look like* a generator suffix → **no**, `cc` accepts: a word list would have refused all six |
| `probe-probenurteil-typ.gab`, `probe-rueckgabetyp.gab` | does anyone see the *type* of what a probe returns → no (`return 7;` in a `can_fail`: 0 errors, `cc -Werror` accepts); it is a gap in `M1` (`passt` compares ranges, and `Typ::Wahrheit` has none) |
| `probe-probenurteil-schleife.gab` | `N045` on a probe whose only exit stands in a `forever` → it fires, **wrongly** (`for (;;)` has no end; `endet_immer` read every loop as falling through) |
| `probe-traverse-grundname.gab`, `probe-elems-feldname.gab` | `traverse` over a `let`-bound name: 0 of 41, and `D017` switched on over 476 files gives 0 new refusals; the field name in the suffix of `elems of` is read by nobody → became `D019` (`gift/431`) |
| `probe-transport-*.gab`, `probe-ecam-faehigkeitenlauf.gab`, `probe-region-schnitt-und-nullen.gab`, `probe-netz-rahmen-und-ergebnis.gab` | transport (`poll_used`, kick address computed at run time, feature negotiation, queue setup, reset), PCI capability walk, region carve, a whole ARP frame: **unwritten**, not unwritable — checked, lowered, `cc` accepts; the overflow gets a *name* in Gabbro instead of a `None`; `want as u32` falls at `M101` where Rust truncates silently |
| `probe-opak-am-feld.gab` | does `N030` fire when the wrong `opaque` value comes from a *field* → **no** (one error at four wrong places); became `O7` |
| `probe-tagged-wird-gebaut.gab` | can a `tagged type` value be *built* → until 2026-09-14 no, in none of four spellings (nine `tagged type`s in the corpus, all only taken apart; «B9» a third time); since lane 167 yes (`Case(payload)`, `Case()`, bare `Case`; `beispiele/120`, `121`, `N280`–`N284`) |
| `probe-marke-an-retry-und-traverse.gab`, `probe-fehlerkanal-verbundwert.gab` | `next` at a `retry` mark: `0 errors` at the checker, `C001` at the generator (found by the *corpus hiding it*: all `leave`/`next` of `beispiele/41` name `forever` marks) → `D21`; `let x = f() else (e)` with a record: `0 errors`, `cc` says *invalid type argument of '->'* (found by *reading the body*, not by a pattern) → `D22` |
| `probe-besitz-zwei-typen.gab` | does the ownership hand-over carry Caprock's *exclusion* or only its shape → both writable, `beispiele/66` chose the weaker form; two `linear type`s with the write path only on the driver side give it back (`gift/671`–`673`, `O10`) |

`messung/fnptr-proben/p1.gab … p8.gab`, `h1.gab`, `h2.gab` are the hand probes behind the
function-pointer decision («B8»): the four halves one by one (generator, call over a place,
lowering, contract), `p8` the unbooked find (`fn(…)` lay on `Typ::Unbekannt` and was compatible
with everything: `let x : u32`, `: bool` and `: ptr<…> Treiber` from the **same** `t->bereit`,
zero type errors), `h1`/`h2` the same shape written correctly. They are not poison probes (no
`-- erwartet:` line, no guardian runs them, the mutation run does not know them); `zeugnis_stmt2`
reads `p5.gab`. *Evidence for a report, not part of the coverage.*

### 4.2 `messung/fragmente/` — the completed fragment corpus
`F01.gab` … `F10.gab` are the ten fragments of `FRAGMENTE.md` made into programs: byte-identical
to the frozen excerpts, plus exactly the declarations the excerpt calls and does not name (head of
each file lists what was added and what was not; nothing rewritten, nothing left out, no refusal
defined away; where an error stands after completion it belongs to Gabbro). The state is read by
`./instrumente/zaehle-fragmente.py`; the quoted run below is **evidence in the tool's own
language** — it moves when the tool's output moves, and the number guardian reads two of its lines
(`N von 10 prüfen sauber`, `N von 10 senken ab`):

```
$ ./instrumente/zaehle-fragmente.py
9 von 10 prüfen sauber        (über den Ausschnitten: 5)
9 von 10 senken ab            (über den Ausschnitten: 3)
9 von 10 sind DURCHGESTOCHEN  — F01, F02, F04, F05, F06, F07, F08, F09, F10
```

(The three figures were re-read against the per-file `gabbro pruefe` runs of 2026-10-17; the tool
itself was not run, since it needs the debug binary in its own tree.) The history of the figure
is in `FRAGMENTE.md` §3 and in `HISTORIE.md`.

### 4.3 `instrumente/sonden/` — where a `falsifier` can become a program
*Created 2026-08-21; before it there was no such place, and that was the finding:* of 27
assumptions naming a probe (26 distinct names) **zero** existed as a program — a `falsifier` whose
probe exists nowhere asserts the *absence of a refutation* (R15, W10). A probe does not belong in
the tree of checked programs (`namen.rs`: *"`expects` names an EXTERNAL probe, like `assume …
falsifier`: it does not stand in Gabbro because it RUNS"*) — it belongs beside it. Runner:
`./instrumente/pruefe-sonden.sh [--runden N]`. **The contract**, return value `0` = not refuted
in this run **and that is all it means** · `1` = **refuted**, or the probe proved itself blind ·
`77` = cannot run here (no device, no right, one core): the third state the grammar lacks
syntactically (*falsified / not falsifiable with a reason / not run*) exists as an exit class.
Each probe prints `sonde <name> :: <assumption>` on its first line (a human reads the mapping;
the runner does not check that the probe hits the assumption in its name) and its **work quantity**,
and carries its own **sensitivity probe**:

> A probe that finds nothing has two possible reasons: there was nothing, or it cannot see. Whoever
> does not separate them has no measurement but a reassurance.

`sonde_release_sichtbarkeit` separates them with a **positive control**, a third arm in which the
writer sets the flag deliberately *before* the payload; that arm **must** fall. Measured
2026-08-21 (20 cores): 204 693 observations, **3 079** violations of the control arm over 1.5 M
rounds, 0 for the release arm (expected: x86 is near sequential consistency for this shape).
*Falsifiability has a direction:* the booking *"not falsifiable: running cannot refute the memory
model"* argues the **green** direction; falsifiability is the red one — a single observation of a
visible flag over a stale payload kills the assumption for good, with the witness printed. **What
must not stand here:** a probe whose green run reads as confirmation; an **analogy** (masking
POSIX signals instead of interrupts measures POSIX); a probe that runs the checker (that is what
the poison probes and the mutation run measure — a probe measures the *environment*). Of the 26
names the first booking estimated: ring 0: 9 · a device: 9 · a mechanism the generator does not
generate: 4 · userland: 4 (`sonde_mxcsr_rne`, `sonde_keine_ueberbreite`, `sonde_tsc`,
`sonde_rdtscp`, all four built 2026-09-04). *The class "runs in userland" is empty;* the estimate
per name is a judgement, not a measurement. The directory today holds the `.c` probes listed by
`ls instrumente/sonden/`.

### 4.4 Emission evidence and witness pairs
| Directory | What it pins |
|---|---|
| `messung/proben/emission-141/` | direct byte operations with the run bound: `PUFFER[3]` stays plain for a constant index; a dynamic read carries `(i < 16u ? PUFFER[i] : (__builtin_trap(), 0))`; a dynamic write binds the index once and traps past the bound. Over all 647 `.gab` files under `beispiele/` and `messung/proben/` old versus new `gabbro emit`: zero exit-code diffs and exactly one C diff (`beispiele/32-zeichenkette.gab`) — the byte-identity method for an additive emitter change |
| `messung/proben/emission-143/` | seven C forms that were open in `grammatik/Grammatik/Erhaltung.lean`'s table, one minimal unit each, all **admit** (neither lowered nor refused): `static inline` helpers, `const D *restrict` readers, volatile-cast dereference, error-channel call `gib_opt(&v, &e)`, width-bound complement `(u16)~(u16)(x)`, bounded retry counter, `sizeof(q->slots)/sizeof(q->slots[0])`; each emission compiled under `-std=c11 -O0/-O2 -Wall -Wextra -Werror` (14 of 14); the rulings are `messung/CFORM-REGEL-*.md` |
| `messung/proben/emission-155-c1/` | witness pairs for `typedef`, `#define`, `enum` (6 units, 12 of 12 compile); `zeigerArithmetik` (491 sites) stays open — a refusal that fired on `u32` arithmetic because `wert_ctyp` resolves through scope-blind maps was withdrawn the same day (*a refusal that fires on integers is not strict, it is loaded*); `cInclude` (408 sites) stays open — the four-line preamble is load-bearing line by line |
| `messung/proben/zeugnis-c2/` | five witness pairs, one named C form each (`zuweisung`, `wenn`, `ruf`, `rueckgabe`, `literal`; probes `c2-01-zuweisung.gab` … `c2-05-literal.gab`); `pruefe` reports 0 errors and `emit` writes the named fragment (`= 41`, `else`, `gib()`, `return`, `8`). **`EXPECTED.md` in that directory is read by the test `c2_witness_pairs_run_clean_and_emit_their_form` and stays a file of its own**; the Lean side recomputes the form half (`zeugenPaarGueltig`), the test the execution half; a green pair links the probe to the tabled form, it does not prove what the C fragment means |

### 4.5 `messung/netz/` — the network stack against published vectors
`./instrumente/zaehle-netz.py [--zeige-c]` runs the stack (`udp-echo.gab`) over the classic IPv4
header (RFC 791, checksum `b861`), the same header *with* its checksum (the sum must be 0 — the
property the whole receive path rests on, and the only one of the three a wrong folding does not
survive) and the RFC 1071 §3 example (`ddf2`), each against a second implementation written
differently (every step folds in Python; only the end folds, twice, in Gabbro). Rule A: no new
construct without a program that needed it; **rule B: and the template comes from outside**,
otherwise a stack measures how well Gabbro fits Gabbro. The quoted run is evidence; the number
guardian reads its last line (`N von 3 Proben grün`):

```
$ ./instrumente/zaehle-netz.py
ok   ohne   Gabbro b861  Gegenrechnung b861   IPv4-Kopf, Feld genullt (RFC 791)
ok   mit    Gabbro 0000  Gegenrechnung 0000   derselbe Kopf MIT der Summe — muss 0 sein
ok   summe  Gabbro ddf2  Gegenrechnung ddf2   RFC 1071, Abschnitt 3: die Summe
3 von 3 Proben grün
```

What the stack found is in `FRAGMENTE.md` (*The network stack*).

---

## 5. The language switch to English — the order is the whole rule

*Decided 2026-09-01 (the repository points at a public tree); costed on 2026-08-31 before the
decision.* What was already English at the time: the checker's diagnostics (33 → 0 German
message lines), `gabbro help` and every subcommand help, `README.md`; what is English today: the
documents, the commit messages, the diagnostics. The costing, kept because it explains the
rule:

* **98 `.md` files, 40 879 non-empty lines, 49 % German** (`messung/` 9 488 of 14 297,
  `dokumente/` 7 210 of 20 768, root 3 207 of 5 045); *German* meaning a line with at least one
  word of a closed function-word list — a lower bound for the effort and an upper bound for the
  line count (W25: the denominator is stated).
* **Sub-command names** were the other cost. Of 17, 4 were English (`emit`, `abi`, `lean`,
  `alias`), 13 German. The additive way — one more pattern per name in the flat `match` of
  `main.rs` — breaks none of the 608 call sites (225 in code, 383 in documents); it is what was
  done: today the table `COMMAND_NAMES` lists English first, German second (`check`/`pruefe`,
  `fragments`/`fragmente`, `obligations`/`pflichten`, `costs`/`kosten`, `ceremony`/`zeremonie`,
  `certificate`/`zeugnis`, `blindspots`/`blindstellen`, …), with `erstnamen.rs::PAARE` and
  `fahnen.rs::UNTERBEFEHLE` as drift guards. Two hooks that belong to the decision: the name
  handed to `split_with`/`read_preamble` for a message must be the name the user *typed* (a
  message naming another command than the one typed is W16), and `alias` (alias analysis of
  pointers) collides with the word "alias" for a command's second name.
* **The number that is the real one: 7.** *21 of 54 instruments* read a `.md` **and** carry a
  German literal in a detection position. Three classes, confirmed on the text: **(a)** whoever
  parses a German *label* out of a document goes **silently blind** when the heading is
  translated (`pruefe-todo.py`, `pruefe-zahlen.py`, `pruefe-grammatiktafel.py`,
  `pruefe-widerruf.py` — four) — *proven here once already*: a mere rewording (not even a
  translation) of the rule-count wording in `TODO.md` made a `pruefe-todo.py` pattern hit nothing
  for weeks; **(b)** whoever reads the German *output* of other guardians goes red *en masse*
  (visibly: `pruefe-waechter.py`, `abnahme.py`, `abschnitt.py`) — their abort-word list is already
  half bilingual; **(c)** the proof that (a) is no thought experiment, as described above.
* **The rule.** Patterns become bilingual *before* the document moves: first the pattern in both
  languages, then the document, then — much later — the German alternative is removed. Whoever
  reverses it gets a green guardian that measures nothing. Example already in the tree: `(\d+)
  (?:EBNF-Regeln|Regeln, 0 offen|rules, 0 open)`.
* **Watcher stage 0 (2026-09-12) did exactly that**, with these standing results: `pruefe-todo.py`'s
  speech test no longer grades invented lists against the live `DONE.md` (it aborted over its own
  subject); `pruefe-klauseln.py` books the homonym `version` (an AST clause `Format.version` versus
  the ledger field `Ledger.version` in `kostenledger.rs`: *different struct, same field name* — the
  `kosten` trap one field over); `pruefe-englisch.py` prints every sink hit and feeder hit
  **before** the ratchet verdicts, so a broken ratchet cannot hide its own evidence; 36 of the 37
  German-only labels of `pruefe-zahlen.py` carry an English alternative (exactly one capturing
  group each, checked mechanically over all 91 entries). Already bilingual and verified:
  `pruefe-widerruf.py`, `pruefe-todo.py`, `pruefe-wortschatz.py`, `pruefe-sondendeckung.py`
  (structural identifiers), `pruefe-grammatiktafel.py`, `pruefe-klauseln.py`/`-deckung.py`/
  `-gestalt.py`. The cell moves it proposed were all applied or superseded by now; nothing in this
  section depends on them.
* **Quoted runs stay in the tool's language.** A translated transcript is no longer a transcript,
  and the number guardian reads some of them (§4.2, §4.5): they change when the *tool's* output
  changes, not when the document does.

---

## 6. When something red looks like a finding

* **Look first for the numbers the guardian no longer prints.** A guardian that *aborts* reads
  like one that passed; one whose abort drops six figures the number guardian reads produces six
  findings in the wrong register (2026-09-08: a new probe named a `falsifier` for which no
  program exists, the counter `aussen` rose 13 → 14, `pruefe-sondendeckung.py` aborted at its own
  speech test). Measure the base in a throw-away worktree at the state before the merge.
* **A guardian that cuts at the first hit answers *is there at least one*, not *which fire*.**
  Eleven wildcard branches were replaced by `panic!`; six "fired", five "were silent" — wrong: the
  first hit ends the process and hides every later one (`emit.rs:3488` was reported silent and
  fires 148×); with `eprintln!` seven fire. This applies to `--fail-fast`, `set -e` in measurement
  scripts, `panic!` instrumentation and every checker run that stops at the first error. `cargo
  test` needs `--no-fail-fast`; `abnahme.py` says *what stands behind an ABBRUCH was not measured,
  neither yes nor no*.
* **Never wait with `pgrep -f`.** The whole invocation stands in the command line of the waiting
  shell, so the pattern finds itself — the loop reports "still running" forever and leaves an
  orphan. Ask `ps -C python3`, or write the output to a file and read its last line.
* **Two tools in one tree measure a mixture** (`cargo test` and the Lean corpus run together:
  phantom Lean errors; a `rsync` into a directory where a mutation run works: two green suites
  turned red). One heavy run at a time, one directory per agent.
