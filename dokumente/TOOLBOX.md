# Toolbox — the four guardians, the tools, and the working rules

**What this is.** What measures the project (four guardians), the helper parts and tools beside
them, the probe corpora, and the working rules **W1–W29** the old instrument folder earned.
*On 2026-10-17 the folder of 95 entries (54 `pruefe-*` guardians, 22 `zaehle-*` counters, a mutation
run, `abnahme.py`, helpers) was cut to four guardians (Simon's decision: exactly four).* Everything
else stays in Git: `git show 414feafc:instrumente/<name>`.

**Admission condition for a rule:** it comes from a *mistake in this folder* and the mistake is named.
The rule ids are cited from source comments and other documents and are never renumbered.

## 1. The four guardians

| Guardian | Subject | Stages |
|---|---|---|
| `instrumente/pruefe-lean.py` | the Lean model (`grammatik/`) and stage 0 (`stage0/`) | `lake build` of both · `gabbro_ziel` and its siblings depend on exactly `propext`, `Classical.choice`, `Quot.sound` (`NachpruefungZiel.lean`) · no `sorry`/`admit`/`native_decide`/`sorryAx`/`unsafe`, no `axiom` outside `teile/kein-sorry-allowlist.txt` · at most 20 entries per folder · the stage-0 probes `stage0/proben/` print what they must |
| `instrumente/pruefe-llvm.py` | the LLVM compiler | `cargo test --test llvm` (IR, refusals `Y101`–`Y106`, model-coverage register, noalias, the Lean certificate elaborating with plain `lean`) · four programs through `teile/baue-llvm.sh` (`opt -O3`, `llc`, `ld.lld`, static, no INTERP/NEEDED) on x86_64 and aarch64 (qemu) with the same, expected exit code |
| `instrumente/pruefe-pruefer.py` | the checker (Rust) | `cargo test --workspace --no-fail-fast` (poison probes, examples, tutorial, grammar and word tables, doc code blocks, certificates) · sentence register `teile/saetze.py` (60 codes without a sentence is the booked ratchet; a sentence for a rule that does not exist is always red) · every code issued from one place (`teile/kennungen.py`) |
| `instrumente/pruefe-gabbrov.py` | GabbroV (`programmlogik/`) | `lake build` without `sorryAx` · the person's proofs and the GabbroV files carry no `sorry`/`axiom` · `gabbro prove` GREEN on the four proof units · `cargo test -p gabbro-cli --test beweismessung` (no GREEN unless Lean checked something) |

```bash
./instrumente/abnahme.py                 # all four, one after the other
./instrumente/abnahme.py --lean          # or --llvm, --pruefer, --gabbrov
```

**Exit codes, the same in all four:** `0` measured and green · `1` measured and something is open ·
`2` **nothing, or not everything, was measured** (a missing tool, a stage that could not run). `2` is
never green, and what stands behind it was not measured. Each guardian prints its work quantity beside
the verdict (W17) and runs with a pinned locale.

**A fifth guardian is not built.** What is to be checked next becomes a test in `cargo test`, a Lean
theorem, or a stage in one of the four. The old counters (mark ratchets, document-figure guards,
the mutation run, the C-emitter stages) are retired (the C emitter itself was removed on 2026-10-17, tag `archiv/c-emitter-2026-10-17`); their figures in other documents are dated
results, not guarded values.

**Heavy runs — one at a time, with `free -g` beside them:** `cargo build`, `cargo test --no-fail-fast`,
`lake build`, the acceptance run. Never two in one tree (`cargo test` rebuilds the model with `lake` and
replaces the `.olean` files running `lean` processes read). An agent gets its own working directory.

### Known open items of the guardians
* `bruecke/` is not measured: its `lake build` fails on a missing `mathlib` manifest entry.
* `pruefe-gabbrov.py` covers four proof units; the tree-wide duty run (`gabbro prove` over every unit)
  and the obligation-manifest completeness comparison (E1) are not wired in.
* The mutation run over the checker (388 anchors, 34 measured nothing at the last run) is retired and
  not replaced.
* The German comment ratchet (8 600 of 48 500 checker comment lines are German) is not guarded.

## 2. The working rules

*The rule texts below name instruments that were retired on 2026-10-17 (the counters, the document-figure guards, the mutation run). The lesson stands; the instrument is in Git.*

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
measurements (`MEASUREMENTS.md`), not quoted: **R1** the protocol is committed before the first
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

## 3. Helper parts, tools and probe corpora

**Parts** (`instrumente/teile/`, called by the guardians, not run on their own): `saetze.py` (sentence
register) · `kennungen.py` (issued-code uniqueness, source trust: no bidi or invisible characters) ·
`lean-layout.py` + `lean-layout-rules.py` + `lean-layout-map.json` (the 20-entry layout rule; `--apply`
moves new modules into place and rewrites imports) · `llvm-modelldeckung.py` (the register of Lean
constructors/fields the LLVM lowering must cover, with `dokumente/llvm-modelldeckung.tsv`) · `baue-llvm.sh`
(end-to-end LLVM build and run) · `korpus.py` (the example corpus reader) · `kein-sorry-allowlist.txt`.

**Tools** (`instrumente/`): `erzeuge-abi-tabelle.py` (ABI table, used by a test) · `arm-bau`, `arm-probe`
(queued builds of `arm/`) · `silicon-harness/` (x86 differential harness, work stopped 2026-10-07) ·
`sonden/` (C programs that decide a named hardware assumption; a `falsifier` clause names one).

**Corpora:** `beispiele/` (clean examples: each must check clean) · `beispiele/gift/` (poison probes:
each must fall with exactly its booked code) · `messung/proben/` (the smallest programs that decide a
question) · `messung/fragmente/` (the ten completed fragments of `dokumente/FRAGMENTS.md`) ·
`messung/netz/` (the network stack against published vectors) · `messung/llvm/` (LLVM end-to-end programs).

## 4. The language switch to English — the order is the whole rule

Working language is English (everything except the conversation). When a document changes language,
every pattern that reads it becomes bilingual FIRST and the document moves second; the other order
leaves a stretch in which a check reports green and measures nothing. With four guardians and no
document-figure readers this risk is small today, but the rule stands for any new reader of a document.

## 5. When something red looks like a finding

Before calling red a finding, ask who has to change: the tree or the set-up. Typical set-up causes:
a binary older than its sources (`cargo build`, never `touch`), a stale `programmlogik/.lake` (an
`incompatible header` says something about the olean, not the program), a missing tool (exit `2`), an
agent tree not on `master`, two runs in one tree. A guardian that aborts reads like one that passed:
look for what it no longer printed.
