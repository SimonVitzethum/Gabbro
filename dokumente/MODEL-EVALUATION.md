# MODEL-EVALUATION — how well each model proves, errs and reviews

*Kept by the lead since 2026-11-12 (owner: "halte für jedes Modell fest, wie gut es ist im Beweisen und wie oft es
Fehler macht … auch Review-Leistung bewerten"). One row per finished task. The record decides which model gets
which kind of task next (AGENTS.md "Team"). Numbers are counts from the lead's check, not impressions; a judgment
is marked as one.*

## 1. How a task is scored

Agents never build. The lead merges a whole wave and builds once; what is counted is what that build and the
lead's reading find.

**Implementation and proof tasks**

| Column | Meaning |
|---|---|
| lines | lines added or changed in the delivered commit(s) |
| build errors | Lean errors of the delivered work in the first build of its wave |
| repair | what it took to make it build: `0` nothing, `L` the lead repaired it (lines changed by the lead), `R` returned to the agent (rounds), `X` dropped |
| rule breaks | each counted once: `sorry`/`admit`/`axiom`/`native_decide`, a build run by the agent, a file of 500 lines or more, a non-module file, a guessed lemma name, a missing witness, German in the tree, changes outside the task |
| statement | the reviewer's and the lead's verdict on the delivered STATEMENTS: `ok`, `weak` (true but says less than its name), `vacuous`, `wrong` |
| done | share of the task that was delivered: full, part (what is missing), none |

**Review tasks** (statements only; proofs are valid once they build without `sorry` on the standard axioms)

| Column | Meaning |
|---|---|
| read | theorems and definitions the review covered |
| findings | findings reported |
| confirmed | findings the lead confirmed by reading or by a check |
| false | findings that were wrong |
| missed | defects the lead knew or found later in the reviewed material and the review did not report |

**Derived per model**, recomputed when a row is added: build errors per 100 lines; share of tasks that built
without repair; rule breaks per task; for reviews precision (confirmed / findings) and recall
(confirmed / (confirmed + missed)).

## 2. Models and limits

| Model | Access | At most at once |
|---|---|---|
| Claude Fable 5.2 | `claude-fable-5-2` | one agent of the three Claude models in all |
| Claude Opus 5.5 | `claude-opus-5-5` | (same slot) |
| Claude Sonnet 5.5 | `claude-sonnet-5-5` | (same slot) |
| GPT 6.1 Sol | codex `gpt-6.1-sol`, `reasoningEffort: high` | three |
| Muse Spark 1.3 Contributor | `opencode-go/muse-spark-1.3-contributor` | five |

The lead itself is Claude Fable 5.2; its own work is listed for comparison and is not an agent slot.

## 3. Record

### 3.1 Implementation and proof

| Date | Wave | Model | Task | lines | build errors | repair | rule breaks | statement | done |
|---|---|---|---|---|---|---|---|---|---|
| 2026-11-12 | — | Fable 5.2 (lead) | seven Stage-0 forms (`d9019873f`, `0675bb884`) | 489 | 9 over 8 compiler builds | L | 1 (a mechanical edit corrupted a file, reverted) | ok; one statement withdrawn (zero record in `konstWert`, against a recorded guarantee) | full |
| 2026-11-12 | — | Fable 5.2 (lead) | lock stage 1, written unbuilt in the writing tree (`fb136900f`) | 119 | 4 over 4 stage0 builds (one `omega` bound, three overlooked construction sites) | L (9 lines) | 0 | not yet reviewed | full |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M2 ticket lock code and uncontended runs | 0 | — | X (restarted as W1-M2b with an explicit "finish before you stop") | 1 (ended its turn after reading, without a file, a commit or a report) | — | none |
| 2026-11-12 | 1 | GPT 6.1 Sol | W1-G1 documentation pass over five documents against the plan's review table (no Lean) | 588 (285 added, 303 removed) | — (no Lean) | 0 (merged as delivered, `af297f700`) | 0 | — ; read by the lead: the AGENTS.md edits say exactly O12–O14 and leave "Team" and "Builds" untouched; it reported three contradictions the task had not listed, one of them in the plan itself (row D4), confirmed and fixed | full |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M1r repair of `Pruefer.lean` from six listed build errors | 0 | — | X (given to Opus 5.5 as W1-M1r2) | 1 (ended its turn after one remark, without a change, a commit or a report; the second such run of five Muse implementation runs) | — | none |
| 2026-11-12 | 1 | GPT 6.1 Sol | W1-G3 split of four elaboration files near 500 lines into eight modules (pure moves) | 1 580 moved | 0 | 0 | 0; it asked one question (two target folders were full), a fault of the brief | — | full |
| 2026-11-12 | 1 | GPT 6.1 Sol | W1-G2 `spec fn` with parameters whose arguments are type-checked (`uSpecArgs`), gate rule, two probes, four witnesses | 300 in 17 files | 3 kinds: a structure literal whose later fields were indented less than the first; a `private` fixture named in public theorems; three witnesses proved by `rfl` that only the kernel decides | L (about 25 lines; witnesses moved to a module with `decide +kernel`) | 1 (changes beyond the task: it removed an early inlining path and tightened `foldRange`; both reasoned in its report, and the corpus did not fall) | ok: all four witnesses are true as stated; both probes pass | full |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M2b ticket lock code (`nimmT`, `gibT`), one new step lemma, the two uncontended runs | 230 in 4 new files | 2 kinds: two files did not import the code file; one cast goal `ofInt (↑a + 8) = ofNat (a + 8)` left open | L (6 lines) | 0 | not yet reviewed | full |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M3 soundness of the hold bound: delivered the syntactic level only (every section body's cost fits its bound) and said exactly why the run level is not provable from what exists | 449 in 2 new files | 11 in the first build: a doc comment in front of `mutual`, a guessed type name (`vertrag`), theorem heads mixing named binders and pattern arms | R (one round, W1-M3r, 175 lines changed, then built) + L (the witness lacked the kernel-evaluation imports) | 1 (guessed name) | not yet reviewed; honest about the level reached | part: level (c) of (a)/(b)/(c) |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M4 finite call depth excludes `abstieg` (four files, mutual induction over the semantics) | 869 in 4 new files | 8 in the first build of the first file (a guessed type name, case arms written `=> by`), then 14 of substance there, then 27 in the second file | L for names and syntax, then R twice: W1-M4r (Sol) made the first file build, W1-M4r2 (Opus) the other three | 1 (guessed name) | not yet reviewed; restricted by its premise to programs without indirect calls, as the report said | full after two returned rounds |
| 2026-11-12 | 1 | GPT 6.1 Sol | W1-M4r repair of the four stack depth files from a list of 14 errors in three kinds | 300 changed | first file: 0; second file: 27 (section hypotheses not included, `dsimp` with nothing to reduce, indirect-call arms left open); third and fourth not reached | R (to Opus) | 0 | — | part: one of four files built; its report named no single uncertain place |
| 2026-11-12 | 1 | Opus 5.5 (effort high) | W1-M4r2 repair of the remaining three stack depth files from 27 errors in three kinds | 91 changed in 2 files | 0: built at the first try, witness included | 0 | 0 | — ; it gave each uncertain place a failure chance of 5 to 15 % and a fallback; none failed | full |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M1 `accepts` gives the goal theorem's checker on units without arena, accumulator or check | 219 in 1 new file | 6: wrong projections out of a four-fold conjunction in three small lemmas, an instance mismatch in the main rewrite | R twice: W1-M1r (Muse) ended without work, W1-M1r2 (Opus) built | 0 | not yet reviewed | full after the Opus round |
| 2026-11-12 | 1 | Opus 5.5 (effort high) | W1-M1r2 repair of `Pruefer.lean` from six errors; it also corrected two later steps the build had not reached | 70 changed | 0: built at the first try | 0 | 0 | — ; failure chances of 5 to 10 % stated per place; none failed | full |
| 2026-11-12 | 2 | GPT 6.1 Sol | W2-G1 character literals in the lexer (`'a'` is its byte), 18 kernel witnesses, two probes, a paragraph in SYNTAX.md | 260 in 9 files | 1: a `private` helper used by the exposed scanner | L (1 line) | 0 | ok: all 18 witnesses decided by the kernel; both probes pass | full |
| 2026-11-12 | 2 | GPT 6.1 Sol | W2-G2 wildcard `match` arm as a source rewrite in front of the call hoisting, 16 kernel witnesses, two probes | 430 in 10 files | 3 kinds: `private` helpers (module), `private` fixtures (witnesses), one witness mixing two error types in a `bind` | L (9 lines) | 0; the same `private` mistake as in W1-G2 and W2-G1 | ok: all 16 witnesses decided by the kernel; both probes pass | full |
| 2026-11-12 | 1 | Muse Spark 1.3 | W1-M6 a compiler front end written in Gabbro and run through the built Stage 0 (the agent could run the compiler and the runner, not Lean) | 1 267 Gabbro in 4 files, plus a findings file | — (no Lean); the unit compiles and runs, exit 87 as it reported, confirmed by the lead | 0 | 0 | — ; 13 refusals recorded with the wanted form, the exact refusal text and the workaround; its three mutation checks of the failure exits not re-run by the lead | full |

### 3.2 Review

| Date | Wave | Model | Material | read | findings | confirmed | false | missed |
|---|---|---|---|---|---|---|---|---|
| 2026-11-12 | 1 | Muse Spark 1.3 | research W1-M5: which forms of machine G the `Body` model and the bridge carry (read-only, a table of 146 constructors with file and line) | 146 constructors | 1 main finding (the bridge carries 4 of 34 statement forms; `Stimmig` excludes requires, reasons, invariants, statics) with about 60 line references | 3 of 3 spot-checked references exact (`stmtBody` arms, `Stimmig.ohneGlob`, the four simulation theorems) | 0 found | not yet known; entries marked "inferred" by the agent are unchecked |
| 2026-11-12 | 1 | Opus 5.5 (effort high) | review W1-R1: the statements and definitions of the lead's work of 2026-11-12 (cost, hold and pass bindings, the export gate, the call hoisting, the slot zero value, lock stage 1, the array and record elaboration) | about 150 declarations (about 40 theorems and witnesses) | 14 (4 `wrong`, 1 `weak`, 6 `missing`, 2 notes, 2 marked suspicions; one item counted twice here by severity) | 12 confirmed by the lead reading the code; of these 4 real defects in pushed code, all fixed: a second `costs` clause was never checked, a parameter hiding a constant was valued as the constant, a prototype's cost expression passed the gate unvalued, `S += f()` moved the call in front of the read of `S`; 1 suspicion confirmed and fixed (reason binder not local in an `else` body); 1 suspicion not verified (two modules declaring one constant name; closed conservatively) | 0 | 1 of the 6 defects the lead had noted beforehand (the bound `L.sye < 2^31` inside `InSync`); the review found 4 defects the lead had not known |
| 2026-11-12 | 1 | Sonnet 5.5 (effort high) | review W1-R2: the SAME material and brief as W1-R1, on a tree that still held the defects | about 270 declarations (its count) | 16 (3 `wrong`, 5 `weak`, 4 `missing`, 4 notes; several marked "likely" or "suspicion") | 13 confirmed by the lead reading the code. Of the 5 real defects W1-R1 established it found 4 (`S += f()`, the second `costs` clause, the prototype cost, and the parameter that hides a constant as a suspicion) and missed 1 (the reason binder). It found 3 defects W1-R1 did not: a function-pointer type's other clauses pass the gate unchecked, the unit word of `bounded N <unit>` is never compared with `ops` (both confirmed in the code), and a census function still calls the tagged-field resolver without the record step; and it named the bound inside `InSync`, which W1-R1 missed | 0 found; 3 not verified (payload copy in the static read, an immutable local hiding a static array, duplicate function names) | 1 of the defects known when it ran (the reason binder) |
| 2026-11-12 | 1 | Fable 5.2 (effort high) | review W1-R3: the SAME material and brief, on the same tree state (`d1a1986f0`), told not to read the later commits or this file | about 265 declarations (its count) | 15 (2 `wrong`, 4 `weak`, 6 `missing`, 3 notes) | 13 confirmed by the lead. Of the 8 defects the two earlier reviews had established it found 5 (`S += f()`, the second `costs` clause, the parameter that hides a constant, the prototype cost, the unit word of a bound) and missed 3 (the reason binder, the unchecked clauses of a pointer type, the census function without the record step). New and confirmed in the code: constants are valued in list order, so a constant defined by a LATER one has no value (a refusal only); the hold walker bounds the body without the release step and the pass walker the body without invariant and loop charge | 0 found; 2 not verified (a name that is both a record and a tagged type; a function of the unit missing from the gate's members) | 3 of the 8 defects known when it ran |
| 2026-11-12 | 2 | Muse Spark 1.3 | design W2-M1: narrowing a value by the condition that guards it (read-only, with probes against the built compiler) | the typing of ranges, the elaborator's fit checks, `narrow` and `eng` through syntax, semantics and lowering, with file and line | 1 design in five parts: two variants with estimates, three rewritten examples, four probes; and 1 warning of an unsound case | the central facts confirmed by the lead where checked (`uCond` elaborates both branches in the unchanged context; the bound computation from a condition already exists for `exchange` arms); the recommendation is usable after one correction by the lead (the value form `eng` instead of a `narrow` with a dummy `return`, which would add a return path to the user's duties) | 1: the warning that non-negated `!=` yields equality bounds is a misreading of two adjacent lines; the code is sound there | — |
| 2026-11-12 | 2 | Muse Spark 1.3 | analysis and design W2-M2: why a call that writes another module's table is refused, and what is missing (read-only, eight probes against the built compiler) | modules through parser, name resolution, hull check, effect elaboration, the call's frame rule and the gate, with file and line | 4 refusals reproduced with smallest programs, each classified (a deliberate rule, or a form the elaborator does not bind), 1 unlisted fifth refusal, 2 fixes with estimates | the diagnosis confirmed by the lead's own probe (the caller cannot name the foreign table in its effects; the frame rule itself is right); line references not individually checked | 0 found; it did not try the `::` spelling of the place, which the lead probed (a parse error) | — |

## 4. Standing per model

After wave 1 (2026-11-12). Small numbers: one to four tasks per model; read as first evidence, not as a ranking.

**Reviews of statements** (the same material and brief for all three; 8 real defects established in it in total):

| Model | found of the 8 | findings | confirmed | false | unverified | found that no other review had |
|---|---|---|---|---|---|---|
| Sonnet 5.5 | 7 | 16 | 13 | 0 | 3 | the pointer-type clauses, the unit word, the census function |
| Opus 5.5 | 5 | 14 | 12 | 0 | 1 | the reason binder |
| Fable 5.2 | 5 | 15 | 13 | 0 | 2 | the order of constants; what the hold and pass walkers leave out |

No review reported a false finding. Each review found something the other two missed, so two different models on
the same material found more than one model twice would have (the union is 8 defects; the best single review 7).
All three marked their uncertain items as suspicions. Reviews cost no build.

**Implementation and proof without a build** (wave 1, six builds of the assembled wave in all):

| Model | tasks | built as delivered | built after the lead's repair | returned | ended without work |
|---|---|---|---|---|---|
| GPT 6.1 Sol | 6 (documents, file split, a typed check through 17 files, lexer sugar, a source rewrite, one proof repair) | 2 | 3 (each after a few lines: `private` in an exposed module three times) | 1 (the proof repair: one of four files) | 0 |
| Muse Spark 1.3 | 9 runs (4 proof tasks, 2 repairs, 1 research, 1 program in Gabbro, 2 designs counted with research) | 0 of the proof tasks | 1 (ticket lock) | 3 (all three built in the end: one after a Muse round, two after Opus rounds) | 2 |
| Opus 5.5 | 2 proof repairs from error lists | 2 | 0 | 0 | 0 |

What the builds showed about proofs written blind: none of the four proof tasks built as delivered. The errors were
of three kinds, in falling frequency: names and syntax nobody checked (a guessed type name twice, a missing
import, a doc comment before `mutual`, `=> by` in a tactic arm, theorem heads that are not valid Lean); proof steps
that assume a reduction Lean does not do (`rfl` where the kernel is needed, a `match` left unreduced after `cases`,
a `split` on the wrong `match`); and index mistakes in dependent types. No delivered STATEMENT was found false so
far, and every agent listed honestly where it was unsure. A failing module stops the build at that module, so a
wave of blind proofs needs one build per layer of errors, not one build: the six builds of wave 1 each uncovered
the next layer. Mechanical work (Sol) built at once or after trivial repairs.
Where an agent CAN run a checker the picture turns: the Muse run that wrote 1 267 lines of Gabbro against the
built compiler delivered a working program and a precise list of refusals. The weak point is not the model's
proving but proving without feedback.
Opus repaired two blind proofs (six and 27 reported errors) so that they built at the first try, and its stated
failure chances were honest. On this evidence the cheapest route for a proof is: a first draft by any model, ONE
build by the lead, the error list to Opus. Sol repeats one mistake (`private` definitions in a module whose section
is exposed); briefs for Sol now say so.
