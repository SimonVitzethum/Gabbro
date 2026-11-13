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
| 2026-11-13 | 3 | GPT 6.1 Sol | W3-G1 qualified effect places (`b::T.slots`) in the parser, witnesses, two probes | 205 in 7 files | 0 in its own modules, but it broke the parser round trip `effekt_rund` in a module it had not looked at (2 unsolved goals) | L (rewritten as "ordinary expression first", 30 lines) | 0 | ok; both probes pass | full after the lead's rewrite |
| 2026-11-13 | 3 | GPT 6.1 Sol | W3-S3 named string constants; an indexed array read as the stored value of a slot write | 15 files | 1: a `let` over a `match` of tuples without its type | L (2 lines) | 0 | ok; 3 of 4 probes pass as written, 1 probe text used a call inside an expression that the compiler refuses for another reason | full |
| 2026-11-13 | 3 | GPT 6.1 Sol | W3-S4 five repairs from the statement review (capture refusal, `count` binder, fold ranges, wildcard bodies; the bool argument left open with the reason) | 200 changed in 7 files | 0: all three leaf modules built as delivered | 0 | 0 | ok | full (4 of 5; the fifth correctly not approximated) |
| 2026-11-13 | 3 | GPT 6.1 Sol | W3-S2 `bool` record fields as truth values; equality of tagged values as a match expansion | 467 in 19 files | 1: a lemma stated over a type without the instance (`Wert bool`); and both features broke the read-back theorem (`reihe_cond`, `bindWert_int`), not noticed | L (restated the lemma; both features put under the compiler's switch, 40 lines) | 0; the probe texts used a record literal syntax that does not exist (`T { f: v }`) | ok after the switch; 4 probes pass after the text repair | full after the lead's repair |
| 2026-11-13 | 3 | Sonnet 5.5 (effort high) | W3-C1 narrowing by the guarding condition in the elaborator (the total `eng` form, nothing new in machine G), 9 witnesses, 2 probes | 403 in 9 files | 0 in its own modules (built unchanged under Opus's commit); it said itself that the read-back theorem no longer held and left the decision to the lead | R (to Opus, by design) | 0; its witness module was not registered in `Grammatik.lean` | ok | part: sound design, the proof side handed back |
| 2026-11-13 | 3 | Opus 5.5 (effort high) | W3-O1 the narrowing behind a switch of the elaborator context so that the read-back theorem keeps its text; only locals a block reads are narrowed; 5 witnesses | 249 changed in 20 files, 6 statements changed | 0: all seven leaf modules built at the first try, the read-back and the `cbv` witnesses among them | 0 | 0 | one design fault found by a probe: the continuation's filter could not see the block's ending, so `if i >= 10 { return 3; } return T.slots[i].v;` was not narrowed (lead: 4 lines) | full |
| 2026-11-13 | 3 | Muse Spark 1.3 | W3-M2 lock stage 2b draft: ticket class, sync invariant, pair lemmas | 251 in 4 new files | 2: an existential over an unused variable without a type; `subst` in the wrong direction | L (5 lines) | 0; modules not registered | — ; the hard parts (free at entry, switching `AgreeW`, `locksCode`) left open as told | full for the draft |
| 2026-11-13 | 3 | Fable 5.2 (lead) | own work: a call returned in a branch, a bare case into a slot, the goal checker theorem, the duplicate-function refusal | about 120 | 3: a hash set the kernel cannot evaluate broke 19 compile witnesses; a namespace not opened; one probe with a wrong range | L | 0 | the goal checker theorem inherited a dead hypothesis and an unsatisfiable premise (found by both reviews) | full after repair |
| 2026-11-13 | 4 | GPT 6.1 Sol | W4-S1 the traverse header check accounts for calls through the callees' declared effects; 13 statements moved from a per-item to a per-unit predicate | 14 files | 3 in the witness module only (a structure literal's layout, `decide` without `DecidableEq`, `kernel_rfl` on a conjunction); the 13 changed proofs built as delivered | L (6 lines) | 0 | ok; both probes pass | full |
| 2026-11-13 | 4 | Opus 5.5 (effort high) | W4-O1 the judged `Einheit`: `accepts` judges the compiled entry as a start (stricter), the bridge on an `Einheit` with the real checks, the dead hypothesis used, a joint witness | 387 in 10 files | 3 small list goals (`filterMap` over a projected type; `[] = []` left by `simp only`), and one witness by term `rfl` that made the elaborator unfold the compiler (15 GB, stopped by the lead) | L (12 lines; the witness dropped) | 0 | ok: no existing probe or witness flipped under the stricter check; it listed exactly what stays a premise | full |
| 2026-11-13 | 5 | GPT 6.1 Sol | W5-S1 three refused forms: a one-field record (parser fuel), a call with a string literal in an expression (`ruhig`), a tagged slot field read into a local | 15 files, 9 witnesses, 4 probes | 1: a structure literal's layout in a fixture | L (2 lines) | 0 | ok; all four probes pass as written | full |
| 2026-11-13 | 5 | Opus 5.5 (effort high) | W5-O1 the difference of two locals under a guard (`if a >= b { return a - b; }`), by rewriting the guarded block instead of a fact store, because a store would have made read-back theorems false | 199 new + 2 files changed, 8 `cbv` witnesses | 0: built at the first try, both probes pass | 0 | 0 | ok; it named what is not covered (the enclosing block's ending, u64 differences) | full |
| 2026-11-13 | 6 | GPT 6.1 Sol | W6-S1 census with record tables, function/case name clash refused, option payload binders, the statement's source line in diagnostics | 17 files | 1: one witness with a wrong expected text | L (witness dropped; behaviour checked by running the compiler) | 0 | ok; both probes pass | full |
| 2026-11-13 | 6 | Opus 5.5 (effort high) | W6-O1 lock stage 2, the part that leaves the tree building: ticket analogues of the frame lemmas, the new code layout, and the missing tie between lock words and the held set (`HeldIn`, `HeldIn.frei`) | 3 commits, 5 files | 0: built at the first try | 0 | 0 | — ; it refused to deliver a half-switched tree and said why the switch is one atomic step | part, as agreed |
| 2026-11-13 | 7 | Opus 5.5 (effort high) | W7-O1 "held sets grow along a block" (it found the model already proves it and added only the corollaries) and the lock theorem on the ticket code as a standalone theorem (`locks_okT`, with its own frame relation), 5 new files | about 600 | 1: a missing import (`ls_init`) | L (1 line) | 0 | ok; it found that a pair lemma of the earlier draft was unusable (one memory base for take and body end) and computed the class directly | full |
| 2026-11-13 | 8 | Opus 5.5 (effort high) | W8-O1 the lock switch as ONE commit: the held set threaded through the statement simulation (`Umf`, 66 induction hypotheses, `FunSpec.run`), `lowS` emits the ticket lock, the old path deleted | 114 files (101 changed, 13 deleted) | 0: all of stage0 (5 668 jobs) built at the first try | 0 | 0 | ok; corpus unchanged, two-thread probes 200 runs each without deviation; its own estimate had been a 15–45 % chance of a repair per file group | full |
| 2026-11-13 | 7 | Muse Spark 1.3 | W7-M1 the Gabbro front end rewritten with the new forms, run against the built compiler; FINDINGS updated with counts | 1 267 → 1 194 lines of Gabbro in 4 modules | — (no Lean); exit 87 and the three failure exits confirmed by the lead | 0 | 0 | — ; an honest negative result: 0 of about 115 `narrow` sites converted, because the guards are equalities; five new findings with minimal texts, three of them fixed the same day | full |
| 2026-11-13 | 8 | GPT 6.1 Sol | W8-S1 bridge: statics in the world relation (`GRel`, `encG`, typing) and the static read (`sideExprG`, `lowGlobRead_sim`), beside the existing statements | 323 in 3 new files | 4: a recursion over a mutually inductive type (the `induction` tactic refuses; WF recursion after `cases` loses the equation), a missing `dsimp only` before a heterogeneous step, two bare numerals for `Fin` | L (45 lines) | 0 | ok | full after repair |
| 2026-11-13 | 9 | GPT 6.1 Sol | W9-S1 equality and inequality guards narrow at an end of the range | 2 files, 8 witnesses, 2 probes | 0: built at the first try | 0 | 0 | ok; both probes pass | full |
| 2026-11-13 | 9 | GPT 6.1 Sol | W9-S2 record-field operands and computed slot indices in the call rewrite; string escapes with the lexer's round trip strengthened to every string value (2 statements changed) | 19 files, 20 witnesses, 4 probes | 0: all five checked modules built at the first try, the round-trip proofs among them | 0 | 0 | ok; all four probes pass; it corrected the lead's belief that the call rewrite runs only on the compiler path | full |
| 2026-11-13 | 9 | GPT 6.1 Sol | W9-S3 bridge duties per function: definitions and the assembly of the logic duty; it STOPPED at a missing premise (an open start with a `requires` needs an initial-memory duty) and showed it by a fixture | 2 new files | definitions and lemmas: 0; the witness module: 14 (a `decide` on a Prop without an instance, a `change` that does not unfold, hand proofs by `rfl`) | L (witness removed; rewritten in the follow-up) | 0 | the stop was right: the design had missed the start duty | part, correctly |

### 3.2 Review

| Date | Wave | Model | Material | read | findings | confirmed | false | missed |
|---|---|---|---|---|---|---|---|---|
| 2026-11-12 | 1 | Muse Spark 1.3 | research W1-M5: which forms of machine G the `Body` model and the bridge carry (read-only, a table of 146 constructors with file and line) | 146 constructors | 1 main finding (the bridge carries 4 of 34 statement forms; `Stimmig` excludes requires, reasons, invariants, statics) with about 60 line references | 3 of 3 spot-checked references exact (`stmtBody` arms, `Stimmig.ohneGlob`, the four simulation theorems) | 0 found | not yet known; entries marked "inferred" by the agent are unchecked |
| 2026-11-12 | 1 | Opus 5.5 (effort high) | review W1-R1: the statements and definitions of the lead's work of 2026-11-12 (cost, hold and pass bindings, the export gate, the call hoisting, the slot zero value, lock stage 1, the array and record elaboration) | about 150 declarations (about 40 theorems and witnesses) | 14 (4 `wrong`, 1 `weak`, 6 `missing`, 2 notes, 2 marked suspicions; one item counted twice here by severity) | 12 confirmed by the lead reading the code; of these 4 real defects in pushed code, all fixed: a second `costs` clause was never checked, a parameter hiding a constant was valued as the constant, a prototype's cost expression passed the gate unvalued, `S += f()` moved the call in front of the read of `S`; 1 suspicion confirmed and fixed (reason binder not local in an `else` body); 1 suspicion not verified (two modules declaring one constant name; closed conservatively) | 0 | 1 of the 6 defects the lead had noted beforehand (the bound `L.sye < 2^31` inside `InSync`); the review found 4 defects the lead had not known |
| 2026-11-12 | 1 | Sonnet 5.5 (effort high) | review W1-R2: the SAME material and brief as W1-R1, on a tree that still held the defects | about 270 declarations (its count) | 16 (3 `wrong`, 5 `weak`, 4 `missing`, 4 notes; several marked "likely" or "suspicion") | 13 confirmed by the lead reading the code. Of the 5 real defects W1-R1 established it found 4 (`S += f()`, the second `costs` clause, the prototype cost, and the parameter that hides a constant as a suspicion) and missed 1 (the reason binder). It found 3 defects W1-R1 did not: a function-pointer type's other clauses pass the gate unchecked, the unit word of `bounded N <unit>` is never compared with `ops` (both confirmed in the code), and a census function still calls the tagged-field resolver without the record step; and it named the bound inside `InSync`, which W1-R1 missed | 0 found; 3 not verified (payload copy in the static read, an immutable local hiding a static array, duplicate function names) | 1 of the defects known when it ran (the reason binder) |
| 2026-11-12 | 1 | Fable 5.2 (effort high) | review W1-R3: the SAME material and brief, on the same tree state (`d1a1986f0`), told not to read the later commits or this file | about 265 declarations (its count) | 15 (2 `wrong`, 4 `weak`, 6 `missing`, 3 notes) | 13 confirmed by the lead. Of the 8 defects the two earlier reviews had established it found 5 (`S += f()`, the second `costs` clause, the parameter that hides a constant, the prototype cost, the unit word of a bound) and missed 3 (the reason binder, the unchecked clauses of a pointer type, the census function without the record step). New and confirmed in the code: constants are valued in list order, so a constant defined by a LATER one has no value (a refusal only); the hold walker bounds the body without the release step and the pass walker the body without invariant and loop charge | 0 found; 2 not verified (a name that is both a record and a tagged type; a function of the unit missing from the gate's members) | 3 of the 8 defects known when it ran |
| 2026-11-12 | 2 | Muse Spark 1.3 | design W2-M1: narrowing a value by the condition that guards it (read-only, with probes against the built compiler) | the typing of ranges, the elaborator's fit checks, `narrow` and `eng` through syntax, semantics and lowering, with file and line | 1 design in five parts: two variants with estimates, three rewritten examples, four probes; and 1 warning of an unsound case | the central facts confirmed by the lead where checked (`uCond` elaborates both branches in the unchanged context; the bound computation from a condition already exists for `exchange` arms); the recommendation is usable after one correction by the lead (the value form `eng` instead of a `narrow` with a dummy `return`, which would add a return path to the user's duties) | 1: the warning that non-negated `!=` yields equality bounds is a misreading of two adjacent lines; the code is sound there | — |
| 2026-11-12 | 2 | Muse Spark 1.3 | analysis and design W2-M2: why a call that writes another module's table is refused, and what is missing (read-only, eight probes against the built compiler) | modules through parser, name resolution, hull check, effect elaboration, the call's frame rule and the gate, with file and line | 4 refusals reproduced with smallest programs, each classified (a deliberate rule, or a form the elaborator does not bind), 1 unlisted fifth refusal, 2 fixes with estimates | the diagnosis confirmed by the lead's own probe (the caller cannot name the foreign table in its effects; the frame rule itself is right); line references not individually checked | 0 found; it did not try the `::` spelling of the place, which the lead probed (a parse error) | — |
| 2026-11-13 | 3 | Muse Spark 1.3 | design W3-M1: the duty generator V1 and its meeting point with the bridge (read-only) | the duty files, the generic theorems of `programmlogik`, the bridge's computed statement and template, the front end's 61 functions | 1 design in six parts; its main point: no printer is needed, because the duties are already a computed Lean term (`Pflichten src`) with a generic theorem (`nutzer_aus_quelle`) and a goal template (`vorlage`); an order of eight forms for the bridge with estimates; `Stimmig` checked condition by condition against the front end | confirmed by the lead: the three definitions exist as described; there are 5 tracked duty files, not the 241 the lead's brief implied (it corrected the brief, and noted that no duty file has a loop duty) | 0 found; the per-form function counts are marked inferred | — |
| 2026-11-13 | 3 | GPT 6.1 Sol | review W3-R1: the statements of waves 1–2 (typed spec parameters, the checker bridge, ticket lemmas, call depth, hold sections, wildcard arm, character literals) | 100 theorems, 111 definitions (its count) | 14 (4 `wrong`, 5 `weak`, 2 `missing`, 3 notes), each with a concrete counterexample | 14; three semantic defects of the spec-argument check (binder capture, `count` body in the outer context, a bool argument only read) and the unsatisfiable start premise of the bridge for a plain `main` | 0 | the dead hypothesis of the bridge (found by Muse) |
| 2026-11-13 | 3 | Muse Spark 1.3 | review W3-R2: the SAME material and brief | about 240 declarations (its count) | 9 (3 `weak`, 2 `missing`, 4 notes) | 8; the dead hypothesis `zertifizierbar` and the synthetic `Einheit` of the bridge | 0 false, 1 half right (a refusal it said was not witnessed is witnessed in a neighbouring file) | the three semantic defects Sol found |
| 2026-11-13 | 3 | Muse Spark 1.3 | analysis W3-M3: six unverified suspicions of earlier reviews, each to be decided from the code | six code paths | 6 verdicts: 3 real, 3 not a defect | 2 real confirmed (duplicate function names compile and the first wins: measured, exit 1; the census without record tables), 3 cleared with the excluding lines | 1 false: "a record and a tagged type of one name are admitted" — the compiler refuses it one stage earlier, which it had not read | — |
| 2026-11-13 | 3 | Muse Spark 1.3 | analysis W3-M4: why a `traverse` body with a call is refused by the export gate | the gate from the source check to `bodyWrites` | the cause (`touchesVerified` gives up on any bound call), its class (a Bool stricter than the model rule), a change proposal; it also showed that one observation of the original finding cannot be explained by the gate | cause confirmed by Sol's implementation following it | 0 | — |
| 2026-11-13 | 5 | Muse Spark 1.3 | design W5-M1: lock stage 2 (free at entry, the switch of `AgreeW.sync`, the new `locksCode` with every exit) | the model's lock rules, the Stage-0 lock proofs, the runner's futex lemmas | a design in three parts with file:line tables, a build order, the code layout with jump literals | the layout and literals were re-derived by Opus and agree; the claim that the simulation ties lock words to the held set only by assumption was confirmed by Opus's reading | 0 found; items it marked "grep only" stayed unverified | — |
| 2026-11-13 | 8 | Muse Spark 1.3 | design W8-M1: the bridge for local bindings, assignment and statics | the bridge's translation and simulation, the `Body` model, the lowering of bindings | a design in four parts: `Body` needs no new syntax; the one proof idea (the run induction must follow `Endblock.bind`); seven steps with sizes; "no function of the front end is bridged after these steps, because the duties are per unit" | the scaffolding step was implemented from it by Sol and built; the per-unit finding led to the next design | 0 found so far | — |
| 2026-11-13 | 8 | Muse Spark 1.3 | design W8-M2: bridge duties per function instead of per unit, decided from the proofs | premise (b), the bridge chain, every unit-wide condition | "yes, under call-closure", with the split duty and the three proofs to redo | the split and the closure constraint held up in Sol's implementation; MISSED: the start duty of an open root (found by Sol), and that both invariant duties follow unit-wide | 0 false; 1 missed premise | the start requirement |

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

**After wave 3 (2026-11-13).** Fourteen tasks, three builds of the assembled wave, single-module checks between.

- **Opus 5.5**: third and fourth blind task that built at the first try (20 files, 6 changed statements, the
  read-back theorem repaired through a context switch). Its one fault was of design, not of proof, and only a
  running probe showed it. First choice for anything that changes a statement other proofs unfold.
- **GPT 6.1 Sol**: four implementation tasks, 1 built as delivered, 3 after small repairs; the `private` mistake
  did not recur once the brief named it. New recurring fault: a change to a parser or elaborator function breaks
  a theorem ELSEWHERE that unfolds it (the round trip, the read-back, twice), and Sol does not look for those
  unless told; briefs now say "grep every theorem that names the function you change". It also invents surface
  syntax in probe texts. As a reviewer Sol was the strongest so far: 14 findings, 14 confirmed, each with a
  counterexample, three of them real semantic defects.
- **Muse Spark 1.3**: analysis remains its strength (the cause of the traverse refusal, the dead hypothesis of
  the bridge); its first false finding came from reading one stage of the pipeline only — a claim "X is accepted"
  from Muse is measured with the compiler before it is acted on. Its proof draft needed two small repairs, the
  best blind proof result of Muse so far (the statements were simple).
- **Sonnet 5.5**: a sound design, delivered with an honest account of the theorem it broke; the proof side went to
  Opus.
- **The lead's own work** broke the most modules of the wave (a hash set inside a function the kernel evaluates:
  19 witnesses) and stated a bridge theorem with a dead hypothesis. The lead's code is reviewed like an agent's.

Two reviews by different models on the same material again found disjoint defects (Sol the semantic ones, Muse
the vacuity of the bridge): the pair is kept. What the builds showed this time: no blind PROOF failed by more
than a few lines; what failed was what nobody had looked at — theorems that unfold a changed function, and probe
texts nobody could run. A wave that changes the elaborator therefore gets, before its build, single-module checks
of the round-trip and read-back modules (`Parser/Round/**`, `Gen/Text/Invers/**`).

**After waves 4–6 (2026-11-13).** Seven tasks, four builds of the assembled waves.

- **Opus 5.5** built at the first try in two of three tasks and needed 12 lines in the third; eight blind tasks
  so far, six built unchanged. It also made the two best design calls of the day unasked (no fact store in the
  context; no half-switched lock). One new fault class: a witness by term `rfl` over a compiled unit, which the
  elaborator (not the kernel) tried to evaluate — 15 GB. Briefs now forbid it.
- **GPT 6.1 Sol**: three tasks, all built after at most six lines; the faults were all in witness modules
  (literal layout, `decide` without an instance, an expected text nobody ran). No fault in a changed proof, and
  none of the "breaks a theorem elsewhere" kind once the brief asked for the grep.
- **Muse Spark 1.3**: the lock design was detailed enough that Opus implemented from it.

The cheapest route found so far: a design by Muse (read-only, with file:line), the implementation by Opus or Sol
from that design, single-module checks of the leaf, read-back and round-trip modules by the lead, then ONE build
of the wave. Waves 5 and 6 needed one build each plus a rebuild after a witness repair.

**After waves 7–9 (2026-11-13).** Nine tasks, three builds of stage0, three of the bridge.

- **Opus 5.5** delivered the largest blind change so far — the lock switch over 114 files with 66 induction
  hypotheses — and it built without one error. What made that possible was its own preparation: it first proved
  the standalone theorem and wrote the file-by-file list, and refused to switch half way. Ten blind tasks, eight
  built unchanged, two after at most twelve lines.
- **GPT 6.1 Sol** built at the first try in two of five tasks, among them a change to the lexer with its
  round-trip proofs. Its weak spots are now narrow and known: recursion over mutually inductive types, and
  hand-written witness proofs over concrete units (use `match` on `Fin`, never `decide` on a Prop without an
  instance). It stopped correctly at a missing premise instead of assuming it.
- **Muse Spark 1.3**: the measurement on the Gabbro front end changed the plan (equality guards), and its two
  bridge designs carried the implementation; one design missed a premise that the implementer found.

A measurement by an agent that can RUN the compiler was worth more than any review this day: it showed that the
feature the lead had counted as the largest win (narrowing by the guard) removed no workaround on real code until
equality guards were added.

**After waves 10–17 (2026-11-13).** Sixteen tasks; four builds of stage0, four of the bridge, single-module
checks of `grammatik/`.

- **Opus 5.5**: the lock gate (returns inside `locks` with real releases, 82 files, blind) needed ONE kind of
  repair — a missing implicit argument at seven call sites of one lemma — and then built; the corpus went from
  368 to all 376 probes. Earlier in the day it found that the lead's own stage-3 statement was unprovable as
  written and restated it with indexed return relations. Thirteen blind tasks, nine built unchanged.
- **GPT 6.1 Sol**: seven tasks. Built unchanged or after one line: the bridge chain consolidation (166
  declarations deleted), the six comparisons, the mutable-local snapshots (where it found the lead's continuation
  rule unsound, with a counterexample). The contended lock paths (12 modules, 28 theorems) needed three lines
  and corrected three points of the brief against the code. Failed first delivery: the number `match` (a keyword
  as a name, sixteen kernel witnesses, broken round-trip proofs); its own repair then built at once. The port of
  the async model needed eight repairs by the lead, all of the kind a port without a build produces (visibility
  of witness definitions, a `rw` through an unreduced match, structure-literal layout). Twice it STOPPED at a
  wall instead of weakening a statement (shadowing: the invariant-only change is false, with a counterexample
  from the definitions) — the most valuable behaviour of the day. When a task is too large it delivers a built
  foundation and says plainly what is missing.
- **Muse Spark 1.3**: designs and measurements only. The runner-speed measurement and the async design were
  usable as delivered; the speed-against-C analysis cites the language documents rather than the Lean model and
  one earlier claim of the form "X is accepted" was false when measured. Rule kept: a Muse claim about what the
  compiler accepts is measured before it is used; its designs name what they could not verify.

Statement reviews: Sol's reading of the ported async model found five theorems whose names claim more than their
statements (`asyncOk_refines` does not use its checker premise; `cancellation_no_leak` is relative to free
parameters). Those are not cited as safety results until the G instance exists.

**After waves 18–27 (2026-11-13, second half).** About forty tasks; the lead checks module by module on throwaway
branches and returns error lists instead of repairing more than a few lines.

- **Opus 5.5**: image theorem T2 (six proof modules) built after three one-line repairs; the whole-body extension
  (four commits) built WITHOUT any repair. Its kernel witnesses are its weak spot: two witness modules in a row
  did not finish in the kernel within 15 minutes (its own estimate: 1–4 minutes). Brief rule: a witness module is
  delivered separately and checked alone with a time limit.
- **GPT 6.1 Sol**: large blind changes now need two to four rounds: the positional bridge chain (about twenty
  repairs), the indexed elaborator scopes (three rounds, then green and measured), the bridge statics (two rounds,
  green), the lowering/prepare speed change (two rounds, still red), the async segment layer (four rounds, still
  red and taken off the integration branch). Recurring causes, now in every brief: structure literals with
  commas or shallow continuation lines; `rfl` between two different recursions; `rw` at the scrutinee of a
  dependent match; implicit arguments that nothing determines; `cases` on a copy of a term that still occurs in
  the goal; lemma names that do not exist (`Bool.and_eq_true.mp`, `List.append_eq_nil.mp`). It stops correctly at
  walls (async: frame-only model; C05: invariant cost without a model meaning) and its reports are accurate.
- **Muse Spark 1.3**: usable as an IMPLEMENTER for small definition-heavy model layers (low-level: architectural
  state, entry frames, masks, priorities, bytes, translation, registers — about 4 000 lines, each module green
  after zero to two rounds with the compiler messages handed back). About every second implementation run ends
  at its first message without doing anything (a status sentence instead of a tool call); the run is simply
  repeated. Measurements stayed its strongest contribution (probe matrices for all 18 C packages, 136 probes,
  no wrong-code fault; long-body cost split; the loop rewrite of the front end with the finding that `retry` is
  unrolled). One reported fault was not a compiler fault (a foreign call's `requires` is unchecked in the model
  too) — still a real gap of the goal, recorded.

The lead is now the bottleneck: nine agents produce unbuilt code faster than one builder can check it. What
helped: check branches for anything on the compiler path, error files handed back verbatim, one repair task per
delivery, and taking a layer off the integration branch when it does not converge.
