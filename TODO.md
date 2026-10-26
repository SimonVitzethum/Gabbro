# Open work

*Updated 2026-10-20. Only what is OPEN, in five areas: heap, Lean model, checker, LLVM backend, translation validation.
IDs (`Oxx`) are stable: comments in the tree that say `OFFEN Oxx` or `TODO.md Oxx` mean these entries. Closed and removed items are in the
appendix, one line each. History is in git.*

**How to read this file.** Each entry gives the state in a sentence or two, then `Open:` with what is missing. Designs and long
reasoning live in the linked plans, never here. Keep an entry to one short paragraph; if it needs more, write it in a plan and link it.

## Right now

- **Phase A step 4 (the combined `Spec.lean` diff "M8": arena plus payload) is PAUSED** (Simon, 2026-10-19). Nothing is merged or pushed.
  The arena foundation (M3) is green on Lean/Mathlib 4.35.0 (820 jobs); the full library is not (7 modules, one a real heartbeat
  timeout in `ArenaErkZeugeBaum.lean`); the payload half still lacks its global history induction (O21 in the plan). The work sits in an
  uncommitted worktree under `.claude/muse-arbeit/kratz/spec-arena-recovery/`.
  Exact state, outstanding obligations and resume order: `dokumente/PLAN-DYNAMIC.md` §8a, part H.

## 0. Order of work (Simon, 2026-10-17)

Strictly in this order. Every step is Lean-first (model, then exporter, checker, compiler), no legacy, no German words in syntax.

### Phase A: dynamic data structures and their invariants

Plan: `dokumente/PLAN-DYNAMIC.md` §8a. Covers O4-O6, O11, O14, O20, O29.

| Step | What | State |
|---|---|---|
| 1 | `free`/`grow` as G blocks over the arena sugar; free-list invariant | Built (`ArenaFrei.lean`) |
| 2 | Invariants over live slots: links in range, acyclic along a walk, tree shape (capability tree), free list disjoint from live slots | **Done in Lean** (2026-10-18, §8a.1, THEOREM-MAP 79): one recognizer `Erk K` for list, tree and both on one arena, loops, function bodies `ErkE`, executed forms, `revoke` of a subtree, witnesses and planted defects. |
| 3 | Concurrency of arenas (O20): `grow` as a locked commit | **Done in Lean** (2026-10-18, §8a.2, THEOREM-MAP 79): a shared arena IS the lock invariant (`Dekl.sperr`), section theorems, `grow_atomar`, machine bridge `erkE_maschine`. |
| 4 | `Spec.lean` diff: dynamic structures and table/group invariants leave NOT CLAIMED, `invRuhe`/`invSicht` non-vacuous; `gabbro_ziel` re-proved; two independent verdicts | **Paused**, see "Right now". |
| 5 | Exporter/elaboration, then checker (O11), then three examples (list, tree, hash chain) with certificates and poison probes | Not started |

- **Open in step 2:** wiring the recognizer into `Akzeptiert` (§8a.3: an arena as an invariant name, the `ErkE` derivation a certificate in
  the unit); the exporter for these forms; calls inside writers; releasing a whole revoked subtree; recognizers for hash chains and the
  sibling demand.
- **Open in step 3:** the ABA ownership predicate; the commit bound (no `dynFrisch` form, frames do not name `zaehl`/`komm`); the footprint
  of a pure `pop` (`schuldet` counts tables only: a DECISION for step 4); the arena at writer entry; loops in the machine bridge; the
  migration D1 (needs a `Syntax.lean` split and a full rebuild).
- **Open decisions:** first structures (recommended: list and tree); links as indices in one arena (recommended); `free` across function
  boundaries (follows the `own` boundary rule).

### Phase B: weak memory

State: GX/W model carries atomics with the rely; release/acquire is enforced.

1. **Message passing with a plain payload under release/acquire, no lock** (O25, `N291`). The memory-model half is PROVED
   (`Speichermodell/Payload/`, THEOREM-MAP 80: no race after the await, the value, counter-models, litmus tests). Open: the `Spec.lean` diff
   D1-D6 and the checker rule R0-R4 (proposed in `PLAN-DYNAMIC.md` §11, four decisions for Simon in §11.5); no concrete W/GX fixture
   yet; 11 corpus examples wait for it. The Lean integration is the payload half of the paused M8.
2. **Weak memory beyond DRF-SC:** name and prove what is claimed (standard patterns); shrink the NOT CLAIMED line.
3. **Hardware bridge:** x86-TSO, ARMv8 and RISC-V (RVWMO) refine W/GX access by access through the ISA-neutral `Need` list of Track L.
   Needs the CPU models (built by Simon).
4. **Orderings and primitives:** `consume`, `seq_cst` total order, stand-alone fences, mixed-size access, atomics over floats; litmus tests
   (MP, SB, LB, IRIW) as the yardstick.
5. **Shared atomics across link boundaries** and the merge discipline of per-core cells (O17); lock-free structures (SPSC/MPSC ring, Treiber
   stack, seqlock, RCU) with happens-before over the payload; device and DMA ordering.

### Phase C: the rest, in this order

1. **Track P and Track L**, both running now in parallel with Phase A.
   Track P: complete Lean parser (coverage matrix, then elaboration replaces `lean_g.rs`). Track L: refinement down to the binary with an
   ISA-neutral `Code` and no CPU model. Plans: `PLAN-TRANSLATION-VALIDATION.md` §9a/§9b.
2. **Model gaps behind existing lowerings:** `boot` and `entrust` semantics; aarch64 `vector`/`via` meaning; port space and `asm` (LLVM
   lowerings exist without a model).
3. **Remaining O-items:** interrupts and cores (O19 rest), arenas under concurrency (O20), `child` without a model (O21), gate
   preconditions (O23), strings (O24), source forms without a complete G export (O27), linking (O28), regions in G (O37). See §2.
4. **Termination, waiting bounds, fairness, stack depth,** floats beyond the IEEE kernel.
5. **Benchmark against GCC `-O3`:** only after the compiler lowers much more and strong optimisation is in (Simon).
6. **Housekeeping:** see §3 (legacy cleanup); file split to an average under 500 lines (`instrumente/teile/lean-teilen.py`); the frozen
   Isabelle `.thy` set.
7. *Done 2026-10-18 (Simon's decision):* comments as in most languages: `//`, nesting `/* */`, `///` doc comment as trivia
   (`Token.doku`); the `--` comment is removed everywhere. Lean first, then `lex.rs`, then ~1270 files (THEOREM-MAP 83).
   Left: a formatter or doc tool that reads `Token.doku`/`Art::Doku`.
8. **Adequacy of the generated test set** (Simon, 2026-10-18). Goal: if a program-neutral checker/compiler handles every generated test
   program, it handles all valid programs correctly. Result in Lean (`grammatik/Grammatik/Adaequanz/`, `CHECKER.md` §16, THEOREM-MAP 85):
   program-neutral alone admits NO finite test set (`kein_endlicher_test`). With a state bound the W-method set is sufficient and
   astronomically large for Gabbro. For the class "verdict = conjunction of local premises and whole-program patterns" the answer is exact
   and small: one single-fault program per isolable refusal cell plus valid programs covering the accepted cells (124 premise cells, 146
   child-position cells, at most 4 540 pattern cells, independent of program size). EXACT CELLS (2026-10-20, `CHECKER.md` §16.6a): the global patterns are 124 cells with 20 bad, not 4 540; `gen-zellen` witnesses 75 of 104 good and 9 of 20 bad cells strictly (valid program / single-fault program), from a generator that emits each program with its proof (`Gutes`, `Schlechtes`), against the Lean model only (the Rust checker is never an oracle). Open: the local refusal cells need source mutants,
   so the G-to-source printer of Track P; the coarse accepted cells (4 of 459 covered); the metamorphic tests for hypotheses H1-H8.
9. **Refinement down to the binary: EETV-R version 3** (the ONLY refinement item; Simon's design, 2026-10-18). LLVM stays an UNTRUSTED
   producer; Lean checks the binary against the certificate through a small UB-free core K, bridge steps justified by Gabbro facts, and a
   backend validator over chip-learned instruction semantics. Nothing built; the first steps start with extending `Code`. Full design,
   hardware contract and research risks: `PLAN-TRANSLATION-VALIDATION.md` §9c.
10. **One-off corpus of ALL generated programs** in a git submodule (at most 30 GiB, counting-and-unranking generation). Not started.
    `dokumente/PLAN-LONG-RANGE.md` §1.
11. **`async fn` and `.await`** as a verified state-machine transformation (sugar; machine G and `Spec.lean` stay untouched). Not started.
    `dokumente/PLAN-LONG-RANGE.md` §2.
12. **Self-hosted checker and compiler in Gabbro** (Simon, 2026-10-25): Lean specifies and proves, Gabbro computes (checking,
    compiling, generating and running M, N, R, coverage, IR validation); `gpruef` and `gkomp` proved terminating, deterministic
    and neutral, correct on every program through M and N, the adequacy theorem and GabbroV logic proofs; LLVM stays the back
    end. Not started; first the language needs (region release, strings in G, file-gate contracts, measure-based loops).
    `dokumente/PLAN-SELF-HOSTING.md`.

*Items 10-12: Simon asked for no new agents for now.*

---

## 1. Heap and stack

- **Built:** pressure-sampled unbounded arenas, slot release, external free-list links for small elements, per-chunk live counts, physical
  return of empty anonymous payload pages; whole-arena reset. All direct and compatible indirect recursive cycles use a loop dispatcher
  with explicit growable continuation storage (allocation failure is an explicit trap); checked static range zeroing; guarded
  per-invocation thread stacks, group spawn before join, stack unmapping after join.
- **Open:** `free` across function boundaries (Lean audit and plan: `dokumente/PLAN-DYNAMIC.md` §12); aliases outside the tracked ownership discipline; complete `ArenaForm`/`DynForm` export and
  the G form of the newer memory statements. No checker refusal or source obligation was relaxed. CPU/final-byte refinement is §5.
- **Evidence:** `dokumente/LLVM-BACKEND.md`; coverage is the Lean constructor/field register, checked by
  `python3 instrumente/pruefe-llvm-modelldeckung.py` (examples never define it).

## 2. Lean model

- **O1-Rest (duties beyond the machine).** L50/L52 carry the leg `folge`, L24 the invariant legs, L34 stands as an existence with witness.
  Open: the name of `breaking` in the G rest (brand layer plus re-proof of all per-statement theorems); the block-restoration duty in (b);
  axiom/register events in the call log; path-sensitive `ende` (per return site); an ordering field in `Einheit` filled by the exporter.
- **O4 (`cdt_wohlgeformt` at a free slot).** Waits for O5; `delete_leaf` holds only conditionally, `revoke` inherits the condition.
- **O5 (sibling consistency as a table-invariant demand).** Indexing THROUGH the option (`slots[s.next_sibling]`) is blocked; a `requires`
  at each call site is a substitute, not supply-once.
- **O6 (DEMAND 3 as an unbounded rank witness).** Works for the refutation; the proof direction (`unsat`) over the rank form plus four
  undrawn reachability rows stays with the demand.
- **Generator support for aggregates (2026-10-25).** G has `Ty.arr`/`Ty.str` and their seven `Expr` forms (THEOREM-MAP 100);
  the generator gives them size `unendlich` and never draws them, so test sets M and N do not cover them yet.
- **Front end, exchange and awaits (2026-10-26).** `exchange` has only the `update` form with one value in the
  Lean front end; open: the compare form (`… when old(A) == x returns r`: what `returns` binds needs a model
  decision), payloads and `awaits` at an exchange, exchanges at table elements (`REGEL[r]`), update bodies with
  `if`. `let x : T = A awaits { … }` still drops the written type `T` in the surface tree (`SAnw.await`); `swap`
  carries it since 2026-10-26.
- **End-block forms (2026-10-26).** `Endblock.narrow`/`exchange`/`ite` (THEOREM-MAP 102): the generator does not draw
  them (size `unendlich`); arena ownership (`chkE`) and the cost mirror (`spiegelE`) refuse them; the Rust exporter
  does not construct them.
- **Stage 0: the Lean front end over the whole syntax (2026-10-25).** Measured with `grammatik/kratz/Deckung.lean` over
  `beispiele/` (first refusal per example): 43 of 177 accepted after arrays/strings, half-open ranges and aggregate
  fields. Open, model work first where marked (M):
  * (M) records as values (`Treiber`, `Completion`, `Platz`; O15 was priced and refused for C, revisit for stage 0);
    tables of atomics (`atomic A : [T; N]`); a translator and library calls (a table as a value, translation-time
    evaluation); `format` (wire layouts over byte buffers); `rcu`, `accumulates`, `walk`, `entrust`, `boot`,
    `profile`, `gate`, `check`, `axiom` items; `ptr<_, _> u8` byte regions; the `shr` result range (`h1 >> l2`,
    the checker's, instead of `0 .. h1`).
  * (front end) floats (`f64`, `Ty.fl` exists); `exchange update` loops; `count x in slots` as a value; `narrow`
    of a place and at the top level of a body; `let mut` of an aggregate and element writes into a local;
    `use`/module paths (qualified names: the `gabbro-qn` session); `deadline` on foreign bodies; tree tables,
    `owner`, `backed`; registers' fields; `loop`, `await`, `drops`/`takes`/`posts`.
- **O14 (arena chains: two statement shapes without a form).** Specification and exporter have the form; two statement shapes close no chain.
- **O19-Rest (handlers and cores).** Since 2026-10-18 (Lean): G has a per-core interrupt-mask state over the layer `KernZ`
  (`KernMaske.lean`); the core schedule is DERIVED from the machine (`kernPlan_aus_lauf`, `kernHaltE_iff_M`); `Code` has `Instr.imsk` with the
  named assumption `MaskHw` and the refinement `MaskRel.lean` (`PLAN-DYNAMIC.md` §8a.4, THEOREM-MAP 81). Open: the `Spec.lean` proposal
  (not applied) and its GA twin; composing the `Code` steps with the interleaving of all threads of a core (H3); re-entry and
  handler-on-handler preemption; `Einheit` names no handler; `H102` fires only on `via idt`; no Rust/LLVM emitter for `imsk`.
- **Reader/writer lock (decision 2026-10-18).** In Lean as the layer `RwSchritt` over machine G: exclusion, rank order, no wait cycle, no
  write-write/write-read race (premise `LeserLos`), a `Code` lowering on one state word with refinement `RwRel`, witnesses and planted
  defects (`PLAN-DYNAMIC.md` §8a.5, THEOREM-MAP 82). Open: the `Spec.lean` diff (mode in G recommended); the syntax (`lock L rank N rw`,
  `reads L { }`: proposals); the `Ziel` legs with no layer twin; the checker rule deriving `LeserLos`; fairness; no Rust/LLVM.
- **O20 (arenas under concurrency).** Generations and the commit ceiling assume one thread of control and roots entered once. Lean (Phase A
  step 3) covers the locked commit. Open: ABA ownership predicate, commit bound, footprint of `pop` (`schuldet`), entry fact of a writer.
- **O21 (`child` without a model).** The child thread exists in the checker; its code between gate call and region is unchecked for the child.
- **O23 (gate preconditions not in the goal).** NUL path and frame length are named, not modelled.
- **O24 (strings checked, not represented).** NUL, `max` ceiling, aggregates.
- **O27 (source forms without a complete G export).** The exporter stays partial, notably float, byte-pointer/string and dynamic-arena
  forms. A working LLVM lowering is not a Lean judgment; track the boundaries in `dokumente/llvm-modelldeckung.tsv`, not counts of examples.
- **O28-Rest (linking).** The `Spec.lean` diff had no independent review round; no semantic equivalence/refinement for contracts (normal-form
  trees); no certificate for linked programs. Name spaces are in Lean (THEOREM-MAP 97); the Rust checker still resolves against the whole
  unit -- it must resolve against the project's visible names and refuse an own top module named like a dependency.
  The model side of linking is complete (THEOREM-MAP 94-99); open: the Rust link check (`bindeB`), build files, GabbroV
  certificate reuse by fingerprint, LLVM linkage and TV of the link step.
  Qualified names are in Lean (THEOREM-MAP 101: an item is its path, place heads may be paths, `pre108` resolves);
  the Rust side does not follow yet: `parse.rs` still reads `x::y::C` as a field chain, the checker keys carriers
  and functions by short name and `N039`/`N042` still refuse a second item of one short name, `llvm.rs` keys its
  globals by short name.
  `pub` and the closed export hull are in Lean too (THEOREM-MAP 102); the Rust `N038` still compares short names.
- **O41 (registers as Lean, not as `.tsv`; Simon, 2026-10-20).** `dokumente/llvm-modelldeckung.tsv` is a hand-written list of the model's
  members with an LLVM status per member; it proves nothing, its member column duplicates the total match of `Gen/Abdeckung/Mitglieder.lean`,
  and `instrumente/teile/llvm-modelldeckung.py` checks it against the Lean sources by regex. `messung/fallen-klassifikation.tsv` has no reader.
  Open: the LLVM status as a total Lean function over the constructors (a new constructor stops the build; the status stays a claim about
  `llvm.rs` until translation validation); stage 6 of `pruefe-lean.py` (`gen-abdeckung`) takes its members from Lean, reading no file; delete
  both `.tsv` files and the Python script; update `llvm.rs`, `CHECKER.md`, O27, `pruefe-lean.py`, `pruefe-llvm.py`.
- **O42 (complete test sets M and N; `dokumente/PLAN-TEST-SET.md`).** Proved: Theorem 5 `vollstaendig_hinreichend` (a conjunctive checker
  that agrees with the model on M and N agrees on every program), step 1 `akzeptiertX_zellen` (the model's Bool IS the conjunction over the
  cells), unreachability of five cells (`ZellenUnmoeglich.lean`). The generator emits only proof-carrying `Gutes`/`Schlechtes`, one program
  at a time (`Strom`), with contracts. Open: M and N as concrete values for the whole model with `Vollstaendig` proved (a witness or an
  impossibility theorem per cell, `gut_in_n`); the remaining cells without witness; stage 3 (R, text level), stage 5 (model mutations), the
  lowering cells from `lowerS_ok`.
- **O43 (contracts on function-pointer types; 2026-10-21).** Pointer types are structural (`Deklaration.passt`, `SigPasst`), but a
  `fn(..)` type's `requires`/`ensures` have no model: contracts on function-pointer types (requires/ensures carried by `SigPasst`, with
  contravariance) need the model first. Until then a non-`true` contract on a pointer type is refused by name; `costs` travels nowhere,
  as at a function.
- **O37 (regions in G).** No byte pointers in the model (`Ty.ptr` is a carrier capability); nothing frees a region (no ownership closure at
  the gate parameter); Gabbro bodies pass on no extent (only a foreign `ensures … <= lenof(result)` carries).
- **Computational universality (2026-10-24).** Partial results in `grammatik/Grammatik/Berechenbarkeit/` (THEOREM-MAP 91): exact normal
  completion of `runsUntil` over existing syntax, decreasing-rank fuel bounds, real writing witnesses, and an accepted finite G program
  reaching arbitrary stack depths. That recursive witness admits no semantic `MassPflicht` for any measure; its unmeasured non-tail cycle
  has class `abgelehnt`. Open: a finite-program, oracle-free universal-machine encoding and a generic push/pop/controller simulation with
  halting/output correspondence, budget adequacy and precise admission conditions. Unbounded stacks and conditional exits are not that proof;
  do not claim Turing completeness from them. No syntax, acceptance rule or goal premise was weakened.
  **Complete proof plan:** [PROOF.md D5](dokumente/PROOF.md#d5-complete-universality-proof-and-brainfuck-compiler-plan-2026-10-24),
  packages U0-U10: all eight Brainfuck commands compiled through finite Mathlib TM2
  to the actual G machine, with input loading, safety/admission, bidirectional halt and output-prefix preservation, nested-fuel adequacy,
  conditional time/space bounds and a partial-recursive-function/undecidability bridge. Resolve real push/pop and admission at U0 first.
  **Checked intermediate milestone:** `Brainfuck/{Machine,ToTM2,Fuel,Witnesses}.lean` proves the eight-command byte semantics,
  exact BF-to-TM2 step/evaluation/halting/output correspondence and finite halting certificates, with nested-loop and divergence probes.
  `AdmissionBoundary.lean` proves generic rejection of reachable unmeasured non-tail cycles. `TerminationCompatibility.lean` proves
  incompatibility with a complete computable halting test under an explicit reduction premise. Raw-text parsing, Gabbro storage/backend,
  admission, initialization and the universality bridge remain open. Simon confirmed: checked classes/proofs with conditional runs allowed.
  The target is additionally bundled as finite Mathlib `FinTM2` with its regular input entry, and one fixed BF/TM2 program reaches
  arbitrary tape depths. `Storage/CallReturn.lean` proves a real G call/return restores a retained bit (class `endet`, core-checker accepted).
  This primitive does not solve the admission of an unbounded recursive stack service. Simon authorized an explicit, fallible region without
  an element ceiling. Its storage semantics and safety proofs are now in `Bausteine/Arena/Unbounded/`; see `PLAN-DYNAMIC.md` section 13.
  Whole-program G admission/export, production lowering and the final universality theorem remain open.
  The linked TM2/BF heap backend now preserves and reflects halting and output from allocated input, with OOM separated from normal halt
  and a conditional four-operation bound per BF transition (`PLAN-DYNAMIC.md` 13.3). This target is the new storage component, not yet G.
  Concrete, value-sensitive G push/pop/free prefixes and a whole finite core-accepted `endet` witness are now proved (`PLAN-DYNAMIC.md`
  13.4). G's fixed index bound, full source ownership admission and the unbounded whole-program TM2/G bridge remain open.
  G stack operations now carry exact ownership-grant effects (13.5); an actual G `runs until stack-is-empty` loop has the exact
  proved boundary `initialStack.length < passes`, including a core-accepted conditional-class function witness (13.6).

## 3. Checker

- **Legacy cleanup** (fixed rule 2026-10-17: no legacy in compiler, checker, parser). Done: `cnamen.rs`, `N041`/`N046`/`N052` with sentences and
  17 poison probes, 42 dead functions and constants, the Lean folder `CBackend` (22 233 lines, deleted 2026-10-18; tag
  `archiv/c-emitter-2026-10-17`). Open: 13 compiler warnings in `llvm.rs`/`nulpfad.rs`/`certstmt.rs` (two unreachable patterns, the
  link-unit init for constants, never-read fields); the C templates in `schablonen.rs`; comments naming `emit.rs`/C11. Remove, do not rename.
- **Differential harness** (`CHECKER.md` §12.6). Class (b) is empty over 62 000 generated programs. The groups of class (a) left
  (`ERWARTET_A`: costs, `locks`/`reads` effects, `N511`/`N275` user logic, `const fn`) need Lean components; the model gaps (`return` under
  `locks`, `Endblock` formers, `Block.arenaAlloc` at the top level) are listed there with the exact change. Open rulings: `M104`, `N001`,
  `M133`, `M147`. Track P: 79 % of the generated space is outside the elaboration fragment.
- **Guardian remnants** (four guardians since 2026-10-17). `bruecke/` is not measured (its `lake build` fails on the missing `mathlib`
  entry); the tree-wide `gabbro prove` run and the E1 comparison (duties manifest) hang in no guardian; the mutation run over the checker
  is dropped without replacement; 8 600 German comment lines in the checker are unguarded. Details: `dokumente/TOOLBOX.md`.
- **O11 (guardless invariant).** A `table`/`group` invariant that no function `maintains` is booked by NOTHING (`N275`-`N277` check only
  anchored ones).
- **Alias / `own`** (built 2026-10-17). `R014` (error) and `R015` (hint) separate pointer roots at call boundaries; Lean has `ParamGetrennt`
  and `ObjGetrennt` with a bridge to `R014`; LLVM sets `noalias` on internal writable pointer parameters. Paper: `dokumente/A1-OWN-PAPER.md`.
  Open: records over byte buffers (range objects in the model, `LG005`/`LG001`); the four bridge hypotheses (`ParamVerschieden`,
  `RechteOk`, `HerkunftTreu`, `FrischNeu` only for the model allocator) and the checker's `let` run in Lean; `R004`/`R007` as special cases
  of `R014`; `noalias` is no Lean judgment (O27).
- **O26-Rest (foreign lock primitives).** Own primitives are checked (`N481`-`N483`); foreign ones stay assumed (weak memory assumes
  acquire/release).

## 4. LLVM backend

Full table: `dokumente/LLVM-BACKEND.md` §5.

- **Lowerings without a Lean model** (2026-10-17; rule: language follows the Lean model). Built, evidenced only by text/qemu: aarch64
  `entry` (the meaning of `vector`/`via` on aarch64 is the lowerer's reading; `LANGUAGE.md` and the model are silent), `masks irqs`, the
  x86_64 port space, assembler bodies. REFUSED because lowering would invent semantics: `boot` and `entrust`. To do: put the aarch64
  meaning of `vector`/`via` into the model, then fix `boot`/`entrust` in the model.
- **O22 (group execution and stack lifecycle; built 2026-10-17).** Every invocation owns a guarded mapping and completion word; all roots start
  before any join; kernel `clear_child_tid` ends the join after actual exit. Open: runtime syscall numbers still belong to the Linux profile;
  OS-neutral bindings/profiles and the target-to-GX proof.
- **`entries` (12 sites).** Hardware dispatch without a model; refused by name.
- **Stack gates and `child` (12).** The `clone` trampoline is missing.
- **`publish` with a payload (11).** Not covered by the goal theorem: Phase B item 1.
- **Shared locks (3), library calls (3).** Own primitive / payload model missing.
- **O40-Rest (emitter names).** Checker half built (`N042`); module-qualified names are missing (LLVM mangles `m_` only on a collision).

## 5. Translation validation (MUCH later)

Prerequisite chain, in this order; none of it is O27 work:

1. **A complete Lean model of a CPU.** Without it no refinement: the long pole (`ARM-PLAN.md`: Sail Arm plus multicore model).
2. **And more:** per-access bridge (goal to W/GX simulation), gate and entry lemmas per target (raw instruction, `_start` with stack, state,
   exit/`never`), O28 link closure, O26 foreign orderings.
3. **Automatic for all programs.** No per-program step by hand. That makes the chain more expensive than O27, not cheaper: O27 widens the set
   of judged programs one program at a time, while validation must run for ALL of them without help afterwards.

Design of the final validator: `PLAN-TRANSLATION-VALIDATION.md` §§0-5 and §9c.

## Appendix: closed or removed (ID → reason)

- **Built:** O3, O7, O8 (lane 167), O9, O13, O18 (F10), O31 (rest: build/hardware), O34, O35, O36, O38.
- **O25:** the atomic rely IS the goal (`gabbro_ziel`), closed; the payload half is Phase B item 1.
- **Withdrawn or declined:** O2 (falsifiers without threshold); O15/O16 (priced and REJECTED, zero corpus benefit); O30 (superseded:
  Rust backend plus Lean validator instead of self-hosting; for a front-end-only self-hosted compiler see Phase C item 12).
- **Not a topic of this list:** O10 (measurement layer); O12 (single program, no model case); O32 (hardware/runtime); O33 (process
  bookkeeping); O39 (kernel-module world; count: `N574`-`N577` built, unload window is hardware).
- **Out of scope:** O29 (Simon).
