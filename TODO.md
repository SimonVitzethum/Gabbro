# Open work

*Updated 2026-10-20; references and "Right now" updated 2026-11-01 (the entries themselves were not re-audited). Only what is OPEN, in five areas: heap, Lean model, checker, LLVM backend, translation validation.
IDs (`Oxx`) are stable: comments in the tree that say `OFFEN Oxx` or `TODO.md Oxx` mean these entries. Closed and removed items are in the
appendix, one line each. History is in git.*

*A name marked † is a plan that was removed in the owner clean-up of 2026-11-01 (`15efa71da`); read it with
`git show 15efa71da^:dokumente/<name>` (`ARM-PLAN.md`† lay at the top level).*

**How to read this file.** Each entry gives the state in a sentence or two, then `Open:` with what is missing. Designs and long
reasoning live in the linked plans, never here. Keep an entry to one short paragraph; if it needs more, write it in a plan and link it.

## Right now
- **C14 base-placement duty:** Prove that loader/runner image placement supplies `Nat.lcm 8 N ∣ b` for every positive declared global alignment; the relative layout and `aligned_abs` premise do not yet discharge this duty (THEOREM-MAP §127).

- **Stage 0: every userspace Gabbro form to IR, formally verified (2026-11-01).** The lanes IR-01..IR-14, their checkpoints
  and the C-package designs are in [IR-COMPILATION-LANES.md](dokumente/IR-COMPILATION-LANES.md); team, scope and build caps are
  in [AGENTS.md](AGENTS.md) ("Current work"). No legacy Lean source runtime and no unrelated side project.
- **C-package status (2026-11-02).** Integrated into `c-runde1`: all C packages except C01 and C10, including C07
  and C08. Stage 0 admits C12 tables in named spaces and pointers into them (rights decoded by `DataRights.decode`),
  C14 `when TESTBUILD` (selection before Stage 0), C17 `decreases` measures, C18 `narrowRequired` (lowered with stop
  code 107; no source syntax yet), and C08 `bindAxiomOpt` with a value. C08 void and fallible optional binders
  now have connected lowering cases and accepted-image/outcome witnesses; lead validation of this completion is pending.
  - **C09/C12 branch inventory before the round-one merge:**
  - **Stage-0 refusals with their missing step (C09/C12 line):**
    - C08 void `bindAxiomOpt` and `bindAxiomOptElse` (payload `none`): refused; lowering correctness lemmas missing.
    - C08 `axiomCallElse`: no source syntax; statement calls must end in `;`, and `else` exists only for bindings.
    - C11 `retScoped`/`retWhyScoped`: refused; scope unwinding is not lowered to Stage-0 IR.
    - C11 `by consuming`: source export and its generic elaboration arms are implemented on
      `front-consume`, UNBUILT; the lead must check the connected pipeline.
    - C17 `const` functions: no certified replacement of call sites by the compile-time value before export.
    - C10 RW locks: reader-wait liveness remains open.
    - C09 owner flows: mint (`mints`) and handback moves (`moves`) elaborate with
      witnesses and refusals (c09-mint, lead to build). Body-level `retires Mark;` now exports
      to `Stmt.retires`, removing exactly one held mark; owner `consumes` uses terminal moves
      (`after := none`), ordinary C16 consumption uses the same retire statement. Positive call/retire
      and negative drop/loan/unheld/double-retire witnesses, plus the Stage-0 image witness, are
      implemented on c09-retire, UNBUILT (lead checks). The dynamic escrow replay and C08
      software-call/root-once mint admission remain open; Stage 0 still refuses mint effects.
    - C18 end-block-level required allocation and allocation with `else`: still refused; connected lowering remains open.
    - C12 `own@…` through borrowed marks: owned reads/writes (`thruOwn`/`assignThruOwn`, same carrier
      as `thru`/`assignThru`) and call-scoped `borrows` loans (`OwnerFlow.loans`) lower end to end, with the
      borrow/return witness and the no-mark/forged-loan refusals (c12-own, lead to build). The Stage-0 Senke
      side (`lowE`/`lowS` arms reusing the plain slot paths, generic `lowE_ok`/`lowS_ok` arms, `OwnProben`
      read-then-write image witness) is added on `s0-c12own`, unbuilt; lead to check. Open: byte/raw/entry
      targets (still refused: no live grant/history interface yet).
    - C14 `profile`/`requires profile`: the checked binding (`ProfileBinding`, admitted by `bindungB`) is now
      carried from `Prepared` through `CanonicalSourceProgram` into `Emitted.Correct`/`irBild_correct`, with inconsistent
      bindings refused by name. Open: elaboration of admitted profile blocks (still refused at the Stage-0 gate).
    - C14 `aligned`/`section`: relative grid (`wordAlign`, `globStarts`) plus the conditional absolute placement
      lemma (`layU_ga_lcm_dvd`, connected to `irBild_correct` via `Emitted.Placed`) are proved, with an aligned-16
      witness; named sections are refused by name (flat runner image has no relocation policy). Open: the unconditional
      loader-base duty (`Nat.lcm 8 N ∣ b` for every positive N stays an explicit hypothesis).
    - C14 `entrust`: refused by the model (no isolation/call service).
    - C07 fallible indirect calls: Stage-0 arms being added.
  - **Stage-0 refusals (source audit 2026-11-03).** Exact constructor tables, checks, proof connections and
    refusal witnesses: [measured coverage](dokumente/IR-COMPILATION-LANES.md#stage-0-coverage-measured-2026-11-03).
    No builds were run for that audit. Remaining refusals include:
    - Scoped returns inside lock bodies. `consumeTraverse` follows `verbrauchLauf` in Stage 0
      (`consumeTraverse_case`); its consuming source producer, typed contexts, metadata binding and source witness
      are implemented on `front-consume`, UNBUILT. Missing decreases/touches, absent/ambiguous/non-self edges,
      invalid measures, insufficient write effects and leave/next of the consuming binder remain named refusals.
    - Unrepresentable tag dispatch / byte spans, oversized folds/code/addresses,
      and unsupported entry-snapshot subtrees. Aggregate payload and wide byte implementation checks are pending below.
    - Foreign gates without an explicit selected binding
      (named refusal). Optional value/void binders and fallible indirect bindings have IR arms.
    - **Foreign result completion (`s0-foreign`, 2026-11-03; lead validation pending):** fallible Bool,
      reference and nominal region-capability answers, plus multiword answers through explicit C14
      `result area REGISTER`, have implementation/proof/witness declarations connected to the actual
      lowering path. The result area uses `copyValue_run`; the exact provider write footprint is a
      binding/user-logic duty. Missing areas and overlapping hidden/source registers remain named refusals.
      Open: lead checks of the changed grammar/parser/printer modules, Stage-0 dependents and witnesses,
      standard-axiom/guardian validation and the executable Bool probe. Area profiles combined with
      pointer-buffer arguments remain refused. Supplying/mapping fresh region storage and original-source
      provider contract admission are not discharged by capability transport.
    - Fallible indirect statement-else source syntax is implemented, including expression AST, printer,
      generic round trip and export to `Stmt.callIndElse`; acceptance/refusal witnesses await the lead build.
      Fallible void pointer statements and pointer expressions beyond locals/function references remain refused.
    - Original source metadata without a checked duty binding: invariants, declared costs/scheduling, providers,
      owner-qualified/byte/raw/entry capabilities, shared locks/RCU, residual const/generic calls/module headers,
      counterprobes and annotated placement. Static-arena allocation has connected narrowing/store arms.
      Residual generic calls and module-template/use headers now go through the expansion-aware Stage-0 gate
      (`syntax-s0`, needs the lead build): the gate checks the expanded unit, with the expansion certificate.
    - Boot/device-register forms (outside userspace scope), entrust, hardware entry obligations, named sections and
      incompatible runner ABI; supported TESTBUILD selection and consistent profile preparation are present.
  - **C18 static-arena allocation:** canonical required/else lowering and source-image witness declarations exist.
    The 2026-11-03 source audit finds the original metadata gate still rejects allocation-with-else; required
    immutable unannotated allocation is admitted. The witnesses were not rebuilt in that audit.
  - **Additional branch implementation notes (lead checks pending).**
  - **Stage-0 refusals with their missing step:**
    - C08 `axiomCallElse`: no source syntax; statement calls must end in `;`, and `else` exists only for bindings.
    - C11 `retScoped`/`retWhyScoped`: refused; scope unwinding is not lowered to Stage-0 IR.
    - C11 `by consuming`: refused by design.
    - C17 `const` functions: no certified replacement of call sites by the compile-time value before export.
    - C10 RW locks: reader-wait liveness remains open.
    - C09 owner flows: escrow simulation in progress.
    - C12 `own@…`, byte/raw/entry targets: ownership and target support still missing at the Stage-0 gate.
    - C14 `profile`/`requires profile`: the checked binding (`ProfileBinding`, admitted by `bindungB`) is now
      carried from `Prepared` through `CanonicalSourceProgram` into `Emitted.Correct`/`irBild_correct`, with inconsistent
      bindings refused by name. Open: elaboration of admitted profile blocks (still refused at the Stage-0 gate).
    - C14 `aligned`/`section`: relative grid (`wordAlign`, `globStarts`) plus the conditional absolute placement
      lemma (`layU_ga_lcm_dvd`, connected to `irBild_correct` via `Emitted.Placed`) are proved, with an aligned-16
      witness; named sections are refused by name (flat runner image has no relocation policy). Open: the unconditional
      loader-base duty (`Nat.lcm 8 N ∣ b` for every positive N stays an explicit hypothesis).
    - C14 `entrust`: explicit `via SERVICE` source bindings now resolve declared C08 foreign
      contracts, export software provenance and their exact requires/ensures, generate ordinary
      fallible wrappers, and retain every descriptor in canonical and Stage-0 admission.
      The source-to-image witness and named refusal twins are written (THEOREM-MAP §150).
      Open: lead compilation, witness reduction and standard-axiom checks; no build was run by
      the implementation worker. Additional source region inputs remain refused until the
      source adapter can retain each transferred capability with its resolved owner resource;
      register/privileged handover and unknown ABIs stay refused. `Spec.lean` is unchanged.
    - C07 fallible indirect calls: Stage-0 arms being added.
  - **C18 static-arena allocation:** required allocation and allocation with `else`, at block and end-block level,
    already expand into the connected `lowB_ok`/`lowEnd_ok` narrowing and store arms. Source-image witnesses now
    cover both levels and the last fitting slot; semantic witnesses cover success, ceiling preservation and required
    capacity failure (stop 107). Duplicate counter-depth arms and two witness import paths are corrected.
    Open: the lead's Lean checks of these witnesses and the connected pipeline; the implementation worker ran no builds.
  - **Conditional refusal follow-up (`s0-gaps1`, 2026-11-03; lead checks pending).** The original metadata
    gate now admits immutable unannotated static-arena allocation with an explicit else, recursively checking
    that continuation. `EndAllocWitness` connects original-gate acceptance, canonical source and image correctness.
    Block/end `narrow` and `narrowRequired` reuse the complete-span interval kernel; empty target intervals
    select failure, and required failure remains stop 107. Wide `istSome` uses the canonical presence tag.
    Generic proof arms and accepted witness declarations cover these changes; no Lean or execution checks
    were run by the implementation worker. Long `strCat` now copies into a fresh complete span at
    the runtime first length; long/mixed `strLt` uses the descending presence/byte-key scan.
    Generic helper proofs are attached to `lowE_ok`; typed acceptance/model witnesses and
    `str-span-cat-order.gab` cover both operand orders, prefixes and different lengths.
    Only actual capacity/frame/code representability checks remain on these string paths.
    Open: lead Lean validation of the changed closure, axiom checks and runner regression;
    the implementation worker ran no Lean, Lake, compiler, runner or guardian checks.
  - **Computed wide `floatOf` implementation (`s0-gaps1`, 2026-11-03; UNCHECKED).** The binary64
    compiler hook now normalizes the complete integer magnitude with balanced leading-position
    comparisons, retains a 56-bit prefix with sticky and reuses the existing IEEE nearest-even packer.
    Small runtime values inside wide intervals use the proved scalar continuation. Generic field,
    rounding and hook proofs connect through `blockFloatOfComputed_case` and `lowB_ok_floatOf`;
    exponent overflow is rejected before the ordinary range test and remains stop 107.
    `WideFloatProbe` declares accepted image fixtures for ties, sticky tails, signs, carry, maximum
    finite, overflow and small values in wide intervals, plus a generic-hook variable witness.
    Open: lead single-module Lean checks, axiom audits, image acceptance and runner execution.
    No new compiled-coverage measurement is claimed. The implementation worker ran no Lean,
    Lake, compiler, runner or guardian checks.
  - **Aggregate sums and byte spans (`s0-gaps1`, 2026-11-03; UNCHECKED).** Actual `.case` and
    `onTag` lowering now embed and bind complete product/float/string/wide payloads using the
    shared aggregate encoding, with recursive validity and zero padding; packed integer tags
    retain `sumOff`. Generic construction/dispatch proofs connect through `lowE_ok` and
    `lowS_ok_onTag`; constant initialization preserves the selected payload's validity too.
    `getBytes` captures its start once and emits <=8-byte kernels per canonical limb. `putBytes` captures the full value
    and index before iterating the existing write kernel; chunk-count induction preserves
    byte order, overlapping-copy reads and the complete write trace. The actual dispatch /
    wide-byte paths keep only ordinary layout/frame/code checks and an explicit `<2^31`
    tag-count / byte-span representability gate. Accepted-image witness declarations cover
    all payload kinds and 9/13/16/17-byte boundaries, high limbs, zeros and overlap; boundary
    refusal declarations pin the wrappers. Coverage rows are updated as a source audit only.
    Open: lead Lean checks of the changed dependency closure, standard-axiom audits, witness
    image acceptance and runner execution. No Lean, Lake, compiler, runner or guardian ran.
- **Lean module system and the 500-line limit (2026-11-01).** Every Lean file becomes a module and drops below 500 lines
  (AGENTS.md). Measured 2026-11-01 with grep/wc: 0 of about 1500 Lean files start with `module`; 214 files have 500 lines or
  more (194 in `grammatik/`, largest `Parser/Elab/Uebersetze.lean` with 6455). No `grammatik/` change until this is merged.


- **Phase A step 4 (the combined `Spec.lean` diff "M8": arena plus payload) is PAUSED** (Simon, 2026-10-19). Nothing is merged or pushed.
  The arena foundation (M3) is green on Lean/Mathlib 4.35.0 (820 jobs); the full library is not (7 modules, one a real heartbeat
  timeout in `ArenaErkZeugeBaum.lean`); the payload half still lacks its global history induction (O21 in the plan). The work sits in an
  uncommitted worktree under `.claude/muse-arbeit/kratz/spec-arena-recovery/`.
  Exact state, outstanding obligations and resume order: `PLAN-DYNAMIC.md`† §8a, part H.

## 0. Order of work (Simon, 2026-10-17)

Strictly in this order. Every step is Lean-first (model, then exporter, checker, compiler), no legacy, no German words in syntax.

### Phase A: dynamic data structures and their invariants

Plan: `PLAN-DYNAMIC.md`† §8a. Covers O4-O6, O11, O14, O20, O29.

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
   D1-D6 and the checker rule R0-R4 (proposed in `PLAN-DYNAMIC.md`† §11, four decisions for Simon in §11.5); no concrete W/GX fixture
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
   ISA-neutral `Code` and no CPU model. Plans: `PLAN-TRANSLATION-VALIDATION.md`† §9a/§9b.
2. **Model/export gaps behind existing lowerings:** `boot` semantics; the `entrust` source/service binding; aarch64 `vector`/`via` meaning; port space and `asm` (LLVM
   lowerings exist without a model).
3. **Remaining O-items:** interrupts and cores (O19 rest), arenas under concurrency (O20), `child` without a model (O21), gate
   preconditions (O23), strings (O24), source forms without a complete G export (O27), linking (O28), regions in G (O37). See §2.
4. **Termination, waiting bounds, fairness, stack depth,** floats beyond the IEEE kernel.
5. **Zero-cost abstractions without objects** (owner, 2026-11-02; after the C packages): adapters, embedding, specs,
   generics, parametric modules, `tagged … by`, `dyn`, O43, then the slow-code diagnostics. Plan:
   [ABSTRACTION-SYNTAX-PLAN.md](dokumente/ABSTRACTION-SYNTAX-PLAN.md).
6. **Benchmark against GCC `-O3`:** only after the compiler lowers much more and strong optimisation is in (Simon).
7. **Housekeeping:** see §3 (legacy cleanup); file split to an average under 500 lines (`instrumente/teile/lean-teilen.py`); the frozen
   Isabelle `.thy` set.
8. *Done 2026-10-18 (Simon's decision):* comments as in most languages: `//`, nesting `/* */`, `///` doc comment as trivia
   (`Token.doku`); the `--` comment is removed everywhere. Lean first, then `lex.rs`, then ~1270 files (THEOREM-MAP 83).
   Left: a formatter or doc tool that reads `Token.doku`/`Art::Doku`.
9. **Adequacy of the generated test set** (Simon, 2026-10-18). Goal: if a program-neutral checker/compiler handles every generated test
   program, it handles all valid programs correctly. Result in Lean (`grammatik/Grammatik/Adaequanz/`, `CHECKER.md`† §16, THEOREM-MAP 85):
   program-neutral alone admits NO finite test set (`kein_endlicher_test`). With a state bound the W-method set is sufficient and
   astronomically large for Gabbro. For the class "verdict = conjunction of local premises and whole-program patterns" the answer is exact
   and small: one single-fault program per isolable refusal cell plus valid programs covering the accepted cells (124 premise cells, 146
   child-position cells, at most 4 540 pattern cells, independent of program size). EXACT CELLS (2026-10-20, `CHECKER.md`† §16.6a): the global patterns are 124 cells with 20 bad, not 4 540; `gen-zellen` witnesses 75 of 104 good and 9 of 20 bad cells strictly (valid program / single-fault program), from a generator that emits each program with its proof (`Gutes`, `Schlechtes`), against the Lean model only (the Rust checker is never an oracle). Open: the local refusal cells need source mutants,
   so the G-to-source printer of Track P; the coarse accepted cells (4 of 459 covered); the metamorphic tests for hypotheses H1-H8.
10. **Refinement down to the binary: EETV-R version 3** (the ONLY refinement item; Simon's design, 2026-10-18). LLVM stays an UNTRUSTED
   producer; Lean checks the binary against the certificate through a small UB-free core K, bridge steps justified by Gabbro facts, and a
   backend validator over chip-learned instruction semantics. Nothing built; the first steps start with extending `Code`. Full design,
   hardware contract and research risks: `PLAN-TRANSLATION-VALIDATION.md`† §9c.
11. **One-off corpus of ALL generated programs** in a git submodule (at most 30 GiB, counting-and-unranking generation). Not started.
    `dokumente/PLAN-LONG-RANGE.md` §1.
12. **`async fn` and `.await`** as a verified state-machine transformation (sugar; machine G and `Spec.lean` stay untouched). Not started.
    `dokumente/PLAN-LONG-RANGE.md` §2.
13. **Self-hosted checker and compiler in Gabbro** (Simon, 2026-10-25): Lean specifies and proves, Gabbro computes (checking,
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
- **Open:** `free` across function boundaries (Lean audit and plan: `PLAN-DYNAMIC.md`† §12); aliases outside the tracked ownership discipline; complete `ArenaForm`/`DynForm` export and
  the G form of the newer memory statements. No checker refusal or source obligation was relaxed. CPU/final-byte refinement is §5.
- **Evidence:** `LLVM-BACKEND.md`†; coverage is the Lean constructor/field register, checked by
  `python3 instrumente/teile/llvm-modelldeckung.py` (examples never define it).

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
- **Front end, exchange (2026-10-26).** Open: exchanges at table elements (`REGEL[r]`: atomic tables have no G form,
  model work), `update` bodies with statements other than guarded `return`s; guard narrowing against literals, named
  constants and number locals/parameters by their range (also negated and under `and`/`or`), not against other
  expressions; a body ending in a `match` or a nested `if` gets an unreachable
  trailing return of a default value of its result type (refused for result types without one).
- **End-block forms (2026-10-26).** `Endblock.narrow`/`exchange`/`ite` (THEOREM-MAP 102): the generator does not draw
  them (size `unendlich`); arena ownership (`chkE`) and the cost mirror (`spiegelE`) refuse them; the Rust exporter
  does not construct them.
- **Stage 0 compilation (2026-10-31, THEOREM-MAP 105).** The former Lean source runtime is removed; no work is
  done on that execution path. Lean stage 0 only translates Gabbro into the IR `S0IR` (§2.1); a formally verified x86-64 machine-code runner runs it (§2.2), its
  instruction model written anew and tested against the CPU; 64-bit words everywhere; multithreading required. Target: `gkomp` compiles its own ≈ 500 000 lines on the runner in
  under one hour. Built (2026-10-28, `runner/`): `S0IR` (24 opcodes, `spawn` on real OS threads, every system call),
  the x86-64 subset with its CPU tests and x86-TSO litmus tests (stage 8 of the Lean guardian), the runner's bytes,
  `runner_entry_tso`/`runner_entry_sc` from the process's first instruction (the loader proved) for any number of
  threads, with the witness on the real file. Open: `ir_sim` (S0IR against the thread machine) and the lowering; the provider freshness of the open region in the model; the front end and the subset gate
  over the whole language; the Rust exporter `lean_g.rs` writes `aschreibt := false` for every gate and refuses a
  gate's `writes` (the model and the Lean front end accept it). The active task is complete Gabbro-to-IR compilation; the assembly runner may be corrected when necessary. The lowering and
  `irBild_correct` now exist for part of the language; current state in `IR-COMPILATION-LANES.md`, not here.
- **Stage 0: the Lean front end over the whole syntax (2026-10-25).** Measured with a scratch file `grammatik/kratz/Deckung.lean` (not in the tree) over
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
  named assumption `MaskHw` and the refinement `MaskRel.lean` (`PLAN-DYNAMIC.md`† §8a.4, THEOREM-MAP 81). Open: the `Spec.lean` proposal
  (not applied) and its GA twin; composing the `Code` steps with the interleaving of all threads of a core (H3); re-entry and
  handler-on-handler preemption; `Einheit` names no handler; `H102` fires only on `via idt`; no Rust/LLVM emitter for `imsk`.
- **Reader/writer lock (decision 2026-10-18).** In Lean as the layer `RwSchritt` over machine G: exclusion, rank order, no wait cycle, no
  write-write/write-read race (premise `LeserLos`), a `Code` lowering on one state word with refinement `RwRel`, witnesses and planted
  defects (`PLAN-DYNAMIC.md`† §8a.5, THEOREM-MAP 82). Open: the `Spec.lean` diff (mode in G recommended); the syntax (`lock L rank N rw`,
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
  `pub` and the closed export hull are in Lean too (THEOREM-MAP 104); the Rust `N038` still compares short names.
- **O41 (registers as Lean, not as `.tsv`; Simon, 2026-10-20).** `dokumente/llvm-modelldeckung.tsv` is a hand-written list of the model's
  members with an LLVM status per member; it proves nothing, its member column duplicates the total match of `Gen/Abdeckung/Mitglieder.lean`,
  and `instrumente/teile/llvm-modelldeckung.py` checks it against the Lean sources by regex. (`messung/fallen-klassifikation.tsv` was removed with `messung/` on 2026-11-01.)
  Open: the LLVM status as a total Lean function over the constructors (a new constructor stops the build; the status stays a claim about
  `llvm.rs` until translation validation); stage 6 of `pruefe-lean.py` (`gen-abdeckung`) takes its members from Lean, reading no file; delete
  the remaining `.tsv` and the Python script; update `llvm.rs`, `CHECKER.md`†, O27, `pruefe-lean.py`, `pruefe-llvm.py`.
- **O42 (complete test sets M and N; `PLAN-TEST-SET.md`†).** Proved: Theorem 5 `vollstaendig_hinreichend` (a conjunctive checker
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
  **Complete proof plan:** `PROOF.md`† D5,
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
  an element ceiling. Its storage semantics and safety proofs are now in `Bausteine/Arena/Unbounded/`; see `PLAN-DYNAMIC.md`† section 13.
  Whole-program G admission/export, production lowering and the final universality theorem remain open.
  The linked TM2/BF heap backend now preserves and reflects halting and output from allocated input, with OOM separated from normal halt
  and a conditional four-operation bound per BF transition (`PLAN-DYNAMIC.md`† 13.3). This target is the new storage component, not yet G.
  Concrete, value-sensitive G push/pop/free prefixes and a whole finite core-accepted `endet` witness are now proved (`PLAN-DYNAMIC.md`†
  13.4). G's fixed index bound, full source ownership admission and the unbounded whole-program TM2/G bridge remain open.
  G stack operations now carry exact ownership-grant effects (13.5); an actual G `runs until stack-is-empty` loop has the exact
  proved boundary `initialStack.length < passes`, including a core-accepted conditional-class function witness (13.6).

## 3. Checker

- **Legacy cleanup** (fixed rule 2026-10-17: no legacy in compiler, checker, parser). Done: `cnamen.rs`, `N041`/`N046`/`N052` with sentences and
  17 poison probes, 42 dead functions and constants, the Lean folder `CBackend` (22 233 lines, deleted 2026-10-18; tag
  `archiv/c-emitter-2026-10-17`). Open: 13 compiler warnings in `llvm.rs`/`nulpfad.rs`/`certstmt.rs` (two unreachable patterns, the
  link-unit init for constants, never-read fields); the C templates in `schablonen.rs`; comments naming `emit.rs`/C11. Remove, do not rename.
- **Differential harness** (`CHECKER.md`† §12.6). Class (b) is empty over 62 000 generated programs. The groups of class (a) left
  (`ERWARTET_A`: costs, `locks`/`reads` effects, `N511`/`N275` user logic, `const fn`) need Lean components; the model gaps (`return` under
  `locks`, `Endblock` formers, `Block.arenaAlloc` at the top level) are listed there with the exact change. Open rulings: `M104`, `N001`,
  `M133`, `M147`. Track P: 79 % of the generated space is outside the elaboration fragment.
- **Guardian remnants** (four guardians since 2026-10-17). The tree-wide `gabbro prove` run and the E1 comparison (duties manifest) hang in no guardian; the mutation run over the checker
  is dropped without replacement; 8 600 German comment lines in the checker are unguarded. Details: `dokumente/TOOLBOX.md`.
- **O11 (guardless invariant).** A `table`/`group` invariant that no function `maintains` is booked by NOTHING (`N275`-`N277` check only
  anchored ones).
- **Alias / `own`** (built 2026-10-17). `R014` (error) and `R015` (hint) separate pointer roots at call boundaries; Lean has `ParamGetrennt`
  and `ObjGetrennt` with a bridge to `R014`; LLVM sets `noalias` on internal writable pointer parameters. Paper: `A1-OWN-PAPER.md`†.
  Open: records over byte buffers (range objects in the model, `LG005`/`LG001`); the four bridge hypotheses (`ParamVerschieden`,
  `RechteOk`, `HerkunftTreu`, `FrischNeu` only for the model allocator) and the checker's `let` run in Lean; `R004`/`R007` as special cases
  of `R014`; `noalias` is no Lean judgment (O27).
- **O26-Rest (foreign lock primitives).** Own primitives are checked (`N481`-`N483`); foreign ones stay assumed (weak memory assumes
  acquire/release).

## 4. LLVM backend

Full table: `LLVM-BACKEND.md`† §5.

- **Lowerings without a Lean model** (2026-10-17; rule: language follows the Lean model). Built, evidenced only by text/qemu: aarch64
  `entry` (the meaning of `vector`/`via` on aarch64 is the lowerer's reading; `LANGUAGE.md` and the model are silent), `masks irqs`, the
  x86_64 port space, assembler bodies. REFUSED because lowering would invent semantics: `boot` and `entrust`. To do: put the aarch64
  meaning of `vector`/`via` into the model, then connect the `boot` model and bounded `entrust` service export.
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

1. **A complete Lean model of a CPU.** Without it no refinement: the long pole. The Sail-Arm plan (`ARM-PLAN.md`†) and the `arm/` model were
   retired on 2026-11-01; no CPU model is being built now.
2. **And more:** per-access bridge (goal to W/GX simulation), gate and entry lemmas per target (raw instruction, `_start` with stack, state,
   exit/`never`), O28 link closure, O26 foreign orderings.
3. **Automatic for all programs.** No per-program step by hand. That makes the chain more expensive than O27, not cheaper: O27 widens the set
   of judged programs one program at a time, while validation must run for ALL of them without help afterwards.

Design of the final validator: `PLAN-TRANSLATION-VALIDATION.md`† §§0-5 and §9c.

## Appendix: closed or removed (ID → reason)

- **Built:** O3, O7, O8 (lane 167), O9, O13, O18 (F10), O31 (rest: build/hardware), O34, O35, O36, O38.
- **O25:** the atomic rely IS the goal (`gabbro_ziel`), closed; the payload half is Phase B item 1.
- **Withdrawn or declined:** O2 (falsifiers without threshold); O15/O16 (priced and REJECTED, zero corpus benefit); O30 (superseded:
  Rust backend plus Lean validator instead of self-hosting; for a front-end-only self-hosted compiler see Phase C item 12).
- **Not a topic of this list:** O10 (measurement layer); O12 (single program, no model case); O32 (hardware/runtime); O33 (process
  bookkeeping); O39 (kernel-module world; count: `N574`-`N577` built, unload window is hardware).
- **Out of scope:** O29 (Simon).

## Round 2 / round 3 compilation follow-up (2026-11-02)

- C01 `prod`, `prodGet` and `prodSet` have actual Stage-0 emitters and generic `lowE_ok` arms;
  ordinary block bindings/assignments reuse them. Product source-image, local build/read/update/read,
  and multiword-field preservation witnesses are included in the package and axiom audit.
  Open: the lead's Lean checks of these connected modules and witnesses; no build was run by the implementation worker.
- The current `Block.float` emitter, generic proof arms and remaining source-float boundary are recorded in
  [the Stage-0 coverage inventory](#stage-0-coverage-inventory-2026-11-03).
- C11: the Gut side and the `rufAt_gut`/`rufAt_treu` migration remain in progress.
- C11 consuming traversal, noninterference (`ni-verbrauch`, 2026-11-03, unbuilt): the relational cases for
  `GRest.verbrauch`/`verbrauchRest` in `kr` and for `kLeave`/`kNext` on `verbrauchRest` mirror the `trav`/
  `travRest` low-equivalence arguments (measure/invariant/member/edge reads from the `nR` footprint, new
  `KRel.opt` congruence for the deterministic `verbrauchWahl` choice); `kNext_rel` takes the residue-form
  premise, discharged at its sole caller. Open: the lead single-module Lean checks of the three touched
  modules; no build was run by the implementation worker.
- C15: per-core accumulator uses elaborate to guarded update/fold bodies whose `add`/`or`/`and` overflow stops with `Logik.kapazitaet` (required narrowing, never a dropped contribution or a neutral restart); admission and link Bools carry the connected core query (`qs`/`aqs` default to `[]`, shadowing refused). The hardware provenance of the generated core-query axiom now elaborates (THEOREM-MAP §135): `accumulates … assume a` names the assumption, the `n#query` wrapper binds the foreign query, `declOf` sets `axHerkunft`/`axBeleg`, and the fixture (`assume` + `accumulates` + update + read) is accepted by `Akzeptiert` with the query list. Open: the lead build of the branch.
- C09: escrow call/return witnesses now share a concrete machine fixture with one push and one return (THEOREM-MAP §132); the lead still needs to check the unbuilt witness modules.
- C16/C02 round-3 work remains open. Compact implementation inventory (16 items, grouped from the designs in `IR-COMPILATION-LANES.md`):
  1. C02 lossless library-call arguments and region tokens.
  2. C02 resolved translator/library identity and export metadata.
  3. C02 typed input schemas and sound decoders.
  4. C02 canonical translator map and payload typing.
  5. C02 source-bound translation certificates.
  6. C02 pure execution, termination and effect/cost obligations.
  7. C02 immutable payload initialization and ordinary call expansion.
  8. C02 connected source/image correctness and refusal witnesses.
  9. C16 declared-check identity and checked expansion (done on `c16-a`, THEOREM-MAP §178: `CheckIdentitaet`, `identitaet_aus_zulassung`, elaborated identity record).
  10. C16 generated producer/probe/gate functions (done on `c16-a`, THEOREM-MAP §178: Duty in probe `nimmt`/`gibt` and wrapper `nimmt`, `bool` wrapper forwarding).
  11. C16 actual measurement samples and floor results (done on `c16-a`, THEOREM-MAP §178: `messWert`, `bodenHalten`, `berichtDeckt` with witnesses).
  12. C16 completed reports for both verdicts and linear Duty discharge (done on `c16-a`, THEOREM-MAP §178: `CheckAbschluss`, `CheckEntladung`, `CheckEntladungErfolg` with both-verdict witnesses).
  13. C16 report/token provenance through call push and normal return (done on `c16-a`, THEOREM-MAP §179: `BerichtHerkunft`, `HerkunftSchritt`, `rueckUrteil` over `RufEreignisF` with fixture witnesses and error-channel refusals).
  14. C16 G/GX replay and ownership conservation (done on `c16-a`, THEOREM-MAP §179: `CheckErhaltung`, `erhaltung_kreislauf`, `replayEintrag` with witnesses).
  15. C16 counterprobe binding, artifact identity and measured status (done on `c16-a`, THEOREM-MAP §179: `SondenEindeutig` with exact decider, `SondenBindung`, `Gemessen` with measured/unrun/stale witnesses).
  16. C16 connected export/Stage-0 correctness with emitted sample work (implementation attempts on `c16-a`/`c16-close`, THEOREM-MAP §§179–180; not yet measured green): derived `uCheckDecls` with a real declared Duty, source-to-`lowerAllg`-to-`checkB`/`AkzeptiertX` witnesses for the minimal check, passing/failing local floors, a bound ordinary counterprobe and infallible/fallible C08 foreign gates. `Pruefung/Lauf/Recording` now emits private typed return reporters whose actual arguments are the captured samples, separately evaluated floors over those snapshots and written verdict. `Lauf/History` decodes G/GX's saved `Env` values, appends evidence at the probe return and retains it after consumption; replay proves the recorded sample/floor origin, with distinct ghost activation points. The previous supplied-report fold is deleted. C14's explicit `--check CHECK GATE` selection generates a driver and physical consumer before the actual Stage-0 lowering: the producer threads its invocation permit, the selected consumer invokes the wrapper then retires its returning Duty with empty outputs on both channels. Foreign errors are explicitly retired and rethrown with their exact reason identity. New source/acceptance and history witnesses cover the complete cycle, unconsumed Duty, double consumption and fabricated samples. Counterprobe adapters and exact-image `SondenNachweis`/`sondenNachweisB` remain required; unrun never means passed. `Lauf/Treue` adds generic event/whole-log conservation and the completed-history `CheckTreueG`/GX attachment; the Stage-0 emitted-program theorem retains the same generic IR execution certificate. Open: lead compilation of all changed modules/importers, validation of these generic attachment attempts, axiom checks and guardians. The round-one merge retains the corrected `bericht` evidence field; no additional `Spec` or owner-flow change is made here. Parameterized gates and ordinary reason-channel gates retain their existing named refusals because no argument/failure policy is declared. No final IR execution or external measurement is claimed.
- Generic functions (§5.2, check model A): connect parser, instance closure and exporter;
  `Parser.Elab.Generic.Substitution` supplies preliminary surface substitution and C17 argument evaluation.
  On `syntax-s0` (2026-11-04, needs the lead build): `Stage0.Frontend.ExpansionGate` checks the expanded
  unit with the expansion certificate (`expansion_gate` ties acceptance to the elaborated unit), and
  source-text-to-image witnesses cover generics, parametric modules, tagged dispatch and `dyn`
  (THEOREM-MAP §§138-141). Open: the lead build of the branch.
- Range folds (§4.4, step 1b): generalized on `syntax-s0` (2026-11-04, needs the lead build) beyond the
  direct integer add-fold return: arbitrary literal bounds, `min`/`max`/`and`/`or` folds and nested folds
  over array variables, by expansion to the existing traverse forms, with the `expandNested_ok`
  elimination theorem and source-text-to-image witnesses (THEOREM-MAP §142). Closed on `syntax-s0`
  (needs the lead build): nested folds over table row projections (traverse over the table domain,
  value type inferred from the row expression, one loop per collection) and folds outside direct
  returns (`let` bindings and subexpressions hoist to a fresh accumulator loop before the statement,
  with order-shape and freshness-gate theorems), with front-end and image witnesses. Open: symbolic
  short bounds, nested float elements, provider-backed tables and folds in contract/cost clauses,
  constant initializers, type bounds and traverse/lock headers still refuse.
- C02 items 1-4 on branch `c02-a` (2026-11-03, needs the lead build): `Logik/Vertraege/UebersetzungDecoder.lean`
  (decoder soundness, immutable payload typing, expansion shape, token-grammar refusals) and
  `Parser/Stmt/LibraryIdentity.lean` (payload position, key correspondence, head normalization,
  translator-free expansion, qualifier selection, nested-region round-trip), wired into `Alle/Teil1`
  (THEOREM-MAP §136). Items 5-16 stay open.
- C02 items 5-8 on branch `c02-a` (2026-11-03, needs the lead build): `Logik/Vertraege/UebersetzungReinheit.lean`
  (pure execution, termination, effect obligations), `Parser/Stmt/LibraryZertifikat.lean` (recomputed
  certificate identity, Rust-output cross-check), `Parser/Stmt/LibraryErweiterung.lean` (actual-path
  expansion identity, purity and resolution refusals) and `Parser/Stmt/LibraryAnnahme.lean` (end-to-end
  acceptance of the unqualified call, expansion ordinariness through the generic lowering), wired into
  `Alle/Teil1` (THEOREM-MAP §137). Items 9-16 stay open.

## Stage-0 coverage inventory (2026-11-03)

Code-reading inventory at `25d1da48044bf96eb657385e54b39fdff2111aba` (`s0-inventar2`, integration snapshot).
Updated by code inspection on `front-gaps1`: scoped returns, indirect discard-else and foreign block/end-block binders now have producers
and preservation/source-witness arms; all await the lead build.
Integration correction on `sammel-c3`: retain the already present owned-access lowering/proof arms,
C16 retirement producer and explicit foreign-answer profiles. Original snapshot line references below
remain historical unless a row names its current implementation.
No Lean/lake/build, runner, guardian or executable coverage measurement was run. A **yes** below means an
implementation/proof arm exists in the inspected source, subject to its guards and recursive operands;
it does not certify that this snapshot builds or that every parameterization of that constructor compiles.
Counts are by constructor, not example, operator spelling, type instantiation or helper lemma:
**143 = 64 Expr + 34 Stmt + 22 Block + 23 Endblock; 137 lowered with a connected generic proof arm,
0 lowered without such an arm, 6 without lowering.**
Of the 137, **8 have no connected source producer**, leaving **129 with a source producer and lowering/proof
arms, 0 with lowering but no proof arm, 14 unavailable at the source-to-IR boundary**. Six of those 14 are
out-of-scope device forms; the remaining 8 are userspace gaps. These are structural counts, not a claim
that 129 cases have been compiled successfully. The 13 `Ty` constructors below are a separate representation
inventory and are not added to the 143 syntax cases. `Ty.index n` is the alias `.int 0 (n - 1)`.

The `front-gaps2` source reinspection annotates individual rows below (no Lean/build execution):
finite float narrowing and labelled breaking export were added; breaking remains refused by the
unchanged invariant metadata gate. Retirement already had a producer, so its old row was stale.
Advance markers now preserve declared stage orders and use checked adjacent transitions; unstaged
marks still have no successor. Missing check-statement and byte-span syntax is
identified explicitly. The later `front-floatof` change adds the documented integer-to-float conversion
export. The original snapshot totals above have not been remeasured.

Locations use these exact file abbreviations (a suffix `:N` is the source line; e.g. `E:64` means
`stage0/Stage0/Senke/Ausdruck.lean:64`):

- `E` = `stage0/Stage0/Senke/Ausdruck.lean`; `A` = `stage0/Stage0/Senke/Anweisung.lean`.
- `Q` = `stage0/Stage0/Senke/Ausdruck/Satz.lean` (`lowE_ok`, line 46).
- `P` = `stage0/Stage0/Senke/Anweisung/Satz/Teil5.lean` (`lowS_ok`, line 53;
  `lowB_ok`, line 168; `lowEnd_ok`, line 232). `Q:N`/`P:N` identifies the constructor's arm of that named theorem.
- `Gk` = `grammatik/Grammatik/Parser/Elab/UebersetzeAllg/Teilk.lean`;
  `G3V` = `grammatik/Grammatik/Parser/Elab/UebersetzeAllg/Teil3Values.lean`;
  `GI` = `grammatik/Grammatik/Parser/Elab/UebersetzeAllg/Eingebaut.lean`.
- `Hk` = `grammatik/Grammatik/Parser/Elab/UebersetzeAllg2/Teilk.lean`.
- `J/name` = `grammatik/Grammatik/Parser/Elab/UebersetzeAllg3/name.lean` (including the split `Returns` module).
- `Uk` = `grammatik/Grammatik/Parser/Elab/Uebersetze/Teil/Teilk.lean`;
  `U5R` = `grammatik/Grammatik/Parser/Elab/Uebersetze/Teil/Teil5Rest.lean`.
- `T` = `stage0/Stage0/Senke/Tor.lean`; `L` = `stage0/Stage0/Senke/Ausdruck/Aggregat/Layout.lean`;
  `V` = `stage0/Stage0/Senke/Ausdruck/Aggregat/Werte/Encoding.lean`.
- Helper paths beginning `Old/`, `Aggregat/` or `Quant/` are relative to
  `stage0/Stage0/Senke/Ausdruck/`; `Typen/` and `Syntax/` are relative to
  `grammatik/Grammatik/Kern/Syntax/`.

The proof connection is the actual compiler path, not a witness-only import: `Compiler.compile`
(`stage0/Stage0/Compiler.lean:48`) calls `lowerAllg` and `OldSource.restore`, then checks `OldSource.accepts`.
`compile_source_program` (same file:149) identifies that canonical program. `IRBild.emit`
(`stage0/Stage0/IRBild.lean:44`) passes it to `Senke.bild`. `lowFun`
(`stage0/Stage0/Senke/Funktion.lean:41`) calls `lowE`, `lowPost` and `lowEnd` (body at line 47).
`Umgebung.lean:6` imports `Ausdruck.Satz`, `Stopp.lean:10` imports `Umgebung`, and the statement path
imports `Stopp` (`A:19`); `Anweisung.Satz` publicly imports its
`Teil1`–`Teil5`, including the mutual `lowS_ok`/`lowB_ok`/`lowEnd_ok`. `lowFun_spec`
(`stage0/Stage0/Senke/Rekursion.lean:20`, calls at :130 and :200) uses these generic proofs;
`start_ok` (`stage0/Stage0/Senke/Start.lean:120`, call at :148), `bild_ok`
(`stage0/Stage0/Senke/Images/BildSatz.lean:445`) and `bild_ok_u`
(`stage0/Stage0/Senke/Welt/Anordnung.lean:13`) carry them to `Emitted.correct`
(`stage0/Stage0/IRBild.lean:108`) and **`irBild_correct`** (same file:180).
Its execution conclusion is conditional on runner `Kern`/`CloneOK`, gate/view contracts, initial image/world,
frame/code bounds and successful emission; it does not prove total language coverage or source user duties.

| form | front end | Stage-0 lowering | generic proof | refusal reason |
|---|---|---|---|---|
| `Expr.lit` | yes, G5:33 | yes E:64, arbitrary integer words | `lowE_ok`, Q:102 | — |
| `Expr.tru` | yes G5:295 | yes E:66 | `lowE_ok`, Q:113 | — |
| `Expr.fls` | yes G5:296 | yes E:67 | `lowE_ok`, Q:118 | — |
| `Expr.var` | yes G3:63 | yes E:68, complete value copy | `lowE_ok`, Q:123 | — |
| `Expr.glob` | yes G3V:26 | yes E:197, `globalValueC` | `lowE_ok`, Q:354 | world layout/address and complete-value load guards |
| `Expr.slot` | yes G3:134 | yes E:198, `slotValueC` | `lowE_ok`, Q:357 | world layout/address guards |
| `Expr.thru` | yes G3:77 | yes E:200, resolved table/index; capability is ghost | `lowE_ok`, Q:357 | world layout/address guards |
| `Expr.ptrOf` | yes H2:214 (pointer argument branch) | yes E:196, ghost zero | `lowE_ok`, Q:343 | only declared table capabilities; no raw address |
| `Expr.fnref` | yes J/Seq:205, J/Rest1:139 | yes E:195 | `lowE_ok`, Q:112 | E:195: `else none` if function address is not `lit32` |
| `Expr.oldG` | Stage-0 restores numeric source old(global); `Old/Source.lean:43` | E:222 current-world reads; postconditions use entry snapshots | `lowE_ok`, Q:458; `lowEnsAt_ok`/`lowEns_ok` | E:222: `else none` when `currentOld = false`; handled by `lowEnsAt`, not silently current state |
| `Expr.oldS` | yes G3:143 | E:223 current-world reads; snapshot emitter for ensures | `lowE_ok`, Q:460; `lowEnsAt_ok`/`lowEns_ok` | E:226: `else none`; `Old/Code.lean:50`: `else none` for unsupported entry-index/column snapshot |
| `Expr.widen` | yes G2:369 | yes E:69, `resizeIntegerL` | `lowE_ok`, Q:99 | recursive operand/representation guards |
| `Expr.add` | yes G2:350 | yes E:71, scalar or wide add | `lowE_ok`, Q:125 | recursive operands |
| `Expr.sub` | yes G2:354 | yes E:75, scalar or wide subtract | `lowE_ok`, Q:140 | recursive operands |
| `Expr.neg` | yes G3:16 | yes E:85, scalar or wide negate | `lowE_ok`, Q:204 | recursive operand |
| `Expr.mul` | yes G2:362 | yes E:79, scalar or wide multiply | `lowE_ok`, Q:155 | recursive operands |
| `Expr.div` | yes G2:421 | yes E:107, unsigned or wide divide | `lowE_ok`, Q:305 | source requires nonnegative numerator, positive denominator |
| `Expr.rem` | yes G2:438 | yes E:110, unsigned or wide remainder | `lowE_ok`, Q:309 | same source range rule |
| `Expr.sdiv` | yes G2:425 | yes E:113, signed or wide fallback | `lowE_ok`, Q:313 | denominator must exclude zero; minimum-word case uses wide fallback |
| `Expr.srem` | yes G2:442 | yes E:118, signed or wide fallback | `lowE_ok`, Q:317 | denominator must exclude zero |
| `Expr.getBytes` | skipped: SYNTAX.md defines no byte-span expression; Lean `parseSuffixe` (`Parser/Expr/Ausdruck/Teil2a.lean:264`–`:285`) parses one index only | yes E:218, `readBytesWideL` captures the start once; `readBytesWordsL` emits <=8-byte kernels in canonical limb order | `lowE_ok`, Q:419 → `getBytes_ok` → `readBytesWide_ok`/`readBytesWords_ok` | no 8-byte cap; refuses `n ≥ 2^31` before expansion and inherited layout/frame/code failures; whole-span bounds/rights are constructor premises; source export and lead Lean/image checks pending |
| `Expr.band` | yes G2:378 | yes E:123, scalar or wide bits | `lowE_ok`, Q:321 | source operands nonnegative |
| `Expr.bor` | yes G2:395 | yes E:126, scalar resize or wide bits | `lowE_ok`, Q:325 | source width/range rule |
| `Expr.bxor` | yes G2:409 | yes E:130, scalar resize or wide bits | `lowE_ok`, Q:329 | source width/range rule |
| `Expr.shl` | yes G2:463 | yes E:134, scalar or wide shift | `lowE_ok`, Q:333 | source shift-bound rule; not a blanket 64-bit refusal |
| `Expr.shr` | yes G2:478 | yes E:138, scalar or wide shift | `lowE_ok`, Q:337 | source shift-bound rule |
| `Expr.lt` | yes G5:245 | yes E:95, scalar or wide comparison | `lowE_ok`, Q:271 | recursive operands |
| `Expr.le` | yes G5:246 | yes E:89, scalar or wide comparison | `lowE_ok`, Q:240 | recursive operands |
| `Expr.eq` | yes G5:243 | yes E:99, scalar or wide comparison | `lowE_ok`, Q:288 | recursive operands |
| `Expr.fllt` | yes G5:212 | yes E:103, integer comparison of canonical float bits | `lowE_ok`, Q:170 | finite kernel float inputs |
| `Expr.flle` | yes G5:213 | yes E:104 | `lowE_ok`, Q:174 | finite kernel float inputs |
| `Expr.and` | yes G5:303 | yes E:105 | `lowE_ok`, Q:178 | recursive operands |
| `Expr.or` | yes G5:310 | yes E:106 | `lowE_ok`, Q:191 | recursive operands |
| `Expr.not` | yes G5:314 | yes E:88 | `lowE_ok`, Q:224 | recursive operand |
| `Expr.none` | yes G4:111 | yes E:183, complete option encoding | `lowE_ok`, Q:341 | — |
| `Expr.some` | yes G4:115 | yes E:184, packed or multiword option | `lowE_ok`, Q:350 | recursive index |
| `Expr.istSome` | yes G5:341 | partial E:188 | `lowE_ok`, Q:352 | E:192: `else none` when `n > 2^63` |
| `Expr.case` | yes G5:51, :60 | partial E:193, `lowN` | `lowE_ok`, Q:364; `lowN_ok` | E:193: `else none` unless `sumFits`; E:236: `\| _, _ => none` for noninteger payload |
| `Expr.why` | yes G5:45 | yes E:194, complete reason words | `lowE_ok`, Q:348 | reason index must be in family |
| `Expr.forallSlots` | yes G5:353 (also array/tree expansion) | yes E:208, `quantL` | `lowE_ok`, Q:423; `quantL_ok` | `Aggregat/Hilfen.lean:184`: `else none` if finite unrolled code/index budget fails |
| `Expr.existsSlots` | yes G5:363 | yes E:209, `quantL` | `lowE_ok`, Q:426; `quantL_ok` | same `quantL` refusal |
| `Expr.reaches` | yes G5:280 | yes E:214, `reachesL` | `lowE_ok`, Q:429; `reachesL_ok` | `Aggregat/Hilfen.lean:211`: `else none` if chain code budget fails |
| `Expr.refEq` | yes G5:231 | yes E:215, one-word identity comparison | `lowE_ok`, Q:51 | reference validity/initialization remains required |
| `Expr.slotRef` | yes G3:201 | yes E:216, `slotValueC` | `lowE_ok`, Q:54 | reference validity and layout; provider boundary below |
| `Expr.arrNil` | yes G5:191 | yes E:142 | `lowE_ok`, Q:67 | — |
| `Expr.arrCons` | yes G3V:236 | yes E:143, complete element spans | `lowE_ok`, Q:68 | recursive elements |
| `Expr.arrGet` | yes G3V:186 | yes E:148, direct singleton or `arrGetL` | `lowE_ok`, Q:71 | `Aggregat/Hilfen.lean:245`: `else none` if array empty or element displacement exceeds bound |
| `Expr.arrSet` | yes G3V:218 | yes E:151, direct singleton or `arrSetL` | `lowE_ok`, Q:74 | `Aggregat/Hilfen.lean:258`: `else none` if array empty or element displacement exceeds bound |
| `Expr.strLit` | yes G3V:178 | yes E:155, packed short or padded long value | `lowE_ok`, Q:79 | declared maximum |
| `Expr.strLen` | yes G3V:194 | yes E:157 | `lowE_ok`, Q:80 | recursive string |
| `Expr.strCat` | yes G3V:227 | partial E:160 | `lowE_ok`, Q:82 | E:161: `else none` for `n + m > 1` |
| `Expr.strGet` | yes G3V:189 | partial E:162, short or long string | `lowE_ok`, Q:87 | E:166: `else none` if index interval is not `scalarFits` |
| `Expr.strEq` | yes G5:220 | yes E:167, short/mixed/long paths | `lowE_ok`, Q:91 | recursive operands and helper code bounds |
| `Expr.strLt` | yes G5:222 | partial E:172 | `lowE_ok`, Q:96 | E:173: `else none` unless both capacities are at most 1 |
| `Expr.strWeit` | yes G3V:208, only source widening | yes E:174, short/expand/take paths | `lowE_ok`, Q:85 | source refuses shrinking (`G3V:208`: `else .error "string longer than the maximum"`) |
| `Expr.wenn` | yes J/Kopf:411, guarded atomic update | yes E:218, `wennL` | `lowE_ok`, Q:376 | `Aggregat/Hilfena.lean:68`: `else none` if branch instruction span does not fit |
| `Expr.eng` | yes G5:148 | yes E:202, scalar or wide narrowing expression | `lowE_ok`, Q:393 | recursive operands |
| `Expr.intBuiltin1` | yes GI:83–111 | yes E:219, `BitBuiltin.unary` | `lowE_ok`, Q:454; `BitBuiltin.unary_ok` | typed operation/width, recursive operand |
| `Expr.intBuiltin2` | yes GI:47–125 | yes E:220, `intBuiltin2L` | `lowE_ok`, Q:450; `intBuiltin2L_ok` | typed operation/width, recursive operands |
| `Expr.count` | yes GI:160, G5:400/:427 | yes E:210, `countL` | `lowE_ok`, Q:433; `countL_ok` | `Quant/CountCode.lean:31`: `else none` if finite index/code budget fails |
| `Expr.prod` | yes G5:167 | yes E:211, `prodL`/`lowA` | `lowE_ok`, Q:438; `prod_ok`/`lowE_ok_args` | complete ordered field arguments |
| `Expr.prodGet` | yes G5:175 | yes E:212, field-span copy | `lowE_ok`, Q:441; `prodGet_ok` | recursive base |
| `Expr.prodSet` | yes G5:184 | yes E:213, field-span replacement | `lowE_ok`, Q:445; `prodSet_ok` | recursive base/replacement |
| `Expr.thruOwn` | yes G3:108/:124 | yes E:212, `slotValueC`, same carrier as `thru` | `lowE_ok`, Q:359 (unbuilt) | owned resource and slot-layout guards remain required |
| `Stmt.assignSlot` | yes H1:219 | yes A:88, `slotStoreC` | `lowS_ok`, P:83 | layout/store guards |
| `Stmt.assignThru` | yes H1:182 | yes A:92, resolved table/index | `lowS_ok`, P:84 | layout/store guards |
| `Stmt.assignGlob` | yes H3:103 | yes A:80, `globalStoreC` | `lowS_ok`, P:79 | layout/store guards |
| `Stmt.putBytes` | skipped: SYNTAX.md defines no byte-span store statement; `Parser/Stmt/Anweisung/Defs2a.lean:31`–`:83` has ordinary place assignment only | yes A:83, `putBytesL`/`putBytesWideL`; captures value and start before all chunk stores | `lowS_ok`, P:122 → `putBytes_ok` → `putBytesWide_ok`/`putBytesWords_ok` | no 8-byte cap; refuses `n ≥ 2^31` before expansion and inherited layout/frame/code failures; whole-span bounds/rights are constructor premises; source export and lead Lean/image checks pending |
| `Stmt.assignVar` | yes H3:306/:321 | yes A:38, copies complete value | `lowS_ok`, P:66 | A:42: `else none` if parameter/protected span would be overwritten |
| `Stmt.shift` | yes H4:54 | partial A:107 | `lowS_ok`, P:123 | A:117: `else none` unless source/prestate intervals fit signed word; runtime prestate mismatch stops 106 |
| `Stmt.ite` | yes J/Struct:46 | yes A:43 | `lowS_ok`, P:69 | recursive branches/code size |
| `Stmt.onOption` | yes J/Struct:128 | partial A:49 | `lowS_ok`, P:125 | A:58: `else none` for `n > 2^63` |
| `Stmt.onTag` | yes J/Struct:96/:105 | partial A:60, `lowTags` | `lowS_ok`, P:71 | A:65: `else none` unless `sumFits`; A:346: `else none` for tag index ≥256 |
| `Stmt.onWhy` | yes J/Struct:116 | partial A:66, `lowGrund` | `lowS_ok`, P:127 | A:71: `else none` for reason count ≥2^31; A:359 same arm-index bound |
| `Stmt.call` | yes H3:75 | yes A:72, `lowA`/`callC` | `lowS_ok`, P:73 | recursive arguments, image/frame bounds; fallible calls need else form |
| `Stmt.callInd` | yes H4:29 | yes A:59, `lowInd` | `lowS_ok`, P:129 | signature/address/argument guards |
| `Stmt.locks` | yes J/Struct:35 | partial A:176, `locksCode` | `lowS_ok`, P:131 | A:180: `else none` unless `retFreiB body` and jump offsets fit; scoped source returns now export through J/Returns |
| `Stmt.breaking` | added, UNCHECKED: `Uebersetze/Breaking.lean` transports `breaking I { ... }`; `J/Struct` resolves the invariant and emits G | yes A:139, recurse into body | `lowS_ok`, P:113; exporter `uBreaking_exact`/`lowStructStep_breaking` | full source units STILL REFUSED by unchanged invariant cost/runs/by metadata gate; unknown/ambiguous invariant and unclosed scope also refused |
| `Stmt.traverse` | yes J/Struct:59/:69 | partial A:118, `travC` | `lowS_ok`, P:111 | A:123: `else none` if count not signed-word representable |
| `Stmt.retry` | yes J/Struct:80 | yes A:127, `retryC` | `lowS_ok`, P:133 | counter/branch/recursive-body guards |
| `Stmt.forever` | yes J/Struct:138 | partial A:131, `foreverC` | `lowS_ok`, P:135 | A:138: `else none` if reserved/protected counter pair unavailable; bounded compiled passes |
| `Stmt.axiomCall` | yes H3:60 | A:144, `torC0` | `lowS_ok`, P:137 | gate ABI checks T:128–137; only zero-reason form |
| `Stmt.regWrite` | yes H3:349/:366 | refused by wildcard | refusal-only P:146, not an execution arm | A:183: `\| _, _, _, _, _, reserved => none`; device access out of scope |
| `Stmt.transition` | no source producer; device declarations refused U12:322 | refused by wildcard | refusal-only P:147 | A:183: `\| _, _, _, _, _, reserved => none`; U12:322: `.error "device transition without G form"`; out of scope |
| `Stmt.publish` | yes H3:178/:209, payload-free atomics | partial A:83, release store | `lowS_ok`, P:81 | A:87: `else none` unless address and `aggregateFits`; source payload export restricted |
| `Stmt.advances` | yes `uAnw1` (`SAnw.step`) → `UebersetzeAllg2/Marken.lowAdvancesL`, dispatched by H4:`lowStmtL`; `declOf.stufen` preserves declared orders | yes A:140, ghost/no instructions | `lowAdvancesL_exact`; existing `lowS_ok`, P:115 | checked adjacent labels, unique mark, held input stage and no loan; terminal-stage advance refused by name. Three-stage/two-advance source witnesses added; build/axiom/runner checks pending lead validation. Header `advances` clauses remain refused. |
| `Stmt.retires` | yes `uAnw1` → `UebersetzeAllg2/Marken.lowRetiresL`, dispatched by H4:`lowStmtL`; C16 generated `retireMark` retains its declared check Duty producer | yes, ghost/no instructions | `lowRetiresL_exact` (any held stage); existing `lowS_ok`, P:116; `retires_export`/`retires_lower` | ordinary retirement rejects borrowed, unknown, unheld or repeated marks and supports the final stage; generated retirement checks an actually held, declared check Duty. Source witnesses added; build/axiom/runner checks pending lead validation. |
| `Stmt.ret` | yes J/Returns:232 | yes A:77, shared ensures epilogue | `lowS_ok`, P:76 | exact contract-end resources required; local scopes use `retScoped` |
| `Stmt.retWhy` | yes J/Returns:226 | yes A:75 | `lowS_ok`, P:148 | separate reason channel; local scopes use `retWhyScoped` |
| `Stmt.leave` | yes J/Seq:265 | partial A:142 | `lowS_ok`, P:105 | A:142: `else none` if jump not `lit32`; source loop scope required |
| `Stmt.next` | yes J/Seq:268 | partial A:143 | `lowS_ok`, P:108 | A:143: `else none` if jump not `lit32`; source loop scope required |
| `Stmt.assignSlotRef` | yes H1:370 | yes A:103, `slotStoreC` | `lowS_ok`, P:151 | valid provider reference/layout required |
| `Stmt.consumeTraverse` | yes U9:83, J/Struct:109; UNBUILT | yes A:124, `Consuming.lower` | `lowS_ok`, P:155; `ExportQuantifiers.consuming_traversal_lower` | Existing A14 domain/filter and one declared optional-self child edge; explicit `decreases` and `touches consumes` required. Outer invariant/measure, one member binder, two ordered edge binders; no source leave/next of the consuming binder. Shared header reader binds original metadata. Source-text `UebersetzeProben35.consuming_traversal_source_zeuge` added; no Lean/build/execution measurement, lead validation pending. Baseline inventory counts above were not remeasured. |
| `Stmt.retScoped` | yes J/Returns:242 `lowRetStmt` (unbuilt) | yes A:181, `lowRetScoped` | `lowS_ok`, P:161 | exact contract-end resources plus precisely the lexical locks required |
| `Stmt.retWhyScoped` | yes J/Returns:240 `lowRetStmt` (unbuilt) | yes A:182, `lowRetWhyScoped` | `lowS_ok`, P:164 | same exact-resource check; reason must be in the declared channel |
| `Stmt.axiomCallElse` | yes J/CallElse:25 | partial A:145 | `lowS_ok`, P:140 | A:170: `\| _, _ => none`; only VOID or nonnegative integer result, checked reason map and branch bounds |
| `Stmt.callIndElse` | yes J/IndirectElse:11 `lowCallIndElse`, both explicit and shared marker dispatch (unbuilt) | yes, `lowIndElse`/`elseC` | `lowS_ok` | pointer result must be a value; nonempty reason channel, signature conformance and closed ending handler required |
| `Stmt.assignThruOwn` | yes H1:202/:256 | yes A:79, `slotStoreC`, same carrier as `assignThru` | `lowS_ok`, P:85 (unbuilt) | owned resource and slot-layout/store guards remain required |
| `Block.nil` | yes J/Seq:27–29 | yes A:187 | `lowB_ok`, P:181 | — |
| `Block.cons` | yes J/Seq:32 | yes A:188 | `lowB_ok`, P:183 | recursive statement/rest |
| `Block.bind` | yes J/Seq:66/:69 | yes A:192 | `lowB_ok`, P:185 | recursive value/rest |
| `Block.bindCall` | yes J/Seq:90 | yes A:223 | `lowB_ok`, P:187 | ordinary call/frame bounds |
| `Block.bindCallInd` | yes J/Seq:213 | yes A:228 | `lowB_ok`, P:191 | indirect dispatch/signature bounds |
| `Block.bindCallElse` | yes J/Seq:129 | yes A:196 | `lowB_ok`, P:193 | recursive reason handler and rest |
| `Block.bindAxiom` | yes J/Seq:98/:103 | yes A:236, `plainForeignC` | `lowB_ok`, `plainForeignC_ok` (unbuilt) | register answers include checked int/bool/ref/ptr/never; multiword answers require an explicit result area and its provider contract |
| `Block.bindAxiomElse` | yes J/Seq:114 `bindAxElse` arm (unbuilt) | yes A:265, `fallibleForeignC` | `lowB_ok`, `fallibleForeignC_ok` (unbuilt) | nonempty reason channel and closed ending handler; checked errno map; register or explicit result-area answer profile |
| `Block.regRead` | yes J/Seq:245 | refused by wildcard | refusal-only P:209 | A:331: `\| _, _, _, _, _, reserved => none`; device access out of scope |
| `Block.regReadElse` | yes J/Seq:258 | refused by wildcard | refusal-only P:210 | A:331: `\| _, _, _, _, _, reserved => none`; device access out of scope |
| `Block.awaits` | yes J/Seq:237 | partial A:316, one load | `lowB_ok`, P:211 | A:320: `else none` unless address and `aggregateFits`; no waiting liveness claim |
| `Block.exchange` | yes J/Seq:230 | partial A:321, CAS loop | `lowB_ok`, P:213 | A:327/:328: `else none` for code-size/address/single-word guards |
| `Block.narrow` | yes J/Seq | yes, multiword `narrowC` | `lowB_ok` (unbuilt) | recursive operand/continuation and frame/code bounds |
| `Block.check` | skipped: no standalone surface statement in `SAnw` or `parseStmt` (`Parser/Stmt/Anweisung/Kopf.lean:95`, `Defs2a.lean:92`); C16 `check` is an item | yes A:310, condition plus end-handler | `lowB_ok`, P:219 | no standalone source check syntax; format-field checks are not a statement producer |
| `Block.float` | yes J/Seq:78 | yes A:330, software IEEE add/sub/mul/div | `lowB_ok`, P:221 | recursive values/range/code guards; stale TODO claim that this constructor is wholly refused is superseded |
| `Block.floatLit` | yes J/Seq:73 | yes A:211, `floatLiteralL` | `lowB_ok`, P:225 | kernel-rounded binary64 value and range |
| `Block.floatOf` | added, UNCHECKED: documented `f32(n)` / `f64(n)` parse as calls; U8 `uBindWert` retains the operand and declared float range; `J/Seq` emits `Block.floatOf` | yes A:213, literal or computed conversion | `lowB_ok`, P:227; exporter `lowSeqStep_floatOf` | integer operand required; closed rational target ranges supported, exclusive float upper bounds refused by name; canonical `Endblock.floatOf` absent; both source widths retain the existing binary64 model; computed source-text witnesses await lead checking |
| `Block.floatNarrow` | added, UNCHECKED: `narrow x to finite else { ... }` in continuing blocks; `U8` `uNarrowKopf`, `J/Seq` float arm | yes A:202, range/fallback | `lowB_ok`, P:229; exporter `lowSeqStep_floatNarrow` | fractional ranges and end-block narrowing remain refused; no canonical Endblock float-narrow constructor; NaN endpoints lower the fallback |
| `Block.narrowRequired` | yes J/Seq; arena expansion too | yes, multiword `narrowC` | `lowB_ok` (unbuilt) | failed runtime capacity stops 107; recursive operand/continuation guards |
| `Block.bindAxiomOpt` | yes J/Seq | yes, `plainForeignC` for values, `torC0` for VOID | `lowB_ok`, foreign helper proofs (unbuilt) | explicit register/result-area profile and provider duties for values; existing VOID restrictions |
| `Block.bindAxiomOptElse` | yes J/Seq | yes, `fallibleForeignC` for values; VOID errno dispatch | `lowB_ok`, foreign helper proofs (unbuilt) | checked reason map and branch bounds; register/result-area profile for values |
| `Block.bindCallIndElse` | yes J/Seq:224 via `nestedElseN` | yes A:260 | `lowB_ok`, P:203 | corrected success binder; recursive handler/rest |
| `Endblock.ret` | yes J/Ende:41, J/Rest1 via `lowRetL` | yes A:367 | `lowEnd_ok`, P:244 | source lock/resource restrictions |
| `Endblock.retWhy` | yes J/Ende:35 | yes A:365 | `lowEnd_ok`, P:255 | valid reason/resource transition |
| `Endblock.leave` | yes J/Ende:44 | partial A:363 | `lowEnd_ok`, P:258 | A:363: `else none` if jump not `lit32` |
| `Endblock.next` | yes J/Ende:46 | partial A:364 | `lowEnd_ok`, P:261 | A:364: `else none` if jump not `lit32` |
| `Endblock.cons` | yes J/Ende:49, J/Rest1:416 | yes A:370 | `lowEnd_ok`, P:247 | recursive statement/end block |
| `Endblock.bind` | yes J/Ende:52 | yes A:374 | `lowEnd_ok`, P:249 | recursive value/end block |
| `Endblock.bindCall` | yes J/Ende:74 | yes A:384 | `lowEnd_ok`, P:251 | ordinary call/frame bounds |
| `Endblock.bindCallElse` | yes J/Rest1:272 | yes A:378 | `lowEnd_ok`, P:264 | recursive reason handler/rest |
| `Endblock.bindAxiom` | yes J/Rest1:70/:84 and J/Ende:73/:79 (unbuilt) | yes, `plainForeignC` | `lowEnd_ok`, `plainForeignC_ok` (unbuilt) | same checked register/result-area profiles as `Block.bindAxiom`; provider duties remain explicit |
| `Endblock.bindAxiomElse` | yes J/Rest1:288 and J/Ende:216 (unbuilt) | yes, `fallibleForeignC` | `lowEnd_ok`, `fallibleForeignC_ok` (unbuilt) | same checked reason and answer profiles as `Block.bindAxiomElse` |
| `Endblock.regRead` | yes J/Ende:143, J/Rest1:206 | refused by wildcard | refusal-only P:280 | A:491: `\| _, _, _, _, reserved => none`; device access out of scope |
| `Endblock.regReadElse` | yes J/Ende:154, J/Rest1:225 | refused by wildcard | refusal-only P:281 | A:491: `\| _, _, _, _, reserved => none`; device access out of scope |
| `Endblock.awaits` | yes J/Ende:137 | partial A:461 | `lowEnd_ok`, P:282 | A:465: `else none` unless address and `aggregateFits` |
| `Endblock.bindCallInd` | yes J/Ende:108, J/Rest1:147 | yes A:389 | `lowEnd_ok`, P:284 | indirect dispatch/signature bounds |
| `Endblock.narrow` | yes J/Ende | yes, multiword `narrowC` | `lowEnd_ok` (unbuilt) | recursive operand/continuation and frame/code bounds |
| `Endblock.exchange` | yes J/Ende:131, J/Rest1:185 | partial A:466 | `lowEnd_ok`, P:290 | A:472/:473: `else none` for code-size/address/single-word guards |
| `Endblock.ite` | yes J/Ende:256, J/Rest1:354 | yes A:394 | `lowEnd_ok`, P:253 | recursive branches |
| `Endblock.narrowRequired` | yes J/Ende, J/Rest1 | yes, multiword `narrowC` | `lowEnd_ok` (unbuilt) | failed runtime capacity stops 107; recursive operand/continuation guards |
| `Endblock.retScoped` | yes J/Ende:30 → J/Returns:269 `lowRetEnd` (unbuilt) | yes A:489 | `lowEnd_ok`, P:292 | exact contract-end resources plus precisely the lexical locks required |
| `Endblock.retWhyScoped` | yes J/Ende:30 → J/Returns:267 `lowRetEnd` (unbuilt) | yes A:490 | `lowEnd_ok`, P:295 | same exact-resource check; reason must be in the declared channel |
| `Endblock.bindAxiomOpt` | yes J/Ende | yes, `plainForeignC` for values, `torC0` for VOID | `lowEnd_ok`, foreign helper proofs (unbuilt) | same checked answer profiles and provider duties as the continuing form |
| `Endblock.bindAxiomOptElse` | yes J/Ende | yes, `fallibleForeignC` for values; VOID errno dispatch | `lowEnd_ok`, foreign helper proofs (unbuilt) | same checked reason/answer profiles as the continuing form |
| `Endblock.bindCallIndElse` | yes J/Rest1:171; J/Ende uses export helper | yes A:426 | `lowEnd_ok`, P:274 | recursive reason handler/rest |
| `Ty.int lo hi` (also `index`) | yes U3:104/:108/:118 | `integerWords`, V:21; arbitrary-width local/call copies | `encodeWords_length`, `lowE_ok` arithmetic/variable arms | consumers such as narrowing/byte spans/gates retain the individual bounds above |
| `Ty.bool` | yes U3:97 | one word | `encodeWords_length`, `lowE_ok` Boolean arms | — |
| `Ty.opt n` | yes U3:113 | L:39, V:23–26; multiword when `n > 2^63` | `encodeWords_length`, `lowE_ok` arms `none`/`some` | introduction/copy broader than `istSome`/`onOption`; those still refuse large options |
| `Ty.sum cs` | yes named tagged schemas, G5:51/:60 | L:40; packed scalar or tag/payload word spans V:30 | `encodeWords_length`, `lowE_ok` arms `var`/`case`, `lowS_ok` arm `onTag` | L:20: `\| some _ => false`; `sumFits`: ≤256 cases and integer payload span <2^56; general introduction/match absent |
| `Ty.why n` | yes U5R:128, H2:167 | arbitrary-width reason value, V:27 | `encodeWords_length`, `lowE_ok` arm `why`, generic return arms | reason match still requires `n < 2^31`; gate reason maps require one-word channel |
| `Ty.never` | yes U5R:133, U6:164 | no inhabited value (V:40: `nomatch v`); foreign result checker emits stop T:165 | `encodeWords_length` empty case; generic axiom/return proof | not a materializable value; no extra syntax case counted |
| `Ty.fl lo hi` | yes U3:98 (`f32`/`f64` map to `uFloatTy`); closed rational `in` ranges added, UNCHECKED | binary64 bits V:38; software arithmetic A:330 | `lowE_ok` arms `fllt`/`flle`, `lowB_ok` arm `float`, `blockFloatArithmetic_case` | this inventory does not establish a separate binary32 execution path; top-level source float model gap below |
| `Ty.fnptr sig` | yes U5R:151, J/Seq:205 | address V:29; ordinary/indirect call ABI | `lowE_ok` arm `fnref`, `lowS_ok`/`lowB_ok`/`lowEnd_ok` indirect arms | E:195: `else none` for non-`lit32` function address |
| `Ty.ptr cap` | yes U3:120–127; table capabilities only, resolved owner/space | ghost zero V:39; accesses name resolved table | `lowE_ok` arms `ptrOf`/`thru`/`thruOwn`; owned store and copied-value proofs | live byte capability refused U3:121/:127; `DataTarget` has only `table`; source provider admission remains an explicit boundary |
| `Ty.ref t` | yes U3:118; provider result U5R:132 | cell number V:28; `slotRef`/`assignSlotRef`/`refEq` and foreign register answers | corresponding `lowE_ok`/`lowS_ok` and foreign-answer proofs, with `ValueValid` (unbuilt) | `chkC` checks the nonnegative reference word; freshness, mapped storage and source provider-contract admission are separate duties |
| `Ty.arr τ n` | yes U3:129–133 | complete recursive element spans V:34 | `encodeWords_length`, `lowE_ok` array arms | element displacement/frame bounds; foreign arguments remain restricted; answers use an explicit result area |
| `Ty.str n` | yes U3:134–138 | packed capacities 0/1, otherwise length + padded byte words V:35 | `encodeWords_length`, `lowE_ok` string arms | long concatenation/order still refused; foreign arguments remain restricted; answers use an explicit result area |
| `Ty.prod name fields` | yes named record schemas, G5:167/:175/:184 | complete field spans V:33/:43–53 | `encodeWords_length`, `prod_ok`/`prodGet_ok`/`prodSet_ok` via `lowE_ok` | foreign arguments remain restricted; answers use an explicit result area; no blanket local/ordinary-call refusal |

Shared restrictions and source consistency findings:

- All `Option`-returning lowerers propagate an operand/continuation's `none`. The function-level wrapper
  `lowFunE` reports `.error ("ir: the function " ++ name g ++ …)` at
  `stage0/Stage0/Senke/Images/Bild.lean:131`, ending with `" uses a form outside the IR fragment"`
  at :138 (or a postcondition/snapshot/invariant explanation at :133–137).
  A wildcard refusal is not a diagnostic per constructor.
  Layout/address/frame/code-size checks are additional to the form-level table. World multiword loads/stores
  use `globalValueC`/`slotValueC`/`globalStoreC`/`slotStoreC`; the older `aggregateFits` comment alone does not
  establish that all world storage is single-word. Atomics remain explicitly single-word.
- Gate parameters: T:109 checks at most six registered arguments, each `wortTy` (one-word integer, bool or
  table pointer, T:29–33); T:131/:132 return `none` for bad/missing binding. The buffer path T:115–130 needs
  exactly one readable normal-space unowned table capability, a byte column, bounded count and matching
  layout. Nonfallible bindings use `torC0` (T:137); fallible forms validate the error map and branch spans.
  The integrated `chkC` accepts one-word integer ranges with supported bound checks, normalized bool,
  nonnegative reference words, ghost table capabilities and never. `Tore/Code.plainForeignC` and
  `fallibleForeignC` additionally transport complete multiword answers through an explicit checked
  result-area profile, with `plainForeignC_ok`/`fallibleForeignC_ok`. Missing areas and hidden/source-register
  overlap refuse; area profiles combined with pointer-buffer arguments still refuse. These unbuilt arms
  retain provider footprint/freshness/mapping duties and do not establish original-source provider admission.
- Entry-old reads use `lowEnsAt_ok` (`stage0/Stage0/Senke/Ausdruck/Old/Sound.lean:27`) and `lowEns_ok`
  (same file:296), then `lowPost`/`lowFun`. The numeric old(global) bridge is
  `stage0/Stage0/Senke/Ausdruck/Old/Source.lean:41–66`; other source trees containing it reach
  `.error "ir: unsupported source expression containing old(global)"` at :66. Ordinary `lowE_ok` assumes
  entry=current only when `currentOld = true`; the postcondition fallback sets it false. This is a real
  conditional boundary, not permission to substitute exit state for entry state.
- **Unbuilt source-level blockers visible by inspection:** the earlier missing owned-access arms
  are superseded by `s0-c12own`'s `lowE`/`lowS` and generic `lowE_ok`/`lowS_ok` arms retained here.
  The canonical `Endblock` constructor list (`Syntax/Teil2.lean:259–358`) has no `float` or `floatLit`,
  yet J/Ende:58/:63 and J/Rest1:51/:56 reference `Endblock.floatLit`/`Endblock.float`; no definition of
  either name exists in `grammatik/Grammatik/**`. The ordinary function-body path `lowerFnPlain` →
  `lowBody` → `lowBodyF` reaches those references, so a continuing `Block.float` arm does not close the
  top-level source-float case. The misspelled indirect-else success binder in J/Seq has been
  corrected on `front-gaps1`. These are source findings, not measured compiler diagnostics; the connected theorem source
  graph must not be advertised as a checked green pipeline at this snapshot.

Refused/unavailable forms, grouped by the first missing component (overlapping parameter restrictions are
listed above, not counted as extra constructors):

- **Model:** none of the 143 listed constructors is absent from the model. Additional existing source
  forms still lack a canonical form: live byte capabilities (`DataTarget` has no byte target; U3:121/:127),
  and top-level/end-block float introduction/arithmetic (dangling references above). Device ASM/boot/raw
  addresses and register access/transition are outside this userspace inventory's unfinished-work count.
- **Front end:** `Expr.getBytes`, `Stmt.putBytes` and `Block.check` still have no surface producer;
  `Stmt.advances` has an unchecked exporter preserving declared stage orders and adjacent changes;
  retirement supports any held stage. Header `advances` clauses remain refused. `Stmt.breaking`
  has an unchecked exporter, but complete source units remain blocked by the invariant metadata gate.
  `Block.floatOf` and `Block.floatNarrow` have unchecked continuing-block exporters; their end-block
  forms remain absent. Retirement, consuming traversal, scoped returns, indirect call handlers and
  foreign `let .. else` retain their newer exporters listed above, all awaiting lead checks.
  `oldG` has the Stage-0 numeric bridge, not a general canonical
  parser export. Provider-reference initialization and top-level float source compilation remain separate
  connected-path gaps even though their component constructors appear in the positive structural count.
- **Lowering (6 constructors):** out-of-scope `Stmt.regWrite`, `Stmt.transition`, `Block.regRead`,
  `Block.regReadElse`, `Endblock.regRead`, `Endblock.regReadElse` (wildcards quoted above).
  Partial lowerings additionally refuse large option tests/matches, general tagged payloads,
  long string concatenation/order, nonword atomics and unsupported gate profiles.
- **Proof:** no emitted constructor was found with only a detached witness and no connected generic arm.
  Owned read/write and the integrated foreign-answer profiles have generic proof arms; their lead checks
  remain open. Proof presence is not build evidence.
