# Gabbro-to-IR compilation lanes

**Latest Lean scheduling rule:** Up to four global concurrent Lean checks, each capped at 5 GiB
(MemoryHigh=4G, MemoryMax=5G, MemorySwapMax=0), supersede the earlier single-check rules below.
Slot locks: `/home/simon/.cache/gabbro-stage0-build.slot-N.lock`, N=1..4. IR-01/11 share slot 1,
IR-02 uses slot 2, IR-03 uses slot 3, IR-04/12 share slot 4. Release per module/check, preserve artifact
isolation and one check per worktree. No grammar rebuild. IR-03 foundation publication has priority
within its slot because consumers depend on it.

**Latest scope update (2026-10-31).** This compiler assignment covers existing userspace Gabbro. Embedded
source ASM, boot code, proposed privileged instructions and raw memory-address syntax are outside it,
alongside device-register forms. The existing assembly IR runner stays in use. IR-11 continues userspace
foreign calls/syscalls/bindings; IR-12 continues userspace entries/profiles/images. Their earlier ASM/boot
responsibilities below are superseded. A temporary seventh planning-only agent writes the future low-level
language design in Markdown; no canonical grammar change or build is authorized by that planning task.
Final coverage must state this precise domain rather than claim all syntax except registers only.

**RESUMED (2026-10-31).** The owner authorized up to six parallel Sol 6.1
implementation agents, each owning one lane, followed by one final integration/proof agent. Root coordinates
interfaces, performs direct review and measures form coverage. Do not advance a round by declaring an
incomplete lane complete.

**Scope.** Compile all existing Gabbro except device-register reads/writes/fallible reads and register
transitions to S0IR, with generic formal correctness for every actual lowering. Stage 0 only compiles; the
former Lean Gabbro interpreter/runtime stays removed. Reuse the assembly runner; change it only for a concrete
missing or incorrect capability required by the actual translation. No independent timing, hardware or
instruction-cost projects, no weakened checks, no unproved hook activation and no program-specific compiler.

**Common build rule.** Never rebuild `grammatik/`; reuse its compiled artifacts. Exactly one Lean build or
direct check globally, protected by `/home/simon/.cache/gabbro-stage0-build.lock`. Use the established direct
Stage-0 checks, unset `ELAN_TOOLCHAIN`, and apply memory scopes. Each active worker has its own worktree and
scratch. Shared interfaces are agreed before parallel edits; serialize mutations of common emitter, mutual
induction, root-import and image modules. Do not restore legacy execution to make a translation test pass.

**Checkpoint.** Integrated and pushed compiler baseline: `067c4f0a1`, tag `stage0-ir-only-20261031`.
The former Lean source runtime, replay/fast execution, syscall C trampoline and their generators are removed.
The pure gate binding parser is `Stage0/Bindung.lean`; the compiler entry is `Stage0/Haupt.lean` -> `IRBild`.
Existing computed `floatOf` and real protected-counter `forever` lowering must be retained.

| Preserved worker | Last committed HEAD | Uncommitted work at pause | Resume owner |
|---|---|---|---|
| `/home/simon/.t3/worktrees/Gabbro/t3-857b75c9`, `t3/stage0-forever-ir-lowering` | `241f925d6` (signed64 literals; includes inventory `f31e1f68a`) | unsigned64 materialization/bit-operation edits in `Ausdruck.lean`, `Gleichungen.lean`, `Satz.lean`, `Wort.lean`; interrupted check, not accepted as green | IR-02 |
| `/home/simon/.t3/worktrees/Gabbro/t3-30ae6751`, `t3/stage0-float-lowering` | `a490d09aa` (actual RIGHT execution through copy/increment/endjump to LEFT) | LEFT reentry `Pre` restoration in `Arithmetik/Initialisierung.lean`; interrupted check, not accepted as green | IR-04 |

Both delegated runs were explicitly stopped; no replacement was started. Their committed changes are not yet
merged into the pushed baseline above. All tracked edits and untracked scratch remain in their worktrees.
Additional binary patches, HEADs, tracked status and SHA-256 hashes are stored locally on persistent disk in
`/home/simon/Dokumente/Gabbro/.scratch-integration/reboot/checkpoint.json`, `integers-wip.patch` and
`float-wip.patch`. These patches duplicate the current edits: do not apply them over the already modified
worktrees. Ordinary reboot retains this state; no claim is made that uncommitted work has been pushed.

**Resume procedure.** Inspect actual HEAD/status and the checkpoint hashes first. Preserve all work; never
reset, clean, delete worktrees or reapply a patch blindly. Do not trust an interrupted build or its cache as a
green result. Recheck the dirty modules under the global lock before committing them. Continue the two
implementation lanes below under the explicit resume now recorded above. Reuse existing compiler checks; do not rerun
unchanged broad suites in place of closing a connected translation case.

## Work packages

## Authorized seven-round schedule

**Staffing update:** The owner increased concurrency to six implementation agents. The original round
table remains the lane allocation; it no longer limits execution to two slots. IR-01 and IR-03 continue;
IR-02, IR-04, IR-11 and IR-12 start on four additional slots. Shared ABI changes from IR-03 must be
coordinated before consumers integrate; independent emitter/frontend work proceeds meanwhile. All Lean
checks remain globally serialized. The single final integration/proof agent still follows lane completion.

| Round | Agent A | Agent B |
|---|---|---|
| 1 | IR-01 frontend and type coverage | IR-03 shared value representation and ABI |
| 2 | IR-02 integers and Booleans | IR-04 floating point |
| 3 | IR-05 options, sums and dispatch | IR-06 memory and references |
| 4 | IR-07 regions and ownership | IR-10 functions and contracts |
| 5 | IR-08 control and source budgets | IR-09 concurrency and RCU |
| 6 | IR-11 foreign calls and ASM bodies | IR-13 formats and generated constructs |
| 7 | IR-12 profiles and images | IR-14 compiler integration |

**Rolling six-agent execution.** Round numbers are an allocation, not synchronization barriers. As soon as
one agent completes its lane, start the next ready lane on that free slot while the other continues.
Never wait for the other lane merely because it has the same round number. Keep at most six implementation
agents active; only genuine interface dependencies may delay a particular successor. Integrate and check
the prerequisites needed by that successor. Each lane must implement its real compiler
path and connected generic proof, not merely produce an inventory or isolated helpers. Report unresolved
dependencies explicitly and continue resolving them; seven rounds are an allocation, not a correctness claim.
Root serializes shared interfaces and merges. Exactly one Lean check runs globally under the shared lock.

After round seven, one final implementation agent composes the proofs and proves structural coverage of
all canonical source syntax except the explicitly excluded register forms. Prove both semantic correctness
of emitted IR and completeness for supported well-formed non-register syntax within explicit target/resource
limits; correctness conditional on successful emission alone does not prove coverage. Root reviews the
result directly. No claim of full coverage is allowed while any syntax family or nested variant is missing.

A lane owns a family through its actual source frontend, model/desugaring obligations, IR generation and
connected correctness theorem. Another lane may provide a representation or primitive, but ownership does
not transfer silently. Already working cases are preserved, not reimplemented. A detached helper, prototype,
conditional whole-run assumption or a test-only path is not a completed lane.

| Lane | Complete responsibility and remaining work | Interfaces / dependencies | Required result |
|---|---|---|---|
| **IR-01 — Frontend, names, types and compile-time evaluation** | Modules/imports/public visibility, aliases and type elaboration, constants, specification functions and translators. Account for every `SExpr`, `STyp`, `SAnw` and item variant within its owning family; implement missing source-to-model adapters rather than silently erasing semantics. Records as values share IR-03's representation. | Establish the source/model interface first; coordinate value layouts with IR-03 and linked units with IR-12. | Every in-scope surface variant is exported to its canonical model or has a named unresolved model prerequisite; no residual unsupported variant is counted complete. |
| **IR-02 — Complete integer and Boolean operations** | Materialization, signed/unsigned64, genuinely wider bounded integers, arithmetic/comparisons/division/remainder, bit operations/shifts and expression narrowing. Preserve the signed64 work above; distinguish signed division/comparison from unsigned words. | IR-03 supplies shared multiword values; stabilize scalar contracts first. | Actual expression emitter and generic expression/top/frame proofs support the complete integer domains, with no accidental signed32/signed64-only cap. |
| **IR-03 — Shared value representation, aggregates and ABI** | One centralized representation for wide values, records, arrays and strings; variable placement, loads/copies, indexing/update, concatenation/order/length and binding. Cover arbitrary declared lengths, nested values, local/global/table storage, snapshots and parameter/result widths through shared interfaces. | First agree widths, offsets, encoding and frame separation with IR-02/06/10; consumers then close their integration. | Remove empty/singleton and length-one limitations without parallel special-case ABIs; prove encoding, placement and generic compositional simulation. |
| **IR-04 — Complete source floating point** | Existing source float comparisons/literals/conversion/narrowing plus Add/Sub/Mul/Div; actual normalization, IEEE rounding/carry/packing, zero/subnormal/ties/overflow and range Stop107. Finish the actual candidate, not a detached differently emitted pipeline. | Existing scalar IR primitives; IR-03 frame/value interface. Prioritize formats actually exposed by the source model. | Real `Block.float` hooks and mutual soundness are connected for all source operators; preserve computed `floatOf`. |
| **IR-05 — Options, sums, reasons and dispatch** | All option/sum/reason constructors, payloads and matches, exhaustive cases and error-arm binding. Remove sentinel/index/tag/payload-size limitations through the shared representation. | IR-02 arithmetic and IR-03 layouts; coordinate call error channels with IR-10/11. | Generic construction, decoding, branching and environment extension with no unsupported in-scope case or payload variant. |
| **IR-06 — Memory, bytes, references and tables** | Variables/globals/table and capability reads/writes, references/reachability, byte ranges, table/global declarations and layouts. Remove eight-byte and single-word data limits; maintain exact footprints and permissions. | IR-03 base layout; export primitives to IR-07 and IR-09. Close open-region integration when IR-07 supplies its provider contract. | Actual load/store/copy paths preserve the source memory relation and support all represented field/value shapes. |
| **IR-07 — Arenas, regions, ownership and table states** | Arenas/allocation/release, open-region providers, owner/backed relationships, group/table invariants, ordinary table-state transitions, `breaking`, `advances` and `retires`. Device-register transitions remain excluded. | IR-01 source export, IR-03 values, IR-06 memory primitives, IR-08 control and IR-09 synchronization interfaces. | Missing model/provider obligations are closed generically before acceptance; ownership, freshness, invariants and declared failure/capacity behavior are preserved. |
| **IR-08 — Control flow, blocks and source budgets** | Conditions, quantifiers, sequencing, checks/narrowing, traversal/retry/forever, leave/next and terminating blocks, with actual exits/targets, invariants, nested protected counters and configured source-budget stops. | Stable value/frame and child/callee contracts from IR-03/10; integration closes those contracts, not assumed whole-body execution. | Mutual block/statement/end-block correctness covers every in-scope child combination and exit, retaining existing forever support. No new separate machine-cost project. |
| **IR-09 — Concurrency, locks, atomics and RCU** | Atomic declarations/read-modify-write, publish/await payloads, exchange, lock modes/early exits, shared state, concurrent starts and RCU. Preserve the G/GX/world and ordering guarantees. | IR-06 memory, IR-08 exits; agree lifetime interfaces with IR-07 before final RCU integration; IR-12 connects roots/images. | Formally connected concurrent lowering without dropped effects, weakened memory assumptions or unsupported legal body combinations. |
| **IR-10 — Functions, calls, contracts and snapshots** | Function declarations; direct/indirect calls, arguments/results, recursion/depth, return/reason paths, pre/postconditions, multiple/computed `old` snapshots and full end-block contexts. | IR-03 shared ABI, IR-05 error payloads, IR-08 control, IR-11 foreign interfaces. | Generic function/callee/ABI/image theorems close on the same actual memories; no one-word or single-snapshot limitation remains. |
| **IR-11 — Foreign calls, assumptions, syscalls and ASM bodies** | Foreign signatures, declared assumptions, axiom calls and result/error channels, syscall variables/bindings, generic buffers and real source ASM bodies. An exported signature is not executable ASM support. | IR-10 call contracts, IR-06 buffers and IR-12 profiles/linking. Use existing runner capabilities or a narrowly required verified addition. | Actual callable paths with generic effect/result/error correctness. Do not silently turn software/OS behavior into a new hardware axiom. |
| **IR-12 — Profiles, entries, boot, entrust and final images** | Targets/profiles, conditional `when` declarations, entries and ABI setup, boot/entrust, unit linking/relocation, roots/start arguments, image layout and compiler options. No new ISA/backend project. | IR-01 unit/name exports, IR-07 regions, IR-09 roots, IR-10/11 ABI and bindings. | Correct source-to-image integration for the declared profiles; no implicit dropped declaration, unresolved supported entry or legacy Lean execution fallback. |
| **IR-13 — Formats, declared checks, accumulators and walkers** | `format`, check declarations, `accumulates` and `walk`; wire layouts, field validation, generated operations, traversal and aggregation semantics. Desugar to proved existing primitives where possible. | IR-01 frontend, IR-02/03 values, IR-05/06 data, IR-07/08 invariants/control, IR-09 concurrency and IR-10 contracts. | Complete source constructs, not only parser nodes or handwritten replacement examples, with generic expansion/lowering proofs. |
| **IR-14 — Integrated compiler and formal closure** | Shared package/root/CLI integration, final `irBild` pipeline, combined generic soundness, accepted image/ABI/profile correspondence and final form coverage. Root owns this lane and all reviews/measurements. | All other lanes. Resolve shared-module integration after agreed interface changes. | Every in-scope family and all its nested surface/type variants is connected; zero missing/restricted semantic cases remain beyond explicit legitimate target/resource limits. No default refusal may conceal an unowned form. |

**Execution order.** First freeze IR-03's shared encoding/width/offset/frame interfaces together with the
scalar/call consumers; do not build independent wide-value ABIs in several lanes. Start IR-01 and scalar
IR-02 work on stable interfaces; retain IR-04's existing continuation. Then close value consumers
IR-05/06/08/10. Arena/synchronization interfaces are agreed before their mutually dependent final integration
(IR-07/09); this is an interface milestone, not permission for cyclic module imports. Foreign/profile work
IR-11/12 and macro declarations IR-13 consume those primitives. IR-14 closes every interface against actual
source lowering. These waves do not raise the six-agent or one-global-Lean-check limits.

**Shared-file rule.** `Ausdruck.lean`, `Anweisung.lean`, the mutual `Satz.lean`, representation/ABI definitions,
`Stage0.lean`, `Nachpruefung.lean` and `IRBild.lean` are integration surfaces. One writer owns a given surface
at a time. Parallel lanes implement separate modules and submit connected changes through agreed interfaces;
IR-14 sequences shared changes. No two workers edit or compile the same tree.

## Exhaustive primary ownership of the current form inventory

The baseline inventory counts 117 typed non-register cases (Float's four operators separately) and 34
non-device top-level families. Each of those 151 families has exactly one primary owner below; this mapping
was checked for omissions and duplicate ownership. It is a planning allocation, not a proof of language
completeness. All nested `STyp`/`SExpr`/`SAnw`/declaration variants, attributes, type domains and syntax sugar
remain obligations of their parent lane. Supporting `Args`, payload, result and arm constructors belong to
the corresponding value/call/dispatch lanes. New discoveries must be assigned explicitly before closure.

- **IR-01:** TopLevel: `modT`, `useT`, `typeT`, `constT`, `specT`, `transT`, `pubT`.
- **IR-02:** Expr: `lit`, `tru`, `fls`, `widen`, `add`, `sub`, `neg`, `mul`, `div`, `rem`, `sdiv`, `srem`, `band`, `bor`, `bxor`, `shl`, `shr`, `lt`, `le`, `eq`, `and`, `or`, `not`, `eng`.
- **IR-03:** Expr: `var`, `arrNil`, `arrCons`, `arrGet`, `arrSet`, `strLit`, `strLen`, `strCat`, `strGet`, `strEq`, `strLt`, `strWeit`; Block: `bind`; Endblock: `bind`.
- **IR-04:** Expr: `fllt`, `flle`; Block: `float.add`, `float.sub`, `float.mul`, `float.div`, `floatLit`, `floatOf`, `floatNarrow`.
- **IR-05:** Expr: `none`, `some`, `istSome`, `case`, `why`; Stmt: `onOption`, `onTag`, `onWhy`; TopLevel: `whyT`.
- **IR-06:** Expr: `glob`, `slot`, `thru`, `ptrOf`, `getBytes`, `reaches`, `refEq`, `slotRef`; Stmt: `assignSlot`, `assignThru`, `assignGlob`, `putBytes`, `assignVar`, `assignSlotRef`; TopLevel: `globT`, `tableT`.
- **IR-07:** Stmt: `shift`, `breaking`, `advances`, `retires`; TopLevel: `arenaT`, `stateT`, `groupT`.
- **IR-08:** Expr: `forallSlots`, `existsSlots`, `wenn`; Stmt: `ite`, `traverse`, `retry`, `forever`, `leave`, `next`; Block: `nil`, `cons`, `narrow`, `check`; Endblock: `leave`, `next`, `cons`, `narrow`, `ite`.
- **IR-09:** Stmt: `locks`, `publish`; Block: `awaits`, `exchange`; Endblock: `awaits`, `exchange`; TopLevel: `atomT`, `lockT`, `rcuT`, `concT`.
- **IR-10:** Expr: `fnref`, `oldG`, `oldS`; Stmt: `call`, `callInd`, `ret`, `retWhy`; Block: `bindCall`, `bindCallInd`, `bindCallElse`; Endblock: `ret`, `retWhy`, `bindCall`, `bindCallElse`, `bindCallInd`; TopLevel: `fnT`.
- **IR-11:** Stmt: `axiomCall`; Block: `bindAxiom`, `bindAxiomElse`; Endblock: `bindAxiom`, `bindAxiomElse`; TopLevel: `protoT`, `asmT`, `assumT`, `axiomT`, `callT`, `varT`.
- **IR-12:** TopLevel: `entryT`, `trustT`, `bootT`, `goalT`, `profT`, `gateT`.
- **IR-13:** TopLevel: `formatT`, `checkT`, `accT`, `walkT`.


## Common completion and reboot gates

1. The actual source construct reaches its canonical model and real IR emitter; any missing model rule is
   solved first. Existing guarantees, named assumptions and refusal discipline are preserved. If this truly
   requires changed grammar definitions that cannot be checked using the current artifacts, report the
   prerequisite and leave acceptance blocked: the no-grammar-rebuild instruction must not be bypassed.
2. Generic correctness is connected through expressions/statements/blocks/functions/images as applicable,
   with jointly satisfiable nondegenerate witnesses, exact frame/context/footprint/effect preservation and
   source-budget/error behavior. A theorem conditional on emission alone does not establish full form
   coverage: arbitrary semantic/representation refusals must also be removed or remain explicitly open.
3. Build the affected connected compiler chain under the global lock. Audit the new statements and
   `gabbro_ziel` for only the standard axioms; no `sorry`, `admit`, `native_decide`, new axioms or weakened
   contracts. Check layout. Root audits form coverage directly; example counts are not coverage percentages.
4. Use actual textual Gabbro -> IR -> assembly execution for relevant behavioral regressions, in addition
   to generic proofs; do not substitute typed-only fixtures or tests for a connected lowering theorem.
   The compiler remains compilation-only; there is no source-execution fallback.
5. Commit every green connected step using the required message file and `commit.sh`; report accepted
   source forms, generic proof attachment and exact remaining limits. Do not claim all-language completion
   while any in-scope family or nested variant remains missing/restricted. Reviews are performed directly
   by Root, not delegated as implementation or substituted by a new guardian.

**Execution is authorized.** Follow the seven-round schedule above; preserve all interrupted work and
never treat it as checked. Final closure is blocked while any in-scope syntax or generic proof is missing.
