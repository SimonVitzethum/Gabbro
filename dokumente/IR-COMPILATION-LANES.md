# Gabbro-to-IR compilation lanes

**RESUMED with two agents (2026-10-31).** The owner ended the pause and authorized exactly TWO Claude
Sonnet 5.5 implementation agents, no others: IR-06 (memory, Lean slot 1) in its preserved worktree
`t3-e67bc9a3` and IR-03 (full multiword ABI, Lean slot 2) in `t3-c7fc551c`. All other lanes stay paused
with their worktrees, dirty changes and scratch preserved. Last checked and pushed integration: `94547b852`.

## Checked frontend follow-up (2026-10-31)

Root integrated IR-01 through `77f74c248`: dependent original scalar/alias scopes, fixed-count
fieldless tables and canonical typing/collector retention for every original array declaration,
including unused declarations. The selected-ABI guard and two-check global limit are preserved.
`Stage0.ArrayWitness` is imported by Stage0 and five generic/joint array statements are audited.

Measured on the merged sources: 13 affected modules through Stage0 and Nachpruefung, all five new
array audits on standard axioms, layout over 1414 Lean files, and 11 textual source-to-IR/ASM or
precise-refusal regressions passed. A SourceWitness check exceeded the initial internal Lean
4096-MiB threshold; its retry and the remaining checks passed at 4608 MiB with the unchanged
MemoryHigh=4G/MemoryMax=5G/MemorySwapMax=0 scope. No grammar rebuild or full guardians were run.
Logs remain in `.scratch-integration/frontend-array/`. This is an incremental compiler result,
not a completed lane, full ABI integration or whole-language verification.

## Checked integration checkpoint (2026-10-31)

Root merged the coherent published IR-01 source/profile bridge through `587dfb27d`, IR-02 integer/runner
lowering through `1f3d586f1`, IR-08 narrowing/traversal through `4c126f4db` and IR-12 source/start-byte
proofs through `e4815ed3f`. Preserve the selected-ABI guard from `63addf850`. Full-ABI dirty work and
later follow-up commits are excluded from this checkpoint; no lane is declared complete.

Combined validation checked 184 distinct Stage0 modules (including missing cache dependencies), root and
central axiom audit. All 37 selected textual compiler/ASM regressions passed their expected execution or
precise refusal results, including the retained image-size bound. Layout is green. The frozen cached
`gabbro_ziel` theorem has exactly `propext`, `Classical.choice`, `Quot.sound`; no grammar rebuild occurred.
Split the unchanged all-27-image kernel witness into finite cases to check it within the 5-GiB limit.
CLI regression execution used `lean --run` and the assembly runner, not a claimed native CLI rebuild.
This is a checked incremental userspace compiler integration, not total language/ISA/platform verification.

Root validation logs are retained in `.scratch-integration/merged/`. Source files stayed fixed throughout
the successful combined checks; artifact-gap and interrupted aggregate-fixture logs are preserved too.
Slot-1 integration priority is released; IR-01 and IR-08 may resume their deferred module checks.

**Parameterized-start activation blocker:** The current fixed `exitSlot = 2*FB+2 = 10` used by
`spawnC`/`startC` overlaps a three-word parameter span at slots 8, 9, 10 in root frame `F = FB`.
Keep the empty-parameter guard. Before activating IR-12 startup, place scratch beyond the shared
parameter/result/status region (using the finalized `receiveTop signature FB` convention or its proved
equivalent), update bounds/footprints and prove initialization survives spawn/call. IR-12 owns that
future activation after the coherent full ABI is published; no second startup ABI is authorized.

**Rolling allocation update:** IR-12 handed back green source/start-byte/profile/CLI checkpoints through
`e4815ed3f`; actual parameterized image startup remains blocked on IR-03's full ABI. Its slot now runs
IR-09 userspace concurrency/RCU. IR-12 is not counted complete and resumes for actual image integration
when the shared dependency is ready. The six-agent cap remains in force.

**Rolling allocation:** IR-11 checkpoint `195d5d284` is green for explicit binding selection and gate
construction; full buffers/results remain blocked on IR-03. Its worker slot now runs IR-08 control-flow
implementation. This is a dependency handoff, not IR-11 completion. Resume IR-11 integration after the
shared foundation is green, without exceeding six active implementation agents.

**Latest Lean scheduling rule:** Up to two global concurrent Lean checks, each capped at 5 GiB
(MemoryHigh=4G, MemoryMax=5G, MemorySwapMax=0), supersede the earlier single-check rules below.
Slot locks: `/home/simon/.cache/gabbro-stage0-build.slot-N.lock`, N=1..2. IR-01/06 share slot 1;
IR-02/03/04/10 share slot 2. Retire slots 3 and 4. This includes audits, witnesses and `lean --run`.
Release per module/check, preserve artifact
isolation and one check per worktree. No grammar rebuild. IR-03 foundation publication has priority
within its slot because consumers depend on it.

**Latest scope update (2026-10-31).** This compiler assignment covers existing userspace Gabbro. Embedded
source ASM, boot code, proposed privileged instructions and raw memory-address syntax are outside it,
alongside device-register forms. The existing assembly IR runner stays in use. IR-11 continues userspace
foreign calls/syscalls/bindings; IR-12 continues userspace entries/profiles/images. Their earlier ASM/boot
responsibilities below are superseded. A temporary seventh planning-only agent writes the future low-level
language design in [LOW-LEVEL-SYNTAX-PLAN.md](LOW-LEVEL-SYNTAX-PLAN.md); no canonical grammar change or
build is authorized by that planning task.
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

## IR-03 shared transport checkpoint (2026-10-31)

The actual variable emitter now calls `copyWords width destination source`; its connected `lowE_ok`
variable branch uses `copyWords_ok`, including the one-word fast path. `WordsAt memory frame base words`
states consecutive word placement using the runner's existing slot addressing. The generic execution
contract copies arbitrary word lists from the preserved prefix (`source + width <= destination`) to
fresh storage (`destination + width <= frame capacity`), proves actual IR execution and every output
word, and preserves memory outside the destination suffix. It assumes no child execution. This is
transport only, not a completed multiword ABI: callers must not infer that wide expression emission,
type widths, argument/result placement or aggregate source coverage has been enabled.

IR-03 remains incomplete. `Enc`, `EnvAt`, `frei`/`vslot`, binding, world storage and function/image
contracts still require their coordinated multiword conversion. In particular the current array/string
refusals remain, and no new source-form family is counted complete. IR-02/06/10 must share the transport
interface above; the type-width and encoding interface is not frozen by this checkpoint.

### IR-03 in-progress canonical interface

The controlling compiler scope is existing userspace Gabbro. Source ASM bodies,
boot/privileged syntax and device-register forms are excluded; ordinary safe
regions/references, syscalls, profiles and entries remain in scope.

The shared implementation is `Ausdruck/Aggregat/{Layout,Encoding,Kopie}.lean`.
Consumers use `valueWords` for a type, `contextWords` for parameters/contexts,
`variableOffset` for a variable, and `encodeWords`/`ValueAt` for its complete span.
Integer limbs are little endian two's complement; arrays concatenate complete
element spans and zero-length arrays retain one zero marker. Strings of capacity
at most one retain the proved packed representation; larger strings contain a
length word and a byte-word sequence padded to the declared capacity. `ValueValid`
recursively retains reference and IEEE obligations. A low-word projection is only
an internal view: it cannot establish `ValueAt` for a multiword result.

The ABI reserves `returnWords result reasons`, the maximum of the normal result
and reason widths, after the original parameter span. Status/ensures follows that
entire area; relocated parameters and counters follow status. Headers 0/1 retain
return PC/caller frame, 2 carries entry depth then a return cache tied by
`ReturnMirror` to the canonical result area, and 3 retains the entry snapshot.
`ResultAt`, `ValueOk` and `ResultOk` carry complete results. IR-02/06/10 must use
these definitions rather than introducing another multiword path.

This migration is not yet integration green: expression mutual induction and all
call/return, snapshot, world-memory and image consumers must compile together
before the interface is accepted or new source forms are counted. Ordinary
records remain a named canonical-model prerequisite: `STyp.raw` has no canonical
record/product `Ty` and no ordinary-record `UProg` adapter. Existing array/string
types do not justify inventing record erasure or replacement source semantics.

The independently publishable foundation keeps the pre-migration emitter and
generic compiler contracts intact while importing these shared definitions into
the actual expression compiler. `copyWords_ok` is derived from `copyWords_run`,
whose footprint is exactly the destination span and whose forward-copy condition
is `destination <= source` or `source + width <= destination`. `copyValue_run`
transports complete `ValueAt`; `copyResult_run` also transports the empty result's
zero marker. `ValueProbe.copyValue_run_zeuge` supplies real code, frame, source
words and all execution premises for a three-word copy. `encodeEnv` orders complete
parameter encodings exactly like `contextWords`; its length theorem is shared by
start and call consumers. This foundation does not activate the dirty full ABI
migration or count any additional userspace source form as complete.

This dependency snapshot was checked independently of the preserved dirty ABI
migration: 134 affected Senke modules, `IRBild`, the Stage-0 root and the explicit
axiom audit passed. The eight existing textual source -> IR -> ASM regressions
`arr-empty`, `arr-singleton`, `str-empty`, `str-byte`, `calls`, `old-global`, `loop`
and `eng` matched their expected exit codes (19.574 seconds together). The copy
and connected compiler theorems use only the standard axioms. Checks used IR-03's
dedicated slot 3 with MemoryHigh=4G, MemoryMax=5G and no swap; grammar artifacts
were reused. This validates the dependency commit, not the unfinished migration.
## IR-01 frontend checkpoint (2026-10-31, round 1; incomplete)

Implementation commits `85025ce08` and `e6147444e` add `Stage0.Frontend.Aliases`, called by
`irBild` after `pre108` name/visibility resolution and before `elabU`/`lowerAllg`/`OldSource.restore`/
`AkzeptiertX`/`Senke.bild`. No Senke representation or ABI definitions changed. The adapter expands
integer alias chains in declaration order into existing canonical range syntax. It also folds scalar
constants of alias or explicit range type to nonnegative literal results using the existing
`uFeldTyp` and `uKonstWert` (including existing checked const-function calls). It preserves the declared
constant type. Failed evaluation and negative results retain the prior canonical elaborator path.

Generic local attachment: `bound_correct` proves canonical bound denotation, `aliasBody_correct` proves
that generated ranges elaborate with `uTyp` to the exact looked-up canonical integer type, and
`constant_correct` connects the canonical evaluator result to the integer actually collected by
`uConstsRech`. `aliasBody_correct_zeuge` and `constant_correct_zeuge` jointly instantiate the premises.
`Correctness.lean` now composes those per-declaration facts: `aliasItem_sound` and `constant_sound`
feed `rewrite_sound`, and `normalizeAliases_sound` derives `Normalization` for the entire input list,
including every intermediate declaration environment. `Source.lean` produces a proof-carrying `Source`
with canonical lexer/parser provenance, checked public-interface closure and that complete normalization
derivation. `irBild` consumes `Source.members` directly. `source_sound` and `source_names` establish the
whole-source frontend provenance and exact existing canonical name/visibility preprocessing. The list
proof has a nondegenerate alias-chain/constant witness. These statements do not prove exhaustive frontend
coverage or a new whole-source-to-image execution theorem; image execution remains the existing Senke
contract, with full global IR-14 composition still open.

Measured: direct Lean checks of `Frontend/Aliases.lean` and the modified `IRBild.lean`, using only existing
grammar/runner/compiler artifacts and locally compiled changed modules; global flock and 5G/7G memory
scope; no grammar build. All new theorems and `gabbro_ziel` audited with exactly the three standard
axioms; an intermediate-overflow source still refuses. Actual textual `alias-chain.gab`, `alias-constant.gab` and `alias-const-function.gab` compiled through
`irBild` and the existing assembly runner returned 42 in all three cases. The layout check passed (1386 Lean
files); `git diff --check` passed. These regressions measure behaviors, not complete syntax families.

### Exhaustive surface ownership and remaining adapters

- `modT`, `useT`, `pubT`: existing `pre108` checks `Oeffentlich.huelleZu`, then `Aufloesung.loese`
  resolves names/imports and opens wrappers. Existing theorems include `huelle_geschlossen`,
  `pub_sichtbar`, `ref_aufgeloest` and `schluessel_injektiv`. The actual source frontend now retains checked visibility and canonical preprocessing provenance;
  whole-image name/contract correspondence remains an integration obligation. Cross-unit imports remain coordinated with IR-12.
- `typeT`: canonical `uAliase` collects integer ranges and builtin integer aliases. The new adapter adds
  chains over these ranges. Generic/type parameters, ordering clauses and noninteger alias bodies remain
  open; no claim that silently ignored declaration metadata has semantics. `uSumTabs` separately handles
  tagged raw types. Ordinary record/product declarations have no `Ty` constructor or source-to-model
  adapter; do not encode them as an unrelated array or silently discard fields. IR-03 owns encoding after
  a canonical representation and its field/type semantics are available.
- Every nested `STyp` remains owned: `atom`, `path`, `ptr`, `index`, `range`, `array`, `wrap`, `embed`,
  `raw`, `str`, `entry`. Existing `uTyp` supports integer atoms/ranges, normal-space table capabilities,
  nonoptional indices, arrays and bounded strings; parameter/field elaborators add context-specific
  float/bool/sum/reason/function-reference forms. Paths rely on prior name resolution. Named spaces,
  unsupported capability rights, general products/records and remaining raw/entry/type wrappers are not
  closed by this checkpoint. Field/value transport remains IR-03/06, without a second frontend ABI.
- `constT`: new nonnegative scalar folding covers alias and explicit range types. Existing builtin-word
  folding and integer/nested-array constant paths remain. `Functions.lean` now extracts alias/range-typed
  single-return const-function signatures through canonical `uFeldTyp`, with `fieldType_sound`,
  `constantFunction_sound` and `constantFunctions_sound` proving exact type denotation and source origin.
  The whole normalization certificate includes those function-origin facts, and the actual constant
  evaluator uses those candidates. `alias-const-function.gab` compiles through IR to ASM exit 42. Negative scalar materialization, generalized const-function bodies, noninteger constants and dependency
  cycles/ordering require further implementation or a precise canonical prerequisite. Canonical evaluator
  fuel remains 64; no completeness claim hides that bound. Intermediate overflow still refuses evaluation.
- `specT`: existing `uSpecEin`, `sErsetze` and `uSpecKlauseln` inline specification predicates and refinements.
  Generic capture-avoiding substitution, nested binder interactions and whole-pipeline attachment remain
  open; mere collection of the spec declaration is not completion.
- Every nested `SExpr` remains owned within these families: `lit`, `float`, `tru`, `fls`, `variable`,
  `field`, `index`, `arrow`, `un`, `bin`, `call`, `fnref`, `built`, `old`, `res`, `why`, `ext` (all eight
  `XKind` variants: `all`, `any`, `count`, `mem`, `reach`, `imp`, `text`, `call`). The frozen compile-time
  evaluator only implements literals, variables, builtin min/max fields, selected integer binary operations
  and single-return const calls. It does not establish full compile-time coverage of this list.
- Every nested `SAnw` remains owned for const/translator bodies: `bind`, `bindElse`, `bindLib`, `set`,
  `shift`, `call`, `lcall`, `cond`, `elsif`, `cases`, `arm`, `each`, `retry`, `loop`, `waive`, `trim`,
  `locks`, `watch`, `leave`, `next`, `emit`, `await`, `swap`, `step`, `ret`, `alloc`, `reset`, `grow`,
  `free`, `child`, `start`, `other`, `block`, `allocVon`, plus nested `SEnde`. Existing const-function
  evaluation accepts only a single trailing expression return; parser success for other bodies is not support.

### Named canonical prerequisite: translators and library regions

`SItemTief.transT` exists in the parser, but `uRestFehler` refuses it with `item without G form`.
`Aufloesung.item` does not resolve its signature/body; `UProg` has no translator/library-region component.
`bindLib`/`lcall` have no actual adapter in this path. An ordinary record/product `Ty` is absent as well.
The required canonical work is a typed translator input/result model, region literal/layout semantics,
checked translator termination/cost/effects, library-call payload binding and desugaring correctness into G,
including name/type and checker rules. No source interpreter, declaration erasure, default acceptance or
invented hardware assumption is authorized as a substitute. Owner decision: compiler-side Stage0 adapters
are allowed only when proved against existing canonical semantics; genuinely missing canonical semantics
remain blocked by the explicit no-grammar-rebuild instruction. Separate authorization and canonical-model
validation are needed for that change. IR-01 is therefore explicitly incomplete; the remaining independent
frontend/proof work above also stays open rather than being transferred silently to another lane.

### IR-01 contract mitigation and remaining semantic proof boundary

Root review correctly distinguishes the `Normalization` rewrite trace from source/program denotational
preservation. `source_sound` projects provenance and that local trace; it does **not** prove original
source acceptance, equality to the originally refusing `elabU`, environment-extension preservation or
source-to-image execution. Exact alias/constant environment collection and the semantic program bridge
are still open, independently of translator/record model blockers.

Upstream finding: `Parser/Elab/Uebersetze.lean:uKonstFns` matches `klauseln := _`; `UKonstFn` stores only
name, parameter/result ranges and returned expression. `uKonstWert` evaluates that body without logical
contracts or effects. `Kern/Syntax/Konstanten.lean` likewise has no const-function contract evaluator.
Retaining clauses in `FunctionMeaning` was therefore insufficient as a contract preservation claim.

Mitigation on the actual path: `Functions.evaluationClauses` (in namespace `Stage0.Frontend`) accepts
only pure-effect and cost clauses. Extracted candidates prove that predicate. More importantly,
`Frontend.source` checks **original** constant initializers and nested rows before invoking any baseline
`uConstsRech` or normalization. `Guard.safeConstantName` checks the transitive static const-call hull;
`safeConstantName_sound` derives `SafeHull`, and `source_constant_hull` attaches that derivation to calls
in original scalar initializers. Unsupported logical clauses/effects/bodies refuse explicitly, so falling
back to baseline extraction cannot bypass the check. Original source declarations remain present. Canonical `elabU` explicitly excludes const functions
from runtime `fnItems`; their clauses cannot be justified by assuming a later runtime body check.
This is a safety mitigation and incomplete coverage, not contract-aware const evaluation.

Three textual refusal probes cover alias signatures, builtin signatures (the baseline fallback case)
and a transitive wrapper. Their expected diagnostic is recorded in `.error` files; the existing Lean
guardian's Stage-0 probe loop recognizes compiler-refusal fixtures. The guardian itself was not run,
because it would rebuild the grammar. Direct IO compilations measured all three refusals; the three
positive source-to-IR-to-ASM probes still return 42. The Python guardian change passes `py_compile`.

### IR-01 exact ordered environments (interim accepted-subset check)

`Environments.lean` proves `constants_append`, `aliases_append`, `aliasItem_collected`,
`aliases_collected`, `constant_aliases`, `constants_aliases`, `constantStep_correct` and
`constants_collected`. These retain declaration order and exact bindings/ranges. `typedConstants`
uses canonical `uFeldTyp` and `uKonstWert` in declaration order and retains **all** scalar bindings,
including negatives and duplicate/shadowed names. It does not filter to positive outputs.

Before downstream `elabU`, actual `Frontend.source` now checks that the full ordered environment
collected by canonical `uConstsRech (uKonstFns normalized)` is exactly the successful typed fold.
It also checks stability of the complete alias range environment under those final constants.
`normalize_environments` combines those checked equalities with generic alias collection preservation;
successful `Source` contains `EnvironmentFacts`. This is conditional preservation for the accepted
subset, not total support or a whole-source-to-program execution theorem.

The persistent `negative-dependency` probe exposes a negative intermediate from an alias-result const
function followed by a positive dependent. It now refuses explicitly on the environment mismatch;
no later positive binding can conceal the missing negative. Negative materialization and dependency
support remain implementation work. No source interpreter or grammar modification was introduced.

### IR-01 negative scalar materialization

The former `negative-dependency.error` is now a positive `.code` regression: the negative intermediate
and positive dependent both survive exact canonical collection and ASM exits 42. `negative-alias-min`
also reaches ASM exit 42 with an exact signed minimum and successive negative alias-typed constants.

The actual scalar adapter represents a negative integer as builtin `min` plus a nonnegative offset.
It selects a builtin with the **same canonical range**, checks the output type against that range,
checks evaluation in that range, and checks the full ordered canonical collector extension. Alias
spelling can change internally to the equivalent builtin; source alias declarations and their ranges
are retained. `negative_expression_correct` proves all intermediate range checks and the arithmetic;
`negative_materializes` proves coverage for a selected signed builtin range; `negative_sound` connects
materialized value, exact canonical type and actual collector. `ConstantEquivalent` includes these
facts and the complete normalization proof consumes them. No signed-minimum negation, widened source
range, new source interpreter or ABI change is used. Custom negative ranges with no exact builtin
representative still refuse through the checked environment boundary; no total constant coverage claim.

Measured five textual positive source-to-IR-to-ASM cases (all exit 42), three contract refusals and the
overflow refusal; twenty-five frontend/goal statement audits use only standard axioms. The accepted-subset
environment validation remains in place. Whole-source/program semantic composition is still separate
work; these new arithmetic and collector theorems do not silently close that obligation.

### IR-01 original-source canonical program bridge

`Frontend/Elaboration.lean:elabWithScopes` factors only the existing canonical elaborator phase body.
`elabU_scopes` is proved by `rfl` for **every** old input, using exactly the old wrapper-derived scopes,
including errors and every existing gate. The small frozen-body textual duplication is necessary under
the no-grammar-rebuild rule; any divergence from the imported canonical definition breaks kernel equality.
It introduces no evaluator, execution semantics or new interpretation of a statement.

`typedConstants_aliases` and `constantFunctions_aliases` remove alias normalization from scalar/function
origin facts. `Scopes` then certifies the original declaration-order alias fold, original const-function
candidates and exact typed scalar fold over the **original** source declarations. `Source.scopes` derives
that record from the checked environment facts; complete ordered bindings and canonical ranges remain.
`compileTimeSafe`/`SafeHull` still guard original compile-time calls before any baseline evaluation.

The actual source pipeline is now `Compiler.compile` -> `elabWithScopes` over original runtime declarations
(with the existing old(global) adapter), certified scopes -> canonical `lowerAllg` -> existing snapshot
restoration -> full `AkzeptiertX`. `irBild` consumes exactly that `Compiled.unit` and `Compiled.program`.
`compile_source_program` connects original declaration-derived scopes, unchanged canonical phase body,
and the identical actual `UProg`, `declOf` and `lowerAllg` endpoint. This is a conservative elaboration
extension, **not** the false equation `elabU(original) = elabU(normalized)` under incomplete old scopes.
The Source-to-image runner theorem still needs attachment to this endpoint; total form support remains open.

Measured the changed chain directly under the global Lean lock/memory scope, thirty statement audits
using only standard axioms, five new positive ASM results 42 and six existing call/old-global/old-slot/loop
regressions at their expected exit codes, alongside the three contract refusals and overflow refusal.
No grammar rebuild, additional runner, ABI change or weakened checker was used.

### IR-01 actual source-to-image theorem attachment

`irBild` now projects bytes from the single `emit` path. `Emitted` stores the actual `Compiled` source
program and successful `Senke.bild` equation. `irBild_emitted` recovers that same image from any successful
CLI byte result. `CanonicalSourceProgram` records canonical lex/parse/public provenance, original
source-derived scopes, the unchanged canonical phase composition, actual `lowerAllg`/snapshot endpoint
and full checker acceptance.

`Emitted.correct` composes that original-source program contract with the existing generic
`Senke.bild_ok_u` theorem for the identical program. `irBild_correct` attaches it to the actual returned
bytes. It retains exactly the inherited runner kernel/clone, gate/view and initial-memory contracts;
there is no added whole-run premise or execution interpreter. Successful source compilation therefore
has a connected canonical source-program-to-IR execution statement. This does not establish total syntax
coverage, source initial-world/image initialization beyond the inherited memory contract, or missing
canonical source forms. A concrete joint formal fixture for the new entire source/image contract remains
an explicit witness obligation; existing local fixtures and IO regressions do not replace it.

Direct checks of the connected chain and thirty-three statement audits passed with standard axioms.
The actual source-to-IR-to-ASM regressions continue to match expected results; no guardian or grammar
build was run. IR-01 remains incomplete on the listed forms/model prerequisites and witness/coverage work.

### IR-01 validated image options attachment

`Source`, `Compiled` and `Emitted` are indexed by the same `Profil.Options`; their public
constructors retain default options. Before `pre108`, `source` calls the identity-only
`Profil.prepareItems` validator and retains both original-list equality and runner compatibility.
`emit` passes that exact options value's architecture and target to `toreVonFor`; neither a
second default nor an implicit target override occurs. `CanonicalSourceProgram` and the actual
byte/image correctness theorem retain this options index and compatibility proof. This integrates
IR-12 foundation 09871c8f8 and IR-11 binding selection 195d5d284; it introduces no profile semantics.

Measured direct module checks: Profil, Bindung, Source, Elaboration, Compiler and IRBild green.
Actual target fixture images executed by the existing ASM runner return 24 for explicit `first`
and 23 for explicit `second`; explicit `aarch64` is refused before image emission with the runner
ABI diagnostic. Checks use slot 1, MemoryHigh=4G, MemoryMax=5G, MemorySwapMax=0, isolated output,
and frozen grammar artifacts. CLI argument parsing remains IR-12's integration responsibility.

The controlling coverage domain is existing userspace syntax: embedded ASM, boot/privileged
syntax and device-register operations are excluded. Safe regions/references, generic calls and
syscalls, supported entry/image/profile obligations remain in scope. Translator and ordinary
record semantics remain explicit canonical-model prerequisites; this validator is not lane closure.

### IR-01 jointly inhabited source/image witness

`SourceWitness` constructs one actual `emit` result for a character-pinned source declaring
`type A = u8; type B = A; const C : B = 40 + 2` and an ordinary function returning `C`.
`accepted_image` proves acceptance of this exact image; `source_scopes` proves the two original
alias ranges, scalar scope `C = 42`, one function and nonempty generated code. Generic helper
constructors instantiate a concrete empty-carrier world/oracle and empty entry environment,
plus memory containing the actual image bytes. `InitialState` holds all four inherited initial
contracts together, not independent hypothetical implications. `source_image_joint_zeuge`
combines accepted emission, nondegenerate source/image facts and that inhabited initial state.
`entry_ir_simulation_zeuge` applies the generic image theorem to those exact values.

`Emitted.Simulates` names the unchanged execution conclusion previously inline in `Correct`;
this avoids repeatedly unfolding the entire concrete compiler result during dependent elaboration.
The witness uses an explicit local IR kernel relation and a proved clone instance, with no external
axioms or foreign gates. It is a satisfiability witness for the inherited abstract IR contracts,
not verification of a physical syscall implementation or ASM hardware execution. The generic
source/image theorem retains all of its original assumptions.

Measured direct IRBild and SourceWitness checks green under slot 1 / 4G soft / 5G hard scope.
Axiom audits for Emitted.correct, irBild_correct and both joint/entry witnesses report exactly
propext, Classical.choice and Quot.sound. No additional language form or totality claim follows
from this fixture; remaining userspace form adapters and named canonical prerequisites stay open.

### IR-09 concurrency inventory and lock-body extension

The canonical frontend already collects `atomT` into atomic globals and exact
payload lists, lowers atomic reads, publish and exchange into G, and checks
concurrent declarations. The actual Stage-0 emitter already implements scalar
publish (store), awaits (load), exchange (CAS loop) and exclusive recursive locks
(take/body/release, including leave/next release stubs). Their generic proof path
is `lowS_ok`/`lowB_ok`/`lowEnd_ok`, `locks_ok`, `awaits_ok`, and the image theorem
consumed by `irBild_correct`. These are existing cases, not new IR-09 coverage.
All inherited `WeltAt`, `SyncOK`, `SichtOK`, gate and runner-kernel premises remain.
This inventory does not identify the sequential image simulation with a complete
GX interleaving/weak-memory compiler theorem.

The lock-body admission gate now recursively accepts `onWhy`, `floatLit` and
`floatOf` when their continuations are return-free. `retFreiGrundArms_istZ` and
the extended mutual `retFreiS_istZ`/`retFreiB_istZ` prove that every admitted
body still excludes both ordinary and reason returns. The existing actual
`lowS` lock branch consumes this gate, and its existing generic `locks_ok`
composition supplies release on normal completion, leave and next. Float range
failures remain logic stops. No ABI representation or atomic algorithm changes.

Exact remaining prerequisites/restrictions:

- Canonical `uRestFehler` refuses `rcuT` with `item without G form`.
  Syntax.lean describes observes as a lock, but the canonical elaborator has no
  RCU declaration/reclamation adapter. Reusing that lock alone would not establish
  reader lifetime or reclamation correctness; no RCU declaration is erased.
- `uAnwReihe` refuses shared lock holding with `shared lock without G form`;
  `uSperre` only accepts its represented declaration shape and masks (`irqs`).
  These source/model boundaries are not bypassed by Stage-0.
- Actual returns inside locks remain refused: the existing lock epilogue handles
  normal/leave/next outcomes, not function returns. General retry/forever and
  fallible-call combinations still need their own return-free control argument.
- Atomic/global payload representation remains subject to the existing scalar
  memory/emitter domain. Full aggregate ABI and memory migration belongs to
  IR-03/06; no low-word aggregate representation is introduced here.
- Root argument/multiplicity/frame work stays with IR-12; this lane does not
  duplicate its pending integration or claim an additional root theorem.

This is an independent connected lock-body extension, not closure of IR-09.

The canonical source reader does not yet construct float binders (also recorded
by the existing `FloatProbe` fixtures); the float gate extension is G-to-IR
coverage only until IR-04 connects those source forms. The new textual case is
reason dispatch under a lock, including loop early exits and subsequent lock
reacquisition. Float binders must not be counted as newly accepted source forms.

Measured for this extension: direct slot-4 checks of Code, OhneRet, the dependent
statement/block/endblock and image proof chain, current Frontend/Compiler/Bindung,
IRBild and Sperre.Proben passed in the private artifact overlay. Six textual
source-to-IR-to-ASM cases matched: lock-reason-dispatch, why-dispatch, why-jumps,
atomic-payload-lock (42 each), sperre and atomar (208 each). The RCU declaration
probe refused explicitly with `item without G form`. Axiom audits of
retFreiGrundArms_istZ, retFreiB_istZ, locks_reason_zeuge, locks_ok, lowS_ok and
irBild_correct contain only standard axioms (the admission/emission witness
needs only propext and Quot.sound). No grammar build or guardian ran. Scratch
and full logs remain local in scratch/ir09; no aggregate consumer ABI was changed.
### IR-01 nested constant-array contract guard closure

The frozen `elabWithScopes` body retains the canonical nested
`uKonstArrays alias (uKonstFns ms) consts ms` call. All canonical `uKonstWert`/`uKonstFns`
call sites were inspected: scalar collection and recursive constant arrays are the only
function-aware evaluation paths; global integer initialization supplies an empty function list.
`ConstantLeaf` describes scalar leaves at arbitrary row depth. `safeConstantValues_member`
and `safeConstantValue_leaf` prove the existing whole-payload guard reaches each leaf;
`Source.source_constant_leaf_hull` connects every original nested initializer call to its
complete SafeHull derivation before any normalization or downstream evaluator is entered.
The generic leaf witness contains two row levels and an actual pure const-function declaration.

Direct Guard and Source checks are green. The persistent `contract-array` negative regression
contains a logical-contract function called inside two array dimensions and measures the exact
compile-time-contract refusal from actual `irBild`, rather than a parser failure. This is mitigation
for the known canonical const-function clause-erasure boundary, not a contract-aware evaluator
or total support for logical-contract compile-time functions. No unchanged broad suite rerun.

### IR-01 direct canonical scalar scopes and custom negative ranges

The current scoped canonical elaborator consumes original declarations and explicit certified
scopes, so the former normalized builtin-only collector encoding is no longer its scalar consumer.
`deriveScopes_of_compatible` proves every old successful complete collector comparison yields
exactly the same entire Scopes record through the direct path.
`elabWithScopes_collector_redundant` specializes that equality to the actual canonical consumer
for arbitrary runtime declaration lists, including every error branch. This justifies removing
that obsolete representation restriction without changing any formerly accepted endpoint.

`deriveScopes` now calls the existing strict `typedConstants` fold over original declarations.
Each step uses exactly canonical `uFeldTyp` and `uKonstWert`, preserving the original range for
every expression intermediate and retaining the entire ordered value environment.
`typedConstants_append` proves source-list composition passes the complete intermediate scope.
`DerivedScopes` retains both original declaration/type/function provenance and `ScopeStable`: the
full final value environment must leave resolved alias ranges unchanged. `Source` stores this
result, `Compiler` supplies it to the unchanged canonical phase body, and CanonicalSourceProgram
now explicitly includes final alias stability. Original SafeHull checks still precede evaluation.
The legacy comparison definitions remain only as the conservative-extension theorem's precise
reference, not a fallback evaluator or a second actual compiler path.

`deriveScopes_custom_negative_zeuge` proves a custom -10..100 range retains NEGATIVE=-1 then
ANSWER=42, although the former complete collector check refused it. The persistent actual
`custom-negative-dependency` source compiles to an image and the existing ASM runner returns 42.
`custom-negative-overflow` computes a final apparent 42 through intermediate 101 and is explicitly
refused at the original canonical range. The nested array contract regression still refuses with
its exact guard diagnostic. Direct Environments/Source/Elaboration/Compiler/IRBild/SourceWitness
checks are green; eight relevant generic/whole-source/witness axiom audits report only the standard
three axioms. No grammar rebuild, widened arithmetic, ABI change or new interpreter.

Remaining limits include alias ranges requiring constants unavailable to the initial canonical
alias preparation, unsupported const-function bodies/logical contracts, non-scalar constant
adapters and the remaining form inventory. Translator/ordinary-record canonical prerequisites
remain separate. IR-01 is incomplete; this step removes one real custom-range restriction.

### IR-01 certified functions in canonical constant arrays

`elabWithScopes` now accepts an optional function scope, defaulting to the exact frozen
`uKonstFns (uOhneSenken (uMembers items))` expression. Its all-old-input `elabU_scopes` equality
remains `rfl`, including errors and gates. Actual Compiler explicitly supplies the original
source-derived Scopes.functions to the existing canonical `uKonstArrays` call. This removes the
second builtin-only signature extraction that prevented alias-typed const calls in array leaves.
No array evaluator or storage semantics is added. `Scopes.functionMeaning` derives every supplied
function's original body, safe clauses and exact canonical signature ranges; the whole-source
CanonicalSourceProgram theorem explicitly retains that generic fact and the identical actual
function list passed to canonical elaboration. Source SafeHull still guards nested rows first.

`canonical_array_functions_zeuge` proves the canonical array result with a source-derived alias
signature, and the failure of the former builtin-only extraction on the same leaf. Actual
`alias-const-array` source compiles through irBild to an ASM result 42. This measured case has one
element, fitting existing lowering; wider aggregate transport remains IR-03's responsibility.
The contracted nested-array call still refuses explicitly. Changed Environments, Elaboration,
Compiler, IRBild and concrete SourceWitness checks are green; six relevant generic/witness audits
use the standard three axioms. This remains a conservative scoped elaboration extension, not an
equality claim between new supplied scopes and the incomplete old scopes for newly supported syntax.

## Rolling worker handoff: concurrency checkpoint

IR-09 published checked lock reason-arm lowering as `e67b53dc8`. It remains incomplete for RCU,
shared lock holding, function returns under locks, full GX composition and dependent ABI/root integration.
Its active slot now implements IR-10 functions/calls/snapshots; it shares Lean slot 4 with IR-04.
This is a worker handoff, not completion of IR-09. Root integrates the coherent green checkpoint separately.

## Rolling worker handoff: control checkpoint

IR-08 published coherent `4ccced168`, including the source-empty-table adapter and genuine large-count
source fixtures. It remains incomplete pending common interval-test deduplication and multiword children.
Its active slot now implements IR-06 memory/byte/reference lowering and shares Lean slot 1 with IR-01.
IR-03 retains frame/call ABI ownership; existing world-layout/relation changes require explicit coordination
before IR-06 mutates shared definitions. The certified producer-v1 pair is immutable preparation evidence,
not a public full-ABI integration milestone.
### IR-01 empty fixed-count tables in the existing canonical model

`Frontend.Tables.tableWithEmpty` adds precisely fixed-count declarations with an explicitly empty
slot field list. It preserves source name, exact `uAnzahl` count, shared flag and tree metadata;
negative newly admitted counts refuse. All invariant-part eligibility checks remain, and original
items remain for canonical `uInvs`, shared-guard checks, remaining elaboration and the full checker.
Nonempty/open/other declarations continue through unchanged `uTabelle`. `tableWithEmpty_sound`
proves every successful export is either exactly canonical or has `EmptyTableMeaning`, including
complete original declaration provenance, canonical count evaluation and empty columns.
`emptyTable_model` proves the existing declOf count is unchanged, fieldCount=0, the field type is
empty and the table is closed. No field, occupancy mark, provider or storage semantics is invented.

`elabWithScopes` takes an optional table-lowering function defaulting exactly to frozen `uTabelle`;
its all-old-input `elabU_scopes` equality is still rfl. Actual Compiler supplies tableWithEmpty and
CanonicalSourceProgram includes its generic source-provenance contract as well as the identical
actual canonical elaboration/program endpoint. This remains a compiler elaboration extension
over existing canonical table semantics, not a claim old uTabelle accepted empty fields.

Actual `empty-table` source retains count 2^32 and compiles to ASM exit42. A negative-count source
measures the explicit adapter refusal. SourceWitness now includes a real count-2^32 empty table:
`table_count`/`fieldless` prove its exact count and empty field domain; a generic fieldless-world
constructor provides its concrete World without allocating nonexistent field cells. The accepted
source/image, initial memory/arguments/gate/view contracts and actual IR simulation remain jointly
witnessed. This does not test executing a 2^32-iteration traversal. IR-08 owns the separately green
wide traversal and fieldless_table_layout theorem; fieldCount=0 from this model bridge is its exact
interface. No image, word, layout or resource bound was weakened.

Tables, Elaboration, Compiler, IRBild and updated SourceWitness direct checks passed under slot1
4G/5G scope. Eight generic/whole-source/witness audits retain only the standard three axioms.
No grammar build or Senke file was changed. Wider source traversal integration is a separate
combined-snapshot validation with IR-08; IR-01 coverage remains incomplete.

### IR-01 dependent scalar/type scope discovery

`DependentScopes.elaborateScopes` preserves every successful conservative deriveScopes result
exactly (`elaborateScopes_preserves`), and only attempts discovery after a refusal. Discovery
reuses existing alias/constant normalization and the frozen collector to propose values; these
proposals are untrusted. `resolveCandidate` evaluates the full ORIGINAL ordered typedConstants
fold using canonical uFeldTyp/uKonstWert, then compares the COMPLETE alias environment against
`original.foldl (aliasStep finalValues) []`. It stores finalValues, not discovery input. Every
integer alias declaration must resolve on this new path; unresolved cycles refuse, and bounded
discovery never converts exhaustion into acceptance. Existing initial-path behavior is unchanged.
`resolveCandidate_final` and `discoverScopes_final` prove final-original-value alias provenance.

Scopes now records aliasConstants and its origin: frozen canonical initial collector values
(for the existing path), or the final strict original scalar values (for discovery). Its alias
fold and ScopeStable are indexed by those explicit inputs. Compiler's whole-source contract
retains this origin together with exact ordered scalar values, original function meaning and
actual unchanged canonical elaboration/lowerAllg/checker endpoint. No new expression evaluator,
widened builtin, default-zero binding, filtered negative or invented translator semantics occurs.

Actual `dependent-alias` and `dependent-alias-negative` source->IR->ASM both return42, including
a computed alias-typed LIMIT, dependent range, further alias chain, and negative intermediate.
The original-range overflow case and cyclic type/initializer case measure precise refusals.
The formal dependent-scope witness proves the former conservative path refuses its fixture.
SourceWitness now jointly includes the actual alias-typed pure negative function, NEGATIVE=-1,
C=42, dependent Bound/Final ranges, ANSWER=42 and count-2^32 fieldless table; aliases_final proves
this accepted source/image uses final original values. Its concrete initial contracts and actual
IR simulation remain jointly inhabited.

Environments/DependentScopes/Source/Elaboration/Compiler/IRBild/SourceWitness checks green; nine
relevant generic/whole-source/witness audits use only the standard three axioms. Slot1 checks
were deferred during root's requested merge-check priority, then resumed after explicit release.
No grammar build, Bindung change, pre-emit ABI-guard edit, Senke/ABI edit or broad unchanged suite
rerun. Discovery completeness for all dependency graphs is not proved; nonmaterializable custom
negative bounds and further constant/signature forms may still refuse. IR-01 remains incomplete.

### IR-01 canonical typing of every original constant array

The frozen uKonstArrays collector silently filters failed folds; logical-contract call guards
already blocked known unsafe functions, but unused unknown calls or wrong-dimensional literals
could otherwise disappear. Actual Compiler now calls `ArrayConstants.checkArrays` after the exact
canonical unit is elaborated and before lowerAllg. Each original array must have its exact uTyp,
a value from the existing uKonstZeile evaluator with the certified function/value scopes, and a
closed typed Expr from existing Allg.lowLit in the ACTUAL unit's declaration universe. This checks
every dimension and element range; malformed non-array row initializers explicitly refuse.
No replacement evaluator, fake declaration universe or inferred function contract is introduced.

Compiled retains all original ArrayMeaning facts, and CanonicalSourceProgram/source->image
correctness includes them. `arrayMeaning_collected` proves each such original array is present
in the canonical collector with its exact typed literal, closing the filterMap omission boundary.
SafeHull still checks original nested calls before any scalar/array evaluation. This strengthens
source validity; it is not logical-contract-aware const evaluation or full aggregate transport.

A combined large dependent-source/array witness exceeded the mandated kernel memory cap. The
limit was not raised. The existing rich negative/dependent-alias/fieldless SourceWitness stays
green; ArrayWitness separately compiles a real nondegenerate nested array source, proves exact
parsed array shape, typed value and collector membership, and constructs the same jointly
inhabited initial contracts through reusable InitialState.ofFieldless. Its actual entry IR
simulation is proved. Proofs avoid full source-AST equality reduction and unsupported AST BEq
soundness assumptions by using Option.get membership and a kernel-checked exact shape.

Measured: unknown unused array call, wrong length, intermediate overflow, scalar row initializer
all refuse with exact diagnostics; nested alias-typed const-function array access executes as
ASM42; contracted nested array still refuses. ArrayConstants/Compiler/IRBild/SourceWitness/
ArrayWitness direct checks pass within 4G/5G scopes. Nine generic/whole-source/witness audits
report only propext, Classical.choice, Quot.sound; layout check passes all1399 Lean files.
No unchanged broad suite or grammar build was run. Two Lean checks globally now control work:
IR01 stays slot1, all own harnesses route each check/run/audit through the same capped slot1
launcher with unset ELAN_TOOLCHAIN and isolated outputs. Other workers' slots remain root-owned.
No Bindung/pre-emit ABI guard or Senke code was edited. IR-01 remains incomplete on the listed
remaining constant/type/signature forms, discovery completeness and canonical prerequisites.

### IR-05 bounded inventory (base c84ef50cc, 2026-11-01)

The canonical frontend is `uOptEin`/`lowOpt`, `uBool`/`lowEns`,
`UebersetzeSum`, `lowSeqL`/`lowArmsT`/`lowGArmsL`, and `uWhys`;
Stage0's scoped frontend retains those consumers. The canonical typed forms are
table-index options and sums with zero or one bounded-integer payload; other
payload shapes refuse in the frontend. All nine owned forms have model and
frontend paths; none is wholly missing. Status below describes the actual
baseline emitter, not complete family coverage.

| Form | Baseline status and exact remaining boundary | Connected proof |
|---|---|---|
| Expr `none` | Compiled; word -1, no payload. | `lowE_ok` |
| Expr `some` | Compiled when its index expression lowers; keeps that word. Wide indices and sentinel-safe consumers remain restricted. | `lowE_ok` |
| Expr `istSome` | Compiled for table bound <= 2^63; larger bounds refused. | `istSome_ok` through `lowE_ok` |
| Expr `case` | Compiled for <=256 tags, every payload interval width <2^56, and selected payload lower bound in signed32; child emission must succeed. Other cases refused. | mutual `lowN_ok`/`lowE_ok`, `packSum_ok` |
| Expr `why` | Compiled for reason count <2^31; larger counts refused. Encodes the ordinal, not the external code. | `lowE_ok` |
| Stmt `onOption` | Compiled for bound <=2^63 and compilable arms; sentinel test preserves the Some index binding. Larger bounds refused. | `onOption_ok` in `Anweisung/Satz.lowS_ok` |
| Stmt `onTag` | Compiled for the same packed sum limits, signed32 payload lower bounds in all arms and compilable bodies. Other cases refused. | `onTag_ok`/`lowTags_ok` through `lowS_ok` |
| Stmt `onWhy` | Already compiled for count <2^31 and compilable reason arms; no payload binding. Larger counts refused. | `onWhy_ok`/`lowGrund_ok` through `lowS_ok` |
| TopLevel `whyT` | Compiled by canonical `uWhys` for exhaustive declarations; non-exhaustive reasons explicitly refused by the frontend. Binding code separately retains external reason codes. | canonical source provenance in `compile_source_program`/`Emitted.correct`, then `irBild_correct` |

`lowB` and `lowEnd` call `lowE` for binders and `lowS` for nested
statements; the mutual `lowS_ok`/`lowB_ok`/`lowEnd_ok` dispatcher connects
these forms to function/image correctness. Fallible-call reason bindings use
the existing slot-2 result-or-reason channel and status at FB+parameter-count+1.
The canonical direct `let x = f()` adapter also refuses sum-valued results
with `call without a value`, although canonical sum expressions/results exist.
Sum arguments likewise refuse with `argument without G form`. These call
adapters remain IR-10 prerequisites, not new constructor cases.
Multiword payloads, shared widths/ABI and broader frontend/model prerequisites
remain open with their owning lanes. The first bounded step selected the
signed32-lower-bound refusal of the one-word `case` constructor; the decoder
follow-up below closes the matching dispatch restriction. The ABI is unchanged.


The selected `Expr.case` extension is now connected: `packSum` reuses
`wordConstant` for the payload lower bound, and `lowN` no longer requires that
bound to fit signed32. The existing small-immediate path, packed encoding,
`sumFits` guards and child-emission requirements remain. The extra materializer
scratch word is included in the returned high-water mark. `packSum_ok`, the
mutual `lowN_ok`/`lowE_ok`, the statement/block/end-block dispatcher and
`irBild_correct` compile on that same implementation. The real-memory
`AggregateProbe.Case.simulation_zeuge` jointly supplies all expression premises,
proves the exact word 10753 (tag 1, offset 42), and checks top=7 at destination 4.

Measured in the private `.scratch-ir05` overlay, each Lean invocation under the
capped slot-2 lock: 131 affected modules through IRBild/Haupt plus Aggregate/Proben
pass. Three new textual constructor probes (positive, negative and unsigned64
lower bounds) and five existing option/tag/reason probes execute with their
expected ASM exit codes. The new probes execute runtime-payload construction;
the exact packed result is checked by the formal witness. The same three new
sources were explicitly refused by the baseline emitter. At that checkpoint, two
additional textual probes refused width 2^56 and large-bound tag decoding.
All 13 audited statements use only propext, Classical.choice and Quot.sound;
`gabbro_ziel` retains exactly those three. Layout passes for all 1471 Lean files;
all six changed Lean modules remain below 500 lines. Grammar artifacts were reused.
That constructor-only checkpoint left large-bound `onTag` open. Wider sums,
options/reasons beyond the listed domains and multiword ABI integration remain open.


The decoder mirror step now removes the signed32 payload-lower-bound refusal
from `tagPayloadC` using `wordConstant`. Its small-immediate path, packed
encoding, `sumFits` and width-2^56 refusal are unchanged. The existing three-word
dispatch scratch bound covers the materializer. `tagPayload_ok`/`tagArm_ok`,
`lowTags_ok`/`onTag_ok`, mutual `lowS_ok`/`lowB_ok`/`lowEnd_ok` and
`irBild_correct` compile on the actual emitter. The real-memory
`TagDecodeProbe.simulation_zeuge` constructs word 10753 and decodes 2^32 + 42;
`dispatcher_zeuge` admits positive, negative and unsigned64 lower bounds.
All 246 private direct module checks through Haupt, Stage0 and Nachpruefung pass.
Twelve textual source-to-IR-to-ASM executions pass, including both runtime
payload endpoints, skipped large-bound arms, and the promoted former decoder
refusal (`case-offset-dispatch`). The width-2^56 probe still refuses. All 14
focused axiom audits, including `gabbro_ziel`, report exactly propext,
Classical.choice and Quot.sound. Layout passes for 1472 Lean files; the five
changed Lean modules stay below 500 lines. Checks use the private worktree
overlay and capped slot-2 lock; grammar artifacts are reused. This closes one decoder
restriction, without extending the remaining packed-width, option/reason or ABI
domains above.

### IR-07 bounded inventory (base a6970b425, 2026-11-01)

Read against canonical `Kern/Syntax/Syntax`, `Kern/Semantik`,
`Bausteine/Arena` and `Parser/Elab/Uebersetze{,Allg,Allg2,Allg3}`;
Stage0 uses `Frontend.elabWithScopes`, `Compiler.compile`, `lowE`/`lowS`/
`lowB`/`lowEnd` and the mutual `Anweisung/Satz` dispatcher. No device-register
transition is included. A typed emitter alone is not textual form coverage.

| Owned form | Baseline status and exact boundary | Connected proof / prerequisite |
|---|---|---|
| Stmt `shift` | Compiled for signed-word field intervals, signed32 old/new stage numbers, compilable index and address. Other representable old/new constants are refused solely by the emitter. Frontend `uZustandVon`/`lowShiftL` checks declared transition, destination range, write effects and guards. | `shift_ok` in `lowS_ok`, then `lowB_ok`/`lowEnd_ok`, function/image correctness. Selected bounded extension: materialize both signed-word state constants with the existing word materializer. |
| Stmt `breaking` | Typed emitter compiles its body and the mutual proof recurses into it. Textual `breaking` (`SAnw.waive`) has no `uAnwReihe` export case: refused as `stmt without G form: waive`. | Existing model rule and `lowS_ok` branch; missing canonical frontend export, not missing IR emitter. Invariant restoration at returns must remain mandatory. |
| Stmt `advances` | Typed emitter emits no instructions, matching `execStmt`'s unchanged runtime world. Source statement (`SAnw.step`) is refused as `stmt without G form: step`; function `moves` clause as `clause without G form`. | Existing model rule and `lowS_ok`; missing mark/signature export (`declOf` has `Marke := Empty`, no owner marks), not missing emitter. |
| Stmt `retires` | Typed emitter likewise emits no instructions with a connected `lowS_ok` branch. Source `quits` clause is refused as `clause without G form`. | Existing model consumes a held mark and names its assumption. Missing canonical mark/signature export, not missing emitter. |
| TopLevel `arenaT` | Fixed positive capacity, scalar element, no placement: exported to table plus `#used` static. Block-position `alloc A(v) else { ... }` expands through `Block.arenaAlloc`; `reset A` is a counter store. Dynamic ceiling/placement refuse as `arena with a dynamic ceiling without G form` / `arena placement without G form`. Top-level/else-position alloc refuse explicitly in `lowBodyF`/`lowEndL`; alloc without else, grow/free and extended reset are not exported. | Existing `ArenaZucker` and lowerings of bind/narrow/stores connect block allocation; no separate allocator emitter is needed. Dynamic/ownership arena models exist in `Bausteine/Arena`, but their canonical source-to-G bridge and lifetime/availability obligations are missing. Wider element storage additionally needs IR-03. |
| TopLevel `stateT` | Compiled by `uZustand`: named stages become ordinals in first-written order; allowed pairs feed `D.erlaubt`. State-transition requires/effects clauses refuse as `state transition clause without G form`; non-name stages as `state stage without G form`. | Source provenance (`compile_source_program`), checked `lowShiftL`, then `shift_ok`. Clause-bearing transition semantics need a canonical model/export rule; this lane adds none. |
| TopLevel `groupT` | Compiled by `uInvs`/`uInv` for ordinary table carriers and predicates accepted by `uBool`/`lowBool`; locks checked by `uU003` and canonical invariant checking. Arena/global carriers refuse as `invariant carrier without G form`. Runtime compilation still depends on predicate emission. | Canonical `Programm.invariante`, checker, source provenance and function/image proofs; richer carriers need canonical export/checking support, not an isolated group emitter. |

Additional parent-lane obligations: `table ... backed ...` and `owner ...` refuse
as `table without G form` in `uTabelle`; the canonical ownership model exists,
but `declOf` exports neither owner marks nor their resource contracts. Open
`table T from provider` exports a numeric-field region and `alloc T` becomes a
provider call; actual fresh/disjoint provider memory, layout extension and
lifetime contracts remain a missing provider-contract integration (IR-06 memory
primitives already accept supplied region cells). A plain numerical provider
answer cannot close it. No existing guarantee may be replaced with an unchecked
address. Multiword transport remains IR-03-owned. None of the seven owned typed
families is absent from the model; the textual/export restrictions above remain
open even where typed soundness is connected.

The canonical arena sugar does not carry reservation `lo` (`ArenaZucker` documents
that boundary). `uInv` exports the name, carriers and predicate, not the source
cost/online/proof metadata. These source-to-model boundaries are not counted as
completed by the existing primitive emitters.

The bounded `Stmt.shift` step now materializes both state constants with
`wordConstant`, retaining its immediate fast path. The field interval and old
state must fit signed64; the destination still carries its original field-range
proof. Unsigned intervals above signed64, unrepresentable states, missing index
or address emission and the other inventory boundaries remain refused. No ABI,
canonical model, ownership rule, provider contract or source syntax changed.
The existing eight-word scratch allowance covers both materializers. `shift_ok`
uses signed-word injectivity for the old-state comparison and the shared
materialization theorem for the write; the mutual dispatcher, `lowFun_spec`,
`Emitted.correct` and `irBild_correct` remain connected to the actual emitter.

`ShiftProbe.simulation_zeuge` jointly supplies the real code/frame/table-memory
premises: cell one initially holds 2^32 + 41, becomes 2^32 + 42, cell zero stays
zero and protected frame slot three stays 77. Both state constants fail signed32.
Textual stages remain dense named ordinals; the large-constant path is exercised
by this typed memory witness, not by claiming a practical text declaration with
billions of stage names. Four textual source-to-IR-to-ASM executions pass (two
new, two existing), including the state sequence on a signed64-sized field and
failed-prestate stop 106. Two new textual refusal probes retain missing write
permission and undeclared-edge errors.

Measured in the private `.scratch-ir07` overlay: 153 Stage0 modules pass direct
checks, including the statement/block/end-block dispatcher and IRBild/Haupt.
All nine focused axiom audits, including the memory witness and `gabbro_ziel`,
report exactly propext, Classical.choice and Quot.sound. Layout passes for all
1473 tracked Lean files; all five changed Lean files remain below 500 lines.
Every Lean invocation used the capped slot-2 lock, with ELAN_TOOLCHAIN removed;
grammar artifacts were reused. No full guardian or grammar rebuild was run.
This closes the one-word signed-state constant restriction, not the remaining
source-export, provider, ownership or multiword boundaries in the inventory.

### IR-13 bounded inventory

Baseline `6444b5cc3` (2026-11-01). Ownership is exactly TopLevel
`formatT`, `checkT`, `accT`, `walkT`. Read against canonical
`Kern/Syntax/{Syntax,Zucker}`, `Kern/Semantik`,
`Parser/Item/ElementTief`, `Parser/Elab/Uebersetze{,Allg,Allg2,Allg3,Pipeline}`,
`Isabelle/{FormatRoundtrip,AccumulatesMonoid}` and
`Bausteine/Schablonen/SchablonenT5`. Stage0 was traced through
`Frontend.{Source,Elaboration}`, `Compiler.compile`, `lowE`/`lowS`/`lowB`/
`lowEnd`, the mutual `Anweisung/Satz` dispatcher and `IRBild`.

| Owned form | Status and exact refusal | Canonical model, connected primitives and missing boundary |
|---|---|---|
| `formatT` | **Refused: needs grammatik export.** `uRestFehler` has no `formatT` case and returns `item without G form`, including unused declarations. The parser retains optional version/endian, field types/ranges, positions, `offset_into`, `where` and reserved fields; none reaches an executable format export. | `Syntax` describes a count-one table and field checks; `Expr.getBytes`, `Stmt.putBytes`, `Expr.bitfeld`/`embeds` and `bytesZuZahlBig` provide model components. Actual byte emission is limited to at most eight bytes, with `readBytesL_ok` in `lowE_ok` and `putBytes_ok` in `lowS_ok`; `Block.check` reaches `blockCheck_case`/`lowB_ok`. There is no source-format layout/reader/writer/validation expansion or its generic preservation proof. `FormatRoundtrip.roundtrip` is a byte-list theorem, explicitly not the missing world-memory/emitter bridge. `@version` parsing is not version-reader support. Wider represented values additionally need IR-03. |
| `checkT` | **Refused: needs grammatik export.** Every `SCheck` payload reaches `uRestFehler`'s `item without G form`; `claim`, `measures`, `gates`, `can_fail`, optional floors and counterprobes are not exported. | The intended model is a generated `Duty` mark with producing/consuming function signatures (`Signatur.produziert`/`konsumiert`, `Res.marke`, `nachSig`, `RufPasst`). However `declOf` fixes `Marke := Empty`, and `mkSig` exports empty produced/consumed lists. The generated checker, measurement/floor obligations and gate signatures need canonical export and a generic expansion proof. The compiled boolean `Block.check` is a different construct and cannot replace the linear duty. |
| `accT` | **Refused: needs grammatik export.** All five merge operators (`max`, `min`, `add`, `or`, `and`), both ordinary and `per cpu` declarations, receive `item without G form`; no accumulator global or operations are generated. | `Syntax` describes a global plus generated assignment; `Stmt.mergeMax`/`mergeAdd` desugar into ordinary conditionals, reads, arithmetic and stores, whose existing `lowE_ok`/`lowS_ok` branches are connected. `mergeAdd` retains explicit range premises. `AccumulatesMonoid` proves abstract order independence, neutral elements and fold/RMW equality, but explicitly leaves per-core cell layout/initialization and its compiler bridge open. Export of the declaration, all generated operations and the per-core/quiescence contract is missing even for one-word types; plain stores cannot supply it. Larger value transport additionally needs IR-03. |
| `walkT` | **Refused: needs grammatik export.** Every `SWeg` payload receives `item without G form`: constant levels, node type, down field/predicate, leaf predicate and invariants never reach a canonical walker expansion. | `Stmt.walk2` is exactly two nested `Stmt.traverse` terms. The actual traversal emitter uses `travC` with a representable count, emitted invariant and body; `traverse_case` in `lowS_ok` recurses through `lowB_ok`. This supplies reusable primitives, not the declared walker. `walk_hits_mapping` proves membership in an abstract filtered entry list; it does not prove that source down/leaf predicates generate the correct traversal, mapping witnesses or large-page cases. That source expansion and its generic proof are missing. Record-shaped nodes also retain the canonical record-model/export prerequisite; multiword node values additionally need IR-03. |

All four constructors exist in the canonical deep parser; none is a missing
parser node, and **zero of these four source families compile with a connected
lowering theorem**. `uMembers` retains them when opening module/public wrappers;
`Frontend.source` does not desugar them. The first runtime elaboration step in
`elabWithScopes` is the unchanged canonical `uRestFehler`, also used by `elabU`.
`Compiler.compile` propagates its error before `lowerAllg`, the full checker or
any emitter runs. The existing generic primitive theorems continue through
`lowFun_spec`, `Emitted.correct` and `irBild_correct` only when the corresponding
canonical program actually exists; their existence does not close these exports.

No owned form is blocked **only** by a Stage0 emitter/proof. A one-word field,
merge value or one-level walker still encounters the same earlier export
refusal. The bounded implementation condition is therefore false. This task
stops at the inventory: no grammar/model/syntax/ABI change, parallel export,
handwritten replacement program or detached emitter is introduced. The frozen
canonical export is the immediate blocker; the model/expansion obligations
identified above must be checked when that boundary is authorized to change.

Measured in this worktree's private `.scratch-ir13/lib` overlay: ten frontend
modules passed direct Lean checks, including `Frontend.Source` and
`Frontend.Elaboration`. A scratch kernel audit checked eight generic equations:
all four arbitrary constructor payloads are refused both by `uRestFehler` and
by the actual `elabWithScopes` phase, independently of declaration scopes.
All 18 textual probes passed lexer/parser, constructor retention, the actual
`Frontend.source` checks and scoped elaboration's exact `item without G form`
refusal. They cover format endian/version/field variants, both check tails,
all five merge operators, per-CPU accumulation, one/four-level walkers and
module/public wrappers. These measure frontend refusals, not successful IR/ASM
executions or well-formedness of an unexported generated program. No new form,
emitter theorem, full compiler rebuild, full guardian or grammar build is
claimed. Every Lean invocation used slot 1 with ELAN_TOOLCHAIN removed,
`-j1 -DElab.async=false -M4608`, MemoryHigh=4G/MemoryMax=5G/no swap; frozen grammar
artifacts were read only. `git diff --check` passed. Scripts, the corrected
scratch fixture and logs remain in `.scratch-ir13/`; only this inventory is
committed.

### Grammatik export catalogue (2026-11-01)

Read-only audit of **42d30ce4074ef4283a9131e9382c994959353757**. No Lean
invocation, grammar build or execution probe was made. This catalogue refines
the bounded IR-07/IR-13 inventories: a `without G form` diagnostic does not by
itself establish that the canonical model lacks a rule.

**Count: 32 A packages, 8 B packages, 18 C packages.** The counting unit is one
numbered package below, including its explicit bounds, not a parser constructor,
diagnostic occurrence or compiled program. A has an executable G construction
and an actual Stage0 emitter with a connected generic proof branch; source
expansion and its preservation proof remain to be implemented. B has existing
model semantics but also needs Stage0 work. C lacks a canonical source/admission
rule or semantic binding and is **not a pure export**. Abstract value/library
theorems alone do not establish executable source semantics. B/C explicitly
cover the variants outside an A row's domain; an A row is not whole-family
coverage. In particular, the four IR-13 declarations are not four completed
source expansions.

**Coordinates.** All `Uebersetze*.lean:line` references below are exact source
coordinates under `grammatik/Grammatik/Parser/Elab/` at the audited commit.
`S` denotes `grammatik/Grammatik/Kern/Syntax/Syntax.lean`, `Z` its sibling
`Zucker.lean`. `Ty` is defined in `Kern/Syntax/Typen.lean:35`. Their meanings
are `eval` in `Kern/Semantik/Semantik/T1.lean` and `execStmt`/`execBlock`/
`execEnd` in `Kern/Semantik/Semantik/T2.lean`. For example, `breaking` recurses
at T2:216; advances/retires leave the runtime world unchanged at T2:245/246.

| Canonical model | Actual Stage0 emitter and connected proof (paths under `stage0/Stage0/`) |
|---|---|
| `Expr` (S:422), quantifiers/reachability/references/aggregates (S:500/507/510/515) | `Senke/Ausdruck.lean` and `Ausdruck/Gleichungen.lean`; `lowE_ok` in `Senke/Ausdruck/Satz.lean:34`. Successful emission is a premise, not a coverage theorem. |
| `Stmt` / `Block` / `Endblock` (S:569/651/721) | `lowS` / `lowB` / `lowEnd` in `Senke/Anweisung.lean:174/292/415`; mutual `lowS_ok` / `lowB_ok` / `lowEnd_ok` in `Senke/Anweisung/Satz.lean:50/352/459`. |
| `Stmt.breaking/advances/retires` (S:610/637/640) | Emitter branches `Anweisung.lean:279/280/281`, proof branches `Anweisung/Satz.lean:146/151/152`. No separate instruction is necessary for a declaration/resource index. |
| Runtime check, traversal, bytes, state shift | `blockCheck_case` (`Senke/Anweisung/Faelle/Kontrolle/Check.lean:32`), `traverse_case` (`Faelle/Schleifen/Traversal.lean:15`), `readBytesL_ok` (`Senke/Ausdruck/Bytes.lean:17`), `putBytes_ok` / `shift_ok` (`Senke/Anweisung/Bytes/Put.lean:12`, `Shift.lean:17`), called by the mutual dispatchers. |
| Unit/image composition | `Compiler.compile_source_program` (`Compiler.lean:80`) records the elaborated program; existing emission proofs compose through `lowFun_spec`, `Emitted.correct` (`IRBild.lean:96`) and `irBild_correct` (`IRBild.lean:113`). They do not invent semantics for an unexported surface macro. |

**Sweep.** All six `Uebersetze*.lean` modules were searched for literal and
computed error strings, `without G form`, `no G form`, `lacks` and default
matches. The matches were compared with `STyp`, `SExpr`, `SAnw`, `SKlausel`,
`STabTeil` and `SItemTief`. The actual route is `Frontend.source` →
`elabWithScopes` (`Frontend/Elaboration.lean:10`) → `lowerAllg` → compiler and
emitter; `elabWithScopes` still invokes canonical `uRestFehler` first. Existing
Stage0 adapters matter: `pre108` resolves names/imports and opens module/public
wrappers, checked scopes normalize supported aliases/constants, and
`Frontend/Tables.tableWithEmpty` already handles empty fixed-count tables.
Those older canonical refusals are not outstanding packages. The specialized
`104 lowering` and later witness functions in `Uebersetze.lean` are not the
general compiler route and add no count.

**Common preservation duties for A/B:** exact names/types, evaluation order,
old/result scope, guards and declared writes/effects; exact resource indices
(`darf`, `gdarf`, `RufPasst`, `nachSig`, return `Perm`), not empty replacements;
all required invariant restorations, failure/nonreturn outcomes and canonical
budget/recursion accounting. Cost, floor, online/offline, proof and reservation
metadata must not vanish merely because an existing export omits it. Every
new expansion needs generic source-to-G preservation and a nondegenerate witness,
connected to the existing IR proof. Tests or abstract roundtrip/monoid theorems
do not replace that bridge. No row authorizes an OS assumption, numerical
pointer or another interpreter.

**A — pure export, Stage0 ready within the stated domain.** No new model rule
is needed for these bounded constructions. The last column names existing IR
proofs and the still missing export obligations, not a completed source theorem.

| ID / source form | Exact refusal or absent export | Target canonical construction | Existing Stage0 proof; what export must preserve |
|---|---|---|---|
| A01 `breaking I { ... }` | `Uebersetze.lean:2538`, `stmt without G form: waive`, via `uAnwReihe` default | `Stmt.breaking` (S:610) | `lowS_ok` branch :146 recurses through `lowB_ok`. Resolve each invariant name (multiple names become nested scopes); retain body/exits and invariant restoration at return. |
| A02 linear/ghost mark order, `consumes`/`allocs`, advances clause/statement | `Uebersetze.lean:1925/1952/2538`: `effect without G form`, `clause without G form`, `... step`; `UebersetzeAllg.lean:231/232/382` fixes empty signatures/`Marke := Empty` | `D.Marke/stufen`, `Signatur.konsumiert/produziert`, `Res.marke`, `nachSig`, `Stmt.advances` (S:185/89/287/306/637) | `lowS_ok` :151 and generic call/bind/return branches. Export one consistent mark namespace, exact flow/conformance/return resources, possession and `a+1 < stufen`; never produce an owner mark. Complete owner minting is C09. |
| A03 `retires m from s ...` | `Uebersetze.lean:1953`, `clause without G form`; raw `quits` tail has no body export | `Stmt.retires` (S:640), final resource list | `lowS_ok` :152. Resolve mark/stage/assumption, consume exactly that mark on the correct exits and retain assumption provenance. Runtime erasure is not erasure of the obligation. |
| A04 `table ... owner m` guard metadata, given valid initial ownership | `Uebersetze.lean:1172`, `table without G form`; `UebersetzeAllg.lean:382/387` exports no owners | `D.eigner`, `D.braucht` with `.inr (m,s)`, `darf` (S:190/192/301) | Generic `lowE_ok`/`lowS_ok` slot/thru/store proofs. Export shared/owner guards, uniqueness and `eigner_nie_erzeugt`. The current `own`→writable Bool conversion is insufficient; minter/borrow-return semantics are C09. |
| A05 scalar `table ... backed k` and backed accesses | `Uebersetze.lean:1172`, `table without G form`; runtime narrow bounds also :2860 | Static count plus explicit `Block.check`/`Block.narrow` and slots (S:699/703) | `blockCheck_case`, `lowB_ok`/`lowEnd_ok`. Preserve address-space count versus backed bound; prove the backing guard before each access, not just `i < count`. Preserve table identity through narrowing. |
| A06 table constants, `ops insert/remove/relabel`, `occupied f`, on represented scalar tables | `Uebersetze.lean:1132/1163/1165`, `table without G form` for non-invariant parts | Generated Fn/signatures/requires/calls/conditionals/stores (S header :31; ordinary `Stmt`/`Programm`) | `lowE_ok`/`lowS_ok`/`lowFun_spec` for generated functions. Generate freshness/reachability/leaf/occupancy contracts, exact effects and `by ops` writer discipline. No dedicated ops instruction is needed; a generic source generator proof is still missing. |
| A07 scalar dynamic arena ceiling, constant `grow ... by n else ...`, dynamic alloc over represented storage | `Uebersetze.lean:3992` (`arena with a dynamic ceiling without G form`), :2538 (`... grow`) | `DynForm`, `Block.dynGrowB/dynAlloc` in `Bausteine/Arena/ArenaDyn.lean:270/341/362`, reducing to check/narrow/stores | `lowE_ok`/`lowB_ok`/`blockCheck_case`; canonical `dynGrow_commit`/`dynAlloc_simuliert`. Export committed counter, `used <= committed <= M`, failure and effects. Physical provision/commit is B06/C08, not established by a counter update. |
| A08 scalar `free A[i]` and free-list allocation | `Uebersetze.lean:2538`, `stmt without G form: free`; no reuse export | `FreiForm`, `Block.freiVar` (`Arena/Struktur/Formen/ArenaAllocForm.lean:34`), `Block.freiNimm` (`Arena/Struktur/ArenaFrei.lean:386`) | Existing store/bind/check proofs; canonical `freiVar_ausfuehren`/`freiVar_lebt`, ownership `release_post`/`allocList_post` (`Arena/Ownership/Body/Forms.lean:195/125`). Attach the actual ownership judgment: consume origin, invalidate aliases, prevent double-free/use-after-free. Two emitted stores alone do not close this. |
| A09 arena lock carriers and table/arena group invariants | `Uebersetze.lean:1181` (`arena under a lock without G form`), :4338 (`invariant carrier without G form`) | `D.braucht/traeger`, `Programm.invariante`, `Stmt.locks` (S:190/206/813/605) | `locks_ok`, `lowS_ok`/`lowB_ok`. Preserve table-cell footprints, metadata guards, rank/U003 and restores. An invariant over a counter/global has the separate C05 boundary; do not disguise that global as a table carrier. |
| A10 already evaluable constant expressions in counts, bounds, lock ranks, payload ranges and initializers | `Uebersetze.lean:998/1018/1022/1033/1067/1212/1805/2853/2860/3816/3892/3915/4226` | Existing typed bounds, literal indices/counts, `D.rang`, `Expr.lit`, initial values | `lowE_ok` and existing initialization. Reuse checked scopes with exact sign/range/overflow/storage width. Only expressions already denoted by the canonical constant evaluator qualify; arbitrary compile-time control/contracts are C17. |
| A11 constant numeric state stages and transition through a table capability | `Uebersetze.lean:4306` (`state stage without G form`), :2513 (`transition through a pointer without G form`) | `D.erlaubt`, `Stmt.shift` (S:161/588) | `shift_ok` in `lowS_ok` :159. Preserve actual constant stage values, declared edge/range, table identity, write/guard checks and prestate failure. Do not replace numeric stages by ordinals. Edge contracts are C04. |
| A12 implication `p => q` | `Uebersetze.lean:1604`, computed `ensures clause without G form` default | `Expr.impl = or (not p) q` (Z:139) | `lowE_ok` Boolean branches. Preserve predicate/binder scope, footprint and old/result legality, including generated contracts/invariants. |
| A13 domain membership, `a reaches b via f`, chain membership | `Uebersetze.lean:1604/1490`, predicate/compare-side defaults | `Expr.member/chain` (Z:156/169), `reaches` (S:507), `existsSlots` | `reachesL_ok` and quantifier branches in `lowE_ok` (`Ausdruck/Satz.lean:465/468/471`). Preserve guarded table, option-self edge type, bounded-chain meaning and index identities. |
| A14 finite unvisited traversal/quantification over descendants, ancestors, queue, explicit scheduler tables and one-word fixed-array elements | `Uebersetze.lean:1570` (`quantifier domain without G form`), :3173/3174 (`traverse of/domain without G form`) | `Expr.descendants/ancestors/queue` (Z:159/164/173), quantifiers, filtered `Stmt.traverse` (S:611) | `lowE_ok` reach/quantifier branches, `traverse_case` in `lowS_ok`. Derive declared edges/carrier and element indices, filter, binder scope, invariant and leave/next. Use existing arrGet for represented elements. Record fields/mappings are C01, wider arrays B02, consuming traversal C11. |
| A15 ordinary `Held(L)` predicates after resource admission | `Uebersetze.lean:1604`; special `requires Held` collection already exists | Fact `Res.held L in Λ` (S:288/301), checked reification to `Expr.tru` | `lowE_ok` true branch. Prove possession in the current Λ, never accept by spelling; retain lock signature/floor. Shared witnesses depend on C10. |
| A16 string equality/order with both maxima <=1 byte | `Uebersetze.lean:1541` comparison dispatch, :1490 default; `UebersetzeAllg.lean:1189` (`aggregate as a number`) | `Expr.strEq/strLt` (S:531/533), Boolean combinations | `strCompare_ok` in `lowE_ok` (`Ausdruck/Satz.lean:66/69`). Preserve byte/length order and maximum bounds. Longer strings are B02. |
| A17 same-region reference equality/inequality | Numeric comparison path `Uebersetze.lean:1541`; `UebersetzeAllg.lean:1189` / `zahlVon` refuses the nonnumeric side; body values :1651 say `reference as a number` | `Expr.refEq` (S:510), `Expr.not` | `refEq_ok` in `lowE_ok` :40. Retain region identity and valid origins; equality grants no address arithmetic. Provider realization remains B04/B06/C08. |
| A18 one-word context type adapters: Bool/option elements, normal table capabilities as values/results, scalar open-table fields | `Uebersetze.lean:1023/1034/1806/1171`: type/field/result/open-table non-number refusals | Existing Ty and `Expr.var/ptrOf/slot/slotRef`, binds/results (S:422/438/512/654/722) | Scalar `lowE_ok`/`lowS_ok`/`lowB_ok`/`lowEnd_ok`. Carry the complete kind/type through field/parameter/result paths; a capability is a table identity. Provider creation/transport remains B04/B06/C08; wide values B02; records/spaces C01/C12. |
| A19 mutable scalar options/tags/indices/capabilities/function pointers and call results | `Uebersetze.lean:2893/2961/2981/3026` (`let mut ...`), :2424 (`assignment to a pointer or an index`); `UebersetzeAllg2.lean:1168` (`assignment to a non-number variable`) | `Block.bind`, generic `Stmt.assignVar` (S:654/584), call bind | `lowS_ok` :63 and `lowB_ok` bind/call cases, within `wordTy`. Preserve declared mutable type/range, lexical scope, reference/mark provenance. This does not permit owning-value copies. Aggregate mutation is B02. |
| A20 matching binding annotations, scalar noninteger call results and scalar foreign function addresses | `Uebersetze.lean:2980/3004/3474/3513/3064`; `address of a foreign fn without G form`; `uWertArt` omits option/tag results | `Block/Endblock.bindCall/Ind/Else` (S:655/658/661/731/736/774) and typed bind/narrow; checked ordinary-function thunk for a foreign address | Existing `lowB_ok`/`lowEnd_ok`, `fnref_ok` and wrapper `lowFun_spec`. Prove thunk signature/call behavior with the actual gate; nontrivial foreign contracts retain C08. Check actual type, not only numeric range; retain reason context, conformance, continuation resources and alloc failure. Wide/gate results are B02/B04. |
| A21 internal let-else inside an error continuation | `UebersetzeAllg3.lean:412/969`, stale `Endblock lacks bindCallElse` | **Existing** `Endblock.bindCallElse` (S:736), execEnd at T2:375 | `lowEnd:432`, `lowEnd_ok:501`. Repair continuation parsing/scopes and reason/callee resources. No new constructor. The :412 branch is the context-preserving `lowSeqL` mode; bind-capable `lowSeq` already handles this at :438. |
| A22 foreign calls/bindings and fallible numeric foreign calls in error continuations | `UebersetzeAllg3.lean:857/859/966`, `foreign call ... no G form here` / unfinished nested let-else | `Endblock.cons (Stmt.axiomCall ...)`, `bindAxiom`, `bindAxiomElse` (S:616/743/751) | `lowS_ok:340`, `lowEnd_ok:506/510`. Retain effects, gate/hardware failure and reason decoding. The unfinished branch must parse the real error body, not an empty list. Noninteger fallible results are B04. |
| A23 fixed scalar arena alloc at function top level / in an Endblock | `UebersetzeAllg3.lean:957/1251`, `Endblock lacks arenaAlloc` | Existing `Endblock.narrow/bind/cons` (S:727/779), same stores/bump as `Block.arenaAlloc` (`Arena/ArenaZucker.lean:203`) | `lowEnd_ok` narrow/bind/store branches. Define/prove this sugar; retain failure continuation, store/bump order, bounds and ownership. A convenience definition is absent, not an essential core constructor. No-else alloc is C11. |
| A24 declared check's linear Duty and producing/consuming **ordinary function** gates | `Uebersetze.lean:4039`, `item without G form`; mark/signature gap in A02 | `Res.marke`, signature flow, `nachSig`, `RufPasst` (S:89/287/306/345) | Generic call/bind/return proofs. Generate/check exact Duty flow and gate/checker functions; retain can-fail/floor/probe obligations. `Block.check` is a different construct. Full measurement/admission and foreign gate contracts remain C16/C08. |
| A25 format views/checks with each integer access <=8 bytes | `Uebersetze.lean:4039`, `item without G form`; decorated fields :1117 | Count-one view/table, `getBytes`, `bitfeld/embeds` (Z:276/288), `putBytes`, `Block.check` (S:468/580/703) | `readBytesL_ok`, `putBytes_ok`, `blockCheck_case`. Generate/prove layout, endian conversion, offsets, reserved bits, where/range and carrier bounds. `FormatRoundtrip.roundtrip` is not that bridge; @version provides no migration reader. Wider accesses B03. |
| A26 ordinary scalar accumulators, all max/min/add/or/and operators | `Uebersetze.lean:4039`, `item without G form` | Global + generated stores/conditionals/arithmetic; `Stmt.mergeMax/mergeAdd` (Z:206/210) | `lowE_ok`/`lowS_ok`, existing initialization. Preserve neutral value/operator/range (especially add), guard/write effects and generated contracts. Concurrent per-core/RMW claims are not supplied by a plain store; C15. |
| A27 walk's fixed-level traversal projection over modelled table nodes | `Uebersetze.lean:4039`, `item without G form`; mappings uses :1570/3174 | `Stmt.walk2` (Z:306), repeated traversal and filtered down/leaf tests | `traverse_case`, `lowS_ok`/`lowB_ok`. Prove source-derived visitation/mapping and invariant/exit correspondence; `walk_hits_mapping` alone does not. Full generated mapping records are C01; wide transport B02. |
| A28 scalar noninteger constants (Bool, option/tag, <=1-byte string) | Collectors omit them; uses reach `Uebersetze.lean:1453` (`name unknown`) / `UebersetzeAllg.lean:1351` (`constant without G form`) | Typed `Expr.tru/fls/none/some/case/why/strLit` | Existing `lowE_ok` branches. Preserve constant type/identity, checked literal/payload interpretation; never substitute zero. Wide values B02, general evaluation C17. |
| A29 float literals, conversion, narrowing and comparison in the finite IEEE kernel model | `Uebersetze.lean:1023/1806/1657/1663` type/result/value defaults; bare float names also reach :822 (`type unknown`) | `Ty.fl`, `Block.floatLit/Of/Narrow`, `Expr.fllt/flle` (S:488/712/714/718) | Actual `lowB_ok` :445/449/453 and `lowE_ok` :140/144 branches. Export rational bounds, finite/rounded/failure meaning, operand order and binders; retain Stop107. Arithmetic is B01. |
| A30 slot quantifiers beside a represented noninteger scalar result | `UebersetzeAllg.lean:1170`, `quantifier beside a result of this type without G form` | `forallSlots/existsSlots` with actual result `ErgCtx` (S:500/502/803) | `lowE_ok` quantifier proofs. Extend `ergAlsParam`, preserving result type/position under every binder. A tag/option must not become an Int. |
| A31 calls nested in value/return expressions, where already allowed by source checking | `Uebersetze.lean:1663/1490/1541`, value/compare/predicate defaults; special binding-RHS call handling is narrower | Existing `Block/Endblock.bindCall`, `Stmt.call` and result variable, no new `Expr.call` | `lowB_ok`/`lowEnd_ok` call proofs. Lift calls in source evaluation order with contracts/effects/resource states and failure/nonreturn continuations. No repeated/eager evaluation or invented expression-call syntax. Fallible indirect calls C07. |
| A32 Boolean exchange/update and represented scalar nonnumeric atomic payload values | `Uebersetze.lean:3447` (`exchange ... not a number`); `UebersetzeAllg2.lean:1044/1075` (`aggregate atomic without G form`) | Generic `Block.exchange`, `Stmt.publish`, `Block.awaits`, `Expr.wenn` (S:697/634/693/538) | Existing exchange/publish/awaits cases of all three mutual proofs. Preserve pairing, atomic/guard/write checks, CAS retry and weak-memory duties. Only current scalar memory encodings qualify; multiword atomicity is extra work in B02. |

**B — model exists, export plus Stage0 work required.** These are not cases
whose only blocker is the canonical exporter.

| ID / source form | Exact export boundary | Existing model/proof and additional blocker | Preservation / implementation needed |
|---|---|---|---|
| B01 float Add/Sub/Mul/Div | Same type/value defaults as A29 (`Uebersetze.lean:1023/1806/1663`) | `Block.float` (S:709), semantics T2:329; `Anweisung.lean:384` still returns `none`, `lowB_ok:444` only discharges impossible emission | Finish/connect actual arithmetic/normalization/rounding/range candidate and source export. Do not adjust IEEE semantics to match the candidate. |
| B02 wider variants of A16/A18-A20/A25-A29/A32: arbitrary arrays/strings, fields/locals/returns/atomic values | `Uebersetze.lean:1023/1034/1171/2893/2926/2961/2981/3004/3040/3447/3816`; `UebersetzeAllg.lean:1189/1351`; `UebersetzeAllg2.lean:1044/1075/1168` | General Ty.arr/str and typed syntax exist; connected proofs cover only emitted cases. `Ausdruck/Gleichungen.lean:292-317` restricts strings to maxima <=1; scalar assignment requires `wordTy` | IR-03 common encoding must reach every frame/call/memory/initialization consumer and proof. Multiword atomic exchange also needs a real atomic mechanism/proof, never consecutive plain stores. Record Ty itself is C01. |
| B03 integer format accesses wider than eight bytes | `Uebersetze.lean:4039`, `item without G form` | G getBytes/putBytes accepts n bytes; actual `Anweisung.lean:238` checks `n <= 8`, expression byte lowering has the matching restriction | Extend common wide values and byte/range/address/bounds proofs plus source expansion. Total format size >8 alone is not a blocker if all individual accesses satisfy A25. |
| B04 fallible foreign Bool/provider results, other nonnumeric foreign results and richer open-table values/references | `Uebersetze.lean:4158/4161/4162/1806/3040/1171` | `D.aerg : Ax -> Option Ty`, `Block/Endblock.bindAxiomElse`, slotRef already exist. `Anweisung.lean:350/476` accepts only nonnegative Int fallible results; `Senke/Tor.chkC:149` has Int/Bool/never but no reference/aggregate validation | Add actual gate result/region realization and generic proof, preserving reason encoding, fresh/disjoint origins, bounds and failure. Provider user-logic contracts have the separate C08 admission gap. |
| B05 old(static), richer old snapshots in contracts | `Uebersetze.lean:1481-1485` sends old through `uZugriff`; :1330 rejects static places; richer predicates :1490/1604 | `Expr.oldG/oldS` (S:443/444), initial-world semantics T1:250/251. Both emitter equations (`Ausdruck/Gleichungen.lean:112/116`) return `none` | Entry snapshots/IR-03/10 frame and unchanged-region proofs. Loading current memory is unsound. Numeric old(slot) already exports and is an emitter-only limit, not an extra missing export. |
| B06 arena pb/blw, provider realization and physical growth | `Uebersetze.lean:3993`, `arena placement without G form`; existing scalar provider syntax later meets B04 | `D.offen/anbieter`, `Block/Endblock.alloc` (Z:234/254); `Arena/Unbounded/{GForm,GRefine,Realization,Linked}` gives allocation/ownership/region refinements | Connect source expansion, gate binding, layout extension, availability and lifetime to Stage0. `Block.allocationAttempt` / `allocation_grant_bridge` (`Unbounded/GForm.lean:19/70`) is not the whole-image theorem. Preserve threshold/failure and provision as user logic; never invent an address or assume an OS. |
| B07 userspace child body at a checked stack handoff | `Uebersetze.lean:2538`, `stmt without G form: child` | Generic thread-machine `FadenSchritt.kind` and goal rules; `spawn_kind_ziel` is a concrete witness, not a generic compiler theorem; existing `Senke.CloneOK`/clone support is not a source-child attachment theorem | Connect actual gate/stack/entry contract, resource transfer, starts, frame/ABI and parent/child outcomes. No `lowS/lowB/lowEnd` child case; never execute child sequentially in parent. Boot/ASM excluded. |
| B08 richer closed concurrent-start arguments | `Uebersetze.lean:4071`, `concurrent member with an argument outside its parameter's type`; restricted `uStartArg` | Args/Env/starts exist; literal/Bool/None/table-capability starts already export. `StartArgument.expression:11` is proved by the same restricted matcher | Extend reification/extraction and initialization/image proofs for checked constants, Some, tags, arrays/function references. Retain source identity, multiplicity, closure and exact value/type. Large arguments also need B02. |

**C — canonical model/admission rule or semantic binding missing; owner
decision first.** There is no complete emitter+proof for the requested source
semantics merely because an abstract theorem or primitive can be found.

| ID / source form | Exact refusal / default | Model evidence and missing rule | Required decision / preserved guarantees |
|---|---|---|---|
| C01 records/products, record fields/payloads, complete walk mappings | `Uebersetze.lean:1023/1034/4227/4039`, type/field/payload/item defaults; named records also :822/2050 | Ty has no record/product constructor; Ty.sum has only optional integer payloads. `Stmt.verbund` (Z:215) writes a count-one table, not a record value | Define canonical value/field/type/ownership semantics before IR-03 representation and full IR-13 walkers. No unrelated array representation, discarded field or record-free replacement of source semantics. |
| C02 translators, library region payloads and @library calls | `Uebersetze.lean:4039` (transT), :1998 (`fn is not impl` for library fn), :2538 (bindLib/lcall) | No typed translator/region component or executed expansion in UProg. `Logik/Vertraege/Uebersetzung.nutzlastZert` certifies payload typing, not arbitrary translator execution | Canonical map/payload/call binding, termination/effects/cost and name correspondence; existing IR-01 prerequisite applies. No restored source interpreter. |
| C03 nonexhaustive reasons and noninteger/structured tagged payloads | `Uebersetze.lean:4290`, `reason that is not exhaustive without G form`; :4227 (`payload type without G form`) | Ty.why has exactly n reasons, Ty.sum payloads are optional Int ranges (Typen:42/44) | Establish open-reason/payload semantics; numeric error codes or nested representation alone are insufficient. Ordinary exhaustive integer-payload tags already export. |
| C04 transition requires/effects and nonconstant stage expressions | `Uebersetze.lean:4311` (`state transition clause without G form`), :4306 (stage) | D.erlaubt relates Ints; Stmt.shift has edge/range/write/guard premises but no clause-contract rule | Specify edge duties and stage-expression meaning without dropping clauses. Constant numeric stages are A11. |
| C05 group invariants over globals | `Uebersetze.lean:4338`, `invariant carrier without G form` | D.traeger is `Inv -> List Tab` (S:206), no global-carrier alternative | Extend carrier/footprint/restoration/U003 semantics and validate goal guarantees; never omit the global. Arena tables are A09. |
| C06 nontrivial function-pointer requires/ensures | `Uebersetze.lean:4603/4604`, `contract on a function-pointer type without G form` | Signatur/SigPasst has effects/resources/floor but no predicate contract; Programm requires/ensures is indexed by concrete Fn | Indirect caller duty and target conformance rule (O43), preserving every possible target's contracts. Trivial requires/ensures true already pass. |
| C07 fallible indirect calls / pointer reason channels | `Uebersetze.lean:4617`, `pointer type with a reason channel without G form`; :3009/2534 requires let-else | Stmt.callInd/Block.bindCallInd/Endblock.bindCallInd require zero reasons (S:601/658/774); no indirect bind-else | Canonical error continuation/conformance/resource rule before emitter+proof. Do not erase the channel or substitute a direct target. |
| C08 foreign/axiom/syscall contracts, resource effects, provider contracts and fallible void handling | `Uebersetze.lean:4039` (axiomT requires), :4126/4132 (foreign effect/clause), :4186 (gate pre/post), :4156 (reason channel without answer) | D.Ax has typed answers/writes but no requires/ensures or linear signature flow. Ref/provider refinements supply duties, not source contract admission | Establish user-logic contract/admission and provider freshness/disjointness bridge; OS behavior is not hardware. A ref type/TorOK is insufficient. Model a fallible unit/void result explicitly, not as an invented number. |
| C09 complete owner minter and own borrow/return discipline | `Uebersetze.lean:1172/1925/1806/822`, table/resource/result/type boundaries | Owner guards/initial resources exist (A04); Ty has no mark value, foreign calls preserve Λ, `eigner_nie_erzeugt` forbids owner production by every signature (S:203) | Connect unique mint, root/start-once and borrowing/returning an existing mark without production/duplication. `own`→writable Bool at :1005/1758 supplies no such proof. |
| C10 shared locks and full RCU/observes/reclamation | `Uebersetze.lean:1212` (shared declaration), :3590 (`shared lock without G form`), :4039 (rcuT), :2538 (watch); other masks :1203 | Stmt.observes (Z:200) is ordinary locks sugar; Res.held has no reader/writer distinction or grace-period/reclamation state | Canonical shared/RCU lifetime admission preserving rank, exclusion and reclamation. An exclusive lock is not automatically the requested RCU semantics; non-irqs masks need a named mask rule too. |
| C11 consuming traversal, no-else arena alloc, lock-crossing return admission | `Uebersetze.lean:3175/3536/2538`; `UebersetzeAllg3.lean:178/799` (`return under locks`) | Stmt.traverse is a fixed index sweep; Isabelle.Consuming/GabbroV.GvTraversal is not its source expansion. Arena alloc requires a failure Endblock. Stmt.ret requires Λ.Perm V.ende, incompatible with an extra held lock under current admission | Establish the consuming mutation/measure, capacity duty for omitted failure, or resource-aware cleanup/return rule respectively. Stage0 also keeps retFrei restrictions; loosening that gate alone is unsafe. These are control-admission variants, not runtime no-ops. |
| C12 named spaces, unsupported rights, byte/raw/entry pointer wrappers | `Uebersetze.lean:1004/1013/1023/1757/1766`; :963 rejects a nontable pointee | Ty.ptr n rw is a table capability, not a byte extent/space value; fnptr is a checked function identity | Define safe userspace region/code-capability semantics and checked profiles first. No data/code confusion or fabricated table number. Numeric raw addresses remain excluded. |
| C13 count comprehensions, sizeof/aligned, wrapping/saturating and remaining bit builtins without executable G expansion | `Uebersetze.lean:1663/1490/1604/1563`, value/compare/predicate/operator defaults; unknown-width complement :1422/1423 | Zahl.addW/subW/mulW/shlW/addS (`Kern/Semantik/Ueberlauf`) and Zahl.clz/ctz/log2_floor/popcount/rotl/rotr/bswap (`Kern/Syntax/Bits`) are value functions; Expr/eval has no matching case/canonical sugar. No Expr count fold or layout-predicate binding | Approve a canonical checked desugaring/rule retaining storage width, modulo/clamp/shift, count budget and checked layout. A mathematical function is not an emitted-source theorem. Existing known-width complement/wrapping fields already export. |
| C14 profiles/requires-profile, when TESTBUILD, static alignment/section and userspace guest-entry binding | `Uebersetze.lean:4039` (profT/gateT/trustT), :3908 (static placement). Actual earlier guards `stage0/Stage0/Profil.lean:52/53/54`; entry obligations :31-41 | Missing source-to-goal profile/selection/guest binding. Target Lay/address models and syntactic options do not interpret the clauses | Checked selection/ABI/layout/profile and user-logic entry contract correspondence; never discard declarations. Hardware/boot/register-ABI entry work stays excluded. Dispatch-only entries and current target selection already pass their gates. |
| C15 per-CPU accumulator layout/reduction/quiescence | `Uebersetze.lean:4039`, `item without G form` | Isabelle.AccumulatesMonoid has abstract neutral/fold/order/RMW facts, no source-to-G per-core layout/initialization/quiescence bridge | Checked core identity, disjoint cells, initialization, updates and quiescent observation/reduction for all five operators, retaining range/overflow duties. A26 does not supply the concurrent theorem. |
| C16 full declared-check measurement/floor/counterprobe admission beyond Duty | `Uebersetze.lean:4039`, `item without G form` | Res.marke/signature flow models Duty (A24), but no SCheck expansion/admission relates claim/measure/floor/probe to generated producer/gates | Establish that binding with failure paths and foreign gates (C08). A Boolean check or merely introducing a mark cannot certify a measured claim or derive ensures. |
| C17 generic type/order wrappers, source decreases-measure binding and extended compile-time contracts/control | `Uebersetze.lean:1951` refuses the ordinary `decreases` clause (`SKlausel.drops`); typeT has no blanket refusal: :833 collects selected aliases, uses later fail at :822/1023. `uKonstFns:875` only accepts single-return numeric bodies and discards clauses; unresolved uses :1453/1663/3816 | Monomorphic Ty; recursion already has `rufAt`/abstieg (`Semantik/T2.lean:455`) and `lowFun_spec`, but no export binding from the source measure expression to that duty. Konstanten.KExpr covers its arithmetic cut, not arbitrary source contracts/bodies. `stage0/Stage0/Frontend/Source.lean:41` refuses unsupported compile-time call contracts/effects/bodies before normalization | Checked instantiation/non-mark order, source measure-to-recursion obligation and compile-time denotation/contract rule; a missing measure bridge must not be solved by ignoring decreases. Linear mark order is A02. Silent omission is not semantics; never remove the constant-hull guard to make an initializer pass. |
| C18 partial array reset/page release (`reset X at i count n`) | `Uebersetze.lean:2538`, `stmt without G form: reset`; only the no-range arena reset has an export at :2518 | Whole arena reset is existing `Stmt.assignGlob` sugar; typed array stores also exist. The partial-reset/released-page source rule and its provider/lifetime binding do not | Specify checked range, zero-after-reset behavior and explicit user-logic page-return service; retain live-cell/alias safety. A store loop proves zeroing, not page release. Existing `ArenaDyn.discard_live` (`Arena/ArenaSeiten.lean:25`) is an abstract preservation fact, not a source-to-G/image bridge. |

**Remaining diagnostics and scope accounting (no hidden extra A packages).**

- `UebersetzeSum.lean:24/41/53/59` rejects malformed/foreign values or forms
  outside existing tag paths. Valid integer payloads already reach Expr.case;
  richer payloads are C01/C03 and richer calls/bindings A20/A31/B02/B04.
  Tagged case/type defaults at `Uebersetze.lean:4247/4258/4259/4266/4281/4282`
  also include malformed syntax; valid constant payload extensions are A10.
- `UebersetzeAllg{,2}` parameter/index/place/argument/count defaults normally
  enforce type/table/guard/range/count/rights premises. Those are real refusals;
  scalar adapters are A18-A20, wide storage B02/B04, spaces/products C01/C12.
  Non-array indexing, array bounds and empty-array inference failures are not
  permission to add defaults or unmodelled array concatenation. String addition
  already reaches strCat through `addW`; comparison is A16/B02.
- Exchange-tail errors (`Uebersetze.lean:2575/2576/2699/2711/2716/2721/2733/2734`)
  refuse updates outside the represented pure guarded-value grammar. No
  relaxation is needed for its supported updates. Richer calls require A31
  plus atomic evaluation duties; nonnumeric/wide exchange is A32/B02. A
  non-atomic publish/await, wrong payload or missing write right stays refused.
- Loop/retry/forever headers (:2783/2811/2816/2817/2825/2828), match/arm defaults
  (:1527/1533/3228/3311/3321/3329/3341/3384), fuel, block closure, reason mismatch
  and return/leave/next placement mostly enforce grammar/model premises.
  Domain/consuming variants are A14/C11, constant headers A10, richer results
  A20/A31. Missing until/progress is not export-only. The leaf-reader mid-body
  return refusal `UebersetzeAllg2.lean:1380` is already handled by structured
  `uAnwReihe`/`lowSeqL`; lock-crossing return is C11.
- `UebersetzeAllg3.lean:857/859/966/969/957/1251` are unfinished adapters
  (A21-A23), not proof of model absence. Its :412 belongs to context-preserving
  lowSeqL, not the whole bind-capable reader. `UebersetzePipeline.lean` adds
  phase-error propagation, not another missing source-form family.
- Already exported modules/imports/public names, checked aliases/constants,
  empty tables, plain statics/tables/states, tree metadata, ordinary
  contracts/spec/refines, scalar calls/loops/starts/synchronization are not
  relisted, although independent emitter limits can remain. Parser-only holes
  (such as unavailable general array literal syntax) are not Elab exports.
  Ignored cost/proof metadata is admission/preservation debt, not coverage.
- All register/device class/field/bank/mirror/transition errors, observed-by-
  device atomics (`Uebersetze.lean:3963`), ASM bodies, boot, privileged entry and
  proposed raw numeric addresses are excluded. Ordinary safe byte capabilities
  and userspace gate/provider contracts are not excluded merely because they
  are unsupported; they remain C08/C12.

**Effort estimate (engineering days, not measured build time).** A: **20-40
person-days** for the 32 bounded packages with generic export preservation,
witnesses and connected checks. Local adapters typically take 0.5-1 day;
mark/signature, arena ownership and generated IR-13 expansions roughly 2-5 days
each and share substantial work. B: **25-55 person-days** across eight packages,
overlapping existing IR-03/04/06/10/11/12 work; do not add this twice to staffed
lanes. C: **5-10 person-days for canonical design/decisions**, then provisionally
**30-70+ person-days** for model/admission, goal validation and implementation;
no completion date precedes the owner's decisions. Unchanged guarantees and
available Lean slots are assumed.

Critical path: canonical resource/signature/source-expansion interface for
A02-A08/A24; shared value/ABI/gate/region interface for B; owner decisions for C.
A useful first batch is A01, A11-A15, A21-A23 (roughly 3-7 person-days combined),
then shared resource export. Four independent ad hoc IR-13 exporters would
duplicate that boundary. This catalogue grants no implementation/build authority.

Validation is static: refusal coordinates, constructor shapes, emitter matches
and named theorem call sites were read at the stated commit; document counts
and `git diff --check` were checked before commit. **Zero new source cases were
compiled or proved by this planning task.**

### Model extension design: C13, C17, C05, C04 (2026-11-01)

Design baseline: `f40b2537b`; static source inspection only, no Lean edits or builds.
Implement in the order below, with one owner of `grammatik/`. Names marked **new**
are proposed definitions, not claims about existing declarations. Paths below are
relative to `grammatik/Grammatik/`, except explicit `stage0/` paths. These designs
do not close catalogue cells: completion requires the generic source preservation
theorem, accepted exported unit, connected IR proof and compiled pipeline.

**Shared decisions.** Keep arithmetic in typed expressions, recursion measures in
the existing measure interface, invariants over the existing sum of carriers, and
transition clauses in ordinary function contracts. Compared with expanding every
builtin into a large expression tree, a closed typed builtin family preserves
width and gives the emitter one dispatch point. Compared with another transition
machine, checked expansion into ordinary functions reuses contracts, resources,
frames and call logs. Never introduce an executable source interpreter.

Every new constructor is appended at the **end** of its inductive, including the
mutual `Expr` family and exporter intermediates; keep existing constructor numbers.
For all four packages, carry renaming, footprints, ghost checks and declaration
embeddings through `Kern/Syntax/Zucker`, `Kern/Syntax/Extraktion`,
`Nebenlaeufigkeit/Sperren/MitRuhe*` and `Zielsatz/Einbettung/Syntax`. Extend the
GabbroV bridge in `GabbroV/GvBruecke` where its represented fragment changes.
No acceptance component may default to true on a new form.

| Priority | Kernel/model delta | Spec impact | Effort, engineering days |
|---|---|---|---|
| C13 | Closed typed integer builtins; bounded count fold; checked layout sugar | Conservative expression extension; extend cost definitions, no new assumption | 8–14 |
| C17 | Bind source measure to existing `Mass`/`MassPflicht`; no new execution rule | Existing termination premises instantiated, not removed | 2–4; optional generic cut +1–2 |
| C05 | Replace invariant `List Tab` with `List (Tab ⊕ Glob)` throughout; implement the currently refused IR return checks | **Yes:** restoration/closedness/observation also cover global carriers | 8–13 |
| C04 | Checked expansion of named transition contracts and dynamic endpoint expressions | Source meaning made explicit; existing goal applied to generated functions | 5–9 |

Ranges include generic proofs, non-degenerate witnesses and connected Stage-0
work; they are not measured build times. Critical path: C13 expression inductions,
C05 invariant replay and idle-root/link embeddings, then C04 source semantics
review. Optional generic syntax beyond the cut below is not included.

**C13 — arithmetic, bit builtins, layout and count.**

| Layer | Implementable change |
|---|---|
| Typed kernel definitions | In `Kern/Syntax/Syntax`, add **new** `IntBuiltin : List Ty → Ty → Type`, a closed family, and append **new** `Expr.intBuiltin (op : IntBuiltin ts τ) (args : Args D Γ Λ ts) : Expr D Γ Λ τ`. Constructors: `addW/subW/mulW`, `shlW`, `addS`, `clz/ctz/log2Floor/popcount`, `rotl/rotr`, `bswap16/32/64`. Width is `W = w + 1`, never inferred from the current interval. Binary wrapping operands/result are `.int 0 (2^W-1)`; shift/rotate amounts are `.int 0 w`. Saturating operands/result share `.int lo hi`. `clz/ctz/log2Floor` take `.int 1 (2^W-1)` and return `.int 0 w`; `popcount` takes the full unsigned range and returns `.int 0 W`. Byte swaps have exactly their named widths. There is no arbitrary function-valued primitive. |
| G value semantics | Add **new** `evalIntBuiltin`, interpreted only by `Zahl.addW/subW/mulW/shlW/addS` from `Kern/Semantik/Ueberlauf`, and `Zahl.clz/ctz/log2_floor/popcount/rotl/rotr/bswap16/32/64` from `Kern/Syntax/Bits/T2`. In `Semantik/Semantik/T1`, `eval (.intBuiltin op args)` applies it to `evalArgs`; its `orte` is exactly `args.orte`. Import the existing value modules, without a syntax/semantics import cycle. No new `execStmt` rule. Literal operands are widened only with proved inclusion in the declared operand range. |
| Count definition | Append **new** `Expr.count (n : Nat) (body : Expr D (Ty.index (n : Int) :: Γ) Λ .bool) : Expr D Γ Λ (.int 0 n)`. In T1, evaluate the predicate for every index in `alleIndizes (n : Int)` in the same world/environment, count true results, and package the bound `count ≤ n`; `orte = body.orte`. This is one bounded fold for every admitted finite domain. Slots use `(D.count t).toNat` with checked index conversion; array elements use `Expr.arrGet`; descendants/ancestors/chain require the existing checked `reaches` filter and exact domain membership. Metadata enumeration alone reads no cell; predicate/domain reads retain all guards and footprints. |
| Layout sugar | Add **new** checked source layout derivation in `Kern/Syntax/Profil`, with size/field-offset facts tied to the selected representation and a theorem consumed by the emitter's `Lay` correspondence. `sizeof` lowers to `Expr.lit` only after type/place resolution and that derivation; preserve any source-required index evaluation in enclosing binders. It is the source object's declared byte size, not `8 * count` from the runner's column representation (`stage0/Stage0/Senke/Welt/Lay`). Numeric `aligned(x,N)` is the predicate `x mod N = 0`, with positive checked constant alignment; use `Expr.rem` for nonnegative x and signed-remainder sugar for signed x. Preserve operand reads/effects. A capability alignment query needs a layout/address correspondence; `Ty.ptr` evaluates to unit and cannot be treated as an integer. |
| Admission/export | Catalogue coordinates `Parser/Elab/Uebersetze.lean:1663/1490/1604/1563`, complement :1422/1423. Extend `uRechne`, `uWertBlatt`, `uSeiteBlatt`, `uSichert` and the `USide`/`UEns` representations, then `UebersetzeAllg.lowWertE`/`lowEns`. Carry declared storage width through fields, locals and aliases, not just `UCtx.bits` on parameters. Read `.ext .count` using the domain encoding in `Parser/Expr/Ausdruck.parseQuant`; prove binder renaming and domain cardinality. Unknown width, zero-excluding bit operands, shift limits, alignment and bounds are checked before constructing G. `Akzeptiert`/`AkzeptiertX` retain `frag`, `fuss`, `renn`, `stufen`, `antworten` etc.; extend their structural traversals so builtin/count reads reach the existing footprint and atomic-contract rules. |
| IR and connected proof | Extend `stage0/Stage0/Senke/Ausdruck.lowE`, `Ausdruck/Top.lowE_top`, `Ausdruck/Satz.lowE_ok`, aggregate/wide value lowering and `Old/` contract lowering together. Reuse `Arithmetik/Wide/Run.wideAdd_run/wideSub_run`, `MulRun.wideMul_run`, `Bits.wideAnd_run/wideOr_run/wideXor_run`, shift and compare kernels. Mask to **W** bits after arithmetic, including partial top limbs; saturate by an exact sum in a sufficient temporary width before signed/unsigned comparison and clamp. Existing limb kernels alone do not prove builtin semantics. Bit counts/scans/rotates/swaps need composition proofs against the named `Zahl` functions; no CPU zero-case convention. Extend `Ausdruck/Quant` with a counted fold using the existing binder/reservation machinery. Prove its accumulator/index bounds and emitted instruction budget. Thread these cases through `lowEnd_ok`, `Rekursion.lowFun_spec`, `Compiler.compile_source_program` and `IRBild.irBild_correct`. |

Re-establish `Extraktion.eval_liest_nur_orte` (T3), hence
`Zielsatz/ZielOrt/Grundlage/ZielOrtSem.eval_gleichAuf`, by induction on arguments
and bounded indices. The new cases are pure and total; existing statement frame
and race proofs then apply. Extend `Logik/Fortschritt/KostenG/T1.kostenExpr`:
builtin-specific bounded work plus argument costs, and count enumeration plus
`n * kostenExpr body`; prove the corresponding potential bounds before reusing
`frame_schritte_beschraenkt`/`ZeitAb`. This is a conservative extension of the
expressions interpreted by `Spec.lean`, with explicit new cost accounting, not a
new hardware assumption or a claim of physical instruction timing. Recheck
`Zielsatz/Kern/Beweis.ziel_aus`, `Atomar/BeweisAtomar.gabbro_ziel` and SC transfer.

Witnesses: every builtin family at two storage widths, including a partial limb
and a multiword carry; unsigned wrap-underflow, shift 0/W-1, low/high saturation
including signed ranges, bit scans at 1/top bit, popcount at 0/all bits, rotate
inverse and byte-swap involution. Count: empty/nonempty, mixed truth values,
nested binder and guarded/global reads. Layout: padded/packed objects and an
indexed place; aligned and misaligned numbers. Negative fixtures: unknown width,
zero scan, amount W, missing lock, wrong size/layout, unmodelled domain, shared
atomic in a contract, and ghost use. Calls inside operands depend on the checked
call-binding expansion (A31), never on erasing the call. Open/infinite domains,
unsized layouts and capability alignment without correspondence remain refused.

**C17 — source `decreases`, bounded to the existing recursion model.**

The kernel needs **no new constructor or eval/execStmt case**. Existing
`Logik/Terminierung/Mass.Mass` is a per-function list of nonnegative integer
expressions over entry parameters with `e.orte = []`; `Mass.wert`, `lexLt`,
`zykS`, `massTor` and `MassPflicht` already bind a smaller cycle-call measure to
`Logik.abstieg`. `Semantik/Semantik/T2.rufAt` instead counts recursion depth:
fuel zero yields `abstieg`, and positive fuel checks requires/body/ensures and
owed invariants. **Do not identify a numeric measure with this depth fuel.**

| Layer | Implementable change |
|---|---|
| Export and admission | Replace the blanket `.drops` refusal at `Uebersetze.lean:1951` only after collecting the clause in `UFn` and lowering it at the exact entry parameter/resource context. Add **new** `lowerMeasures`, producing `Mass (declOf u)` with the footprint/nonnegativity proofs, plus a source-expression denotation theorem. One source expression becomes a singleton tuple; support tuples only if their surface form is represented. Preserve absence as `[]`, reject duplicate/ambiguous clauses. Constants may normalize, but never replace a source measure with a guessed parameter. |
| Obligations/checker | Export the actual measure with the unit/certificate and in **new** measure provenance fields of `stage0/Stage0/Compiler.Compiled`/`CanonicalSourceProgram`. Decide equal tuple lengths along `zykS` using complete function enumeration. Generate the existing `MassPflicht` as a user obligation for every function/cycle and every required `passes`; do not infer its truth from structural checking or add it as an assumption about hardware. `Akzeptiert(X)` remains the structural safety checker; the termination certificate additionally supplies the duty to `GabbroZielTerminierung`. |
| Existing proof chain | Instantiate `Zielsatz/Atomar/BeweisTerminierung.gabbro_ziel_terminierung` with that exact measure, retaining `MassRuhe.massPflicht_mitRuhe` and cycle-length transfer. `gabbro_ziel` and its ordinary safety premises do not change. Prove source-to-measure equality and substitution through idle-root embedding; no new well-founded recursion engine. |
| Stage 0 | Carry proof metadata through `Frontend.elabWithScopes`, `lowerAllg`, old-state restoration and `compile_source_program`; execution remains `Rekursion.lowFun_spec` over `rufAt n`, including depth guard/stop 105. `IRBild.irBild_correct` does not thereby prove unbounded recursion or a sufficient stack/fuel. Any later execution theorem relating termination to a chosen depth bound must supply that bound explicitly. |

Witnesses: a recursive countdown, mutual recursion with equal tuple lengths,
an acyclic function (`massPflicht_ohne_zyklus`), and a non-tail cycle whose
measure actually falls. Negative fixtures: unchanged/increasing argument,
negative-valued measure, differing cycle tuple lengths, a hidden global/old
read, and unsupported calls in the measure. Each generic export theorem gets a
`_zeuge` satisfying structural admission and the actual measure duty jointly.
No change to `Spec.lean` meaning: its existing (b') premise remains explicit.
Memory-reading measures such as `region.words` are outside this small cut unless
the declared argument is already a by-value aggregate and its projection is
proved world-independent; do not silently widen `Mass`'s empty-footprint rule.

Optional **checked generic instantiation**, only if bounded to 1–2 days:
`Parser/Item/ElementTief.SItemTief.typeT` stores argument types and order words,
while `Parser/Expr/Typ.STyp` has no general type-application constructor and
`uAliase:833` currently ignores these lists in selected aliases. First reject
nonempty lists at unsupported uses instead of erasing them. Admit only explicit,
fully resolved, finite substitutions into existing monomorphic `Ty`, with a
generic capture-free substitution/denotation theorem over parameters, contracts,
bodies and measures; preserve opaque identity and linear resources. No runtime
generic type, inferred default argument or unrepresented application syntax.
If actual applications need a new parser/type rule, retain that refusal and
schedule the full C17 generic package separately. Non-mark order semantics and
general compile-time control/contracts are excluded from this cut;
`Frontend.compileTimeSafe` (`Source.lean:41`) remains mandatory.

**C05 — one invariant-carrier interface for tables and globals.**

| Layer | Implementable change |
|---|---|
| Kernel declarations | In `Kern/Syntax/Syntax.Deklaration`, **replace** `traeger : Inv → List Tab` by `Inv → List (Tab ⊕ Glob)`. Lift all existing table fixtures with `.inl`; no parallel global-invariant registry. Generalize `invarianten_gehalten`: if any carrier is written by signature n (sum elimination to `.schreibt`/`.gschreibt`), every lock in every carrier's `.braucht`/`.gbraucht` occurs in that signature's `.haelt`. Use sum elimination directly inside the structure to avoid depending on later `TraegerSchreibt`. |
| G semantics | Generalize `invSicht` to fold mapped guards of both cases, and `Semantik/Semantik/T1.schuldet` to sum elimination over `D.schreibt f`/`D.gschreibt f`; prove equality to `(D.traeger i).any (TraegerSchreibt f)` only in the later interference layer (that definition is in `InterferenzAllgemein/T1`, so importing it into T1 would cycle). The existing `rufAt` invariant-read/check phase now also selects global writers; do not add another return phase. G's `assignGlob`/`World.schreibGlob` and `eval .glob` already implement accesses. No new `Expr`, `Stmt` or event. Both normal-return restoration and error-return `InvGutGrund` remain required. |
| Export/checker | Fix `Uebersetze.lean:4338`: `uInv` resolves each carrier to a unique table/global, collects all guard locks, and checks predicate reads against that exact declared set. Generalize `uU003` to `f.puts` **and** `f.gputs`; in `UebersetzeAllg` update `invTraeger`, `invOkB`, `traegerD`, `invGehalten`, `declOf` and `UebersetzeAllg3.lowerInvAt`/`lowerInvs` together. Prove successful export preserves the entire declared carrier list; failure of U003 must not turn it into `[]` via the current fallback of `traegerD`. Preserve unknown/ambiguous-name refusal. |
| Footprints/admission | Generalize `Logik/Vertraege/VertragsFuss`, `invOrteP` and `Nebenlaeufigkeit/Rennfreiheit/Interferenz.inv_schreiber_sperren`/`schuldet_hat_schreibtraeger`; every global writer owes the group. Re-establish `fussWB`/`fussWXB` soundness and `akzeptiert_iff`/`akzeptiertSpecX_of`. `AtomarAkzeptiert.vertragsFreiB` must see global group reads via `invOrteP`, so an unguarded shared atomic in an invariant stays refused (N484); atomic race exemption never implies invariant stability. |
| Goal proof repair | In `Zielsatz/Kern/Spec`, replace `InvTraeger`'s table-only existential by membership in the carrier sum and generalize `InvSichtG`'s held-guard premise to both guard functions. In `Eigenschaften/Invarianten.invRuhe_erreichbar`, the global `GleichAuf` branch currently closes by impossible `.inl` equality: replace it with `schuldet = false → gschreibt = false` and `schritt_traeger (.inr g)`. Generalize `invSicht_aus` using the sum form of U003. Propagate through `invRuheG_aus`, `invSichtG_aus`, `ZielOrt/Rahmen/ZielOrtInvGrund`, `ZielOrtInv`, `ZielOrtMehrfaden`, `Kern/Beweis.ziel_aus`, `Atomar/AtomarInvarianten` and `Atomar/BeweisAtomar.gabbro_ziel`. Restore idle-root and linking carrier mappings, including `Einbettung` and `Projekte/Verbund`; old table-only cases must specialize to the former results. |
| Stage 0 | **Current additional wall:** `Senke/Funktion.lowFun:31` refuses every function with a nonempty owed-invariant set. Export the generalized predicate/set, then replace that gate with a shared return epilogue: evaluate ensures first (stop 102), then owed predicates in declaration order (first failure stop 103), preserving result/return flag and snapshot slots. Extend `Senke/Rueckkehr.RetZ0`/`RetZ`, return emission, `lowEnd_ok` and `Rekursion.lowFun_spec` to match `rufAt` exactly. Reuse global expression/store kernels, not nonexistent invariant-return support. A reason return in `rufAt` propagates directly: preserve `RetWhy` behavior and transfer the separate user duty `InvGutGrundA`; do not invent a reason-return runtime check. Preserve shared-memory/global layout agreement and old-value restoration. No runtime global-invariant side service. |

**Spec meaning changes:** group restoration, `InvZu`, `InvRuheG`, `InvSichtG` and
the derived thread/spawn/link claims now quantify over declared global carriers
as well as tables. Update the header's carrier description and the implementation
commit accordingly. Preserve the qualifications: invariant initially true for
closedness/observation claims, only declared predicate carriers, no claim inside
a running writer, and no shared-atomic contract. Do not strengthen start premises
to hide a missing preservation argument.

Witnesses: global-only group, mixed table/global group under two locks, writer
touching only the global, temporarily broken group restored on normal and reason
returns, idle-root transfer and a guarded observation in a two-thread run.
Counterexamples/refusals: omit either lock, read an undeclared global under the
same lock, omit restoration on the reason path, false initial invariant, and
unguarded shared atomic. Show old table-only acceptance and conclusions survive.

**C04 — transition contracts and dynamic stages, without a second machine.**

`Parser/Item/ElementTief.STrans` already carries `tname`, triples of **expressions**
(`schritte`), `voraus` and `wirkung`. `uZustand:4311` discards no clause: it refuses
them; `uStufenNamen:4306` admits only symbolic stage names. Current body
`uZustandVon`/`lowShiftL` reaches `Stmt.shift`, whose constant endpoints carry
`D.erlaubt`, range, effect and guard proofs; `execStmt` checks the current value
and reports `Logik.vorzustand` on mismatch. Retain that existing rule intact.

| Layer | Implementable change |
|---|---|
| Canonical kernel expansion | Add **new** `TransitionWrite D Γ Λ` in `Kern/Syntax/Zucker`, with `slot` (table/field, bounded index, same-typed from/to expressions, `darf`) and `glob` (global, same-typed from/to expressions, `gdarf`) cases; all stage values are integers. Add **new** `TransitionExpansion` relating a list of these writes, a typed clause predicate and an ordinary `Programm` function fragment (signature, requires, ensures, endblock). Its fields assert exact requires conjunction, declared write permissions, snapshot/store expansion and postcondition/frame; prove its semantic soundness in `Kern/Semantik/Semantik` after `World`/`eval` exist. Store ordered typed places and endpoint expressions with their range/guard witnesses; functions use the same `Fn`, `Signatur`, `RufPasst`, contracts and resources as every other function. No new execution constructor or `D.erlaubt := true` escape. A generic expansion theorem relates every successful call to the declaration's full pre-state/post-state relation and frame, not just an example transition. |
| Exact execution meaning | Proposed userspace rule: `requires` is caller logic, conjoined with all source-state equalities; evaluate place indices and all endpoint expressions in the entry world, bind snapshots once, then perform declared stores in written order. Carry snapshots needed by ensures as explicit private generated parameters, with caller bind/argument provenance and a precondition equating them to the entry expressions; never reference body locals from ensures. Requires-only transitions perform no stores. Ensures relates each distinct target to its snapshotted target value; reject duplicate/possibly aliasing targets unless equal-result agreement is proved. This supplies explicit semantics for nonconstant stages and multi-place transitions; it is **not** an atomic multi-place transaction. Keep all required locks across the operation. Symbolic labels keep existing first-occurrence numbering; constant numeric stages use A11's checked normalization. Never coerce an arbitrary name/expression to stage 0. |
| Relation to existing shift | For finite constant edges, generate `Stmt.shift` and prove expansion agrees with its `D.erlaubt`/`vorzustand` rule under the generated requires. For dynamic endpoints, use checked `assignSlot`/`assignGlob` in the private generated function: its requires/ensures and the generic expansion theorem enforce the **named declaration's expression relation**. Admission must establish that the generated body is this expansion and that ordinary callers cannot bypass its requires; merely adding a graph pair or exporting an unrestricted store is insufficient. `D.erlaubt` remains the exact constant-edge projection used by `Stmt.shift`, not a replacement for dynamic clause semantics. |
| Effects and resources | `wirkung` declares permissions, not invented actions. Build the exact ordinary signature: every actual target write is included; `pure` conflicts with a store; reads retain footprints; declared lock/mark flow is checked with the existing signature and return-resource rules. Do not acquire a lock, consume a mark or call a service merely because an effect lists it. If the source operation has no corresponding action to discharge its linear flow, refuse it. Requires/ensures over shared atomics remain disallowed. |
| Source/export | At `Uebersetze.lean:4306/4311`, preserve `STrans` identity, predicates, expression endpoints and effects through `UZustand` and generated `UFn`; never flatten distinct clauses into the same unordered pair list. Resolve places/guards in the declaration's real scope, reject unbound captures, and reuse `uBool`, `uWertBody`, `uEffekte` and `UebersetzeAllg{,2,3}` checked function lowering. Extend the source expansion theorem and `Stage0.Frontend.elabWithScopes` to account for every generated function, caller and preserved clause; retain `uRegiert`'s unique-governing-state check. For a clause-bearing or dynamic declaration, `uZustandVon`/`lowShiftL` must route every source use through that generated call (or refuse it), never leave a raw `Stmt.shift` that bypasses the clause. All use sites must name or unambiguously resolve the declaration; equal endpoint pairs with different preconditions are not interchangeable. |
| Machine/checker/proofs | No new `eval`/`execStmt` cases: expansion uses existing reads, binders, checks at `rufAt`, stores/calls and returns. `Akzeptiert(X)` checks generated functions and complete call graphs just like explicit ones (`frag`, `fuss`, `stufen`, `renn`, resource and answer-site obligations). Source correctness additionally proves the expansion relation, endpoint range and exact effects. Existing `KoerperGutSA` supplies caller duties, frames and return restoration; re-establish the generated unit's `NutzerPflichtA`, then use `ziel_aus`/`zielX_aus` and `gabbro_ziel` unchanged. Do not turn requires into an oracle promise. |
| Stage 0 | Use `lowFun`, existing `Anweisung` shift/store/bind/call lowering, `lowEnd_ok` and `lowFun_spec`; C13 supplies richer endpoint arithmetic. Prove snapshot temporaries survive emission, all generated functions are emitted/reachable and `compile_source_program`/`irBild_correct` carry the transition expansion theorem. Specify failure codes explicitly: existing primitive shift retains 106; the generated function rejects its clause/state-equality requires at 101. Constant equivalence is under the legal-entry premise, not equality of these illegal-entry diagnostics. Preserve guard lifetimes, code/stack bounds and call-log/cost contributions of the generated calls; do not erase a call as proof-only metadata. |

**Spec impact:** no new hardware assumption or goal premise. This makes previously
unrepresented source clauses/dynamic endpoints mean the checked generated program;
the proposal's snapshot/order rule must be recorded as a source-meaning decision
in the implementation commit and reviewed before implementation. Existing constant
`Stmt.shift` behavior stays covered by an equivalence theorem. No implication that
group invariants hold between individual stores; C05 restores them at the already
claimed boundaries. Device/register transitions, privileged behavior and ASM remain
outside this package. Provider/service effects without their C08 rule, unbound
expression names, unresolved state identity, unchecked ranges and unjustified
alias/resource flows remain named refusals.

Witnesses: guarded transition with false/true requires, a requires-only transition,
two ordered writes preserving a mixed group, endpoint/index values read from the
entry world (including a later endpoint reading an earlier target), and equivalence
with a constant `Stmt.shift`. Negative fixtures: omitted effect/lock, wrong current
state, endpoint out of range, two declarations sharing endpoints but differing in
requires, duplicate aliases, resource imbalance, and shared-atomic precondition.

**Rebuild/acceptance handoff (implementation only; none run here).**

| Package | Modules whose changes force a rebuild, plus transitive imports |
|---|---|
| C13 | `Kern/Syntax/Syntax`, `Zucker`, `Profil`; `Semantik/Semantik/T1`; `Syntax/Extraktion/T3` and syntax traversals; `Logik/Fortschritt/KostenG`; `Parser/Elab/Uebersetze*`; `Zielsatz` locality/replay, embeddings and witnesses; Stage-0 expression, quantifier, old-state and value proofs |
| C17 | `Parser/Elab/Uebersetze*`, measure export/witness modules and Stage-0 frontend/compiler metadata; reuse `Logik/Terminierung/{Mass,Klasse,Entscheidung}`, `Zielsatz/Atomar/{MassRuhe,BeweisTerminierung}` without changing their duties; generic normalization only if admitted |
| C05 | `Kern/Syntax/Syntax`, `Semantik/Semantik/T1`, `Syntax/Satz/T4`; all declaration fixtures and carrier clients; `Interferenz*`, `VertragsFuss`, `Zielsatz/Kern/Spec`, invariant/replay/atomic/idle-root/link modules; exporter and Stage-0 `Funktion`, `Rueckkehr`, return emission, invariant-return and recursion proof clients |
| C04 | `Kern/Syntax/Zucker` and expansion witnesses; `Parser/Elab/Uebersetze*`, source normalization/provenance, generated-function lowering and certificates; rebuild existing goal/IR clients of the expansion without altering G's primitive shift |

The grammatik owner batches edits/builds; grammar builds use measured available
memory minus 2 GiB under the prescribed scope and count against the two global
Lean slots. Stage-0 checks retain 5 GiB slot limits. After each implementation
batch: full grammar build, layout check, Lean guardian and witnesses; print
`gabbro_ziel` axioms and require exactly `propext`, `Classical.choice`, `Quot.sound`.
Run affected Stage-0 pipeline proofs and assembly-runner fixtures, plus the required
remaining guardians before integration/push. No erased contracts, added axioms,
weakened footprint/resource checks or detached helper proof can close a package.
This document changes no acceptance result: **zero new source cases compiled or
proved; no builds run.**

### Model extension design: C01, C03 (2026-11-01)

Design baseline: `8805be37e`; static inspection only, no Lean edits or builds.
**New** marks proposed names; other names below were located in this checkout.
Kernel paths are relative to `grammatik/Grammatik/`. This checkout contains
“IR-03 in-progress canonical interface” and `Ausdruck/Aggregat/{Layout,Encoding,Kopie,KopieSatz}`;
the requested heading “IR-03 arrays and strings over the full value span” and
`storeFramePointerSpan` are **absent** here. Treat that store helper as an IR-03
handoff dependency, not an available theorem. Current `Welt/Lay.Lay.elem` still
advances by eight bytes, and `Welt/Schreib` proves single-word writes. The design
must join the completed IR-03 migration before claiming multiword world storage.

**Decision.** Add a real heterogeneous product; generalize the existing sum and
reason families rather than adding competing record encodings or tagged-value
machines. Records preserve declaration identity, field order and field types.
Pure field replacement plus the existing assignment statements is sufficient;
neither a new record heap nor a field-specific locking system is needed. Every
new inductive constructor goes at the **end**, including `Ty`, the mutual
expression family and exporter intermediates. Changes to arguments of existing
constructors migrate all clients in one canonical path; remove replaced numeric
payload adapters instead of retaining a compatibility mode.

| Package | Core model change | Spec impact | Engineering days |
|---|---|---|---|
| C01 | Typed products, field paths, checked field ownership, generated mapping products | Conservative value extension; ownership stage adds an explicit acceptance/preservation clause, described below | 18–30: copyable products 7–11, mappings 4–7, ownership 7–12 |
| C03 | Typed sum payloads; nominal open/closed reasons throughout values and channels | **Yes:** error outcomes and foreign-answer admission range over open reason values and structured payloads | 9–15, including channel/oracle migration |

Ranges include generic proofs, witnesses, exporter and connected IR cases, not
measured build times; shared raw-answer work is counted once in C03. Critical
path: nested `Ty`/`Val` recursion and all syntax inductions, IR-03 world/frame
integration, then ownership and channel replay. Safe walker child resolution is
a separate prerequisite when a source `down` field currently denotes a raw
address; C01 does not authorize raw-address access or privileged boot execution.

**C01 — records/products.**

| Layer | Implementable change |
|---|---|
| Types and values | In `Kern/Syntax/Typen`, append **new** `Ty.prod (name : Nat) (fields : List Ty)` and, at the ownership stage, **new** `Ty.linear (name : Nat) (repr : Ty)`. A resolved declaration number supplies nominal identity; anonymous structural products receive an interned identity derived from their complete ordered schema. Canonical alias expansion preserves the original identity. Export/link relocation must map these identities just as it maps table/signature identities. `Val F passt (.prod r fs)` is the dependent tuple `(i : Fin fs.length) → Val F passt (fs.get i)`; the empty tuple has one mathematical value. `Val F passt (.linear r τ) = Val F passt τ`; the wrapper preserves ownership identity in the type, not an extra runtime word. Extend the nested structural recursion used for arrays to lists of child types, with an explicit decreasing type-size argument if Lean cannot elaborate recursion through `List.get`; no arbitrary depth/fuel cut. Add **new** `prodGetW` and `prodSetW` at typed indices and prove get/set, other-field preservation and extensionality. |
| Typed expressions | `Args` currently follows `Expr`, outside its mutual family (`Syntax/Syntax:553`). Move that same definition into the mutual family before appending **new** `Expr.prod (r : Nat) (args : Args D Γ Λ fs) : Expr D Γ Λ (.prod r fs)`, **new** `Expr.prodGet (v : Expr D Γ Λ (.prod r fs)) (i : Fin fs.length) : Expr D Γ Λ (fs.get i)`, and **new** `Expr.prodSet (v : Expr D Γ Λ (.prod r fs)) (i : Fin fs.length) (e : Expr D Γ Λ (fs.get i)) : Expr D Γ Λ (.prod r fs)`. Keep `Args.nil/cons` and their order. A **new** indexed `FieldPath : Ty → Ty → Type` composes these projections/replacements for nested places; elaboration resolves names to indices, never runtime strings. No general `linear` introduction expression may manufacture an owner. |
| `eval` and assignment | In `Kern/Semantik/Semantik/T1`, `eval .prod` packages the evaluated arguments in declaration order, `eval .prodGet` selects the component, and `eval .prodSet` replaces precisely that component. Their `orte` are respectively argument reads, base reads, and base plus replacement reads. **No new `Stmt` constructor or primitive `execStmt` case:** local `p.f = e` expands to `assignVar p (prodSet (var p) i e)`; a record-valued table field expands through `assignSlot`, `assignThru` or `assignSlotRef`, and a global through `assignGlob`. Capture the place/index and RHS once with existing block/end-block binders before expansion; preserve source evaluation order. A record-field store is a read/modify/write of its containing cell and requires that carrier's existing write permission and guards. Prove the expansion against `execStmt` in T2, including preservation of every sibling. Do not route a state-field update around `Stmt.shift` or erase `where` checks. |
| All value positions | `D.params`, `D.erg`, `D.typ`, `D.gtyp`, `ErgExpr.val`, `Env` and `World.slots/globs` already range over arbitrary `Ty`; use them unchanged for product parameters/results, locals and table/global cells. C03 makes `Ty.sum` payloads arbitrary `Ty`, so products also travel inside sums. Initialization must supply every field exactly once; no zero/default field and no projection masquerading as a whole result. `Stmt.verbund` in `Zucker:215` remains count-one carrier sugar, not the product constructor. Carrier records and by-value records share the resolved schema, but a by-value product is not a table capability. |
| Source export | `Parser/Expr/Typ.STyp.raw` holds brace types; `SItemTief.typeT` holds names/modifiers; labelled `SExpr.call` is the existing `P(a: ..., b: ...)` construction (`SYNTAX.md:660`). Add **new** `URecord` and a checked schema collector in `Parser/Elab/Uebersetze`, preserving field names/order/types and nominal/linear/ghost modifiers. Resolve dependencies acyclically; recursive values require an existing safe indirection. Replace the relevant refusals in `uAliase:822`, `uTyp:988–1023`, `uFeldTyp:1029–1034`, parameter/result elaboration around :1780/:2050, and `uRestFehler:4039`. Reuse the canonical type/field reader for balanced `raw` groups, not a comma splitter. Extend `USide`, `UParamArt.wert`, `UFnKopf.resTy`, `UProg`, `uWertBlatt`, `uSeiteBlatt`, `uZugriff`, assignment and return elaboration; field access to a product must be distinguished from a carrier slot lookup. Reject missing/duplicate/unknown constructor labels and retain source argument evaluation order before arranging fields in declaration order. In `UebersetzeAllg`, extend `declOf`, field typing, `lowWertE`, `lowSideVal/lowSideEns/lowEns`; in `UebersetzeAllg2/3`, extend binding, argument/store lowering, `lowErg`, `lowStructL`, `lowEndL` and `lowerAllg`. Carry schema/constructor/projection/update preservation through the actual `Frontend.elabWithScopes` and `Compiler.CanonicalSourceProgram`, not a witness-only exporter. |
| IR-03 layout | Define **new** `fieldWords fs i = sum ((fs.take i.val).map valueWords)`; `valueWords (.prod r fs) = max 1 (sum (fs.map valueWords))`. `encodeWords` concatenates fields in declaration order, with `[0]` only for the empty product. `linear` has its representation's width/encoding. All spans use the existing 64-bit runner words, aligned to eight bytes, with no internal padding or field reordering. Thus a u8 value still occupies its existing runner-word span. This is the internal ABI, not a packed `format`/foreign layout: use `Speichermodell/RecordLage.{offset,groesse,offset_ausgerichtet}` only for a separately checked byte-layout adapter. Prove each field interval lies inside the product and distinct intervals do not overlap; compose offsets for nesting. `contextWords` has the existing reverse-context placement order, whereas a product's internal fields have declaration order: **do not use `contextWords fs` to derive field offsets**. |
| Emitter/proofs | Extend `Senke/Ausdruck.lowE`, `Ausdruck/Top.lowE_top`, `Ausdruck/Satz.lowE_ok` and their mutual argument/value validity statements: constructor evaluates all fields into reserved disjoint spans; projection copies the entire selected field; replacement first preserves the base then overwrites its selected span. Reuse `Ausdruck/Aggregat/KopieSatz.copyValue_run` and its exact `Agree` footprint, including its forward-copy condition `dst ≤ src ∨ src + width ≤ dst`; use a disjoint temporary for destructive overlap. Extend `ValueValid` recursively over every field and through `linear`, and derive field extraction/reassembly lemmas for `ValueAt` and `ValueOk`. Reuse IR-03's completed pointer-span store/load contracts (including `storeFramePointerSpan` when handed over), never a new record-only store loop. Extend `WeltAt`, `LayIn/LayDis`, initialization, snapshots, `EnvAt`, assignments, `ResultAt/ResultOk/ReturnMirror`, call and return paths; complete product result width feeds `returnWords`. Thread through `lowS_ok/lowB_ok/lowEnd_ok`, `Rekursion.lowFun_spec`, `Compiler.compile_source_program` and `IRBild.irBild_correct`. |

**Ownership is checked per field, not inferred from a byte copy.** Existing
`Res.marke`, `D.eigner`, `Signatur.konsumiert/produziert` and `nachSig` govern
resource marks; `Ty.ptr n rw` alone carries no unique owner (`Val` is unit).
Rust `m2.rs` tracks `Zustand::{Lebt,Verbraucht}` by variable, and `m3.rs` handles
root separation. Neither supplies a generic proof of partial record moves.

The proposed `FieldPath` constructors are identity, one typed product-field
step, a `.linear r τ → τ` representation step, and composition; they carry no
permissions themselves. Define path get/set recursively from `prodGetW` and
`prodSetW`, with get-after-set and disjoint-path frame lemmas. Array indexing
uses existing `arrGet/arrSet`; inventory keys append the evaluated bounded
element index. Representation steps cannot bypass `ValueUse` or unwrap an
owner into a freely copyable capability.

Implement **new** `ValueUse`, an inductive derivation over the existing typed
syntax, with input/output availability maps keyed by local/cell plus `FieldPath`.
Its type-directed leaves are copyable scalars or indivisible `Ty.linear` atoms;
products/arrays split recursively and sums expose only the selected payload.
An explicitly linear outer wrapper is one indivisible obligation even if its
representation has several fields; a non-linear product with linear fields has
one obligation per linear field. Ordinary scalar projections remain copyable.
For scalar observation through a linear wrapper, append **new**
`Expr.fieldView (p : FieldPath τ σ) (h : Observable σ)
(v : Expr D Γ Λ τ) : Expr D Γ Λ σ`, with **new** `Observable σ`:
numbers, bools, reasons and recursively pure
products/arrays/strings, excluding capabilities, references and linear atoms.
`FieldPath` includes a representation step through `linear`; `eval` projects
without consuming, `orte = v.orte`, and `ValueUse` requires the owning atom live.
A borrowed capability needs the existing rights/root/guard discipline plus a
proved borrow lifetime; `fieldView` cannot manufacture one. Include this case
in the same renaming, locality, cost, IR projection and ownership proofs.
The same mechanism covers whole records, parameters, results and payloads:

- Construction moves each linear input into one destination; projection of a
  linear field moves that leaf, making its source path unavailable. A whole
  read/move requires all leaves live. Reading a copyable sibling remains legal.
  Replacement may fill an unavailable leaf, but cannot overwrite a live linear
  obligation; ordinary `prodSet` of a noncopyable base is admitted only with this
  exact transfer derivation, never as a second copy. A temporary for RHS evaluation
  has the same obligations as a named local.
- Calls transfer the paths named by the actual consumed parameter positions;
  callee entry/exit summaries include surviving/produced paths and both result
  channels. Return transfers the result; every other live local obligation must
  be consumed or explicitly survive as required by the existing `leaves` rules.
  Joins require equal inventories on returning branches; loops restore the stated
  carried inventory at back edges and prove all exit inventories. A divergent
  branch has no terminating-exit obligation. No new eventual-consumption claim
  about an infinite run follows from linearity.
- Existing marks remain in `Λ`; a field carrying an owner names that same mark,
  not a newly minted one. Parameter/result transfer renames its location; stage
  changes/retirement use `advances`/`retires` and existing signature transitions.
  Provider freshness and the existing owner-minter obligations remain user logic.
  Ghost linear fields have proof obligations but no independent payload word;
  export them to the existing mark context, with a certificate matching each
  erased field to its resource. `URecord` keeps the full schema and a checked
  source-field-to-runtime-field-or-resource map; `Ty.prod.fields` contains only
  runtime fields, in their relative declaration order. Ghost field access is
  resource access, never `prodGet`; no ghost obligation becomes a default value.
- Add **new** `valueUseB` with a soundness theorem and **new** `AkzeptiertSpec.werte`
  / `AkzeptiertSpecX.werte`; compose with `Akzeptiert`/`AkzeptiertX`. Extend M2 to
  the same field paths and M3's root extraction through products/sum payloads;
  `Logik/Vertraege/Getrennt.traegerVon` currently sees only a top-level pointer.
  Generalize separation to the flattened capability leaves, including leaves
  within one argument, retaining the declared carrier/rights for every leaf.
  No cross-type re-view or int-to-pointer becomes valid by being put in a record.

For linear table/global cells, availability is a ghost inventory over the
existing `Speicher`, keyed by actual `(t,k,f,path)` or `(g,path)`, not a new heap.
A move leaves stale representation bits but no usable permission; its next read
requires a live inventory entry. The shared inventory is updated under the same
carrier guards/owner marks as the store; aliases name the same entry. Computed
indices need a proved equality/disjointness fact, not distinct syntax. Add **new**
`ValueOwnership` relating each live linear atom to exactly one location, and
prove preservation under the existing G/GX step and foreign-call contract.
Foreign consumption/production and initial ownership are explicit user-logic
obligations, not assertions deduced by the checker or hardware assumptions.
Concretely, **new** `ValueFlowDuty` in `NutzerPflicht`/`NutzerPflichtA` supplies
initial inventory uniqueness, semantic cell-identity facts and each foreign
transfer summary, for every relevant world and rely answer. `valueUseB` checks
the finite syntax-directed transfer derivation and which duties it requires;
it does not decide universally quantified cell disjointness or borrow lifetimes.
The preservation theorem uses that derivation **and** those discharged duties,
under the existing guards. Dynamic moves without such a derivation/duty refuse.
Until those obligations and the simulation are connected, refuse linear-cell
transport; never enable it merely because `copyValue_run` copies all the bits.

**Walk mapping products.** Actual source coordinates are `SWeg` in
`Parser/Item/ElementTief:407`, and `Uebersetze:1570/3174/4039` (quantified domain,
traversal domain, declaration). `SWeg` retains `stufen/node/dname/dwhen/blatt/invarianten`.
Rust `umgebung.rs::walkknoten` and `domaene.rs::abbildungsfelder_pruefen` establish
the schema: all node-entry fields plus synthesized `va`, `level`, `index`;
`index[level]` is path-dependent. Generate **new** `WalkShape` (positive finite
levels L, node arity N, node schema and safe child relation), **new** `WalkPath`
(depth and bounded child indices), and **new** `MappingTy` as `Ty.prod` of the
entry fields, `va`, `level` and `[Ty.index N; L]`. Reject synthesized-name
collisions; select `level = L - 1 - depth` (root highest, leaf level zero).
`index[ell]` stores the visited index at level ell; positions below `level` are
canonically zero and the active suffix is `[level,L)`. They are not extra
visited nodes. A **new** `WalkMeaning` relates
the source down/leaf predicates and resolved root/child relation to this product.

Expand finite levels with existing `Stmt.traverse`/quantifiers and product
binders, reusing `Stmt.walk2` only as the two-level expansion pattern. At a node,
evaluate the leaf predicate first; a leaf yields exactly one mapping and stops
descent, including an early large-page leaf. Otherwise descend only if `dwhen`
holds and another level exists. Neither predicate silently replaces the other;
both true still yields one leaf. Preserve lexicographic path order, source
leave/next semantics and invariants at every loop boundary. Prove **new**
`walkMappings_correct`: emitted visits equal all reachable qualifying path/entry
pairs, including their fields/position, with no duplicate *paths*; shared child
nodes reached through distinct paths remain distinct mappings. Prove quantifier
and traversal substitution against that same enumeration and its finite bound,
not merely list membership (`Bausteine/Schablonen/SchablonenT5/T2.walk_hits_mapping`).
`N^L` bounds mappings; work also includes internal-node visits and must be billed
by the sum of level bounds, not `L*N` or only the leaf count.

Two unresolved semantics must be explicit in the implementation review:
`SWeg` has no byte/page scale or child-address binding, and the existing abstract
`walk_hits_mapping` supplies neither. Recommend `va = radix-prefix * N^level`,
where the prefix includes the current entry index in root-to-entry radix-N
order, in logical leaf units; an early leaf covers `N^level` such units. Then
use a checked layout scale for byte `va`; preserve any
established binding's coordinate convention instead of silently changing it.
A numeric `dname` alone cannot select a G region. The root/child access must be a
safe capability/reference relation supplied by the declared storage/binding,
whose correspondence is proved as user logic. Without that relation or an
agreed `va` unit, refuse the affected walker by name; never fabricate an address
conversion, flatten an unrelated table, or claim complete walk coverage. These
are source-meaning decisions for the grammatik owner/owner, not implementation
freedom to guess paging constants. Safe finite walkers proceed independently.

**C03 — open reasons and arbitrary typed tagged payloads.**

| Layer | Implementable change |
|---|---|
| Typed payloads | Generalize the existing `Ty.sum` argument to `List (Option Ty)` in `Kern/Syntax/Typen`; do not add another sum constructor. Generalize `Nutzlast none = Unit`, `Nutzlast (some τ) = Val F passt τ` together with `Val (.sum cs) = Σ i : Fin cs.length, Nutzlast (cs.get i)`. Define this by the same nested type recursion as products. In `Syntax/Syntax`, replace `NutzlastExpr.num` by **new** `.val (e : Expr D Γ Λ τ)` at the end, retaining `.empty`; `Expr.case` keeps its name. `ArmCtx Γ none = Γ`, `ArmCtx Γ (some τ) = τ :: Γ`; generalize `Arms`, `execArms`, `armEnv` and `Ausgang.schrumpfArm`. `Stmt.onTag` still requires exactly one arm per case and binds the whole typed payload. `evalNutz` delegates `.val` to `eval`; `eval .case` packages the tag and payload. No new `Stmt` constructor. Noncopyable payload matching consumes the selected variant under `ValueUse`; its inactive variants create no obligations. |
| Reason descriptor/value | Add **new** `ReasonSpec` before `Ty`: declaration identity `name : Nat`, ordered distinct `codes : List (Fin (2^128))`, and `closed : Bool`. The 128-bit domain comes from `crates/gabbro-syntax/src/ast.rs::ReasonFall.wert : u128`, not a runner-word limit; validate bounds in the canonical parser/exporter too. Replace `Ty.why (n : Nat)` with `Ty.why (r : ReasonSpec)`. **New** `ReasonVal r = { c : Fin (2^128) // r.closed = true → c ∈ r.codes }`. Closed values are exactly declared cases; open values also include codes not yet named, retaining their identity through forwarding. This is an opaque reason value in the source, not an integer: no arithmetic, integer conversion, or manufacture of an unknown case. `Expr.why` constructs a declared code by a bounded case index; append **new** `Expr.whyEq` over two expressions of exactly the same reason type, with code equality and combined footprints. An open/closed or foreign declaration is not implicitly interchangeable. In particular, an open declaration with zero known cases is inhabited and is never “no channel”. |
| Channels and execution | Replace the `Nat` type of `Signatur.gruende` and `Deklaration.agruende` by `Option ReasonSpec` (`none` = no channel); keep these existing field names. Add **new** `reasonTy none = Ty.never`, `reasonTy (some r) = Ty.why r`. Migrate `Vertrag`, `D.gruende`, `SigPasst.gruende`, all call premises (`= none` or `= some r`), `Ausgang.why`, `EndAusgang.why`, `RufAusgang.why` and machine/rest result types to the exact descriptor. Generalize existing `Stmt.retWhy` and `Endblock.retWhy` to take `Expr D Γ Λ (reasonTy V.gruende)`, so a received open reason can be forwarded without reconstructing a declared index; T2 evaluates it once and records its reads. Error binders use the same `reasonTy`, including `Block/Endblock.bindCallElse/bindAxiomElse`. `onWhy` gains a proof `r.closed = true`; `execGrund` converts the declared code to its unique case index and runs the corresponding `GrundArms` arm. Keep `GrundArms` indexed by the known case count. No unknown/default match arm; open matching stays refused (`m1.rs:2170`, M125), while equality tests and forwarding work. `rufAt` keeps distinct normal/reason returns, requires/ensures order and owed-invariant duties. |
| Foreign-answer boundary | Current `Orakel.wirkt` returns one `Int`; `einpassen`, `summePasst` and `axiomAntwortSonst` decode numeric payload/tag packing. That interface cannot be cited as an existing structured-product ABI. Replace its answer component with **new** `RawAnswer` (`value RawValue` or `reason RawValue`), where **new** `RawValue` is a finite tree of integer leaves, ordered product fields and a tag plus optional payload. Generalize `einpassen/einpassenErg`, `AntwortLeer`, `axiomAntwort/axiomAntwortSonst`, `sonstPasst`, `roh` and `Logik/Vertraege/EinpassenVoll.einpassen_voll` against the declared type and exact tree shape. Scalar leaves retain the existing range/IEEE/function-image checks; recursively check product arity, every field, selected payload type and reason membership/bounds. Keep register raw `Int` access unchanged, embedding its scalar answer at the decoder boundary. Structured user bindings provide explicit register/buffer-to-tree correspondence; a syscall's errno decoder maps its declared codes to reason values. Never choose an unspecified product field or map an unknown reason to the first known case. These are raw data checked against G types, not a second interpreter. |
| Source coordinates | `Uebersetze.uWhys:4285–4297` must retain `whyT`'s `ex` flag, source numeric codes and identity in `UWhy`; remove only the blanket nonexhaustive refusal. Preserve N002's distinct-code check (`namen.rs::reason`). Migrate `kanal/resWhy`, `uWhyArme:3210`, argument elaboration at :2175 and `uEndeKanal:3068`/result elaboration through :3125, `UebersetzeAllg2.lowGrund` and all call/else/return lowerings; require `closed` before constructing `onWhy`. `uNutzTyp:4227`, `uSumFaelle:4240`, `uSums:4262` and `USum` must retain a complete parsed `STyp`/resolved `Ty`, not just an integer range; `uBisKlammer` currently stops at the first `)` and must use balanced nesting. Generalize `USVal`, payload binders and `UebersetzeAllg2/3` tag dispatch/export. Resolve bool, arrays/strings, references and products through the one canonical type elaborator. Prove typed payload substitution, exact open/closed descriptor provenance, forwarding and same-declaration equality in the real `lowerAllg` pipeline. |
| IR-03 representation | For generalized sums use a separate tag span `integerWords 0 (cs.length-1)` followed by `max` of the **complete** `valueWords` of possible payload types (`none` contributes zero), with zero padding after the active payload. The empty sum retains the ABI's positive-width marker but has no model value. Keep the existing `sumFits` compact case only when every payload is an integer range and the existing 8/56-bit packing theorem applies; typed products are never squeezed through `sumOff`. Generalize `sumPayloadWords`, `encodeWords`, `ValueValid`, constructors/dispatch and selected-payload `ValueAt`; inactive padding is zero and has no validity/ownership obligations. Closed reasons may retain compact declared-index encoding with a proved code/index bijection; open reasons encode the complete u128 code in two words. `valueWords` depends on the descriptor, not its currently known case count alone. Generalize `returnWords result reasons` to the optional descriptor, with no-channel width zero, still reserving at least `resultWords result`; error status is outside both complete spans. Update direct/indirect/foreign calls, `Rueckkehr.retWhy_ok`, `RetWhy`, snapshots, relocated parameters and `ReturnMirror` consumers together. Use the same aggregate copy/store/load proofs as C01 and connect the existing mutual expression/statement/block/function/image theorems. |

The raw-answer migration must also replace the current aggregate refusals in
`Logik/Vertraege/EinpassenVoll.WertOk` and `antwortTyB`, not make their checks
vacuous: product inhabitation is the conjunction of field inhabitation, sums
the disjunction over payloads, arrays require an element only when nonempty,
strings admit the empty string, and open reasons are inhabited regardless of
known case count. Recursively preserve IEEE well-formedness. Prove
`antwortTyB_iff` and `einpassen_voll` for these definitions with **one consistent
function image** across all nested function-pointer leaves, then restore
`antwortenB_iff`/`StelleOk` and halt classification. Decoding completeness is not
provider freshness or an owner minting proof. For all-copyable old programs,
`ValueUse`/ownership obligations are empty and derive automatically; stages
must not add an unrelated user premise to an existing accepted scalar program.

**Goal proof obligations and Spec review, shared by both packages.**

1. **Reads, races and separation.** Extend `Expr.orte`,
   `NutzlastExpr.orte`, `Args.orte`, `Syntax/Extraktion/T2.stmtOrte` and
   `Extraktion/T3.eval_liest_nur_orte` through products, payloads and evaluated
   reason returns; prove `ZielOrt/Grundlage/ZielOrtSem.eval_gleichAuf` from those
   facts. A by-value field projection reads no new world location, but a projection
   from `slot/thru/slotRef/glob/oldS/oldG` retains its containing carrier in the
   footprint. Field read/modify/write retains its read and write events.
   G/GX race footprints remain **carrier-granular**, not separately lockable field
   paths: two fields never establish disjoint carriers. Re-establish
   `rennB_iff`, `fussWB_iff`, `Atomar/AtomarAkzeptiert.fussWXB_ok`,
   `vertragsFreiB_ok`, `akzeptiert_iff` and `akzeptiertSpecX_of`; contracts cannot
   hide a shared-atomic read in a nested payload/field. Generalized capability
   leaf separation supplements, never weakens, these existing carrier checks.
2. **Frame, invariants and contracts.** Pure get/set lemmas plus existing
   `World.storeSlot/storeGlob` show all other cells and sibling fields unchanged;
   repair `Logik/Vertraege/RahmenTreu.rufAt_treu`,
   `ZielOrtSem.gleichAuf_storeSlot`, invariant/contract dependency and replay
   proofs. A writer of any subfield owes all of the containing carrier's existing
   invariants; product extension adds no independent invariant registry.
   `Programm.requires/ensures/invariante`, old-state snapshots and result contexts
   must retain full values. Re-establish `VertragAmOrtG`, `SperrInvG`,
   `InvAmOrtG/InvAmGrundG`, `InvRuheG/InvSichtG` and
   `SperrWechselG/SperrSichtG`, including early/reason returns and idle-root/link
   transport. Reason returns still bypass normal ensures; retain
   `InvGutGrund`/`LogikPflichtA` for **every** admitted reason, including unknown
   open values. Do not satisfy them by quantifying only over declared cases.
3. **Addresses.** `Speichermodell/Adressen/Bereich.storeSlot_aussen`,
   `execStmt_blatt_aussen` and `rufErreichbarGX_aussen` remain the route to
   `speicherAdressen`: only an in-extent existing cell is replaced. A product
   field span lies inside that cell's representation; prove this and sibling
   disjointness in the IR-03 layout relation and compose with
   `Adressen/Layout.zelle_im_bereich` under `LayoutOk`. `AdressLayout`'s field
   means `D.Feld t`, not an arbitrary nested product path. No narrower race or
   physical-address claim follows just from a word offset, and no new address
   space, freshness or memory-provider assumption is introduced.
4. **Ownership and Spec meaning.** Copyable products and typed sums conservatively
   enlarge the values/programs quantified over by `Spec.lean`; existing safety
   conclusions keep their qualifications. At the ownership stage, add **new**
   `WertLinearG`: every reachable G/GX machine admits a `ValueOwnership` inventory
   whose transfer history is compatible with `ValueUse`; no live atom has two
   locations, unavailable paths cannot be used, and terminating scope exits have
   no undeclared outstanding local obligation. Prove it by the same machine-step
   induction, including starts, spawn, return and linking, and carry it as an
   additive `Ziel`/`ZielX` conclusion. Record this **strengthening** and the new
   acceptance component/user ownership duties in the Spec header and commit;
   it is not an axiom, a weakening of `BesitzStart`, or eventual reclamation.
   C03 also changes the meaning of the reason alternatives/foreign-answer
   domain in `KopfHalt`, `InvAmGrundG`, `InvGutGrund`, `HardwareAnnahmen` and the
   derived goals: open values include undeclared codes, structured answers have
   all fields checked. Preserve the existing named assumptions; any foreign
   ownership/freshness claim stays user logic. The implementation needs an
   explicit Spec diff/review, not the label “representation only”.
5. **Remaining theorem closure.** Extend renaming, ghost/fragment checks,
   `Syntax/Geist`, `Syntax/Fehler`, `Syntax/Extraktion`,
   `Nebenlaeufigkeit/Sperren/MitRuhe*`, `Zielsatz/Einbettung/Syntax`,
   `Speichermodell/Maschine/GXMaschine` and atomic replay for the changed syntax
   and outcome types; update the represented `GabbroV/GvBruecke` fragment.
   Extend `Logik/Fortschritt/KostenG/T1.kostenExpr` and statement/binder costs for
   construction, replacement, typed matching and evaluated reason returns,
   then `frame_schritte_beschraenkt` and the corresponding `ZeitAb/ ZeitAbX`
   proofs. Re-establish progress/halt classification without an “unknown reason”
   stuck case. Recompile `Zielsatz/Kern/Beweis.ziel_aus`,
   `Atomar/BeweisAtomar.gabbro_ziel`, `gabbro_ziel_gx`, `gabbro_ziel_sc_aus`
   and `gabbro_ziel_verbund`; source call logs, budgets, locks and interruption
   guarantees retain their existing premises. Audit exactly `propext`,
   `Classical.choice`, `Quot.sound`; no added axiom or executable interpreter.

**Witnesses and refusal boundaries.** Every generic syntax/translation theorem
gets a non-degenerate `_zeuge` satisfying all premises jointly; source examples
must actually pass export, `AkzeptiertX`, IR emission and the assembly runner.

| Package | Positive witnesses | Negative twins / retained refusals |
|---|---|---|
| C01 values/layout | Empty and heterogeneous scalar product; two equal-shape nominal records; nested record/array/string and a >64-bit field; field replacement preserves siblings; record parameter → table cell → sum payload → call result; old-field contract; overlapping-copy temporary | Foreign nominal identity, unknown/missing/duplicate field, wrong range/type, recursive-by-value schema, out-of-range array index, truncated result, unsupported byte layout, state/where bypass, unguarded carrier or shared-atomic contract |
| C01 ownership | Move one linear field and use its scalar sibling; refill moved field then move whole record; two linear fields transferred independently; linear payload match; guarded cell handoff through an alias; both normal/error exits conserve ownership; ghost mark/stage survives erasure | Read moved path/whole partial record, duplicate field move, overwrite/drop live leaf, unequal branch inventory, missing consumes position, forged owner, aliasing computed cell, unproved initial/provider ownership, ghost runtime use |
| C01 mappings | L=1; N=2/L=3 with real child links; unreachable/nonleaf entries excluded; early large-page leaf; shared child at two distinct paths; every node field plus va/level/index; nested quantified binder and generated invariant | Zero/unknown levels, invalid down target, synthesized-name collision, missing safe child binding/va scale, L*N domain bound, wrong active index suffix, missing invariant restoration; raw-address or boot behavior remains excluded |
| C03 | Closed and open declarations with equal known cases but different identities; undeclared open code survives foreign call → else binder → return → caller equality; open declaration with no known cases; codes >64 bits; bool/record/array/string/reference payloads through match and calls; closed integer tags retain their compact theorem | Open `match` (M125), foreign-reason equality/forwarding, code outside u128, duplicate codes, unknown closed code, absent/extra/wrong payload, malformed nested raw answer, discarded fields, unproved reference provenance, non-atomic multiword exchange |

**Recommended staging and rebuild handoff.** First implement scalar-only
copyable products end to end; then nested products with IR-03 full spans and
typed sum payloads. Next migrate reason descriptors, channel outcomes and raw
answers as one compiling batch; enable open reason transport only after every
return/foreign/error consumer is connected. Then add safe mapping products and
their exact enumeration; resolve the documented va/child-binding questions
before enabling affected source walkers. Finish with the ownership derivation,
first local/call fields, then guarded table/global cells, ghost fields and the
additive Spec theorem. Intermediate stages explicitly refuse the remaining
forms; a green product helper never marks all of C01 complete.

`Typen` and `Syntax` changes rebuild nearly all grammar modules: semantics,
syntax inductions, G/GX machines, acceptance, invariants, costs, idle-root/link
embeddings, goal witnesses, exporter and the GabbroV bridge. C03's changed
`gruende` field also updates every signature/declaration fixture and all oracle
answer proofs. Stage 0 rebuilds aggregate encoding/layout, world/init/snapshot,
expression and dispatch, assignment/binding, direct/indirect/foreign calls,
returns, recursion, start/image and frontend/compiler provenance consumers.
One grammatik owner batches these changes; no simultaneous grammar mutation.
Implementation builds use the authorized available-memory-minus-2-GiB scope
and two global slots; Stage-0 checks use their prescribed 5-GiB slots. Require
full grammar build, layout check, Lean guardian/axiom audit and connected
Stage-0 proofs/runner witnesses after each accepted batch; all remaining
guardians still gate integration. This design compiles **zero new cases** and
changes no measured proof/acceptance status; no builds were run.
