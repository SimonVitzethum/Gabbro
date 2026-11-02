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

**Parameterized-start activation (IR-12, 2026-11-01): done for `main`.** `exitSlot` is gone. A start's scratch
(the spawns in `main`'s frame, the exit code of every thread) is `startScratch f = receiveTop (D.signatur f) FB`, above
the callee header, the complete parameter span, the shared result area and the status word. `bild` takes `main`'s
environment `ρ`; its words (`encodeEnv`, the call ABI's own encoding) are the image's bytes in the first frame at slots
`FB + FB ..` (`Bild.args`, `Bild.bytes`: header, code, first frame via `startFrameBytes`, then zeros). `spawnC_ok` /
`spawn1_ok` leave every slot below the scratch unchanged, `start_ok` takes the words and `ValueValid` of the environment
and derives `EnvAt` after the depth write (`startEnvWords_depth`); `bild_kern` derives them from the loaded bytes
(`startEnvBytes_words`) and preserves them across the spawns (`wordsAt_frame_agree`). `bild_ok`/`bild_ok_u`/
`irBild_correct` quantify over no environment any more: `Emitted.args` is `main`'s fixed environment, the pointer to
the table each parameter's type names (`mainEnv`, G's value `()`, encoded as the zero word); any other `main` parameter
is refused (`ir: main takes a parameter that is not a table pointer: no start-argument form`). Roots stay
parameterless (`ir: a root takes parameters`, guard kept: concurrent start arguments need the `SourceStart` list instead
of the deduplicated name list). No second startup ABI.

Measured on master `f8af1160f` + IR-12: the Stage0 root closure (286 modules rebuilt on IR-03's warm library incl. `Stage0`,
`Nachpruefung`, `Stage0.Haupt`, `StartArgumentProben`, `StartImageProben`, `ProfilProben`) is green; `Nachpruefung` 397
theorems on the standard axioms only, `gabbro_ziel` and its siblings on exactly `propext`/`Classical.choice`/`Quot.sound`
(grammar not rebuilt); layout check clean (`BildSatz` 481 lines). All 218 textual programs of `stage0/proben-ir` pass on
the assembly runner or refuse with the expected text (new: `main-pointer-params` 43, `main-int-parameter`). The old
probes in `stage0/proben`: `hello`, `echo`, `threads` compile and print exactly their `.aus` with exit 0; `upper` was
rewritten on the raw `read`/`write` gates (like `echo`; it no longer relies on the retired Lean driver's `io.ein`/`io.aus`
convention) and now prints `ABC` for `abc` with exit 0, so all four probes pass on the assembly runner.
The full Lean guardian was not run: it would rebuild `grammatik/` in this worktree (no warm `.lake`).

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

The migration is integration green on top of master and IR-06's complete-span world
(2026-10-31, see "IR-03 full value ABI integration" at the end of this file). Ordinary
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
Its active lane now implements IR-10 functions/calls/snapshots on shared Lean slot 2.
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

## IR-03 full value ABI integration (2026-10-31)

The full multiword ABI (`valueWords`/`contextWords`/`variableOffset`/`encodeWords`/`ValueAt`, the
`returnWords` area with `ReturnMirror`, `ResultAt`/`ValueOk`/`ResultOk`) is integrated with master
(`d9fbb37bc`) and IR-06's complete-span world storage (`349b2cc9c`: `WeltAt` is `ValueAt` per cell,
`globalValueC`/`globalStoreC`, `slotValueC`/`slotStoreC` with `_ok` theorems). `Stage0.Haupt` and every
module of the `Stage0` root build, except two (below). Consumer changes made in this step:

- `lowE`: `glob`, `slot`, `thru`, `slotRef` read through IR-06's complete-span emitters
  (`globalValueC`, `slotValueC`); `lowE_ok` takes `hLay : LayIn L`, which the span read proofs need.
  `assignGlob`, `assignSlot`, `assignThru`, `assignSlotRef` use `globalStoreC`/`slotStoreC`; the
  reference's cell membership is read from the validity of the evaluated reference value.
- Word-sized world consumers keep an explicit guard instead of a silent scalar cast:
  `aggregateFits` now also requires `wordCompatB` (canonical single-word view). Consumers: table
  reads inside `reaches`/quantifiers, byte fields, `publish`, atomic `awaits`/`exchange` (a wider
  atomic has no hardware primitive and is refused), gate result bindings (`bindAxiomElse` also
  requires a one-word reason value), gate buffers (byte field of one-word cells).
- `weltAt_slotWord`/`weltAt_globWord` derive the one-word store from IR-06's `weltAt_slot`/`weltAt_glob`.
- Exit status: `ExitErg` replaces `EncErg` in the start/image statements: the low word of the
  canonical result, and for word-compatible results also the full scalar relation (`resultAt_exit`).
- Literals of every range materialize through `constWords` (no `scalarFits` refusal any more).
- `arrGet` of any length selects the complete element through `selectFrameSpan` (`selectFrameSpan_ok`).

Measured: all 227 modules of the `Stage0` closure (root without the two modules below) check;
`stage0/Nachpruefung/Teil*.lean` reports 307+ theorems on only `propext`/`Classical.choice`/`Quot.sound`
(including the new span, store, selection and exit theorems); layout check passes; 116 textual
source -> IR -> assembly programs of `stage0/proben-ir` (compile and execution results or refusal
text) match, run with a runner regenerated from `runner/` sources (the old root build lacks `udiv`).
New textual programs `arr-triple`, `arr-runtime-index`, `arr-nested` (3-element and 2 x 3 arrays,
constant and runtime indices) and `str-long` (capacity-3 string, copy, `lenof`) execute correctly.

Open (exact): `arrSet` for more than one element; `strCat`, `strGet`, `strEq`, `strLt`, `strWeit` on
strings of capacity above one (refused by their guards); ordinary records (canonical-model
prerequisite); `StatementCost.lean` and `EarlyExit.lean` (IR-08's counted statement layer) are NOT
migrated to the new copy/return/store ABI and are excluded from the `Stage0` root import list until
counted versions of the span copy, store and return transports exist; `Nachpruefung.lean` lost
its five `EarlyExitProbe` lines with them.

## IR-03 arrays and strings over the full value span (2026-11-01)

Continued from the full ABI integration above. Each step was rebuilt on the whole `Stage0` root, audited
with `stage0/Nachpruefung/Teil*.lean` (only `propext`/`Classical.choice`/`Quot.sound`, no `sorry`) and checked
with the layout tool and the textual source -> IR -> assembly programs of `stage0/proben-ir`.

Forms that now compile with a connected generic theorem (`lowE_ok` case, `lowE_top`, equation lemma):

- `strGet` of a string of capacity `n >= 2` with an index range inside `[0, n)`: the byte word
  `d + 1 + i` of the complete span through `selectFrameSpan` (`strGet_ok`, `strBytes_word`).
- `strWeit m` widening (`n >= 2`, `n <= m`): the zero padding words are appended with `constWords`
  (`strWeit_ok`: the widened encoding is the old encoding followed by the zero words).
- `arrSet` of an array with more than one element (`arrSetL`, `arrSet_ok`): array, element and index are
  evaluated in consecutive spans; `storeFrameSpan` computes the element's frame address and stores the complete
  element span (`Frame/Store.lean`: `storeFramePointerSpan_run` has the exact footprint scratch word plus
  target span, `storeFrameSpan_ok`, `elementEncoding_get`, `wordsAt_arrSet`). No surface syntax reaches
  `arrSet` yet (the front end has no array-element update), so the textual regression cannot exercise it; the
  model probe `Aggregat/Proben` accepts it.
- `strEq` of two strings of capacity `>= 2` (`strEqLongL`, `strEqLong_ok`, `strEq_ok`): the length word and
  the first `min n m` byte words are XOR-ORed branch-free (`xorOrSpan`, `xorOrSpan_ok`); the accumulator
  is zero exactly when `strEqW` holds (`strEq_words_iff`, `foldl_or_xor_zero`). Textual program `str-eq-long`.

Measured at the final state of this step: the 235-module `Stage0` closure (root and `Stage0.Haupt`) is
rebuilt and fresh, `Nachpruefung.lean` audits 326 theorems on `propext`/`Classical.choice`/`Quot.sound` only
(including `strEq_ok`, `strEqLong_ok`, `storeFrameSpan_ok`, `storeFramePointerSpan_run`, `wordsAt_arrSet`,
`xorOrSpan_ok`, `strEq_words_iff`), the layout check passes, and 123 textual programs of `stage0/proben-ir`
compile to IR and execute (or are refused with the expected text) identically on the assembly runner
regenerated from `runner/`.

Already compiling before this step and unchanged: literals, variables, `arrCons`, `arrGet` (any length and
nesting), `strLen`, copies of every aggregate, the world read/write path of IR-06.

Interface that IR-02 (wide integer kernels) and IR-10 (calls, `var_value_ok`, `constWords`) build on:

- Width: `valueWords τ`, `integerWords lo hi` (little-endian two's-complement limbs), `contextWords`,
  `returnWords result reasons`, `variableOffset`. Encoding: `encodeWords L τ v` (`integerEncoding` for
  integers, `elementEncoding` for arrays, length word plus padded byte words for strings of capacity above one).
- Relations: `ValueAt L m fp base τ v := ValueValid L τ v ∧ WordsAt m fp base (encodeWords L τ v)`,
  `ValueOk` (execution, `Agree fp d K m m'`, `ValueAt` at `d`), `ResultAt`/`ResultOk`, `ReturnMirror`.
  A wide kernel establishes `ValueOk` for its result type with all scratch at slots `>= d`; no low-word view
  may stand for a multiword result (`ValueAt.word` only exists for `WordCompatible` types).
- Materialization and transport: `constWords words d` with `constWords_ok` (execution, `Agree fp d K`,
  `WordsAt m' fp d words`), `copyWords`/`copyValue_run`/`copyResult_run` (exact destination footprint),
  `var_value_ok x lower fits pre : ValueOk .. (ρ.get x)` (`Aggregat/KopieSatz.lean`), and the dynamic-pointer
  transports `loadPointerSpan_run`, `storePointerSpan_run` (world) and `storeFramePointerSpan_run` (frame).

Open (exact): `strCat` (a runtime-offset byte copy needs a loop or a dynamic-offset frame store of the second
operand), `strLt` on long strings (lexicographic scan with a final length comparison), `strEq` between a string
of capacity at most one and a long string, `strWeit` narrowing of long strings (`take`), `strGet` of a long
string with an index range wider than `[0, n)` (needs an in-range test before the dynamic selection), ordinary
records (canonical-model prerequisite), IR-08's `StatementCost`/`EarlyExit` migration to the new
copy/return/store ABI, and `getBytes`/`putBytes`/`shift` at the eight-byte limit (IR-02/IR-06).

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

**Bounded export implementation (2026-11-01).** A12, A15, A21 and A30 now have
source expansions and generic preservation laws on the actual compiler path.
`Parser/Elab/ExportMetadata.lean` restricts these additions to units whose cost,
scheduling, proof, reservation and type-wrapper duties have supported bindings.
The original-source duty result is carried by `UProg.exportGate`, with its
origin recorded by `Compiler.Compiled.metadata` and `compile_source_program`.
The actual new implication/Held/continuation branches and the represented
noninteger result context consume this gate; alias resolution and expanded
spec contracts cannot hide a guarded export. `Frontend/ExportCorrectness.lean`
connects these facts to `irBild_correct`. Existing lowering branches retain
their admission behavior. This is bounded case coverage, not closure of every
variant in these four catalogue rows. Invariant and spec-macro metadata,
declared costs, held-time promises and richer loop/header obligations remain
explicit refusals for the new paths. Local type annotations and constant type
wrappers are included in the original-source duty result.

A01 remains **open**: every source invariant has mandatory `cost` and `runs`
metadata and optional `by` provenance, while the current `UInv` stores only its
name, carriers and predicate. A new `breaking` export must not inherit that loss.
The source exporter continues to refuse `breaking`. No source invariant rule, checker meaning,
`Kern/` definition or goal statement has been changed. A02/A03 still require one
consistent resource-threading change across signatures, calls and every exit;
the current `Empty` mark carrier and fixed-resource sequence interfaces cannot
represent their flow.

**A — pure export, Stage0 ready within the stated domain.** No new model rule
is needed for these bounded constructions. The last column names existing IR
proofs and the still missing export obligations, not a completed source theorem.

| ID / source form | Exact refusal or absent export | Target canonical construction | Existing Stage0 proof; what export must preserve |
|---|---|---|---|
| A01 `breaking I { ... }` | `Uebersetze.lean:2538`, `stmt without G form: waive`, via `uAnwReihe` default | `Stmt.breaking` (S:610) | `lowS_ok` branch :146 recurses through `lowB_ok`. Resolve each invariant name (multiple names become nested scopes); retain body/exits and invariant restoration at return.  **Open after implementation audit:** mandatory invariant cost/runs/by duties have no source admission binding; the new-path metadata gate refuses `breaking`. No completion count. |
| A02 linear/ghost mark order, `consumes`/`allocs`, advances clause/statement | `Uebersetze.lean:1925/1952/2538`: `effect without G form`, `clause without G form`, `... step`; `UebersetzeAllg.lean:231/232/382` fixes empty signatures/`Marke := Empty` | `D.Marke/stufen`, `Signatur.konsumiert/produziert`, `Res.marke`, `nachSig`, `Stmt.advances` (S:185/89/287/306/637) | `lowS_ok` :151 and generic call/bind/return branches. Export one consistent mark namespace, exact flow/conformance/return resources, possession and `a+1 < stufen`; never produce an owner mark. Complete owner minting is C09. |
| A03 `retires m from s ...` | `Uebersetze.lean:1953`, `clause without G form`; raw `quits` tail has no body export | `Stmt.retires` (S:640), final resource list | `lowS_ok` :152. Resolve mark/stage/assumption, consume exactly that mark on the correct exits and retain assumption provenance. Runtime erasure is not erasure of the obligation. |
| A04 `table ... owner m` guard metadata, given valid initial ownership | `Uebersetze.lean:1172`, `table without G form`; `UebersetzeAllg.lean:382/387` exports no owners | `D.eigner`, `D.braucht` with `.inr (m,s)`, `darf` (S:190/192/301) | Generic `lowE_ok`/`lowS_ok` slot/thru/store proofs. Export shared/owner guards, uniqueness and `eigner_nie_erzeugt`. The current `own`→writable Bool conversion is insufficient; minter/borrow-return semantics are C09. |
| A05 scalar `table ... backed k` and backed accesses | `Uebersetze.lean:1172`, `table without G form`; runtime narrow bounds also :2860 | Static count plus explicit `Block.check`/`Block.narrow` and slots (S:699/703) | `blockCheck_case`, `lowB_ok`/`lowEnd_ok`. Preserve address-space count versus backed bound; prove the backing guard before each access, not just `i < count`. Preserve table identity through narrowing. |
| A06 table constants, `ops insert/remove/relabel`, `occupied f`, on represented scalar tables | `Uebersetze.lean:1132/1163/1165`, `table without G form` for non-invariant parts | Generated Fn/signatures/requires/calls/conditionals/stores (S header :31; ordinary `Stmt`/`Programm`) | `lowE_ok`/`lowS_ok`/`lowFun_spec` for generated functions. Generate freshness/reachability/leaf/occupancy contracts, exact effects and `by ops` writer discipline. No dedicated ops instruction is needed; a generic source generator proof is still missing. |
| A07 scalar dynamic arena ceiling, constant `grow ... by n else ...`, dynamic alloc over represented storage | `Uebersetze.lean:3992` (`arena with a dynamic ceiling without G form`), :2538 (`... grow`) | `DynForm`, `Block.dynGrowB/dynAlloc` in `Bausteine/Arena/ArenaDyn.lean:270/341/362`, reducing to check/narrow/stores | `lowE_ok`/`lowB_ok`/`blockCheck_case`; canonical `dynGrow_commit`/`dynAlloc_simuliert`. Export committed counter, `used <= committed <= M`, failure and effects. Physical provision/commit is B06/C08, not established by a counter update. |
| A08 scalar `free A[i]` and free-list allocation | `Uebersetze.lean:2538`, `stmt without G form: free`; no reuse export | `FreiForm`, `Block.freiVar` (`Arena/Struktur/Formen/ArenaAllocForm.lean:34`), `Block.freiNimm` (`Arena/Struktur/ArenaFrei.lean:386`) | Existing store/bind/check proofs; canonical `freiVar_ausfuehren`/`freiVar_lebt`, ownership `release_post`/`allocList_post` (`Arena/Ownership/Body/Forms.lean:195/125`). Attach the actual ownership judgment: consume origin, invalidate aliases, prevent double-free/use-after-free. Two emitted stores alone do not close this. |
| A09 arena lock carriers and table/arena group invariants | `Uebersetze.lean:1181` (`arena under a lock without G form`), :4338 (`invariant carrier without G form`) | `D.braucht/traeger`, `Programm.invariante`, `Stmt.locks` (S:190/206/813/605) | `locks_ok`, `lowS_ok`/`lowB_ok`. Preserve table-cell footprints, metadata guards, rank/U003 and restores. An invariant over a counter/global has the separate C05 boundary; do not disguise that global as a table carrier. |
| A10 already evaluable constant expressions in counts, bounds, lock ranks, payload ranges and initializers | `Uebersetze.lean:998/1018/1022/1033/1067/1212/1805/2853/2860/3816/3892/3915/4226` | Existing typed bounds, literal indices/counts, `D.rang`, `Expr.lit`, initial values | `lowE_ok` and existing initialization. Reuse checked scopes with exact sign/range/overflow/storage width. Only expressions already denoted by the canonical constant evaluator qualify; arbitrary compile-time control/contracts are C17.  **Batch 2 bounded export:** compound counts and ranks reuse exact singleton constant bounds; scalar initializers reuse `uKonstWert` at their declared range, including intermediate overflow checks. `checkConstants` retains original-source metadata duties before normalization. The current image still zero-fills world memory: `Frontend.checkInitializers` precisely refuses newly expanded nonzero scalar initializers before image emission, and this check is retained by `compile_source_program`. Zero initializers, counts and ranks execute; nonzero initializer G preservation is not counted as image completion. General constant-function evaluation remains C17. |
| A11 constant numeric state stages and transition through a table capability | `Uebersetze.lean:4306` (`state stage without G form`), :2513 (`transition through a pointer without G form`) | `D.erlaubt`, `Stmt.shift` (S:161/588) | `shift_ok` in `lowS_ok` :159. Preserve actual constant stage values, declared edge/range, table identity, write/guard checks and prestate failure. Do not replace numeric stages by ordinals. Edge contracts are C04. |
| A12 implication `p => q` | `Uebersetze.lean:1604`, computed `ensures clause without G form` default | `Expr.impl = or (not p) q` (Z:139) | `lowE_ok` Boolean branches. Preserve predicate/binder scope, footprint and old/result legality, including generated contracts/invariants.  **Bounded export connected:** `implication_export/lower/meaning/scope`, original `old(global)` restoration, and character-pinned source witness. Unsupported metadata-bearing invariant/spec contexts remain refused. |
| A13 domain membership, `a reaches b via f`, chain membership | `Uebersetze.lean:1604/1490`, predicate/compare-side defaults | `Expr.member/chain` (Z:156/169), `reaches` (S:507), `existsSlots` | `reachesL_ok` and quantifier branches in `lowE_ok` (`Ausdruck/Satz.lean:465/468/471`). Preserve guarded table, option-self edge type, bounded-chain meaning and index identities.  **Batch 2 bounded export:** slot membership for integer literals, parameters and checked named constants (including false negative/out-of-range values), explicit reach and single-child ancestor/descendant membership preserve table identity, the actual optional-self field and its guard (`reach_sound`, `member_meaning`, `member_footprint`), even for false membership. Numeric membership transports wide operands through the full ABI; equal-sized foreign nominal indices remain refused. Chain source arguments are field names, whereas canonical `Expr.chain` takes index endpoints; this batch refuses that mismatch explicitly rather than treating fields as endpoints. |
| A14 finite unvisited traversal/quantification over descendants, ancestors, queue, explicit scheduler tables and represented fixed-array index domains | `Uebersetze.lean:1570` (`quantifier domain without G form`), :3173/3174 (`traverse of/domain without G form`) | `Expr.descendants/ancestors/queue` (Z:159/164/173), quantifiers, filtered `Stmt.traverse` (S:611) | `lowE_ok` reach/quantifier branches, `traverse_case` in `lowS_ok`. Derive declared edges/carrier and element indices, filter, binder scope, invariant and leave/next. Use existing arrGet for represented elements. Record fields/mappings are C01; consuming traversal is C11.  **Batch 2 bounded export:** one declared self-child edge lowers to finite filtered quantifiers/traversal with an outer seed, shadow-safe binder, outer invariant and unchanged exits. Fixed lexical arrays use one private fieldless carrier per exact declared length; `elems of` binds an INDEX (LANGUAGE section 6), and ordinary `arrGet` transports the complete element through IR-03. Empty predicates are still checked. Queue records, branching trees, consuming/raw-header duties, implicit thread domains and stateful array domains without an explicit binding remain refused. Array-valued call arguments retain the existing source-call refusal; explicit scheduler tables use ordinary slots. |
| A15 ordinary `Held(L)` predicates after resource admission | `Uebersetze.lean:1604`; special `requires Held` collection already exists | Fact `Res.held L in Λ` (S:288/301), checked reification to `Expr.tru` | `lowE_ok` true branch. Prove possession in the current Λ, never accept by spelling; retain lock signature/floor. Shared witnesses depend on C10.  **Bounded export connected:** `lowHeld`, `held_lower/meaning`, actual resource possession and `HeldIn`; ordinary locks without an unbound held-time promise. Shared and metadata-bearing variants remain refused. |
| A16 string equality/order with both maxima <=1 byte | `Uebersetze.lean:1541` comparison dispatch, :1490 default; `UebersetzeAllg.lean:1189` (`aggregate as a number`) | `Expr.strEq/strLt` (S:531/533), Boolean combinations | `strCompare_ok` in `lowE_ok` (`Ausdruck/Satz.lean:66/69`). Preserve byte/length order and maximum bounds. Longer strings are B02.  **Batch 2 guarded export:** all six comparisons reach the canonical string constructors in the generic lowerer. `strings_lower` and `strings_meaning` record exact byte/length semantics for arbitrary represented maxima; the source regression exercises all six short-string operators. The comparison consumes the original-source duty gate; declared-cost metadata without its binding remains a refusal. No scalar ABI path or width-one refusal was added. |
| A17 same-region reference equality/inequality | Numeric comparison path `Uebersetze.lean:1541`; `UebersetzeAllg.lean:1189` / `zahlVon` refuses the nonnumeric side; body values :1651 say `reference as a number` | `Expr.refEq` (S:510), `Expr.not` | `refEq_ok` in `lowE_ok` :40. Retain region identity and valid origins; equality grants no address arithmetic. Provider realization remains B04/B06/C08.  **Batch 2 typed bridge only:** reference variables and same-region equality/inequality now use their declared reference type and the original-source gate, with generic `references_lower`/`references_meaning` and genuine typed-variable witnesses. Provider/origin realization remains C08 and is explicitly refused in the source regression; A17 is not counted as a completed source package. |
| A18 one-word context type adapters: Bool/option elements, normal table capabilities as values/results, scalar open-table fields | `Uebersetze.lean:1023/1034/1806/1171`: type/field/result/open-table non-number refusals | Existing Ty and `Expr.var/ptrOf/slot/slotRef`, binds/results (S:422/438/512/654/722) | Scalar `lowE_ok`/`lowS_ok`/`lowB_ok`/`lowEnd_ok`. Carry the complete kind/type through field/parameter/result paths; a capability is a table identity. Provider creation/transport remains B04/B06/C08; wide values B02; records/spaces C01/C12. |
| A19 mutable scalar options/tags/indices/capabilities/function pointers and call results | `Uebersetze.lean:2893/2961/2981/3026` (`let mut ...`), :2424 (`assignment to a pointer or an index`); `UebersetzeAllg2.lean:1168` (`assignment to a non-number variable`) | `Block.bind`, generic `Stmt.assignVar` (S:654/584), call bind | `lowS_ok` :63 and `lowB_ok` bind/call cases, within `wordTy`. Preserve declared mutable type/range, lexical scope, reference/mark provenance. This does not permit owning-value copies. Aggregate mutation is B02. |
| A20 matching binding annotations, scalar noninteger call results and scalar foreign function addresses | `Uebersetze.lean:2980/3004/3474/3513/3064`; `address of a foreign fn without G form`; `uWertArt` omits option/tag results | `Block/Endblock.bindCall/Ind/Else` (S:655/658/661/731/736/774) and typed bind/narrow; checked ordinary-function thunk for a foreign address | Existing `lowB_ok`/`lowEnd_ok`, `fnref_ok` and wrapper `lowFun_spec`. Prove thunk signature/call behavior with the actual gate; nontrivial foreign contracts retain C08. Check actual type, not only numeric range; retain reason context, conformance, continuation resources and alloc failure. Wide/gate results are B02/B04. |
| A21 internal let-else inside an error continuation | `UebersetzeAllg3.lean:412/969`, stale `Endblock lacks bindCallElse` | **Existing** `Endblock.bindCallElse` (S:736), execEnd at T2:375 | `lowEnd:432`, `lowEnd_ok:501`. Repair continuation parsing/scopes and reason/callee resources. No new constructor. The :412 branch is the context-preserving `lowSeqL` mode; bind-capable `lowSeq` already handles this at :438.  **Bounded export connected:** `nested_else_lower/meaning`, typed `Endblock.bindCallElse` on the real continuation, source witness, and exact reason/callee contexts. Ordinary functions in the metadata domain only. |
| A22 foreign calls/bindings and fallible numeric foreign calls in error continuations | `UebersetzeAllg3.lean:857/859/966`, `foreign call ... no G form here` / unfinished nested let-else | `Endblock.cons (Stmt.axiomCall ...)`, `bindAxiom`, `bindAxiomElse` (S:616/743/751) | `lowS_ok:340`, `lowEnd_ok:506/510`. Retain effects, gate/hardware failure and reason decoding. The unfinished branch must parse the real error body, not an empty list. Noninteger fallible results are B04. |
| A23 fixed scalar arena alloc at function top level / in an Endblock | `UebersetzeAllg3.lean:957/1251`, `Endblock lacks arenaAlloc` | Existing `Endblock.narrow/bind/cons` (S:727/779), same stores/bump as `Block.arenaAlloc` (`Arena/ArenaZucker.lean:203`) | `lowEnd_ok` narrow/bind/store branches. Define/prove this sugar; retain failure continuation, store/bump order, bounds and ownership. A convenience definition is absent, not an essential core constructor. No-else alloc is C11. |
| A24 declared check's linear Duty and producing/consuming **ordinary function** gates | `Uebersetze.lean:4039`, `item without G form`; mark/signature gap in A02 | `Res.marke`, signature flow, `nachSig`, `RufPasst` (S:89/287/306/345) | Generic call/bind/return proofs. Generate/check exact Duty flow and gate/checker functions; retain can-fail/floor/probe obligations. `Block.check` is a different construct. Full measurement/admission and foreign gate contracts remain C16/C08. |
| A25 format views/checks with each integer access <=8 bytes | `Uebersetze.lean:4039`, `item without G form`; decorated fields :1117 | Count-one view/table, `getBytes`, `bitfeld/embeds` (Z:276/288), `putBytes`, `Block.check` (S:468/580/703) | `readBytesL_ok`, `putBytes_ok`, `blockCheck_case`. Generate/prove layout, endian conversion, offsets, reserved bits, where/range and carrier bounds. `FormatRoundtrip.roundtrip` is not that bridge; @version provides no migration reader. Wider accesses B03. |
| A26 ordinary scalar accumulators, all max/min/add/or/and operators | `Uebersetze.lean:4039`, `item without G form` | Global + generated stores/conditionals/arithmetic; `Stmt.mergeMax/mergeAdd` (Z:206/210) | `lowE_ok`/`lowS_ok`, existing initialization. Preserve neutral value/operator/range (especially add), guard/write effects and generated contracts. Concurrent per-core/RMW claims are not supplied by a plain store; C15. |
| A27 walk's fixed-level traversal projection over modelled table nodes | `Uebersetze.lean:4039`, `item without G form`; mappings uses :1570/3174 | `Stmt.walk2` (Z:306), repeated traversal and filtered down/leaf tests | `traverse_case`, `lowS_ok`/`lowB_ok`. Prove source-derived visitation/mapping and invariant/exit correspondence; `walk_hits_mapping` alone does not. Full generated mapping records are C01; wide transport B02. |
| A28 scalar noninteger constants (Bool, option/tag, <=1-byte string) | Collectors omit them; uses reach `Uebersetze.lean:1453` (`name unknown`) / `UebersetzeAllg.lean:1351` (`constant without G form`) | Typed `Expr.tru/fls/none/some/case/why/strLit` | Existing `lowE_ok` branches. Preserve constant type/identity, checked literal/payload interpretation; never substitute zero. Wide values B02, general evaluation C17. |
| A29 float literals, conversion, narrowing and comparison in the finite IEEE kernel model | `Uebersetze.lean:1023/1806/1657/1663` type/result/value defaults; bare float names also reach :822 (`type unknown`) | `Ty.fl`, `Block.floatLit/Of/Narrow`, `Expr.fllt/flle` (S:488/712/714/718) | Actual `lowB_ok` :445/449/453 and `lowE_ok` :140/144 branches. Export rational bounds, finite/rounded/failure meaning, operand order and binders; retain Stop107. Arithmetic is B01. |
| A30 slot quantifiers beside a represented noninteger scalar result | `UebersetzeAllg.lean:1170`, `quantifier beside a result of this type without G form` | `forallSlots/existsSlots` with actual result `ErgCtx` (S:500/502/803) | `lowE_ok` quantifier proofs. Extend `ergAlsParam`, preserving result type/position under every binder. A tag/option must not become an Int.  **Bounded export connected:** `resultKind`, `ergAlsParam`, `result_scope` and a source witness preserve the actual option/tag/reason type and declaration identity under the binder. Existing IR representation and metadata gates still apply; binding an option-returning call is still refused by the existing call profile (`export-result-option-call-refused`), while the double-binder parameter regression uses a reason result. |
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
`Nebenlaeufigkeit/Sperren/Ruhe/MitRuhe*` and `Zielsatz/Einbettung/Syntax`. Extend the
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
   `Nebenlaeufigkeit/Sperren/Ruhe/MitRuhe*`, `Zielsatz/Einbettung/Syntax`,
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

### Model extension design: C06, C07, C08 (2026-11-01)

Design baseline: `a1dad6c92`; static source inspection only, no Lean edits or
builds. **New** marks proposed definitions, not existing declarations. Kernel
paths below are relative to `grammatik/Grammatik/`. This is an implementation
handoff, not closure of catalogue cells. C03's `ReasonSpec`, `reasonTy`, optional
channels and `RawAnswer` are design dependencies, not implemented interfaces in
this checkout. Use that migration, not a second reason encoding.

**Architecture.** Keep `Signatur`/`SigPasst` structural and put typed predicates
beside `Programm.requires/ensures`, after `Expr` exists: putting expressions in
`Signatur` would introduce the cycle `Deklaration → Signatur → Expr → Deklaration`.
Use one **new** `CallContract D S` for pointer and foreign interfaces, with
`pre : Expr D S.params (Signatur.anfang D S) .bool` and
`post : Expr D (ErgCtx S.params S.erg) (Vertrag.vonSig D S).ende .bool`.
Move the existing `ErgCtx` definition before this structure; its meaning stays.
The contract is a normal-return contract with original arguments and entry-world
`old`, just as `EnsAmRueck`; reason exits retain owed invariants and resources,
not an invented normal `result`. Existing concrete function contracts remain
intact. A shared evaluation/locality helper serves all three contract positions.

Extend the existing sequential body-duty judgments with **new**
`CallSitePflicht`: a proof judgment on execution prefixes, recording, at each
indirect/foreign call, the actual operand world, evaluated arguments and its
interface precondition. Its rules follow the existing `execStmt/execBlock/execEnd`
and `execEndH` derivations, including both continuations, loops and abrupt exits;
no second evaluator. Quantify over the same budgets, arbitrary conforming
handlers, lock havoc and atomic rely as `KoerperGutS/KoerperGutSA`. Prove prefix
transport to G/GX by the existing recorded-world replay, rather than assuming a
predicate over reachable machines in the user's premise. This adds caller duty
without passing `Programm` into the pure expression evaluator or replacing the
actual callee by an interface stub. Logical implications belong in (b), never an
unchecked `Bool` or `decide` over arbitrary predicates.

Every new constructor goes at the **end** of its inductive, including `UStmt`,
`GRest`, `RufSchrittG` and any auxiliary proof judgment. Changing arguments of an
existing constructor migrates its clients in one batch; no legacy adapters.

| Package | Core change | Spec impact | Engineering days |
|---|---|---|---|
| C06 | Typed pointer contracts, interface caller duty and universal target refinement O43 | **Yes:** (b) adds interface duty/refinement; concrete target contracts remain in `VertragAmOrtG` | 7–12 |
| C07 | Indirect value/void calls with exact reason descriptors and terminating else continuations | **Yes:** admitted runs/duties include indirect reason exits; existing conclusions retained | 6–10 after C03/C06 |
| C08 | Foreign signatures/contracts, proved software bindings, resource flow, provider realization and fallible void | **Yes:** separate software obligations in (b) from named hardware in (c); strengthen provider bridge | 16–27: contracts/boundary 7–11, resources/void 3–5, provider/IR bridge 6–11 |

Ranges include generic proofs, witnesses, export, GabbroV and connected Stage-0
work, not measured build times. Total 29–49 days for one implementation lane;
C03's raw-answer/channel migration, IR-03's full value-span ABI and C12's
unrepresented region capabilities are counted in their own packages. Critical path: typed contract replay and software/oracle
boundary, C03 channels, provider correspondence to actual memory. No extra
backend, source interpreter, OS model or privileged-code implementation is part
of this design.

**C06 — contracts on function-pointer types.**

| Layer | Implementable change |
|---|---|
| Kern and conformance | Add **new** `Programm.ptrVertrag : ∀ n, CallContract D (D.sigNr n)`. Keep `Val (.fnptr n) = {f // D.passt f n = true}`, `Deklaration.passt_ok`, `SigPasst.params/erg/gruende`, effects inclusion, mark equality, lock inclusion/extra-lock floor and `RufPasst.vonPasst` (`Syntax/Syntax`, `Syntax/Satz/T1`). Add **new** `PtrVerfeinert P`: for **every** `f,n` with `D.passt f n = true`, every entry world `s0`, arguments `ρ` and normal return `s1,v`, (1) interface pre implies `ReqAmEintritt P f s0 (umsig hf ρ)`; (2) interface pre and `EnsAmRueck P f s0 s1 (umsig hf ρ) v` imply interface post after transporting `v` by `SigPasst.erg`. This is contravariant requires/covariant ensures, not equality of predicate text. Quantify over actual two-world values, not just the body result in one fixture. No implication from a reason exit to normal ensures. |
| Target admission | `Parser/Elab/UebersetzeAllg.passtAt:296` currently admits every structural match via `sigPasstB`; it cannot decide O43. Retain structural soundness and add a finite, source-derived candidate-pair table with proof obligations for every positive pair. The table is an untrusted candidate until `PtrVerfeinert` is proved; it cannot acquire authority from an exporter success bit. Address-taking, assignment, parameters/results, stored callbacks and `einpassen`/`O.zeiger` all use the same `D.passt`; every admitted target, including foreign-address thunks, needs its refinement proof. Generate pairs from all potential conversions/binding images, never observed executions or one selected target; missing proof refuses the conversion. Structural typing remains: any function with proved refinement may fit, with no nominal function whitelist. For abstract `D.Fn`, the theorem remains universally quantified; complete finite `fs` enumerations are only the checker/export implementation. |
| Caller duty and G | `CallSitePflicht` for `Stmt.callInd` and both `bindCallInd` positions requires the type's pre in the operand-entry world. From it, `PtrVerfeinert` and `RufPasst.vonPasst`, derive the existing concrete caller duty of `torRuf`/`KoerperGut`, then the concrete `ReqAmEintritt` at the actual push. `RufMaschineG/T2.dannBindCallInd` and the statement/end variants continue to evaluate `p` once, apply `umsig`, push that function's real body and log its `eintritt`; pops retain its actual `rueck/grund`. Use the concrete normal ensures plus refinement to expose the interface post to the continuation. Keep every selected target's own requires/ensures checks in `rufAt` and its own `VertragAmOrtG` entries; do not replace them with the weaker type post. No new execution constructor is needed for C06. |
| Akzeptiert and replay | Extend `fussWB`, contract dependency extraction and `AtomarAkzeptiert.vertragsFreiB` to pointer pre/post footprints with their precise signature entry/exit guards. Contract reads may include protected read-only carriers, not only writes; a shared-atomic read cannot be hidden in a pointer predicate. Check candidate table bounds, structural `SigPasst`, ghost use and complete indirect call-graph closure (`AbgK`/`reachB`); refinement implications remain user proof in `LogikPflicht/LogikPflichtA`. Add pre/post locality lemmas with the same old-state discipline as `ReqAmEintritt/EnsAmRueck`, then use them in `ZielOrtAx`, `ZielOrtRahmen`, `ZielOrtSperre` and atomic replay. Structural acceptance of a candidate does not discharge its O43 obligation in (b). |
| Export coordinates | `Uebersetze.uZeigerVertrag:4599` currently only accepts literal true clauses; `uZeigerSig:4608`, `elabZeigerTyp:4657` currently discard `needs/gives` and set reasons to zero. Preserve and lower all predicates in `UProg.ptrs`, using named/unnamed parameter indices, result context and `lowEns`; build `ptrVertrag` in `UebersetzeAllg3.progOfFn:1540`/`lowerAllg:1595`, including source-to-predicate correspondence and O43 duties. `UebersetzeAllg2.lowCallIndL:1310` and Allg3's :510/:886/:1178 binding paths must carry those duties. `crates/gabbro-check/src/namen.rs::fnptr_traegt_seinen_vertrag`, `m1.rs::fnptr_passt`, `pflichten.rs` and `tests/zeigervertrag.rs` currently enforce N589/N590 and explicitly identify O43: replace only the refusal whose proof now exists; never infer an ensures or turn it into a hint. Held/floor/effect refusals lacking their own connected check remain. |
| Stage 0 | Reuse `Senke/Anweisung.lowInd`, `indC`, `callInd`/`bindCallInd`, `Anweisung/Fnptr.lowInd_ok`, `indStmt_ok`, `indBind_ok` and `Faelle/Fnptr`. Extend their hypotheses/contract instantiations to arbitrary admitted targets with actual entry snapshots and complete argument/result spans; thread the logical interface pre/post through function/image correctness, retaining each callee's emitted concrete contract code. C06's interface proof adds no separate runtime checker or extra dispatch. IR-10 owns old snapshots; IR-03 owns frame/result spans. A proved scalar `indBind_ok` alone does not close the generic source path. |

A type with no predicate clauses has pre/post `true`; this does **not** permit
silently calling a target whose pre is stronger. A target's private post may be
stronger than the type post and remains proved/logged for that target. Two
same-shape functions with different contracts are an essential witness, not an
excuse to collapse their contracts by signature number.

**C07 — fallible indirect calls.**

| Layer | Implementable change |
|---|---|
| Channel/type | Adopt C03's `Signatur.gruende : Option ReasonSpec`, `reasonTy`, `SigPasst.gruende` equality and generalized outcomes. Preserve descriptor identity/openness and full u128 codes. An open channel with zero known cases is still a channel. Keep `Stmt.callInd` and nonfallible `Block/Endblock.bindCallInd` restricted to `gruende = none`; never discard a reason via the present `keinGrundSig` path. No separate pointer-only error type. |
| Syntax and resources | Append **new** `Block.bindCallIndElse` and `Endblock.bindCallIndElse`: `p : Expr D Γ Λ (.fnptr n)`, signature arguments, `hp : RufPasst D V (D.sigNr n) Λ`, `hr : (D.sigNr n).gruende = some r`, `err : Endblock D V l (reasonTy (some r) :: Γ) Λc`, and a success continuation under `Λc := nachSig D (D.sigNr n) Λ`. For a success result `e := (D.sigNr n).erg`, its context is `ErgCtx Γ e`; the block continuation ends in `Λ'`, the end-block continuation must terminate. Use arbitrary `e`, not `he : e = some τ`, so void success binds no value. Append **new** `Stmt.callIndElse` with the same arguments/`hp`/`hr`, `err` and result resource `Λc`; success discards only the normal value and continues in Γ. Implement it as checked sugar over `Block.bindCallIndElse` with an empty success tail and scope projection; no duplicate dispatch semantics. Existing `Stmt.callInd` is unchanged except C03's channel premise. |
| Sequential and G | Extend `execBlock/execEnd` in `Semantik/Semantik/T2` and havoc/rely variants: record `p.orte ++ args.orte`, evaluate once, call `R f` with `umsig hf`; normal value is transported by `SigPasst.erg` into `ergEnv`, reason by `SigPasst.gruende` into the exact `err` binder. Both use `nachSig`; propagate logic/hardware stops unchanged. Generalize `GRest.wartetSonst` (`Logik/Ruf/Maschine/RufMaschineG/T1`) to optional result and C03 descriptor, sharing direct and indirect continuations; migrate direct `bindCallElse` to the same optional-result interface rather than adding a second wait stack. Append push rules for new block/end forms at the end of `RufSchrittG`, patterned on `dannBindCallInd` and `dannBindCallElse`; save selected `f`, entry world/arguments and interface resource equality. Reuse generalized value/reason pop rules, including `retWhy` inside `cons`, without re-evaluating `p`. Statement sugar must retain loop/end continuation and both return paths. |
| Duty/acceptance | C06's pre and universal refinement apply before either outcome. Normal returns expose type post; errors expose reason identity plus owed invariants and `Λc`, not type normal ensures. Extend `vOk/gOk`, fragment checks, `ants`, footprints, masks, `ueberBoden`, terminal/progress predicates and `AbgK` through **both** continuations and every admitted target. `D.eigner_nie_erzeugt` still prohibits minting an owner merely through `produziert`. Error paths cannot restore consumed marks, invent success-only marks or fall off. Preserve locks on reason exits exactly as on ordinary `bindCallElse`. |
| Export coordinates | Remove the `uZeigerSig:4617` reason-channel refusal only after descriptor parsing/lowering; preserve `FnSig.fehler` through `elabZeigerTyp`, `UFn/UFnKopf`, `mkSig` and `sigPasstB`. `uAnw1:2534`, `uBindWert:3009` currently require let-else; add appended `UStmt` forms for indirect else, resolving the pointer variable rather than looking up a direct target. Extend `uAnwReihe`, `uEndeKanal`, `lowZeigerN/lowRufKopfN`, `UebersetzeAllg3` block/end/final binding paths. Type-check annotation/result/channel and preserve shadowing, original arguments, error binder and post-call resource scope. No-channel calls keep existing export. |
| Stage 0 | `Anweisung.lowInd` currently rejects nonzero reasons. Generalize its call assembly independently of outcome dispatch, then use the same checked status/error continuation mechanism as direct `bindCallElse` (`elseC`, `Faelle/CallElse`) for new indirect constructors. Use C03/IR-03's complete return and reason spans with status outside both; void has zero value words and no synthetic source number. Prove new normal/reason versions of `execBlock_ind_eq/execEnd_ind_eq`, `indAntwort/indBind_ok`, and statement-sugar simulation, preserving saved pointer, caller parameters/snapshots, reserved scratch, loop targets and resources. Connect through `lowS_ok/lowB_ok/lowEnd_ok`, function and image theorems, including a runtime-selected target that returns an unknown open reason. |

**C08 — foreign contracts, resources, providers and void.**

| Layer | Implementable change |
|---|---|
| Canonical signature/contract | Replace independent foreign shape fields with **new** `Deklaration.asignatur : Ax → Signatur Tab Glob Lock Marke`; keep `aparams/aerg/aschreibt/agschreibt/agruende` as the single canonical projections, not duplicated stored state. Add **new** `Programm.axVertrag : ∀ a, CallContract D (D.asignatur a)`, with exact argument/result/old contexts. Generalize the existing `AxEns`/`AxVertragO` in `Logik/Vertraege/AxiomVertrag`: its current `Q a σ' v` has neither entry world nor arguments and only sees the normal-result decoder. The new contract relation uses pre-world, original arguments, post-world and C03's decoded normal-or-reason outcome; normal post applies only on normal return. Replace the restricted `AxEnsLokal` rule (only write carriers) with explicit guarded pre/post footprints and two-world replay. Migrate `Einheit.Q` to this canonical relation, derived from the exported contract, not independently supplied as an unrelated stronger predicate. |
| Caller/resource rules | Replace the duplicated `hw/hg/hd/hgd` call premises by `RufPasst D V (D.asignatur a) Λ`; nonfallible `Stmt.axiomCall` requires `aerg = none` **and** `agruende = none`, and exits in `nachSig D (D.asignatur a) Λ`. Add the no-channel premise to ordinary `bindAxiom`. Generalize `Block/Endblock.bindAxiomElse` success to `ErgCtx Γ (D.aerg a)`, error to `reasonTy (D.agruende a) :: Γ`, both under the same `nachSig`; a `none` result has `ErgVal none = Unit` (`Semantik/T1:353`) and adds no local. Generalize `bindAxiom` consistently to optional result to avoid a separate void API. Append **new** `Stmt.axiomCallElse` as scope-erasing sugar over the generalized binder, as for C07. Include foreign signatures in owner-never-produced, floor, held-set, mask and linear-flow checks. Foreign effects must realize consumes/produces/held permissions at both exits; arbitrary `locks` effects need proved acquire/release traces and floor behavior, not a fabricated no-lock frame. Unmodeled masks/publishes/other effects remain refused until their generic trace rule exists. |
| Premise provenance | Add **new** declaration metadata `AxOrigin`: `software` or `hardware (a : D.Annahme)`. It is not inferred from the word `extern`, `syscall`, `axiom` or an ABI number. Add **new** `ForeignPflicht E O` in `NutzerPflicht/NutzerPflichtA`, hence make that duty explicitly parameterized by the actual oracle/binding realization `O`. For every software item its proved implementation/binding establishes frame, held-lock/trace discipline, result/reason decoding, postcondition under pre, resource transfer and provider facts. The body's own `CallSitePflicht` establishes pre at every call. Sequential logic still quantifies over **all** answers satisfying the declared summaries, not just this O. Narrow `HardwareAnnahmen`'s foreign part to explicitly named hardware-origin items; keep genuine register/weak-memory hardware conditions. Re-establish combined per-call `GutO`/contract facts from the two groups, then feed the existing replay proofs. Conditional contracts are used only at a site whose pre is proved; localize any proof currently demanding unconditional `AxVertragO` accordingly. No normalization to an out-of-range raw answer: void and full-range types have no such sentinel. |
| Akzeptiert | Add **new** `schnittstellenB` with a proved iff to a corresponding **new** field of `AkzeptiertSpec`/`AkzeptiertSpecX`: all referenced pointer/foreign signatures and origin names resolve, parameter/result/channel descriptors agree with calls, resource lists have valid stages/multiplicities, foreign-produced marks satisfy owner-never-produced, and contract/boundary-clause reads satisfy guard/ghost/atomic restrictions. Enumerate signatures/origins/clauses from the finite unit; do not infer missing contracts from `fs` alone. Fold the component into `Akzeptiert` and `AkzeptiertX`, and extend their soundness proofs. Reuse existing `stufenB`, `fussWB`, `maskenB`, `antwortenB` for their semantic obligations, including both error branches. `PtrVerfeinert`, software implementation proofs and grant-history realization remain in (b), not this Bool. |
| Existing bridge and required closure | Reuse `Logik/Ruf/FremdRuf/T2.AxPre`, `AufruferPflicht`, `AxVertragOP` and T3's `RufFolgePflicht` to state the pre split, but do not cite `hardware_aus_vertragP` as machine-level closure: its own CUTS require `hraus`, exclude void, and only prove oracle/sequence coincidence. Extend actual `RufSchrittG` axiom/binder rules and their recorded `AxEintrag` replay with precondition-at-call and outcome-sensitive post/resource facts. Generalize `Kern/Semantik/Syscall/SyscallPaarung.KernelEintragG`, `UserSyscallG`, `PaarGut` and `syscall_paarung` to typed/void/open outcomes and resource/extent evidence; tie the proved dispatch/binding implementation to the same `O.wirkt`. An OS implementation proof can discharge this **user** obligation; an unproved OS promise cannot enter (c) under a different name. The current theorem already separates program ABI data from hardware and supplies a reusable pairing shape, not a complete source export. |
| Provider realization | `D.anbieter_passt` proves only open-table/parameter/result shape. `Unbounded/GRefine.RegionRepr` and `allocate_refines` assume the candidate and installed contents; `GRegion.oK` accepts any K. Neither proves physical freshness. Build **new** `ProviderRealisiert` as the provider clause of `ForeignPflicht`, a relation on successful boundary transitions and a history of live grants: region/table identity, cell or extent, byte base/length/alignment/rights, initialized contents, provenance, and an injective mapping to the actual binding memory. Success introduces a grant absent from all live grants; all bytes are in the returned REGION and disjoint from every live grant and compiler frame/code/snapshot allocation. Failure introduces no grant; any other state/resource effect must satisfy the declared failure frame. Release/reuse needs the existing ownership ledger and no outstanding borrow; no new allocator or `int → ref` source form. Use `Schablonen/SchablonenOhneLibc.RegionVertrag/region_zugriff`, `Unbounded.Heap.Valid/allocate_refines` and the ownership interfaces as lemmas in that transition proof, not detached witnesses. Extend the region contract predicate vocabulary/export to retain freshness/disjointness/length clauses as checked semantic relations to this grant history; never lower them to `true`. |
| Provider history in G | Add **new** `BoundaryRecord D` (item, original arguments, entry/exit memories, decoded outcome and declared grant/release identity) and an append-only history field at the end of `RufMaschineG`; `RufStartG` starts from **new** `Einheit.grants0`, the source-declared initial inventory; extend `StartPflicht` to prove its provenance, disjoint realization and correspondence to initial capabilities, rather than assuming an empty external world. Each foreign step appends exactly its actual record; other steps preserve the field. A **new** `GrantInventory` is the deterministic fold of those records: success-grant inserts, declared release removes after ownership/borrow checks, reason return grants nothing. Extend `BoundaryClause` with the explicit release case for existing consumes/release declarations; no implicit collection on scope exit. `ProviderTreueG` relates that history to a single global inventory across all threads and to the binding realization, preventing per-thread freshness from admitting cross-thread aliases. This is ghost specification data, erased from emitted code, not a second executable heap. Lift its step preservation through GX, spawn, idle root and linking. Sequential `CallSitePflicht` carries the same inventory through boundary prefixes; its transport proof identifies it with this global history. |
| Typed boundary clauses | Add **new** `BoundaryClause D S`, a closed typed syntax attached to `CallContract` alongside Boolean pre/post: input extent, output extent, fresh/disjoint output grant and explicit release. Each selector identifies a parameter/result capability and its region/table (for an existing open provider: `aerg = some (.ref n)`, `tabNr n = some t`); bounds are typed nonnegative integer expressions over the original parameter context, with an explicit element/byte unit and checked layout conversion. Its meaning is a Prop over the entry/exit live-grant inventory and the selected capability, with fresh output requiring absence from the entry live set and disjointness from every entry live grant. Pre-clauses must hold at the call; output clauses apply only to success. Store these clauses in `UAx`/pointer metadata and prove exact lowering; add constructors only at the end. They cannot be encoded by `Expr.lit`, a synthesized address or an opaque arbitrary predicate supplied by Rust. For region capabilities whose identity/rights are not representable by current `.ref`/`.ptr` (the latter has unit values), the C12 space/capability model is a prerequisite; retain the full source clause and explicitly refuse that case until it joins, never assert a region length of a unit value. `m1.rs:1672/4490` already transports foreign `ensures n <= lenof(result)` into caller extent facts; bind those facts to these clauses and their user proof instead of treating the checker report as evidence. C06 refinement also preserves applicable input/output boundary clauses, contravariantly/covariantly, so a provider callback cannot drop freshness from its type. |
| Provider → addresses | Compose provider identity and extent facts with `Adressen/Bereich.ImBereich`, `axiomAntwortSonst_aussen`, `rufErreichbarGX_aussen` and `Adressen/Layout.zelle_im_bereich/zellen_getrennt`. Software foreign writes must **prove** their instance of `ImBereichO`; only true hardware behavior may remain a named premise. Keep the existing conditional address leg as well; do not hide an OS assumption in its antecedent. Logical open-region address spaces already separate different tables, but say nothing about two calls reissuing the same cell, or two physical grants aliasing. The new injective physical realization supplies those missing facts. Connect to IR-06's world memory and actual `WeltAt`; `Ty.ref` type checking or a raw positive address alone never authorizes a grant. Provision of dynamic arena pages must establish this bridge before a committed-counter update claims backing memory. OOM/success availability is the provider's user proof; declared failure is user control flow, and a bounded arena's capacity else remains distinct. |
| Export coordinates | Preserve clauses/effects in `Uebersetze.uRestFehler:4039` (`axiomT`), `uAxKlauseln:4116`, `uAxKopf:4135` and `elabGateKopf:4184`; remove the :4156 fallible-no-answer refusal only with generalized binder and decoder. Extend `UAx:658`/`UFnKopf`, `UProg`, `declOf`, `progOfFn/lowerAllg` with canonical signature, contracts, origin and proof-obligation identities; do not just export a typed answer. `elabGateKopf` must retain `sc.gate.pre/post/uses`, and the axiom's falsifier identifies hardware only after the origin decision below. Cover all block/end `bindAx/bindAxElse` paths and `axCall`, including no result and old snapshots; extend source preservation and GabbroV duty export. Refuse unresolvable clauses/resources rather than silently dropping them. |
| IR-11 gates | Keep `Stage0/Bindung.uniqueBinding` and explicit selected target/ABI; extend `Tor`, `TorB`, `rohW`, `torGut/fehlGut` and `Senke/Tor.chkC` to exact result/channel descriptors. Reuse `Anweisung/Tor.TorOK` as a binding/user-logic correspondence to `Kern.ans`; it is not a proof of source contracts, freshness, or the OS. Extend `torC_ok/torC0_ok`, `torBind_ok`, `FehlerLauf.torElse_ok`, buffer frame proofs and `Faelle/BlockFehler/EndFehler` with the actual success/failure memory, grant and resource relation. Void success decodes the ABI's declared status into unit, errors into the reason channel, and never range-checks an invented source integer. ABI success/error sets must be disjoint; preserve unknown open codes under the explicit decoder. Unsupported/unclassified raw answers are refused at binding validation; an unexpected software answer at execution is **new** `Logik.fremdAntwort a` (append in `Semantik/Semantik/T1.Logik`), excluded by `ForeignPflicht` and the existing no-logic-halt conclusion. Only a named hardware-origin decoder violation may retain `.hardware (.annahme a)`. Compose binding correspondence and `ForeignPflicht` through `lowS_ok/lowB_ok/lowEnd_ok`, `lowFun_spec` and the actual `Stage0/Haupt → IRBild` path. Generalized checks must cover multiword/reference answers using IR-03/06, not merely extend scalar `chkC`. |

**Goal proof closure and exact Spec changes.**

1. **`VertragAmOrtG`.** Preserve its concrete `eintritt/rueck` interpretation
   (`ZielOrt/Grundlage/ZielOrt/T1`) and prove C06 refinement at the selected
   target, both ways of C07's continuation, and C08 pre/post at actual foreign
   records. Extend `Logik/Vertraege/AxiomVertrag.VertragA`, `orakelAus_vertrag`,
   `axWelt_vertrag` to original arguments/entry state and outcome-specific
   frames. Replay pre/old/current footprints separately under held guards;
   `LogikPflichtA` must quantify over every unknown open reason and atomic answer.
   Restore `InvAmOrtG/InvAmGrundG`, lock/idle invariants and no-logic-halt on both
   exits; a foreign writer owes every affected carrier invariant. Contract
   locality is not automatically implied by the set of write effects.
2. **`FolgeG`.** `Logik/Fortschritt/Folge`'s `Φ.ind n` covers every `D.passt f n`;
   extend `fS/fB/fE`, `GRest.fR` and `FolgeBeweis` to indirect else and both
   branches, clearing the armed bit after indirect calls as before. Keep concrete
   `eintritt/rueck/grund` events; normal and reason pops cannot masquerade as each
   other. Foreign calls remain log-silent in this function-order theorem, as
   existing axiom calls are; their `AxEintrag`/access trace is separate. Ordering
   a syscall by name requires its ordinary checked function wrapper (and proof
   of that wrapper's real gate), not inventing foreign function-log events.
3. **Memory, resources and progress.** Extend `Syntax/Satz`, `Extraktion`,
   `Geist`, `Fehler`, `RahmenTreu.rufAt_treu`, G/GX/atomic replay, terminal/halt
   classification and costs through new forms. Restore `akzeptiert_iff`,
   `antwortenB_iff`, `vertragsFreiB_ok` and `akzeptiertSpecX_of`; in particular
   fallible void is inhabited success-or-reason, while `never` has no normal
   return. Preserve all trace guards, error effects, floors, masking, resource
   conservation and `speicherAdressen`. Include the new signatures/contracts and
   origin/grant relations in `MitRuhe*`, `Zielsatz/Einbettung` and linking.
   Re-establish `ZeitAb` with dispatch/error-arm costs; no separate cost project.
4. **Spec diff.** C06 adds interface pre/refinement to (b), C07 enlarges the
   outcome/duty domain consistently with C03. C08 changes the current header's
   explicit “hardware and foreign code” reading of (c), `HardwareAnnahmen` and
   `NutzerPflicht(A)`: software frame, contract, resource, extent and provider
   realization are proved in (b) against the actual binding, only named hardware
   remains in (c). Carry that O-dependence through `GabbroZiel`, SC, GX and linked
   statements and `bruecke_nutzer/bruecke_nutzerA`; no unproved software behavior
   can remain implicit in `GutO`, `AxVertragO`, `TorOK`, loader or layout premises.
   Add **new** `ProviderTreueG` to the goal for declared providers: each live grant
   is backed by the proved injective region realization, with ownership transfer
   compatible with its live-grant history. Prove it by boundary/machine-step
   induction and compose the physical correspondence in the IR theorem; do not
   claim `gabbro_ziel` itself describes final bytes. This is a strengthening plus
   premise-provenance correction, not merely representation. Document this in
   the Spec header, relevant plan and implementation commit; existing safety,
   contracts, budgets, order and NOT CLAIMED qualifications are not weakened.
5. Recompile `Zielsatz/Kern/Beweis.ziel_aus`,
   `Atomar/BeweisAtomar.gabbro_ziel`, `gabbro_ziel_gx`, `gabbro_ziel_sc_aus`
   and `gabbro_ziel_verbund` plus their witnesses. Audit **exactly** `propext`,
   `Classical.choice`, `Quot.sound`; no additional axiom, `sorry` or per-program
   substitute for a generic theorem. No package is complete before the exported
   accepted unit, connected source/IR/function/image proofs and pipeline compile.

**Witnesses and remaining refusal boundaries.** Every generic syntax theorem
gets a non-degenerate `_zeuge` with all premises jointly, then source-export,
`AkzeptiertX`, IR and assembly-runner witnesses of the same form.

| Package | Positive witnesses | Negative twins / refusal boundaries |
|---|---|---|
| C06 | Two runtime-selectable same-shape targets with distinct stronger posts/weaker pres; state-reading type pre and `old` post; callback through parameter/table/result and a proved foreign thunk; nonempty effects/mark flow | Stronger target pre, weaker target post, reversed implication, bad second target, forged image pointer, old/current mixup, hidden shared-atomic contract, unproved Held/floor/effect/refinement pair; preserve N589/N590 until the corresponding full path is proved |
| C07 | Both indirect value paths in Block/Endblock; statement and void success; dynamically selected error target; open channel with no known cases; unknown >64-bit reason forwarded through nested calls; consumed/produced marks and a held lock on both exits | Missing else, falling-off error block, wrong nominal channel, zero-known-open treated as none, re-evaluated target, stale/error payload span, normal post assumed on error, early return skipping lock release, different branch inventory |
| C08 | Argument/old/result-dependent extern and named hardware axiom; proved syscall pairing with real buffer write; fallible Bool/reference/void; two fresh grants, preserved first grant, release/reuse with no borrower; provider availability as user proof; no-channel void and never | Missing software proof, hardware label on OS behavior, false pre, return outside declared decoder, malformed open reason/tree, unproved resource effect, owner minted by produces, failure treated as pure, repeated/overlapping/short/misaligned grant, raw int-to-region, read-only grant written, missing backing/availability, ambiguous/unbound gate |

Existing unsupported ABI widths/effects are explicit interim refusals, not a
reason to shrink the source theorem. ASM bodies, boot/privileged execution,
raw-address syntax and device-register forms stay outside this assignment.

**Owner questions — source meaning, with recommendations.**

- **C08 hardware classification:** does existing `axiom ... falsifier ...` always
  mean a hardware-origin operation, or may it declare a software service?
  Recommend classifying by the declared operation and named hardware assumption,
  never keyword alone: OS/provider/service contracts require user implementation
  proof even when spelled `axiom`. Reuse existing assumption references for true
  hardware; refuse ambiguous origin until resolved. This needs an explicit Spec
  and language explanation, not automatic renaming of all foreign items.
- **C07/C08 resource effects on errors:** are declared produces/consumes common
  to every returning exit, or success-only? Recommend the existing ordinary-call
  rule: one `nachSig` for normal and reason exits; no resource rollback on error.
  If the owner intends outcome-specific effects, extend the canonical signature
  with explicit per-outcome flow and migrate direct calls too before acceptance;
  do not introduce that meaning only for syscall/pointer calls.

Normal ensures applying only to normal returns, OS behavior as user logic,
region-only external memory and OOM as user logic are existing rules, not open
choices. No normal-result postcondition on reasons is proposed.

**Staging and rebuild impact.** One grammatik owner first adds typed interface
contracts/O43 and caller-duty replay with scalar no-channel witnesses (C06).
In a separate compiling boundary batch, introduce canonical foreign signatures,
software/hardware provenance and actual-machine pre/post replay (C08 foundation);
keep unproved software bindings refused. Join C03's descriptor/raw-answer batch,
then implement generalized optional-result continuations and indirect else
(C07 and C08 void/resources). Finally connect provider grant/region realization,
IR-11 buffers/gates and IR-03/06 full-span storage, followed by all source and
GabbroV bridges. Commit each building stage; do not activate an exporter branch
before its generic model and connected lowering proof are ready. Origin and
error-resource choices above must be resolved before enabling their source cases.

`Programm`/`Deklaration` changes rebuild nearly all grammar clients; new binders
add cases throughout mutual inductions, machine steps, converse/replay, contracts,
footprints, locks, costs, ownership, idle-root/link embeddings, witnesses and
parser/export. Stage 0 must rebuild call/return ABI, snapshots, gate decoders,
world/init/layout, mutual lowering, function/recursion/image correctness and
frontend/compiler provenance. Existing narrower adequacy CUTS such as
`Logik/Ruf/Adaequat/RufAdaequatRufG/T10` are not proofs of the new cases. Extend
only the generic bridge actually consumed by the pipeline and report remaining
cuts precisely. The implementation owner uses the authorized grammar memory
scope (fresh MemAvailable minus 2 GiB, swap zero), within the current two global
Lean slots; Stage-0 checks retain 5-GiB slot scopes. Require the full grammar
build, layout check, Lean guardian/standard-axiom audit and connected Stage-0
proof/runner checks for each accepted batch; remaining guardians at integration.
This design commit performs none of those builds and claims no new compiled case.

### Model extension design: C09, C10, C11, C18 (2026-11-01)

Design baseline: `7ccd14c9e`; static source inspection only, no Lean edits or
builds. Paths are relative to `grammatik/Grammatik/` unless prefixed otherwise.
**New** denotes proposed declarations, not existing Lean names. These packages
remain open until the generic source/export, G/GX, Stage-0 and image proofs are
connected and compiled. C08's software/provider boundary and C12's capability
representation are dependencies, not facilities already supplied by this tree.

**Architecture and non-negotiable boundary.** Extend the actual typed syntax,
`RufMaschineG` and its GX replay; do not add a parallel execution model. Reuse
`Res.marke`, the arena ownership ledger and structured continuations. Distinguish
static resource names in `Λ` from dynamic ownership/reader/generation records in
the machine: an epoch or handle obtained at run time cannot be a guessed static
`Nat` in an exported type. Use one identity-parameterized location/escrow mechanism
for marks, arena handles and observed versions; C09 adds spent-mint metadata,
not another incompatible notion of lending. Append every new constructor at the **end** of its
inductive, including resources, events, continuations, proof judgments and
exporter intermediates. No new admission branch defaults to true.

| Package | Core change | Spec impact | Engineering days |
|---|---|---|---|
| C09 | One-shot mint authority and stack-aware owner transfer/loan conservation | **Yes:** initial/minted owner provenance and lifetime become checked goal facts; signatures still cannot produce owners | 12–20 |
| C10 | Mode-aware shared locks; separate RCU observation, retirement, grace and reclaim resources | **Yes:** canonical concurrency domain grows; mode-aware invariant visibility and RCU lifetime facts, no race exemption | 30–50: RW 9–15, RCU 21–35 |
| C11 | Consuming loop with current-state selection/decrease; proof-duty narrowing; checked return cleanup | **Yes:** new control/duty cases and costs, same safety/conservation conclusions | 18–30: traversal 8–13, allocation 3–5, cleanup 7–12 |
| C18 | Checked static-array reset plus a proved page-return binding and live-range ownership | **Yes:** reset/provider lifetime and zero observations covered explicitly; no OS assumption | 14–24 |

Ranges cover generic proofs, witnesses, export and connected IR work in one
implementation lane: 74–124 engineering days, excluding C03/C08/C12 and their
shared ABI migration. They are estimates, not measured build times. Critical
path: resource conservation and return replay, then RW/GX integration, then RCU
publication/reclamation and provider realization. Share cleanup and lifetime
interfaces across packages instead of charging for independent implementations.

**C09 — owner mint, linear handoff and scoped borrow/return.**

Present boundary: `Kern/Syntax/Syntax.lean:203` forbids an owner in **every**
`Signatur.produziert`; `nachSig` erases consumed marks and appends produced ones.
`Ty`/`Val` in `Kern/Syntax/Typen` have no owner value, and environments can copy
ordinary values. `Marken.MarkenSchritt` in `Kern/Syntax/Marken` has an `erzeuge` rule that
explicitly excludes owners. `eigner_nachRuf_aus_anfang` and
`eigner_aus_leer_nie` in `Kern/Syntax/Typen` express the
present no-production boundary. Arena handles in `Bausteine/Arena/Ownership`
are a different resource: `State.lend/endLoan`, `borrow_result`, `factory_checked`
and `Ruhe.startOwn_arenen` do not mint `D.Marke` owners. Also,
`Nebenlaeufigkeit/Rennfreiheit/RennfreiVoll` explicitly records that owner-mark
ordering is not proved on G there; do not cite that theorem as this bridge.

| Layer | Implementable change |
|---|---|
| Kern resource interface | Keep `D.eigner_nie_erzeugt` for **ordinary production**, including pointer signatures and foreign effects. Add **new** `OwnerFlow` beside `Signatur`: exact owner inputs, moved normal/reason outputs and call-scoped loans, each referring to an existing `(m,stage)`; no output without a corresponding input. Define **new** `nachOwner` as transfer of those identities, composed with ordinary `nachSig`, never as owner `produziert`. Extend `RufPasst`, `SigPasst`, `Signatur.anfang` and `Vertrag.ende` consistently. Require disjoint move/loan sets, one occurrence per owner identity across stages, bounded stages and equal branch inventories. Preserve the old no-production lemmas with the stronger conclusion “output owner came from input or the distinguished mint transition”. |
| Source values | Represent named `linear ghost` owner bindings by a checked source binding-to-`Res.marke` map, not a copyable `.int`, `.ptr` or unit-valued `Ty` token. Every source variable move, parameter/result handoff and borrow consumes or suspends exactly that map entry. Return metadata carries the same nominal mark and stage. This provides a source-to-resource preservation theorem even though the ghost value has no IR word. `own` on a pointer also requires the matching owner resource and C12's live capability; the current writable Bool is insufficient. No new copyable `Ty.owner` is needed for this ghost fragment; nonghost/stored owner values remain refused until a resource-indexed representation is proved. |
| Unique mint | Add **new** `OwnerMintDecl` mapping each owner to exactly one resolved foreign minter and one root/site. Append **new** `Block.ownerMint` and `Endblock.ownerMint`: execute that binding once, add `.marke m s` only on its successful return, then continue under `.marke m s :: Λ` with the ghost-name resource binding (Block continuation ends in `Λ'`, Endblock continuation terminates). Arguments/effects/software proof use C08; the transition is not an arbitrary owner-producing axiom. The machine carries **new** `OwnerState`, with a permanent spent-mint set and a location for each live mark (active frame, suspended transfer/loan escrow, or retired). A mint requires unspent authority, records it spent, and never replenishes it after consume/return/reset. Append the corresponding event and G push/answer rules; the actual foreign invocation and its call log/effects remain present. Erase an external call only with a proved ghost-only implementation/erasure theorem. |
| Roots and admission | Add **new** `ownerB`/`OwnerAdmission` to `Akzeptiert` and `AkzeptiertSpec(X)`. Check the complete direct/indirect call graph, exactly one syntactic mint site outside all loops, root with no caller/address-taking, one declared occurrence across `E.starts ++ E.gestartet`, and no repeated/spawned execution of that occurrence. `EinzelnPool` is not sufficient: pool-safe roots still cannot mint twice. Extend `Laufzeit.einmal`, `StartZulaessig`, `FadenMaschine` start/child and GX spawn preservation so dormant starts cannot restart the mint. “Once” is at most one execution, not a liveness promise that a branch reaches the call. Initial owners and minted owners have disjoint origins; no unaccounted owner may occur in a start signature. |
| Calls and borrowing | On move, the caller loses use until the actual callee returns the same identity or consumes it as declared. On loan, move authority into a callee-frame escrow and disable the lender, including suspended callers; the callee may use the guard but cannot consume, mint, escape or re-loan beyond its checked scope. Restore exactly the saved identity/stage on every returning outcome. Exceptions/reasons use the common outcome rule agreed in C07/C08; no rollback that recreates a consumed mark. Start/child cannot capture a loan. Terminal consumption moves to retired and cannot restore mint authority. Model nested loans as a stack of exclusive escrows, with one active accessor globally. |
| G/GX proof and Spec | Extend `RufMaschineG/T1` frame/machine state, T2 call/mint/pop rules and T3 starts; prove **new** `OwnerInvG` by reachable-step induction, including suspended frames and spawn. Its projection supplies `Marken.einfaedig_aus_verlauf_getragen`, with appended mint/transfer cases and a spent-set invariant; uniqueness at one instant alone does not prove once-ever minting. Extend `Nebenlaeufigkeit/Allgemein/Geteilt`'s `OwnerAnfang.eigner_nie_erzeugt` interface rather than discarding its premise. Derive owner-guard access provenance and non-overlap for `RennfreiBis(GA)`, preserving the existing unshared-carrier separation checks. Thread the ledger unchanged through GX presented-memory changes. Add owner provenance/conservation to `Ziel`, `ZielX` and `ZielFX`; state this strengthening and the root admission in `Spec.lean`, without hardware authority to mint software permissions. |
| Export and Stage 0 | Coordinates: `Parser/Elab/Uebersetze.lean:822/1005/1172/1758/1806/1925`; `UebersetzeAllg.lean:382–393` currently exports `Marke := Empty` and no owners. Lower one nominal namespace, `owner` guards, real minter/site/root provenance and exact source parameter/result flow. IR-01/07 own this bridge, IR-10 call/return metadata, IR-09/12 starts. Resource-only handoffs emit no bytes after the simulation relates source bindings to the ledger; minter software effects still lower through IR-11. Extend `lowS_ok/lowB_ok/lowEnd_ok`, `Rekursion.lowFun_spec`, `Compiler.compile_source_program` and `IRBild.irBild_correct`; no detached signature witness closes C09. |

Witnesses: one guarded read and write after a root mint; move through two calls;
normal/reason return of the same owner; nested scoped borrow with restoration;
owner stage advance and final consumption; dormant root spawned once. Negative
twins: two mint sites, mint in a loop/callback/contract expression, duplicate
start/pool/restart, initial-plus-minted duplicate, access by suspended lender,
loan escape/consume, wrong returned stage, owner in ordinary `allocs`, and forged
`own` from `rw`. Use existing `beispiele/114`/`115` as source requirements, not
proofs; `crates/gabbro-check/src/kbedingung.rs` and D265–D268 in `saetze.rs` are
the current structural contract to port. Software minter behavior belongs to
user logic under C08, despite the historical “named assumption” documentation.

**C10 — shared reader/writer locks and full RCU.**

Present boundary: `Stmt.locks` and `Res.held` are exclusive; `Stmt.observes` in
`Kern/Syntax/Zucker.lean:200` is just that lock sugar. The existing
`Zielsatz/Eigenschaften/RwSchritt.RwAcq/RwSchritt` layer admits a reader by
executing G with foreign threads hidden (`ohneFremde`). Its `Lese` is an external
thread/lock predicate; `RwOrdnung.LeserLos` is a run premise. These are useful
proofs, not source admission or a mode-aware canonical machine. Reuse their
arguments in G, then remove the replaced independent layer. The old RCU-counter
references in `crates/gabbro-check/src/schablonen.rs` are not a connected
`gabbro_ziel` proof.

| Layer | Implementable change |
|---|---|
| RW syntax/resources | Add **new** `LockMode` (reader/writer); generalize the existing `Res.held L` to `held L mode`, signature holdings/floors, guard requirements and `Stmt.locks L mode`. This changes existing arguments, not constructor order. A read requires reader-or-writer authority; a store/foreign write requires writer authority. Introduce **new** `darfRead/darfWrite` and global counterparts, replacing the shared `darf/gdarf` calls in expressions versus writes; owner obligations stay conjunctive. No Bool write permission can manufacture a writer resource. Carry mode in acquire/release events, `offen`'s mode-aware projection, `HeldGenau` and call conformance. Invariant predicates may be read with reader authority; functions requiring writer-held cannot be called with reader-held. |
| Canonical RW machine | Generalize `RufFreiG`/`dannLocks`/`GRest.frei`/`freiGib` to mode compatibility: reader acquire requires no writer, writer acquire requires no reader or writer; record each actual section's mode, not a fixed `Lese t L`. Reject recursive taking and upgrade; retain increasing `D.rang` over **both** modes, signature floor and handler mask rules. Generalize `RwExkl` to the machine-state invariant and derive `LeserLos` from typing, effects and admitted calls. Writer release restores `S.inv`; reader release preserves it. Reader acquire sees it because there is no writer. No wrapper that hides foreign threads remains on the canonical trust path. |
| RW proofs/Spec | Integrate `RwSchritt.rwExkl_schritt`, `RwOrdnung.rennfrei_rw/rwSicht_schritt`, `RwInv.sperrInvRw_schritt/leser_sieht_inv` and `RwRang.kein_warteZyklus_rw` with the actual G rules. `SperrInvG` gains the stronger reader-only/free case; retain its existing free-lock fact. `InvRuheG`/`InvSichtG`, `SperrWechselG`/`SperrSichtG` and GX analogues must still give unchanged carriers under another holder and invariants at every move. Extend visibility to every reader; replace “holder alone” prose by “writer alone; readers share an invariant-preserving view”. Pairwise reader reads may coexist; every pair with a write remains ordered. Prove the old exclusive specialization and all original invariant facts; do not weaken them to return-only checks. |
| RCU declaration and resources | Give domains their own **new** declaration identity/metadata (protected carriers, publication roots, reclaim place/service), distinct from `D.Lock`. Replace `Stmt.observes` sugar with a canonical scoped observation constructor. Append **new** `Res.observing d site`, `Res.retired d site` and `Res.reclaimable d site`; static sites bind dynamic records in the frame, not runtime epochs in `Λ`. The **new** machine RCU state records nested observations per thread/frame, fresh observation tickets, publication generations, retired object/range identities and grace cutoffs. Observation permits only reads through the captured, live published generation; never grants write, ownership, writer exclusion or a rank. No observation capability escapes its lexical scope or survives reclaim. |
| Publication/retirement/grace | Use one **new** lifecycle judgment, carried by actual ordinary publication, unlink and service calls, rather than inventing surface `retire`/`synchronize` keywords. Publication initializes a fresh, exclusively owned version, release-publishes its capability and transfers it to immutable published state; readers enter before acquiring the root. Unlink removes **all** publication paths to the old version before it becomes retired. A grace operation snapshots the outstanding observations that could have seen it; reclaim authority is issued only after each has exited, including suspended/nested sections. Later readers cannot acquire the retired version. Reclaim consumes that authority and calls the proved provider release; double reclaim and reuse before grace are impossible. A zero counter read or a user `assume` is not this proof. Domain metadata alone does not identify which write unlinks an object: export a checked lifecycle derivation from the actual source calls/contracts, or refuse that reclamation site. |
| Race/invariant boundary | RCU protects lifetime, not arbitrary in-place mutation. `beispiele/31` reads `Konten.zaehler` without the writer lock while another function writes it: that pair cannot be admitted by merely adding `observing`. Published non-atomic carriers remain immutable until grace; updates create another version, and mutable shared payload uses an independently proved atomic interface. Existing lock guards remain obligations: observing cannot bypass `D.braucht` or invalidate `SperrSichtG`. For the first complete cut, use disjoint declared carriers for versions, separate writer metadata locks and a checked version registry. Arbitrary dynamic versions require C12/C08's live region realization and an injective version-to-carrier/extent map. W currently treats a whole table as one location (`Spec.lean` header): do not silently identify different slots with independent W locations or drop table/group invariants. Any finer location extension must retain the aggregate invariant/frame results and be reviewed explicitly; otherwise such same-table updates remain refused. Full lifecycle support is not permission to accept unsafe combinations of existing clauses. |
| GX/weak memory | Extend `Speichermodell/Atomar/AtomarLauf.RufSchrittGX`, `Maschine/GXMaschine`, `Maschine/MaschineW`, `Maschine/Sicht` and `Maschine/DRF`: RCU ledger state is authoritative, unchanged by arbitrary presentations of shared atomic values. Derive publication visibility from the actual release/acquire reads-from chain, and grace completion from a proved synchronization protocol over that history, not the latest G value or one arbitrary GX counter answer. Retired generations cannot be reintroduced by a stale root read: bind observation validity and retirement to the protocol, with validation/retry where needed. Prove **new** `RcuInvG/RcuInvGX`: every observed capability live, every reclaimed object unreachable by outstanding readers, and published invariant stable for the captured generation. User duties cover all allowed shared-atomic answers as `KoerperGutSA` does today. New synchronization steps require a matching W-protocol refinement witness; ordinary GX shared-atomic reads remain arbitrary. A new memory-order primitive needs its W rule and lowering proof before use; never assume SC. |
| Rank, waiting and progress | RW wait edges point only to incompatible holders and retain strict rank. A grace wait is not a lock acquire and cannot inherit a fictitious rank. Admit synchronous grace only outside observations and with **no held locks**, no outstanding joins/loans whose completion readers require; keep readers free of grace/join dependency cycles through transitive callee checks. Extend the combined wait graph and `KeinWarteZyklus` proof to grace edges, using the existing lock/start/join order plus these exclusions. Retire under a writer lock, release it, wait, then reacquire in rank order if needed; defer reclaim when source cannot do that. Extend `FortschrittG/FX` to expose an actual waiting dependency, not a new unproved “hardware” stop. No starvation/grace-time bound follows without the existing separate scheduling/termination duties; synchronous grace with an infinite reader may wait, but must not create a cyclic dependency. Check same-core handler dependencies in `Eigenschaften/KernMaske` too. |
| Export/Stage 0 | Coordinates `Uebersetze.lean:1203/1212/2538/3590/4039`: retain shared declaration/mode, `SItemTief.rcuT`, `SAnw.watch`, reclaim expression and all exits. IR-09 owns shared acquisition/release, atomics and RCU protocol; IR-07 owns lifetime transitions; IR-08/10 share C11 cleanup; IR-06/03 supply captured capability spans; IR-12 supplies starts. `stage0/Stage0/Senke/Sperre/{Code,Lauf,Sync,Satz}` currently proves exclusive `locks_ok`, not shared or RCU. Prove mode-aware assembly protocol and observation/grace/reclaim calls against G/GX/W, including nesting, early return and actual memory effects. Connect through `lowS_ok/lowB_ok/lowEnd_ok` and the function/image chain. Sequential `AgreeW` alone does not establish concurrent synchronization. Reuse the assembly runner; do not create a second runner. |

Witnesses: two simultaneous readers, excluded writer, writer release followed by
reader visibility, reader calling a reader-held function; two published versions,
one old reader crossing unlink, a later reader seeing the new version, nested
observation, grace waiting for the old ticket, then one reclaim/reuse through the
provider. Include old/new nontrivial payload invariants and a weak-memory trace
with a stale root/counter answer. Negative twins: shared write via direct call,
indirect call or foreign effect; upgrade, rank inversion, reader escape, own
observation reclaim, grace under a lock/reader-dependent join, premature/double
reclaim, surviving publication alias, unsynchronized mutable payload, and
`observes` used to bypass an existing lock guard. An RCU declaration without
reclaim metadata may support observation only; never infer a reclamation rule.

**C11 — consuming traversal, capacity duty and returns across lock scopes.**

| Subpackage | Implementable change |
|---|---|
| Consuming Kern/G | Append **new** `Stmt.consumeTraverse`: finite represented domain, current-world membership predicate, declared edge relation/projection, invariant, measure `Expr D Γ Λ (.int 0 bound)` and body `Block D V true (.index (D.count t) :: Γ) Λ Λ`, with the domain predicate/edge tests typed over those represented indices. Define a deterministic current-state selector over `alleIndizes`, selecting a minimal remaining member for the declared well-founded edge relation, with index order as tie-break. Each completed body pass must remove its selected member, introduce no new domain member/edge, preserve the invariant and strictly decrease the measure. The user body's declared `touches … consumes` performs the actual mutation; the traversal must not silently free the object a second time. Recompute selection in the post-body world; a saved initial index sweep is not this semantics. Empty selection terminates only with the selector-completeness theorem. Add matching `GRest` selection/body continuations and `RufSchrittG` cases, carrying the previous measure and finite initial bound. A failed required decrease/invariant is a logical failure, excluded by the user's body duty, never a successful early exit. |
| Consuming proofs/admission | `Isabelle/Consuming.ordnung_bleibt_unter_entfernen`, `blattheit_braucht_minimale_auswahl`, `leermenge` and `umhaengen_kann_zyklus_erzeugen` explain the obligations, but their `Tabelle` is not G storage. Prove a generic projection from actual `World D` and actual emitted mutations to that relation. Prove each selector result belongs to the current domain, minimality, strict fall and completeness; establish a bounded run by the entry measure and finite selection cost. This is a state-reading loop measure, not C17's `Mass` with empty footprint. Require exclusive owner/writer authority over domain/edge mutations, with stable membership while selecting; no concurrent insertion. `Akzeptiert` checks supported finite projection, guards, declared effects and absence of leave/next targeting this consuming binder; `NutzerPflicht(A)` supplies decrease/removal/invariant obligations on all returning passes. Preserve the Rust S008/N580 restrictions in `schleifen.rs`/`saetze.rs`. Return may propagate after C11 cleanup, but then no post-loop emptiness claim is made. Rehanging needs a separately proved current relation/decrease rule and remains refused in the removal cut. |
| Consuming export/IR | `uSchleifenKopf:3175` currently refuses consuming; `UStmt` must retain `touches`, measure, relation and selector metadata instead of reusing `traverseBeg` blindly. Extend the domain adapter from A14, `lowS`, `Anweisung/Faelle/Schleifen/Traversal.traverse_case`, `Anweisung/Schleife` and `Code/Refine/Loops/Traverse` with a consuming branch and dynamic re-selection. Reuse index/load/store primitives; prove binder scope, scratch preservation, remaining measure, work bound and every exit. `GabbroV/GvTraversal.trav_schedule_vollstaendig` proves a fixed sweep, so extend its bridge to the current-state selector; it is not already a consuming theorem. IR-07/08 own mutation/control, IR-06 represented edges, IR-09 exclusion. |
| No-else allocation | Retain `Block.arenaAlloc` in `Bausteine/Arena/ArenaZucker.lean:203` with its explicit ceiling-failure `Endblock`. Add one **new** generic `Block.narrowRequired`/`Endblock.narrowRequired`, the same typed narrowing with a logical failure instead of a source else; derive **new** `arenaAllocRequired` sugar by reusing `arenaRumpf`. Evaluate used/count once, require `used < capacity`, store initialized payload, then bump in the existing order. Failure is a **new** appended capacity case of `Logik`, excluded by `KoerperGutS/SA` and the actual source user's capacity proof. Dynamic committed storage additionally needs availability/commit proof or the explicit provider path; OOM remains user logic. Do not insert `retWhy`, fabricate a value, turn full into hardware failure, or assume a provider never fails. Check branch/call/loop/root allocation counts conservatively, but a Rust count is not the Lean proof. |
| Allocation export/IR | `Uebersetze.lean:3536` and `UebersetzeAllg3.lean:957/1251` separate no-else admission from A23's missing Endblock sugar. Implement both Block/Endblock required narrowing paths and source capacity obligations; keep supplied else semantics unchanged. Reuse existing `lowB_ok/lowEnd_ok` narrow/store/bind code with an explicit failed-capacity trap matching logical failure, proved unreachable under the user duty. Re-establish `ArenaReset.reset_alloc_laueft_rumpf`, fresh-generation facts and `ArenaOwnership` allocation/state agreement on the shared body. IR-07 owns capacity/liveness, IR-08 control, IR-10 duty propagation. |
| Resource-aware return | Replace `Stmt.ret/retWhy` and `Endblock.ret/retWhy`'s bare `Λ.Perm V.ende` evidence by **new** `RueckRessourcen`: exact residual `V.ende` plus a list of locally acquired scopes to close. Exact return is its empty-cleanup case; keep one return API. A **new** scope-indexed `cleanupB` and soundness judgment traverse the actual syntax, recording each lexical acquisition/observation and borrowed signature resource. They must verify that the return's list is exactly the crossed scopes in reverse order, not an arbitrary erase of extra resources. Calls inherit held resources but never acquire permission to release the caller's signature locks. Owner moves/loans remain conserved, marks cannot be discarded as cleanup, and returned capabilities cannot borrow a scope that is about to end. Add this check to `AkzeptiertSpec(X)`/`Akzeptiert`, with proofs and export correspondence. |
| Return G/replay | Evaluate and save the full return value/reason while all required guards still hold. Append a **new** pending-return continuation to `GRest`, retaining the saved result and exact residual resources; unwind each real `frei`/observation scope once, check its owed lock/lifetime invariant, then perform the existing value/reason pop and call-log return. The sequential `execStmt/execEnd` rules propagate the saved result while existing enclosing lock `mapWelt (·.gibt L)` releases it; never also release inside the leaf. Prove sequential/G replay equality with the pending cleanup. Generalize `GRest.anRueck_perm`/`Stmt.istRueck_perm` in `Nebenlaeufigkeit/Allgemein/Verklemmung/T2` to the residual resources **after** cleanup; immediate pop at the inner return is no longer valid. Preserve `SperrWechselG`, `InvAmGrundG`, floors, old-entry snapshots and both success/reason contracts. Leave/next keep their existing `peelFreiLeave/Next` behavior and use the same scoped cleanup relation when generalized. |
| Return exporter/IR | Remove `UebersetzeAllg3.lean:178/799`'s `return under locks` only when scope evidence is generated. In `stage0/Stage0/Senke/Anweisung.lowS`, `Sperre/OhneRet`, `Sperre/Satz.locks_ok` and `retC`, replace the `retFreiB` gate with proved exit classification and one shared cleanup-target mechanism. Save the whole result span in reserved storage across releases/calls; emit reverse-order releases before the outer contract/return epilogue. Share ordinary/reason/observation exits with IR-08/09/10, respecting IR-03 spans and IR-10 old snapshots. Prove releases on every crossing edge, no release of an unentered scope, no double release, restored masks, preserved saved value and exact final resources. Removing `retFreiB` without this proof is explicitly insufficient. |

Witnesses: empty and multi-node consuming tree/queue with deletion and a falling
measure, two eligible leaves with deterministic selection, nontrivial projection
and invariant, early return without an emptiness claim; exact last available
allocation, repeated allocations after reset, required allocation in an Endblock;
return/reason through two locks and an observation, preserving a multiword result
read under the inner guard. Negative twins: no consumes, unchanged measure,
nonminimal leaf, incomplete selector, insertion/rehang/cyclic relation, consuming
leave/next, capacity off-by-one or concurrent allocator, lost committed storage,
caller lock released by callee, skipped invariant restoration, escaped loan and
cleanup clobbering result/old snapshot. None is a new termination assumption.

**C18 — partial array reset and returning backing pages.**

Present boundary: `SAnw.reset` in `Parser/Stmt/Anweisung.lean:85–86` stores the
optional `(index,count)`; only whole-arena reset exports at
`Uebersetze.lean:2518`, otherwise :2538 refuses it. The range source form is for
a zero-initialized **static array**, not an arena (`crates/gabbro-check/src/arena.rs`
`reset_platz`; `dokumente/LANGUAGE.md` §13; N569). `ArenaSeiten.discard_live` proves
an abstract payload-preservation property and `discard_preserves_reuse` keeps the
free-list metadata; neither realizes a provider or executes this source form.

| Layer | Implementable change |
|---|---|
| Kern and range | Add **new** checked `ResetRange` derivation for a resolved writable zero-initialized static array and its C01/B02 representation. Capture `i` then `n` exactly once, preserving any bound source calls (A31); require `0 ≤ i`, `0 ≤ n`, `n ≤ len`, `i ≤ len - n` in mathematical integers before converting to target byte arithmetic. Allow empty ranges at `i = len`. Check multiplication/addition and object/field extent in the selected layout, not runner word size. Prove the post-array is zero at every selected index and unchanged outside it, including padding/metadata that is outside the payload contract. Preserve all read/write guard and footprint obligations; this is not whole-arena counter reset or generation reset. |
| Reset execution | Use a checked expansion into existing typed array/table stores where the representation supports it, with one generic range-store theorem and no second evaluator. A dynamic range needs checked narrowing and the C11 required-duty interface; invalid ranges are logical failures, not clipped/wrapped ranges. Zero is a typed value: initially admit only types with a proved zero representation and no linear/live capabilities erased by the reset. Integer/Bool/represented aggregate zeros must be proved against IR-03's encoding; zero bytes need not encode a valid fnptr, reference or nonzero range. |
| Page-return service | Bind the range operation to an explicit **new** `PageReturnContract` under C08's ordinary software-service interface, using a region/subregion capability plus checked extent; no raw numeric address conversion. The program supplies the implementation and its generic correspondence to actual backing storage. Return only fully covered provider-granule-aligned pages; zero any selected boundary fragments by stores and preserve adjacent elements/live pages. Keep provider/free-list metadata outside released payload, as `ArenaSeiten` requires. The contract preserves the reserved static extent, changes backing ownership for the released pages, leaves every outside byte/provider grant unchanged, and guarantees subsequent admitted reads observe typed zero until the next admitted write to that element, including after recommit. Decommit plus demand-zero is one implementation; zeroing followed by release is another only if the binding proves the same observations. No unconditional OS/madvise/mmap assumption and no promised success from an ignored error result. An infallible source statement needs user proof of service completion/availability, otherwise the existing source form cannot export through that service. |
| Live cells and aliases | Extend the C08/C12 grant ledger and `ArenaOwnership.State`-style location accounting with **new** backing states for static ranges: resident, exclusively pending return, released-with-zero-read contract, resident again. Distinguish permanent logical static-array extent from returned physical backing. The reset needs exclusive authority to mutate the selected range; a page release additionally requires no live owned allocation, borrowed view, outstanding RCU ticket, in-flight service or escaping alias that requires resident old contents anywhere in that entire page. Track aliases through parameters/results, fields, suspended frames, indirect calls and starts; re-use ownership flow, not a new name-only liveness pass. Persistent logical aliases may survive only with the same zero-on-next-read/availability contract and synchronization. Consume pending authority once; never invalidate an outside live cell to obtain page alignment. `ArenaSeiten.EmptyChunk/Live` supplies a reusable abstract lemma after a proved map from actual storage/ledger to those predicates. |
| G/Akzeptiert/Spec | No new leaf is needed for the store expansion. Page-service calls need C08 resource-changing G rules plus actual trace events, grant transfer and checked `PageReturnContract`; metadata alone has no effect. Add **new** reset/lifetime admission to `AkzeptiertSpec(X)` and its Bool: exact object kind/zero type, representation, complete alias/resource scope, guard/mode and service identity; range/availability/zeroing implications are source user duties. Derive exclusivity and live preservation over G and GX, not merely sequential execution. Strengthen provider/lifetime goal facts for released static ranges and their zero observations; retain `speicherAdressen` through reserved logical extent plus physical grant correspondence, `InvRuheG/InvSichtG` and every contract/frame fact. A backing transfer is not permission to write beyond a region or reinterpret a released grant as fresh while a conflicting lease remains. Record this Spec meaning change with C08; add no hardware assumption. |
| Export/Stage 0 | Carry both operands and resolved static-array metadata from `SAnw.reset` through appended `UStmt` reset metadata and `UebersetzeAllg3` Block/Endblock paths. IR-01 resolves arrays; IR-06 proves range loads/stores and byte/layout bounds; IR-07 proves backing/alias transitions; IR-11 proves the user service; IR-09 proves exclusion/RCU compatibility; IR-03 supplies zero encodings. Emit the store loop/boundary handling and actual binding call in the order the service contract specifies, with evaluated operands saved across calls. Extend source expansion, `lowS_ok/lowB_ok/lowEnd_ok`, `Lay`/memory correspondence and the function/image proof. A zero loop alone closes neither page return nor provider liveness. |

Witnesses: interior range, first/last element, zero count at end, unaligned range
with preserved boundary neighbors, one complete returned page, mixed live/free
pages where only the empty page returns, repeated release/recommit and zero
readback through a permitted surviving logical alias. Pair a nontrivial payload
invariant with actual provider memory changes. Negative twins: overflow/outside
range, negative count, nonzero-initialized object, invalid zero type, arena passed
as static array, rounded-outward release over live data, borrowed or RCU-observed
page, forgotten suspended/global alias, raw-address service, unproved service,
ignored failure and stale resident-content assumption after return.

**Shared proof migration and acceptance.**

1. Extend `Kern/Syntax/{Syntax,Typen,Zucker,Extraktion,Geist,Profil,Satz}` and
   `Kern/Semantik/Semantik/T1–T2` first; carry new scopes/resources through
   renaming, footprints, effects, ghost erasure, syntax induction and source
   provenance. Extend `Logik/Ruf/Maschine/RufMaschineG/T1–T4` (residues, transitions,
   starts, log/stack fidelity), `Nebenlaeufigkeit/Allgemein/FadenMaschine` and
   `Speichermodell/Maschine/GXMaschine` without losing dormant-start uniqueness.
   Migrate `Nebenlaeufigkeit/Sperren/Ruhe/MitRuhe*` and `Zielsatz/Einbettung` for every
   new declaration/resource/state field; otherwise idle roots/linking can forge
   authority or forget epochs. Carry GabbroV's represented fragment through
   `GabbroV/GvBruecke` and the actual source-derived obligations.
2. Re-establish `Nebenlaeufigkeit/Rennfreiheit/RennfreiVoll` access/frame/order
   lemmas, `RennfreiG`, `Nebenlaeufigkeit/Sperren/SperreBeweis`, and
   `Zielsatz/ZielOrt/Geraet/ZielOrtSperre/T1–T2`'s `akteurS`,
   `zielInvS_schritt` and `ziel_ort_sperre`. Extend `ZielOrt/Rahmen/ZielOrtRahmen`
   and `Eigenschaften/Invarianten` so cleanup restores invariants **before**
   publication/release/return, and readers observe the right live/versioned view.
   Replay all cases in `Speichermodell/Maschine/SperreSemA` and
   `Speichermodell/Atomar/{AtomarAkteur,AtomarLauf}`; the ledger must survive
   the presented/current-memory distinction. Recheck
   `Speichermodell/Adressen/Layout`'s `geaendert_im_bereich` and foreign extent
   proofs for reset/reclaim, including no-write service transitions.
3. Reprove rank and combined wait-cycle exclusion in
   `Nebenlaeufigkeit/Allgemein/Verklemmung/T1–T3`, progress in
   `Logik/Fortschritt/Fortschritt/T1–T3`, masks in `Zielsatz/Eigenschaften/KernMaske`,
   and costs/potentials in `Logik/Fortschritt/KostenG/T1–T5`. Account for selector
   scans, decreasing-pass bound, capacity checks, cleanup, shared synchronization
   and protocol work; keep `ZeitAb(X)` conditional as today. No new blanket
   scheduler/termination premise disguises a missing proof.
4. Extend `Zielsatz/Kern/Akzeptiert`'s checks and `akzeptiert_iff`, and
   `Zielsatz/Atomar/AtomarAkzeptiert`'s soundness. Preserve `frag`, `fuss`,
   `stufen`, `renn`, `einzeln`, `antworten`, `masken`, contract atomic-freedom and
   all source duties. Reprove `Zielsatz/Kern/Beweis.ziel_aus/zielF_aus`, then
   `Zielsatz/Atomar/BeweisAtomar.zielX_aus/zielFX_aus`, `gabbro_ziel`,
   `gabbro_ziel_gx`, `gabbro_ziel_sc_aus` and `gabbro_ziel_verbund`. The audit of
   `gabbro_ziel` remains **exactly** `propext`, `Classical.choice`, `Quot.sound`.
   Each generic syntax theorem needs a non-degenerate `_zeuge` satisfying all
   premises jointly, plus corresponding source-export/admission/IR/runner cases.
5. Document the precise `Spec.lean` diff in each implementation commit: new owner
   and lifecycle facts; RW reader visibility; grace dependency/progress domain;
   consuming/capacity/cleanup duties; released-page zero/extent interpretation.
   Retain every old exclusive specialization, race freedom with a write,
   deadlock/`KeinWarteZyklus`, `InvRuheG/InvSichtG`,
   `SperrWechselG/SperrSichtG`, call logs and `speicherAdressen`. A versioned
   invariant is additional; it cannot replace an existing whole-carrier/group
   invariant whose restoration the program still owes.

**Owner questions — genuine source-meaning choices, with recommendations.**

- **C09 borrow/return:** should a borrowed owner grant write access and may its
  stage advance? Recommend an exclusive, call-scoped loan, with the lender
  suspended, and return of the identical stage; explicit move/return handles a
  stage-changing handoff. Read-sharing needs its own frozen/read-only authority,
  not duplication of `.marke`. The existing D266 `consumes`+`allocs` refusal is
  lifted only for explicit proved transfer/loan, never owner production.
- **C10 RCU updates and grace binding:** `beispiele/31` and historical documentation
  suggest plain in-place writer updates plus a named grace assumption. That
  conflicts with the standing race guarantee and OS-as-user-logic rule.
  Recommend immutable published versions (or independently atomic payload),
  explicit proved unlink/grace/reclaim service contracts, and refusal of that
  example's unsafe overlapping read/write. Keep existing lock guards; do not
  reinterpret `protects` silently. The first cut uses separate version carriers;
  arbitrary same-table versioning requires an explicit finer-location design
  preserving aggregate invariants, beyond merely adding RCU resource states.
- **C11 consuming selection/mutation:** does the construct itself delete, or does
  its body discharge `touches … consumes`; and which eligible node is next?
  Recommend body-owned removal with no second implicit free, current-state
  minimal selection and stable index tie-break. Empty-domain means the state
  after the last completed pass; early return makes no emptiness promise.
  Other deterministic source selection rules need matching minimality proofs.
- **C11 cleanup semantics:** are normal/reason returns allowed to cross all local
  lock/observation scopes? Recommend yes, saving the result before reverse-order
  cleanup, restoring each owed invariant and retaining caller-owned resources.
  An escaping borrowed result is refused. This is broader admission than the
  present exact `Λ.Perm V.ende`, not permission to abandon resources.
- **C18 zero and service failure:** must reset promise typed zero on every later
  read, and can the page service fail? Recommend the zero-observation contract
  already described by the source form, preserving static reservation and live
  neighbors. For its no-else spelling, prove service availability/completion in
  user logic; do not ignore errors or add an OS assumption. A fallible spelling
  would require a separate owner-approved source rule. Actual allocation OOM
  being user logic and a ceiling else being a capacity path are already decided.

**Staging/rebuild impact.** Freeze the resource-flow, cleanup and provider
interfaces together first. Implement C09 conservation and C11 cleanup/capacity,
then C10 RW, C11 consuming and C18 checked zeroing, then C10 RCU plus C18's real
page-service/lifetime bridge. Keep incomplete subcases explicitly refused; do
not count store-only reset, observations without grace/reclaim, or a signature
without source resource preservation as a completed package. One agent owns
`grammatik/`; this document authorizes no extra builder or agent. Each structural
batch invalidates broad syntax/semantics/embedding proofs and Stage-0 caches:
build the changed model and all generic proofs before exporting its source
cases, audit standard axioms and run the Lean guardian. Follow the current
measured-memory grammar-build exception and the two global slots; Stage-0 direct
checks use isolated artifacts and release their assigned slot per module. Final
pipeline compilation and assembly-runner witnesses follow the same source
fixtures. No build, grammar edit, push or merge was performed for this design.

### Model extension design: C02, C12, C14, C15, C16 (2026-11-01)

Baseline `d13842f9b`; source inspection only. **New** marks proposed names,
including constructor names; unmarked declarations below were located in this
checkout. Kernel paths are relative to `grammatik/Grammatik/`. This supplements
the four preceding design sections, without enabling any export or claiming a
compiled case. Every added constructor goes at the **end** of its inductive,
including parser intermediates, events, continuations and proof judgments.
Changing an existing constructor's arguments migrates all clients together.

**Architecture.** Use checked source expansions into the existing typed program
where possible. C12 supplies the missing capability values; C08 supplies their
software boundary and grant history; C01 supplies payload products, C03 reasons,
C06/C07 callable interfaces, C09 ownership and C11 cleanup. These are proposed
shared interfaces, not already implemented facts. Do not introduce a second heap,
translator interpreter, callback machine, check-token system or execution backend.

| Package | Core change | Spec impact | Engineering days |
|---|---|---|---|
| C02 | Source-bound translation certificate, immutable typed payload and ordinary library-call expansion | Conservative generated-program interpretation; exact translator relation needs the owner decision below | 14–24: identity/export 4–6, certified maps/products 7–13, full call/image closure 3–5 |
| C12 | Space/rights-aware data capabilities, live byte slices and restricted entry handles | **Yes:** live capability provenance/extent and code/data separation; generalize the address-space statement | 20–34: table rights/spaces 5–8, live byte capabilities 10–17, entry handles 5–9 |
| C14 | Source-bound profile, build selection, placement and userspace entry/service correspondence | **Yes:** assumption provenance and selected-program statement; guest boundary remains user logic | 12–20: profile/selection 5–8, layout 3–5, userspace entry 4–7 |
| C15 | Per-core cells with proved identity, initialization, synchronized update and quiescent fold | **Yes:** accumulator/history correspondence, with existing race/time qualifications retained | 16–28: cells/algebra 5–9, concurrency/identity 7–12, export/IR closure 4–7 |
| C16 | Declared-check expansion and verdict/measurement/floor/probe provenance tied to Duty | **Yes:** check evidence and its consumption, never truth of arbitrary claim text | 12–20: expansion/admission 5–8, evidence/replay 4–7, export/IR 3–5 |

These **74–126 person-days** include generic proofs, witnesses, export and
connected Stage-0 work; shared work charged to earlier packages is excluded.
They are estimates, not measured build times. Implementation remains gated by
the explicit source-meaning questions below and the single grammatik owner.

**C02 — translators, payload regions and library calls.**

The actual parser loses essential input: `Parser/Stmt/Anweisung.parseLibRuf`
(:459–480) keeps only `args.length` and skips the balanced region;
`parseLetLib:288` also drops that count. `SAnw.lcall` has names/count and
`bindLib` names only. `SItemTief.transT` retains target, `FnSig` and body
(`Parser/Item/ElementTief:622/1837`); `SKlausel.load` retains the payload path.
`Logik/Vertraege/Uebersetzung.nutzlastZert_mem` proves only entry ranges.
Its header explicitly says the translator is unverified and the output is
checked. `crates/gabbro-check/src/uebersetzung.rs::versuch` admits only exact
integer rows and an identity translator; it is not a generic map proof.

| Layer | Implementable change |
|---|---|
| Lossless source/export | Generalize the existing `SAnw.bindLib/lcall` arguments to one **new** `SLibraryCall` record: resolved library/function paths, ordered `List SExpr` arguments and a balanced token tree for the region, retaining source coordinates for diagnostics. Change `parseLibRuf`, both consumers, equality/printer/round-trip/name-resolution clients together; never reconstruct tokens from the old count. Preserve translator identity, `SKlausel.load`, scopes, declaration visibility and exactly one translator per library function in **new** `ULibrary` metadata in `UProg`. Coordinates: `Uebersetze.lean:1998` (`fn is not impl`), :2538 (unhandled `lcall/bindLib` statement default), :4039 (`transT` default). Library bodies become ordinary checked `UFn`s, retaining all contracts/effects/reasons/costs. |
| Canonical map/input | Add **new** `TranslationDecl D` after typed syntax: source declaration IDs, input schema/region decoder, output schema, pure translator function, payload parameter position and target function. The decoder is a closed, checked relation from the retained token tree to a typed value; identity integer rows are its first constructor. Additional token/tree schemas require an explicit typed schema using C01 products/arrays/sums and a decoder soundness theorem, not a Rust-only convention. Proposed compile-time table parameters/results denote by-value row collections (`Ty.arr` of the C01 row product), with a schema-to-source-type proof; they are not runtime `Ty.ptr` capabilities or reads of an unrelated mutable table. This compile-time interpretation belongs to the C02 source-meaning decision. A general translator needs C17's source-preserving finite instantiation/control rules. Unsupported schemas remain refused. |
| Certificate and totality | Add **new** `TranslationCertificate` recording the exact call site, decoder derivation, translator/body identity, input, output and output typing. Under the recommended stronger map meaning, require an execution derivation of the **existing** pure `rufAt`/`execEnd` semantics from that input to that output, plus source-derived `MassPflicht`/termination and absence of logic/hardware/budget stops. Equality of output types alone is insufficient. Check finite derivations or kernel proofs produced by an untrusted Rust candidate generator; resource exhaustion refuses translation. Do not restore the retired executable Lean interpreter, or call an unrelated evaluator a translator. Pure means no carrier/foreign/atomic/lock/resource effects and no hidden runtime dependence, recursively through direct/indirect callees. Bill compilation work separately from the runtime program's `ZeitAb`; no generic timing project. |
| Payload and G expansion | Materialize one immutable private payload per source call site, with every row/field/value initialized exactly as certified. Map the schema to C01 fields and the selected checked layout; the last library parameter is filled once with its read-only table/region capability, never also supplied by the caller. Add **new** `LibraryExpansion P` relating the source call, payload initialization and an ordinary `call/bindCall/bindCallElse` to the resolved library function. Evaluate ordinary arguments once in source order; compile-time translation has no runtime side effect. The actual call retains requires/ensures, normal/reason outcomes, signature flow, log and runtime cost. Payload lifetime is the image lifetime unless a separately proved nonescaping shorter lifetime is used; no mutable or linear/owner payload is admitted by an immutable byte copy. |
| Akzeptiert and proofs | No new execution constructor is necessary. Add **new** `libraryB`/`LibraryAdmission` to the Bool/`AkzeptiertSpec(X)`, checking finite identities, complete payloads, read-only access, certificate references and generated call closure; kernel-checked certificate correctness is a separate proof, never a trusted flag. Use generated bodies' ordinary `NutzerPflicht(A)` and C06/C08 duties. Re-establish `Extraktion` read sets, `VertragsFuss`, `RahmenTreu`, `Getrennt` capability leaves, `Folge/FolgeBeweis` and `KostenG` for the expansion. Initialization/frame lemmas establish the immutable payload is never overwritten and disjoint from writable regions. The common goal closure below applies without new hardware premises. |
| Stage 0 | IR-01/13 own lossless decoding/schema/source provenance; IR-03/06 own complete payload spans and initialization in `Senke/Welt/{Lay,WeltAt,StartLayout}` and `Ausdruck/Aggregat`; IR-10 owns the ordinary call/return proof. Extend `Frontend.elabWithScopes`, `Compiler.Compiled` and `CanonicalSourceProgram` with exact translation/expansion certificates, then `compile_source_program` and `IRBild.irBild_correct`. Prove source library calls equal their generated calls under the payload relation, including contracts that read the payload, old snapshots and reason paths. `nutzlastZert_mem` is a scalar field lemma inside this proof, not the whole certificate. |

**Spec:** the existing goal applies to the generated accepted program; record
the source-to-generated interpretation explicitly. Stronger translator-result
correspondence changes the current output-only translation promise and requires
owner review; it adds no oracle assumption. Missing/ambiguous translator,
unretained tokens, malformed schema, wrong arity/type, unproved totality/map,
effects, mutable/linear payload and unproved payload precondition stay refused.
Witnesses: existing `beispiele/0106-summe-uebersetzt.gab` identity, a nonidentity
bounded map, two call sites with different regions, multi-field/product payload,
payload-reading requires and both call outcomes. Negative twins include a
well-typed **wrong** translator output, reordered arguments, changed translator
body under the same name, omitted field, escaping mutable alias and wrong profile.

**C12 — safe spaces, rights, byte slices and entry handles.**

`Ty.ptr n rw` currently has `Unit` values; `Ty.ref n` has cell-number values.
Neither describes a live byte extent. `Parser/Expr/Typ.parseRechte` retains a
rights string including `+`/`own@…`; `Uebersetze.uTyp:1004–1023` and
`uParam:1757–1766` reject spaces/rights, while :963 requires a table pointee.
The current `own` to writable-Bool branch is not ownership admission.
`STyp.raw` is a parser carrier for raw **type text**, not authorization for
numeric addresses. `STyp.entry` and `eintrittscode.rs` have a restricted
forward-only meaning (N575–N577), distinct from an ordinary callable `fnptr`.

| Layer | Implementable change |
|---|---|
| One data-capability type | In `Kern/Syntax/Typen`, add **new** `DataRights` (read/write flags and an optional resolved owner identity), **new** `DataTarget.table n` / `.bytes` and **new** `DataCapTy` (nominal space ID, rights, target). Generalize existing `Ty.ptr` to take `DataCapTy`; do not keep an old pointer API beside a new equivalent one. Table capability values remain `Unit` because the table identity is in the type. Byte capability values are **new** `RegionSlice` data: grant identity/generation, logical byte-carrier reference, offset and length, with natural-number bounds, never a numeric machine base. Space/owner/carrier IDs are finite declaration references checked against `Deklaration`, not globally meaningful guessed numbers. Arrays/products/sums recurse through this type using C01/C03. |
| Rights and spaces | Add **new** declaration maps for table/global space, region schema and the owner-ID-to-`D.Marke` correspondence. Canonical rights union handles `r`, `w`, `rw` and combinations without dropping `own@…`; `w` allows stores but not reads/read-modify-write. Reuse C09's `OwnerFlow`/loans for own, not the read/write flags. `x` is admitted only for a checked code interface; never combine data write and execute into an unproved self-modifying-code capability. Different space names are nominally different, not automatically physically disjoint: C08's realization proves backing separation. Reject cross-space coercion unless an explicit proved boundary relation transports the same origin and attenuated rights. Device/mmio/port/boot effects and numeric raw addresses remain excluded. |
| Producers, lifetime and G | Generalize `Expr.ptrOf/thru`, `Stmt.assignThru` and their permission premises to the descriptor; ordinary table dereference still names exactly the existing carrier and guard set. New byte slices come only from declared initial grants, a C08 successful provider boundary, or a checked bounded subslice of an existing live slice; no arbitrary slice literal/int conversion. Attach **new** `CapUse` derivations to uses/flows, checked by **new** `capUseB`, reusing C01 `ValueUse`, C09 loans and C08 `GrantInventory`/`BoundaryRecord`. The dynamic invariant is slice generation live, extent included, rights sufficient, and no revoked loan. Actual grant IDs live in values/ledger, not in a guessed static type parameter. Extend `World` with a **new** read-only grant view for sequential semantics; `RufMaschineG.weltVon` obtains it from the deterministic C08 boundary-history fold, not a second mutable inventory. Foreign steps update that same view via the canonical boundary transition; ordinary memory stores preserve it. Append **new** `Ereignis.capUse` recording grant/generation, selected interval and access mode at a successful use. Prove the view/history agreement through locals, fields, calls, suspended frames, returns, starts, cleanup, GX presented memory and release/reuse. |
| Byte operations | Map a live slice to a declared byte field (`D.typ t f = .int 0 255`) of a closed/open byte carrier via the grant realization. Share `World.bytesAb`/existing byte stores; do not add an independent byte heap. Append **new** `Block.capRead`, `Endblock.capRead` and `Stmt.capWrite` for checked byte-run access, with capability/index operands evaluated once, static run length `n`, exact byte-order rule and ordinary result/continuation contexts. Require at typing/admission the enclosing signature's writes and `darf` proofs for **every** possible root, not just the selected runtime root. At execution resolve the carrier and grant view, check rights/liveness and require `i ≥ 0`, `n ≤ length`, `i ≤ length-n`; invalidity uses existing `Logik.bereich`, excluded on legal runs by user duty. Checks precede memory effects; an unknown root cannot be a stuck match. The success result is `.int 0 (256^n-1)`; empty runs are allowed at the end. All accesses record the resolved underlying carrier's existing guards/effects; footprints conservatively include the finite carrier set permitted by the capability schema. No guessed single carrier for a dynamically returned region. Typed-object byte views require a proved encoding/decoding invariant; initially refuse them rather than letting a byte write create an invalid typed value. |
| Entry wrappers | Append **new** `Ty.entry (space sig : Nat)` with a finite entry-binding identity as value. Add declaration metadata mapping that identity to signature, selected image entry and allowed forwarding site; **new** `EntryUse` is the entry case of `CapUse`. An initial/generated wrapper is the only producer; source `&f` remains `fnptr`, and no Gabbro expression calls, compares, stores, duplicates or casts an entry handle. Its one forwarding use is the matching foreign parameter outside loops, preserving N575–N577. C14 proves the wrapper/root/service correspondence. Ordinary callable `ptr<code,x>` resolves to the existing checked `fnptr`/C06 contract, never to an arbitrary byte-slice offset. Guest-code capability is usable only by its C08/C14 isolation service, not as an ordinary verified function target. |
| Akzeptiert/goal | Add **new** capability/entry admission to `AkzeptiertSpec(X)` and the Bool: descriptor references, rights, exact producer/use paths, finite possible roots and guarded footprints. Semantic disjointness, provider behavior and borrow validity remain source-derived duties, not Bool decisions over arbitrary worlds. Add **new** `CapTreueG` to `Ziel/ZielX/ZielFX`: every admitted live use has the unique grant/entry provenance, valid extent/rights and compatible C01/C09 flow. Reprove G/GX step preservation using C08's single global ledger; releasing a grant with a borrower or queued callback refuses. Extend `Getrennt.traegerVon`/`ParamGetrenntL` and C01's recursive leaf version to grant roots; overlapping slices do not become distinct by having different variables or space labels. |
| Address statement and IR | `Adressen/Layout.LayoutOk.geschlossen/offen` currently fixes closed carriers to space 0 and open tables to separate nonzero spaces; globals are implicitly 0. Generalize `AdressLayout` with global-space mapping and `LayoutOk` with correspondence to declared logical spaces plus **separate** injective region/grant backing realization. Open extents remain separate region identities even when several inhabit one named source space; never place unbounded mathematical regions at overlapping bases in one flat space. Reprove `zelle_im_bereich`, `zellen_getrennt`, `geaendert_im_bereich` and `Bereich`'s outside-write theorem. Extend IR-03 encoding/`ValueValid` with capability spans (origin/slice or checked ABI representation), IR-06 `WeltAt` with one grant-to-storage relation, IR-11 buffer packing/unpacking and IR-12 entry relocation. A machine address appears only inside that proved layout/binding relation. Prove new bounds/read/write cases through `lowB_ok/lowEnd_ok/lowS_ok`, then function/image/source correctness; stale handles cannot pass an unchanged numeric-address check after reuse. |

**Spec:** generalize the named-space/extent interpretation and add capability
provenance/lifetime/code separation, preserving the original conditional
`speicherAdressen` leg and C08's stronger physical realization. No cross-domain
snapshot guarantee follows from a space name: `Kern/Semantik/Adressraum` explicitly
leaves check/copy cuts, and `EinSnapshot` is not supplied by this package.
Uncontrolled concurrent mutation needs a proved software copy/synchronization
binding; it cannot become an implicit hardware or OS promise.
Witnesses: named-space table aliases, write-only store/read refusal, own loan and
return, byte subslices and zero-length boundary, two provider grants, release and
reuse with a stale generation refused, nested capability fields, one entry
forwarding plus a real declared root. Negative twins: `own` without mark,
overlapping writable arguments, out-of-bounds/overflow, forged/dead grant,
space cast, typed-byte corruption, data-to-code, duplicate/late entry forwarding.

**C14 — profiles, selection, placement and userspace guest/entry binding.**

`Kern/Syntax/Profil` already has `Profil.gut/bindet`, `Bibliothek`,
`bindung_fuegt_nichts_hinzu` and keyed `pruefeSchluessel_einigung`, but its CUTS
say it is not wired into the goal. More seriously, `namensGleichheitAux`'s free
case compares predicates at **one existential witness world**, and
`erfuellt .frei = True`; neither establishes semantic assumption identity/truth.
`Stage0.Profil.prepareItems` currently proves exact unchanged syntax and
`arch = x86_64`; its early :52–54 guards precede the Elab refusals.

| Layer | Implementable change |
|---|---|
| Canonical profile binding | Retain one `Profil`/`Bibliothek` architecture. Replace free-entry content comparison by a reference into one source-derived registry of resolved assumption identity, declaration text/class/falsifier and semantic interpretation; duplicate spellings with different declarations refuse. A proof relates that interpretation to the actual named `HardwareAnnahmen` component; never decide equality of arbitrary `Prop`s. For existing free-predicate clients the replacement relation requires identity and equivalence at **every** world, not `∃ σ`. Keep mode projection separate from hardware truth: `profil_modell` may construct a consistent keyed assignment, never prove free prose or hardware by `erfuellt = True`. |
| Checked configuration | Add **new** `ProfileBinding` connecting `SItemTief.profT` (`bedarf` distinguishes requirements), source registry, every linked library's complete requirements, selected target and supported mode interpretation. Preserve duplicate-equal entries as a set; reject conflicts, missing names/requirements and unsupported modes. Resolve every key (`arch`, `rounding`, `fp_contract`, `memory_model`, `interrupt_routing`) by a closed supported decoder, not arbitrary Nat codes or missing-key 0. Defaults, if needed for a profile-free userspace image, are explicit checked image defaults, never synthesized source assumptions. Bind IEEE mode to the actual arithmetic lowering and W/GX model, and architecture to the emitted image; unsupported hardware routing stays refused. |
| Build selection | Add **new** `BuildMode` (shipping default/test) and **new** `Selection` certificate over the **original** parsed items and explicit mode. Recursively interpret `gateT` through modules/public wrappers before name/constant/target/start extraction; retain module scopes. Prove selected declarations and all dependencies (types, constants, contracts, direct/indirect calls, payloads, starts, probes and profile entries) are closed. Preserve the Rust `gatter.rs` G001–G003 rules for ungated dependencies and reserved `TESTBUILD`. Function-tail gates supported by Rust also need lossless canonical parsing: current `FnSig` has no gate field; add one with parser/printer/provenance proofs or retain an explicit refusal, never infer it from raw discarded clauses. |
| Source-to-goal statement | Put the profile/selection/placement certificate in **new** `Einheit` metadata and preserve its structural admission in the `Pruefer`/`PrueferX` unit adapter; raw `Akzeptiert P …` still checks the selected program. Add matching fields to its specification/Bool adapter, not a proof-irrelevant successful option parse. Replace `Prepared.unchanged`/`CanonicalSourceProgram`'s selected-equals-original requirement by the exact `Selection` relation, retaining original lex/parse evidence and scope derivation from the selected tree. State **new** profiled-source correctness: `ProfileBinding` supplies exactly the already named hardware components to `gabbro_ziel` for that selected unit. Library linking transports requirements via `Profil.bindet` without adding software or unlisted assumptions. Prove both modes separately; never infer shipping safety or reports from a test-only proof. |
| Static placement | Preserve `.globT` alignment/section in `UGlob` instead of `uGlobs:3908`'s refusal. Add **new** `PlacementSpec` with source object identity, evaluated positive alignment and section name, and a checked profile section-to-region/permission policy. Require supported power-of-two alignment, checked offset/size rounding, full aggregate span, pairwise disjointness and initializer/zero contents. A section is an opaque selected-image label, not implicitly ELF or a physical address. Actual image mapping establishes the policy, including read-only payloads and no data execute/write-code alias. Extend `AdressLayout`/IR `Lay`, startup initialization and image relocation proofs; a string in metadata alone does not discharge placement. |
| Entry and guest boundary | Distinguish C12's generated forward-only `entry fn` from `SItemTief.trustT` guest entry. Add **new** `UserEntryBinding` tying the former to a generated trampoline, exact declared root/arguments, selected ABI, stack **region** and the C08 start service; prove one forwarding, actual activation/return/join behavior and lifetime against `FadenSchritt`/GX starts. For `trustT`, **new** `GuestBoundary` names a code-region capability, proved userspace isolation/invocation service, allowed memory/resource transfer and return-or-noreturn behavior. Arbitrary guest instructions are not executed as G code or given Gabbro body guarantees: all observable interaction is the proved service contract, with guest-owned storage outside protected live grants. Existing regs/stack fields are retained and interpreted only as arguments to a supported ordinary userspace ABI adapter. Actual register-state manipulation, privileged transfer, boot or unknown ABI stays excluded/refused. The historical `EntrustDecl.annahme` cannot assert OS isolation; link it only to genuine named hardware and prove software isolation in C08 user logic. |
| Export/Stage 0 | Coordinates `Uebersetze.lean:3908/4039`, `Parser/Item/ElementTief:615/623/624`, `Stage0/Profil.lean:31–54`; extend `Frontend/Source`, `Compiler.Compiled/CanonicalSourceProgram`, `Bindung` target selection, `Senke/Welt/StartLayout`, `Bild/BildSatz` and `IRBild`. IR-12 owns source-selected entries, placement and start/image certificates; IR-11 supplies actual service/ABI correspondence. Change early refusals only when their exact source certificate and generic lowering are available; keep `runnerCompatible` until another backend/image proof exists. Dispatch-only entries retain their old specialization. |

**Spec:** hardware assumptions become the explicit profile-selected named set,
with C08's software duties in (b); linking adds no assumption. Runs refer to the
selected unit, whose source provenance includes mode and placement. Extend
`Laufzeit` correspondence for proved entry/start bindings without silently
assuming the OS behavior currently mentioned there. Guest safety is boundary
isolation under the proved binding, never a claim about arbitrary guest logic,
termination or costs. Re-establish the shared goal chain and
`Zielsatz/Projekte/Verbund` profile transport. Witnesses: one profile/two libraries,
same name with conflicting assumptions, both build modes, indirect/test-only
dependency, aligned multiword static in a non-ELF policy, exact entry forwarding,
two joined roots, isolated guest returning through a proved userspace service.
Refuse inconsistent/missing/unsupported profile modes, stale selected manifests,
misalignment/overflow/unknown sections, late callbacks, unproved isolation and
all privileged entry/register/boot operations.

**C15 — per-core accumulators, all five operators.**

`Parser/Item/ElementTief.accT` stores name/type/operator/optional core count;
`Uebersetze.lean:4039` refuses it. `Isabelle/AccumulatesMonoid` proves abstract
fold/permutation/RMW identities, not actual cells. `beispiele/0023-akkumulatoren.gab`
states assignment means merge, the core query is a foreign binding, and live
folds are not atomic snapshots. `Zielsatz/Eigenschaften/KernMaske`'s
`kern : Faden → Nat` is a schedule parameter, not a runtime core-query theorem.
The Rust per-core exemption in `fusswache2.rs::per_core` is explicitly not yet a
G proof. Current `llvm.rs:4729` creates a scalar initialized to 0; this neither
implements N cells nor supplies the `min` neutral value.

| Layer | Implementable change |
|---|---|
| Canonical descriptor/expansion | Add **new** `AccumulatorDecl D` after syntax: declaration identity, positive constant N, storage width/signedness/range, closed merge operator, N distinct private global carriers and locks, core-query binding and generated update/reduction functions. Add **new** `AccumulatorExpansion P` relating every source assignment to merge and every source read to the N-cell fold. Generate **N carriers**, not N supposedly independent W locations in one table: W/races remain carrier-granular. Source writes/effects expand to the full permitted cell set, with real guards. No new G execution constructor is needed; use ordinary bind/call, conditional dispatch, arithmetic/check/narrow, global stores and locks. |
| Core identity | C08's **new** core-query contract returns exactly a `Fin N`-equivalent bounded value with a boundary record identifying the executing core at that query. Tie it to the same declared core assignment used by the userspace scheduler/binding; a Rust thread number, modulo reduction or constant 0 is not evidence. Query once per source update; migration after the query does not reselect the destination. If the owner requires the core at the store rather than at query time, require a proved pinned/no-migration scope spanning both. Runtime scheduling/pinning is software user logic; no implicit OS/hardware assumption. Source cannot supply an arbitrary cell selector. |
| Correct concurrency first | Use one existing exclusive lock per private carrier around the complete load/merge/store. This is a concrete safe expansion for reentrant/same-core updaters and gives live readers race-free cells. It avoids needing an unproved assertion that one hardware core implies one unfinished writer. Generate a compatible total lock-rank order and infer/check caller floors after expansion; update holds only its selected cell lock. Prove an optional lock erasure only when a C09-style unique updater lease excludes every conflicting update/read throughout the emitted sequence; this optimization is not required for completion. Never implement a plain load/store under the Rust per-core exemption, or add an unbounded CAS loop under a bounded source cost. |
| Neutral values/operators | Use the mathematical range `[lo,hi]` plus preserved storage width `w`. `max` starts at `lo`, `min` at `hi`; `add` starts at 0, which must inhabit the declared range; bitwise `or` starts at all-zero and `and` at the w-bit all-ones pattern (signed interpretation is explicit). Require the bit-pattern neutral and every returned fold value to inhabit the declared type; reject a restricted range lacking them rather than silently use 0. Bool or/and use false/true. Prove max/min/bitwise laws on those typed encodings, extending the existing abstract `MergeMonoid` facts; its Nat-max/Bool-or instances do not prove signed word cases. Checked integer add uses mathematical sums with user range/overflow duties at each cell update **and each actual reduction prefix**. It is not automatically a total monoid on a bounded subtype, and wrapping/saturation is never implicit; wrapping needs its explicit C13 type/rule. |
| History and quiescence | Define **new** `AccHistory` from generated update call/store records, grouped by accumulator and queried core. At the actual store, record its saved argument/core and pre/post cell values in the shared ghost history; retain an in-flight contribution until the matching release/completion. A failure before any store adds none; a later failure cannot erase a store already performed. Prove each guarded cell equals its completed fold plus any committed in-flight contribution since one-time initialization. For live reads, take/release cell locks in index order and return the fold of those recorded samples; no whole-fold linearizability claim. Define **new** `AccQuiescent` over the read interval: initialization complete and no update in flight or occurring in that interval. Derive it from a proved joined/frozen writer phase or an internal all-cell lock scope acquired in increasing rank, never from a caller-provided Bool. Under it, prove sampled fold equals fold of all contributions and the abstract neutral-start RMW chain. Conditional permutation equality for checked addition requires all compared prefixes in range; nonnegative contributions suffice if the total fits, mixed signs need the stronger prefix duty. No reset/restart of initialized cells while a writer or observation survives. |
| Admission/Spec/IR | Add **new** `accumulatorB`/`AccumulatorAdmission` to `AkzeptiertSpec(X)` and Bool: N/identity/schema, generated private storage and lock access only, exact core binding, neutral initialization, complete call graphs/effects/floors and source expansion. Semantic query/range/quiescence facts are source-derived `NutzerPflicht(A)` duties. Add **new** `AccumulatorTreueG` to the goal for cell/history equality and conditional quiescent reduction; ordinary `RennfreiBisGA`, group invariants and `KernHaltEA` still apply. IR-09 proves actual lock protocol via `Senke/Sperre/Satz.locks_ok`; IR-02/03/13 provide checked typed merge/fold; IR-11 core binding; IR-12 one-time cell initialization/start ordering; IR-08/10 control/call closure. Connect `lowS_ok/lowB_ok/lowEnd_ok`, `Rekursion.lowFun_spec` and source/image theorems. Count generated dispatch, N reads, checks, locking and query in costs; refuse an unsupported declared bound instead of retaining the source's old constant cost. Lock-wait bounds retain the existing explicit qualifications. |

**Spec:** add cell/history and conditional quiescent equality, with the core
identity provenance in user logic. Do not add a per-core race exemption or make
quiescence/finite waiting universal. Witness all five operators with N ≥ 2,
distinct neutral values (signed max and min especially), same-core reentrancy,
migration after the recorded query, joined/frozen reduction and live sampled
fold. Negative twins: N=0/unknown, out-of-range core, min initialized to zero,
`and` initialized to zero, wrong width/sign, missing lock/lease, read concurrent
with a plain writer, local-add fit but total overflow, mixed-sign intermediate
overflow, premature reduction and reset during an active update. Floats remain
refused (F004); `beispiele/23` is a source fixture, not already accepted evidence.

**C16 — declared-check admission beyond a linear Duty.**

`SCheck` (`Parser/Item/ElementTief:455`) retains all seven fields;
`Uebersetze.lean:4039` drops none, but refuses `checkT`. Existing name checks
N020–N027/N043–N045 in `namen.rs` and Boolean typing in `m1.rs:1318` are useful
constraints, not a generic expansion theorem. In particular N022 currently
tests whether a floor **names** the measured quantity; this proves no useful
lower bound. `spiegel_und_sonde` records the settled rule: `expects` names an
external probe owned by exactly one obligation (N024). Earlier comments saying
this is unresolved do not reopen that owner decision.

| Layer | Implementable change |
|---|---|
| Descriptor and exact expansion | Add **new** `CheckDecl D` after syntax: resolved declaration/claim text, ordered measured place selectors, generated Boolean probe/producer, typed floors, actual gate functions/checks, unique optional external probe identity/text, build mode and source coordinates. Store its finite metadata with `Programm` so `Akzeptiert` sees the same declaration as the generated code; `Einheit` retains its source certificate. A **new** `CheckExpansion P` proves the generated probe is the written `canFail`, every returning path yields Bool and its signature contains all actual reads/calls. Reuse A24's `Res.marke`/`Signatur.produziert/konsumiert` and `nachSig`: no second evidence-token type. Generated names are collision-checked (`erzeugernamen.rs`), not an open external symbol that can replace the source probe. |
| Invocation and gates | A declared check is not itself an execution step. Bind its generated producer to an explicit generated/declared test-driver call site under C14, or a resolved ordinary call, and prove that call through the same G/IR pipeline. The driver observes the returned Bool/report and transfers its Duty to one selected declared consumer; invoking another consumer requires another completed producer invocation. Record that selection in the expansion, rather than auto-running all gates or duplicating one Duty across their list. If a gate is called without the required producer report, ordinary resource admission refuses it. A driver handling a false result still must discharge the completed obligation through an admitted failure-handling consumer. Its policy is explicit user logic; merely declaring `gates` cannot invent execution, measurement or success. |
| Measurements and floors | Resolve measured places and aliases at their true scopes, including locals bound inside the probe only after their definitions and only on paths where they exist. Capture actual sampled values with a typed path-indexed **new** `CheckReport`, identifying source place, observation point, value and guard/region provenance. A report contains copyable observations/ghost provenance, never a second usable owner or a capability surviving its loan; noncopyable measurements need a proved read-only projection or refuse. Missing values on an early returning path are explicit absent samples, never zero. Evaluate applicable floors over those snapshots and retain their Bool outcomes. A check is read-only on program payload: recursively verify actual direct/indirect/foreign effect summaries and frames, not base-name equality or textual absence of assignment. Observation/acquire/await synchronization is allowed only through its proved existing/C10 rule and is recorded; no assumption that repeated reads form one snapshot. Measurement service calls use C08 contracts, including failure and changed software metadata. |
| Admission and obligations | Add **new** `checkB`/`CheckAdmission` to `AkzeptiertSpec(X)` and Bool: source/producer/gate identity, full observation/footprint scope, complete Boolean exits, read-only frame, floors at supported comparison sites, and one-to-one counterprobe ownership. Generate a **new** `CheckSitePflicht` clause of the existing sequential caller-duty judgment, transported by C06/C08 prefix replay: all range/guard/old/availability duties, exact report-to-Duty correspondence and any **declared** gate precondition. A floor contributes a checked Boolean assertion/record, not an inferred theorem because its text mentions a name. Claim/counterprobe strings remain labels; no `ensures` is derived from them or from one successful sample. Contract use of a semantic claim needs an explicit formal predicate and user proof, outside prose interpretation. |
| Duty and both verdicts | Recommended meaning: Duty records a completed measurement/probe **with its verdict**, not proof that the prose claim is true. The generated ordinary producer returns Bool and produces one Duty on **each** normal return, including false; false/floor-failure remain distinguishable report data. A halted/divergent/foreign-failure path produces no completed report unless explicitly returned as a false verdict; no success is silently synthesized. The consuming gate discharges that same report once; a success-only gate needs its explicit user-logic precondition that the report's verdict and applicable floors hold. This preserves the common `nachSig` rule of C07/C08 and avoids a special success-only resource signature. If the owner instead requires all `gates` to demand success implicitly, specify that generated precondition and failure routing before enabling the source; do not secretly produce Duty only on one branch of a fixed signature. Gates naming other checks compose the existing consume/produce flow, with cycle/rank/termination obligations and no duplicate token. |
| Evidence in G/GX | Add **new** `CheckEvidence` to C08/C09's shared ghost history/location inventory: producer call activation, actual report, current token location and consuming gate event. Capture each measured value/floor result through a generated private typed identity-sample function at that exact site: its evaluated call argument supplies the report entry and its result is the same value. The checked expansion identifies these functions and their producer activation; source cannot call them independently. Record samples at their actual pushes, then complete the report at the producer's normal pop and consume it at the admitted gate push. This avoids inventing lost local values at return. Match ordinary function entry/return events and `CheckExpansion`, rather than allowing a public empty `allocs Duty` function to forge completion. Extend `RufMaschineG/T1–T3` and GX replay with this metadata; unrelated calls preserve it. No new execution constructor is required. Add **new** `CheckTreueG` to `Ziel/ZielX/ZielFX`: each live/consumed Duty has exactly one corresponding completed report and compatible transfer history. C09/C01 conservation handles movement through frames/fields; no duplicable report may manufacture a second Duty. |
| Counterprobe admission | Bind the external `expects` name uniquely to the check, exact probe text, selected source/build/image and a typed external test adapter under C08. Record **new** probe status `notRun`, `passed`, `failed` with execution provenance. Structural admission requires a valid unique binding, not a fabricated successful run. A measured acceptance claim requires an actual result for the matching artifact, expected false verdict and satisfied test-setup duties; absence remains unmeasured, an unexpected true verdict fails that measurement. An untrusted test log is evidence metadata, never a Lean axiom discharging a universal claim. Formal proof that a constructed test state makes the probe false is a separate generic/source-derived theorem, not proof that external hardware ran it. |
| Export/Stage 0 | Lower `checkT` into the generated `UFn`s and retained `CheckDecl`, not just `Block.check`. Reuse source statement/expression/old/range lowering for `canFail`, A24 signatures for ordinary gates and C08 signatures/duties for foreign gates; error paths must retain exact C03 reasons and C11 cleanup. IR-13/01 own expansion and scope/measurement identity; IR-10/11 caller/foreign gates; IR-09 observations; IR-12 selected probe/image identity. Emit real probe/floor/observation/sample-call work with existing kernels, prove samples/Bool results agree, and erase only ghost report/Duty bookkeeping after its generic simulation. An identity-sample call may be inlined only with a connected equivalence proof preserving its logical record and accounted cost; it is initially an ordinary emitted call. Extend function/pop/push, `Compiler.Compiled`, `CanonicalSourceProgram`, `compile_source_program` and `IRBild.irBild_correct`; a printed list of measures is not the measured execution. |

**Spec:** strengthen provenance and linear discharge, include check/gate duties
in (a)/(b), retain false reports and make no empirical/universal claim from
prose. Software measurement adapters are C08 user logic; counterprobes neither
add hardware assumptions nor establish hardware truth. Witnesses: true and false
probe with both reports consumed, failed floor, early return before a local
sample, calibrated check gating another check, fallible measurement service,
alias-hidden/transitive writer refused, guarded observation with proper cleanup,
unique external counterprobe with false verdict and a separate unrun status,
shipping/test selection and indirect gate dispatch. Refuse missing verdict,
unknown/ambiguous gate/measure, undischarged/forged Duty, aliased write to measured
state, floor outside its scope, unsupported synchronization, duplicate probe
ownership, stale artifact result and any attempt to infer ensures from claim text.

**Shared goal proof/rebuild handoff (implementation only).**

| Package | Required preservation and rebuild surface |
|---|---|
| C02 | Parser statement/round-trip/name clients, `Uebersetze*`, checked expansion/certificate, payload initialization, source provenance and ordinary call/image proofs. For the scalar identity expansion, primitive G semantics is unchanged; products/region payloads additionally rebuild C01/C12 clients. |
| C12 | `Typen`, `Syntax`, `Semantik/Semantik/T1–T2`, `Syntax/{Extraktion,Geist,Fehler,Satz}`, all pointer/value/signature/declaration clients and new byte binder cases. Extend `Extraktion/T3.eval_liest_nur_orte`, locality in `ZielOrt/Grundlage/ZielOrtSem`, `Logik/Vertraege/{Getrennt,VertragsFuss,RahmenTreu,EinpassenVoll}`, G/GX step/replay and address proofs. C03 `RawAnswer` decoding validates origins through the shared boundary, not by accepting any positive word. |
| C14 | `Kern/Syntax/Profil` and its import dependents; source/parser/selection/profile registry, `Einheit`/unit checker adapters, `Laufzeit`, start/entry/image/layout proofs and `Zielsatz/Projekte/Verbund`. Generated ordinary calls use the existing frame/replay proofs; wrappers add no privileged G case. |
| C15 | Descriptor/expansion/algebra and generated `Programm` declarations; `Nebenlaeufigkeit/Rennfreiheit/{RennfreiVoll,RennfreiG}`, `Nebenlaeufigkeit/Sperren/SperreBeweis`, `Speichermodell/Maschine/{GXMaschine,SperreSemA}` and `Speichermodell/Atomar/{AtomarAkteur,AtomarLauf}` establish the actual guarded cell/history invariant. Re-establish no-deadlock/ranks through `Nebenlaeufigkeit/Allgemein/Verklemmung`, `KernMaske` and start/join visibility; quiescence is interval-specific, not a new global scheduler premise. |
| C16 | `CheckDecl`, generated probe/gate code, report/history fields and `Logik/Ruf/Maschine/RufMaschineG/T1–T4` normal-pop/push proofs; actual observation/world/old snapshots through G/GX replay and ownership. Add zero-effect ghost-history transport to trace/lock/cost/contract proofs, not erased executable probe steps. |

For **each** affected package, extend `Zielsatz/Kern/Akzeptiert.akzeptiert_iff`
and `Zielsatz/Atomar/AtomarAkzeptiert.akzeptiertSpecX_of` with sound finite
admission and all old `frag/fuss/stufen/renn/antworten/masken` checks retained.
Keep shared-atomic reads out of contracts even when hidden in a payload/slice or
probe predicate. Replay concrete calls, reports, grant transfers and old worlds
through `Zielsatz/ZielOrt/Rahmen/ZielOrtRahmen`,
`Zielsatz/Eigenschaften/Invarianten`, `Logik/Fortschritt/{Folge,FolgeBeweis,KostenG}`
and the progress modules. Re-establish `VertragAmOrtG`, normal/reason restoration,
lock visibility, outside-write preservation, call logs and actual expanded costs.
Lift new metadata/invariants through `Nebenlaeufigkeit/Sperren/Ruhe/MitRuhe*`,
`Zielsatz/Einbettung`, `FadenMaschine`, GX starts and
`Zielsatz/Projekte/Verbund`; the idle root creates no grants, checks, entries or
accumulator updates. Carry represented bodies/duties through `GabbroV/GvBruecke`.

Then re-establish `Zielsatz/Kern/Beweis.ziel_aus/zielF_aus`,
`Zielsatz/Atomar/BeweisAtomar.zielX_aus/zielFX_aus`, `gabbro_ziel`,
`gabbro_ziel_gx`, `gabbro_ziel_sc_aus` and `gabbro_ziel_verbund` and their
non-degenerate witnesses. Each generic syntax/export theorem gets a `_zeuge`
jointly satisfying its admission and semantic duties, plus matching source,
`AkzeptiertX`, connected IR and assembly-runner fixtures. Model edits require the
full grammar build, layout check and Lean guardian with **exactly** `propext`,
`Classical.choice`, `Quot.sound`; describe each Spec meaning change in its commit.
One grammatik owner batches changes, using freshly measured available memory
minus 2 GiB and the two global slots; Stage-0 checks retain the 5-GiB slot scopes
and isolated artifacts. No build was performed by this document task.

**Owner questions — genuine source-meaning choices, with recommendations.**

- **C02 output promise:** must output equal the declared translator's map, or
  is any well-typed certified payload the language meaning? Current
  `Uebersetzung`/`uebersetzung.rs` explicitly promise output typing only.
  Recommend exact source-bound map correspondence with kernel-checked execution
  certificates, retaining output typing as one component. This is a stronger
  translation promise and must be approved before replacing the old cut;
  likewise approve table-shaped translator inputs/results as immutable row
  values in the compile-time context, rather than mutable runtime capabilities.
- **C12 named spaces/rights:** does a named space identify a logical namespace,
  a distinct protection domain, or a platform memory-kind policy? Recommend a
  nominal logical namespace with an explicit checked profile/binding realizing
  protection and any barriers; names alone confer neither disjointness nor
  TOCTOU protection. Recommend `own` remain the C09 exclusive loan/move, not an
  extra copyable write bit; this reuses the existing C09 ownership question.
- **C14 guest meaning:** is existing `entrust` intended to admit an ordinary
  userspace isolation-service invocation when its fields match a proved ABI?
  Recommend that bounded interpretation, with software isolation/start behavior
  proved under C08 and only actual hardware in the profile. Unrestricted guest
  execution/register-state entry remains excluded. Profile key equality and
  shipping/test selection already have stated meanings; they are not new choices.
- **C15 core/reduction meaning:** is the destination the core sampled at update
  entry or the core executing the store, and may reads synchronize? Recommend
  sample-once at entry and per-cell guarded live sampling, with exact reduction
  only under proved interval quiescence. Private synchronization is the safe
  baseline; erase it only with a proved exclusive lease. Recommend mathematical
  checked add with explicit intermediate-range duties, never implicit wrap or
  saturation. These choices affect scheduling/cost and must be recorded before
  admitting `accT`; all five operators remain part of the full package.
- **C16 Duty/verdict:** does a gate discharge a completed test obligation even
  when its verdict is false, or may every named gate execute only after success?
  Recommend completed-report Duty, with success-only behavior expressed by the
  gate's explicit formal precondition and failure handling. This preserves one
  common returning resource flow and cannot derive a prose claim. Recommend
  `gates` list alternative consumers, with one fresh completed producer call per
  consumption and an explicit checked driver choosing the consumer. If it means
  an ordered series from one measurement, specify a staged mark/order protocol
  instead; one linear Duty cannot be consumed repeatedly. Recommend
  floors be recorded/evaluated over the actual samples; a missing/false floor
  cannot yield a successful-evidence assertion. External probe identity/unique
  ownership is already decided (N024); whether a release policy demands a run
  is separate from structural source admission, and unrun never means passed.

**Staging.** Freeze the common schema/resource/boundary/capability descriptors
with the grammatik owner first. Build C14 profile/selection and C12 table rights
as conservative foundations; join C01 values and C08 boundaries before C02
identity payloads and C12 byte/entry transport. Then close general C02 maps with
C17 termination/control, C14 actual entry/service binding and C16 check/report
flow. C15 scalar algebra/initialization can proceed early, but enabling updates
requires the actual core-query and lock protocol; quiescent reduction closes it.
Commit each compiling implementation stage and retain named refusals for its
unimplemented remainder. No helper/metadata-only stage closes a whole C cell.

**Overall C-package plan.** Section labels below refer to the existing
`Model extension design` headings on this date: **D1** = C13/C17/C05/C04,
**D2** = C01/C03, **D3** = C06/C07/C08, **D4** = C09/C10/C11/C18,
**D5** = this section. Order is a dependency order for staged slices, not
authorization for parallel agents; a foundation may precede completion of its
whole package. Dependencies in parentheses affect the richer slice only.

| Package | Design | Person-days | Main dependencies | Recommended order |
|---|---|---|---|---|
| C13 builtins/count/layout | D1 | 8–14 | IR-02/03, checked layout | 1 |
| C17 measures/generics/compile-time | D1, bounded measure design only | 12–24 full estimate: 2–4 measure + 10–20 remainder | C13, IR-01; full remainder still needs detailed design | 2 measure; 12 remainder |
| C14 profiles/selection/placement/entry | D5 | 12–20 | IR-12; (C08/C12 entry/service) | 3 foundation; 13 entry |
| C05 global invariant carriers | D1 | 8–13 | invariant-return IR-10 | 4 |
| C01 products/mappings/ownership | D2 | 18–30 | IR-03; (C09/C12 ownership/walk bindings) | 5 values; 14 richer slice |
| C03 reasons/typed payloads | D2 | 9–15 | C01, IR-03/10/11 | 6 |
| C06 pointer contracts | D3 | 7–12 | IR-10, contract replay | 7 |
| C08 foreign/provider contracts | D3 | 16–27 | C06 foundation; C03 outcomes; (C09/C12 resources/grants) | 8 foundation; 15 provider closure |
| C12 spaces/capabilities/entry wrappers | D5 | 20–34 | C01/C08/C09, IR-03/06/11/12 | 9 rights; 16 live bytes/entry |
| C09 mint/owner loans | D4 | 12–20 | C08, common C01/C12 location flow | 10 |
| C11 consuming/capacity/cleanup | D4 | 18–30 | C09; C08/C12; IR-07/08/10 | 11 cleanup/capacity; 17 consuming |
| C02 translators/library payloads | D5 | 14–24 | C01/C14, IR-01/03/10/13; (C17 maps, C08/C12 regions) | 12 identity; 18 full maps |
| C07 indirect reason calls | D3 | 6–10 | C03/C06, common C08 outcome flow | 13 |
| C04 transition contracts/stages | D1 | 5–9 | C05/C13, IR-10 | 14 |
| C16 declared checks | D5 | 12–20 | A24, C08/C14, C09/C11; (C10 observations) | 15 core; 20 observation closure |
| C15 per-core accumulators | D5 | 16–28 | C13/C08/C14, IR-03/09/11/12 | 16 algebra; 19 concurrency/reduction |
| C10 shared locks/RCU | D4 | 30–50 | C09/C11; C08/C12 live regions | 17 RW; 21 full RCU |
| C18 partial reset/page return | D4 | 14–24 | C01/C08/C11/C12; (C10 outstanding observations) | 18 zeroing; 22 page/lifetime closure |

Total full C implementation estimate: **237–404 person-days**, including
the separately identified, still undesigned C17 remainder; without that
remainder **227–384**. This supersedes the catalogue's preliminary **30–70+**
implementation range, which preceded these detailed proof/lifecycle designs.
The earlier **5–10 design/decision days** are separate, not added to implemented
progress. Shared interfaces/ABI work is counted in its owning package; B/IR-lane
work already charged elsewhere must not be added again. Critical path is
value/channel migration → software contract and grant replay → capability and
resource conservation → RCU/entry/page-service closure, under the available Lean
slots and owner decisions. No elapsed completion date or universal speed claim
follows from these person-day ranges.

Validation of this design is static source/name/path inspection and
`git diff --check` only. **Zero new language cases compiled or proved; no Lean
file edited, no build, push or merge.**

### Model extension design: C17 complete (2026-11-01)

Baseline `17f6c1606`; source inspection only. This completes D1's C17 design,
including the newly identified block-meaning gap, and supersedes its optional
generic cut and the later table's “still undesigned” remainder. D1's runtime
`decreases` design remains applicable. **New** below marks proposed declarations,
not existing Lean names. Paths start at `grammatik/Grammatik/` unless prefixed
`stage0/`. No implementation, grammar rebuild or additional agent is authorized
by this document; the designated grammatik owner implements the approved rules.

**Grounded boundary and architectural choice.**

| Current source coordinate | Consequence for the design |
|---|---|
| `Parser/Elab/Uebersetze.lean:859/875/893/930` (`UKonstFn`, `uKonstFns`, `uKonstWert`, call case) | `rumpf : SExpr`; only `.block [] (some (.ret (some e)))` is collected. Clauses are discarded. Arguments are evaluated at the caller's interval, then checked against parameter intervals; the body uses only parameter bindings. This is not a semantics for blocks, contracts or constant captures. |
| Same file :4737/4774/4820 (`elabU`) | Const declarations disappear from runtime functions; array evaluation still calls the expression-only collector. Adding a Stage-0 block evaluator cannot establish a missing canonical meaning. |
| `stage0/Stage0/Frontend/Functions.lean:25/44/76` (`constantFunction`, `FunctionMeaning`, `constantFunctions_sound`) | The source-origin theorem requires exactly that single-return body and `evaluationClauses`; it proves extraction/signature provenance, not a general block execution theorem. |
| `stage0/Stage0/Frontend/Guard.lean:23/43/119`, `Source.lean:41/58` | `safeConstantName`/`SafeHull` are structural guards, including cycle revisits and absent names, not termination/name-resolution proofs. Keep the guard until a stronger canonical certificate replaces it on every path, including nested arrays. |
| `Parser/Item/ElementTief.lean:590/1674/1695/1720`, `Parser/Expr/Typ.lean:25`, `dokumente/SYNTAX.md` §2; `crates/gabbro-syntax/src/ast.rs:256` | `typeT` carries `List STyp` and order words. The Rust `TypDecl.parameter` explicitly includes witness payloads such as `Duty(check)`. `STyp` has no general application or formal-type binder. Do not reinterpret every payload list as generic binders. Linear mark order already has `D.stufen`, `Res.marke` and `Stmt.advances`; it is A02. |

Use **existing typed G blocks plus a checked pure/terminating fragment**, rather
than grow the Nat-valued `Konstanten.KExpr` into a second statement language.
`KExpr.eval` has one Nat parameter, truncated Nat subtraction, total Nat division
and caller-supplied name/function environments; none supplies typed signed
blocks or contracts. Reuse `Konstanten.konstZert`/`konstZert_mem` only after a
source-to-G denotation theorem, with an exact Nat encoding where applicable.
Adding a block field alone or evaluating a Rust AST is insufficient. Kernel
reduction of canonical G semantics for certificates is allowed; no executable
source interpreter, fallback runtime or new runner is introduced.

**Canonical blocks, evaluation and source meaning.**

| Layer | Exact proposed change and obligation |
|---|---|
| Kern representation | In a new module under `Kern/Syntax/`, define **new** `ConstProgram` containing `D : Deklaration`, `P : Programm D`, complete finite function enumeration and source IDs. Its declaration universe contains only const functions and finite enumeration domains: no globals, axioms, registers, locks, marks or invariants; enumeration tables have no fields and have a checked nonnegative `D.count`. Thus no synthetic mutable storage is needed. `P.requires`, `P.ensures` and `P.rumpf` retain their existing types from `Kern/Syntax/Syntax.lean:812`; contracts have empty resource contexts and `D.gruende f = 0`. Initially permit integer/Bool values; by-value `Ty.arr`/`Ty.str`/`Ty.sum` follow their existing value semantics and literal bridges, products depend on C01. Pointers, references, function pointers and linear/ghost values cannot be const data. |
| Purity judgment | Define **new** mutually structural `ConstExpr`/`ConstStmt`/`ConstBlock`/`ConstEnd` judgments over the actual typed `Expr`/`Stmt`/`Block`/`Endblock`, plus **new** `ConstAdmissible (c : ConstProgram) : Prop`. Whitelist literals, typed value constructors/projections, variables, proved arithmetic/comparisons and finite pure quantifiers; prove `e.orte = []`. Admit `Block.nil/cons/bind/bindCall`, `Endblock.ret/cons/bind/bindCall/ite`, `Stmt.assignVar/ite/ret/call` and pure tag/option/reason dispatch with corresponding arm judgments. Every direct call must resolve inside the same certified program. Assignment changes only a declared mutable local; binders retain exact context indices and mutability provenance in the source judgment. Empty footprint alone is insufficient: explicitly exclude oracle/hardware/float blocks, capability construction, indirect calls, memory access, resource operations, `retWhy`, `forever`, retry and traversal in the first slice. Every constructor of the judgment has explicit premises; no accepting wildcard. |
| Elab source representation | Replace `UKonstFn.rumpf : SExpr` by `rumpf : SAnw`, retain original `FnSig`/clauses, and migrate signature ranges into checked typed parameters/result (`List (String × Ty)` and `Ty`); remove the superseded range-only extraction representation. Add **new** `elabConstProgram`, returning a program together with its source derivation and admissibility/termination certificates, or a named error. Factor existing `uAnwReihe`, `uEnde`, `uSichert`, `UebersetzeAllg.lowEns` and `UebersetzeAllg3.lowBodyF`/`lowBody` machinery where suitable; they are not already proofs of this new fragment. Typed bounds and narrowing are checked before G construction, using explicit source semantics for every intermediate, not host arithmetic. |
| Source derivation | Define **new** `ConstElaborates` in `Parser/Elab/`, indexed by original declarations, final checked scope, source function ID and the resulting G function. Its inductive rules relate actual `SAnw.block/bind/set/cond/cases/ret` nodes, `SEnde.ret`, signatures, predicates and scope extensions to the corresponding G nodes. Include original operator spelling, range checks, source branch/binder order, early returns and resolved calls. This is a structural relation independent of the elaborator's success equation; prove **new** `elabConstProgram_sound` and determinacy up to alpha-renaming/function-ID isomorphism. Define source const-call denotation through this relation and G, not through a supplied mathematical function or a handwritten fixture. Prove literal/operator/substitution rules compositionally, so choosing a constant-return G body cannot satisfy provenance for an unrelated source body. |
| Evaluation | Define **new** `ConstCallResult` distinguishing value, contract violation, arithmetic/range failure, unresolved dependency and resource exhaustion. **New** `evalConstCall` checks the exact source argument expressions at their own elaborated types, transports them into `Env D (D.params f)`, and reduces existing `rufAt c.P O passes depth f sigma args` (`Kern/Semantik/Semantik/T2.lean:454`). It projects only `.ok` to a value and preserves all failures. A canonical world exists because enumeration fields and globals are empty; prove independence from world/oracle/`passes` for the admitted fragment, rather than assume hardware. Declared costs and evaluation limits are separate: exceeding a compiler work limit refuses compilation, never supplies a value. No saturation, silent wrapping, `toNat` clipping, unknown-name zero or default result. |
| Generic meaning theorem | Prove **new** `const_call_sound`: for every jointly source-derived, admissible program, typed closed arguments and successful checked evaluation to `v`, every world/oracle/`passes` and every depth at least the certified call-depth bound yield `rufAt ... = .ok sigma v`, with **the same world**. Prove uniqueness, depth stability and error correspondence separately; a failed requires/ensures maps to `.vorbedingung`/`.nachbedingung`, not a successful denotation. The source judgment then yields **new** `const_source_call_sound` for the original source call. Completeness is conditional on well-typed safe arithmetic, true contracts and sufficient evaluation resources, not promised for every syntactically pure function. Transport portable values between const and runtime declaration universes explicitly before `lowLit`; `Wert D` is not generally independent of D. |
| Loop-free termination | **New** `ConstTermination` first records a checked strict rank for every direct call and a computed maximum nested call depth. Structural descent handles blocks/expressions; rank descent handles calls. Calls in arguments and contract expressions belong to the rank graph too. Prove no `abstieg` at adequate depth. The old literal `64` in `uKonstWert`/Stage-0 normalization is an implementation cap, not a language termination proof. Recursive const SCCs remain refused in this slice; D1's `Mass` binds runtime recursion obligations and does not automatically justify const reduction. |

Proposed judgment interfaces, with the existing implicit `D`, `V`, `Gamma`,
`l` and `tau` binders: `ConstExpr : Expr D Gamma [] tau → Prop`,
`ConstStmt : Stmt D V l Gamma [] [] → Prop`,
`ConstBlock : Block D V l Gamma [] [] → Prop`,
`ConstEnd : Endblock D V l Gamma [] → Prop`, and
`ConstTermination : ConstProgram → Nat → Prop` (the Nat is sufficient call
depth, not a source measure). **New** `ConstScope` stores final closed typed
constant bindings, aliases, wrapper descriptors and resolved declaration IDs;
its definition belongs in Kern, without a dependency on Stage-0 `Scopes`.
`ConstElaborates` has indices `(items : List SItemTief) (scope : ConstScope)
(item : SItemTief) (c : ConstProgram) (f : c.D.Fn)`. It is proof data, not a
second representation of an executable block. `ConstCallCertificate` is indexed
by `c`, `f` and `args : Env c.D (c.D.params f)` and carries
`value : ErgVal c.D (c.D.erg f)` plus the source/semantic proofs specified below.
`evalConstCall` accepts those same indices and a compiler work limit; its
`ConstCallResult` value case contains that certificate. Compute a conservative
structural work bound and check it against the limit before kernel reduction;
the bound must include evaluation of predicates and nested calls.

No new `Ty`, `Expr`, `Stmt`, `Block` or G execution constructor is needed for
this block design. New judgment families live outside the existing mutual
syntax; any later constructor additions to existing syntax or parser inductives
must go at the **END**, preserving all existing constructor numbers. Replace
old representations atomically and migrate all pattern matches and fixtures;
do not retain two canonical const evaluators with different accepted meanings.

**Second slice: bounded loops.** Extend the same purity judgments with actual
`Stmt.traverse` over a certified fieldless finite domain, and `Stmt.retry n`
only when its condition, body and overflow block are themselves certified pure.
Reuse `alleIndizes`, `traverseLauf` and `retryLauf` through `execStmt`
(`Kern/Semantik/Semantik/T2.lean:213–226`). The source `SAnw.each` keeps its
domain/mode/header/invariant; parse those fields with the canonical loop export
rules before admitting them. No new numeric `for` syntax is implied. By-value
array traversal uses a checked length/domain correspondence and pure
`Expr.arrGet`, never table reads. Prove finite cardinality, index order, local
accumulator context updates, binder scope restoration, early return and targeted
`leave`/`next` against the same G control outcomes. Loop invariants and retry
overflow paths remain checked exactly where G checks them; retry exhaustion
executes its declared overflow block, not a guessed zero. Nested iteration gets
a structural work bound including each executed body and predicate, and callees
retain their depth bound (iteration count is not recursive call depth).
Resource exhaustion has no logical success result. Open domains, consuming
mutable domains, unbounded loops and recursion without a separate checked
well-founded const rule remain refused; C11 and runtime `MassPflicht` are not
silently imported as const totality. A later recursive slice must prove the
existing measure duties and derive an adequate evaluation depth, not equate
measure value with `rufAt` fuel.

**Logical const contracts.**

| Layer | Required rule |
|---|---|
| Canonical clause lowering | Preserve each `SKlausel.needs/gives` (`ElementTief.lean:74/75`) in source order. Lower conjunctions to `P.requires` over entry parameters and `P.ensures` over `ErgCtx`, binding `result` to the actual result and parameters to entry values, not final mutable locals. The predicate must satisfy `ConstExpr`, have empty footprint and use only typed values and certified closed constants. `Expr` has no ordinary direct-call constructor: a closed predicate helper call may fold only with its `ConstCallCertificate`. A parameter-dependent helper requires a checked expression expansion with a generic result-equivalence **and failure-freedom** theorem over every admitted predicate environment, including its own requires/ensures; finite loop expansion must preserve typed intermediate checks and have an expansion-size limit. Otherwise retain a named refusal for that helper call. Ordinary `bindCall` normalization alone cannot place a block inside `P.requires`. Reject predicate-call cycles, including an ensures that calls its own function. Preserve exact scope, short-circuit behavior and ranges. |
| Call rule | Evaluate arguments once; check requires before entering the body and ensures after normal return, in exactly `rufAt` order. At each nested const call apply the same rule. False/unevaluable predicates refuse the initializer with function/clause/call-site identity. Never infer an ensures from a requires, body, test or successful type check; omitted clauses mean the existing true predicate only when absent in source. Supported pure `effects` are structural checks, not assumptions about behavior. `costs` must be preserved and its bound duty discharged for the concrete call or by a generic certificate; exceeding it is not the same as the compiler's work limit. |
| What is proved | A checked call proves its concrete requires and returned ensures, not the contract for every possible argument. An exported universally valid const contract additionally needs a Lean proof over **all** typed arguments satisfying requires, derived from the actual body and termination certificate. An unused declaration still gets full structural/purity/dependency validation; it is not a fabricated universal contract proof. Calls with runtime arguments stay refused until an explicit runtime instance and ordinary contract proof/lowering exist. Compile-time const calls themselves create no runtime call-log or cost entry. |
| Certificate API | **New** `ConstCallCertificate` records source function/instantiation ID, final environment identity, typed arguments, exact clauses/body derivation, value, termination/work bounds, G evaluation equation and successful predicate checks. Its checker is kernel-computable; prove a generic soundness theorem. Rust may propose values and schedules, but cannot choose clauses or assert ensures. Reuse table certificate membership only after this theorem; every array leaf must have the same checked call rule. |

**Generic type/order wrappers and checked instantiation.**

| Layer | Implementable model and proof design |
|---|---|
| Existing wrapper meaning | Add **new** `WrapperDecl` under `Kern/Syntax/`, keyed by resolved declaration identity, containing flags, typed payload list, optional representation and ordered distinct stage names. **New** `WrapperMeaning` relates the original `SItemTief.typeT` to this descriptor and its existing monomorphic representation. Linear/ghost wrappers map to a fresh `D.Marke`, preserving payload identity and `D.stufen`; a type-equal payload does not merge two marks. `order` names give the existing strict forward-stage rule, not a memory order or sorting comparator. Value wrappers retain nominal/opaque constructor-access evidence even when their represented `Ty` is equal. Multi-field values depend on C01's product rule; do not collapse them to one integer. Names such as `Duty(check)` resolve the declared check identity through C16, not an invented type variable. |
| Formal templates, explicitly new | Full parametric wrappers need a distinct binder/application rule. Proposed **new** `TemplateParam` has `type`, `constant` and `order` binders in a telescope; a constant's type is a `TypeTemplate` scoped over preceding binders. **New** `TypeTemplate` is a finite syntax with bound de Bruijn parameters, closed monomorphic types, bounded arrays, named wrapper application and C01 products when available. **New** `TemplateDecl` retains source ID, parameter kinds, flags, payload/representation templates, order template and source contract/body/measure templates of its associated instances. It contains syntax, never arbitrary Lean functions. **New** `Instantiation` supplies exactly one resolved type/typed closed value/finite distinct stage list per matching binder; dependent constant types are checked after preceding substitutions. Fully resolve actuals; no inferred defaults or unresolved placeholders. These definitions do not reinterpret existing `typeT` payloads. |
| Parser/export rule | Append **new** `STyp.app (name : List String) (args : List TemplateActual)` to `STyp`, and **new** `SItemTief.templateT` carrying explicit kinded binders and the existing wrapper declaration body. **New** `TemplateActual` distinguishes type/value/order syntax. Proposed surface spelling for owner review: `type W<type T, const N : u32, order S>([T; N]) order S;` and explicit applications `W<u8, 4, { raw, ready }>`; existing `type W(T)` continues to mean payload types. Extend `parseTyp`/`parseTypNach`, `parseTypTief`, equality, printing/round trips, `Aufloesung.loese`, `Oeffentlich.huelleZu`, width normalization and Stage-0 source traversals. This is a proposed canonical grammar extension, not an assertion that existing sources already contain this syntax. If the owner limits C17 to existing syntax, close existing checked wrappers and retain a precise refusal for genuinely parametric applications. |
| Checked monomorphisation | **New** `instantiateTemplate` substitutes capture-free through every type, bound/count, payload, contract, effect, body, stage reference and D1 measure; lower only the resulting closed declarations. **New** `InstantiationValid` checks kinds/arity, range/width/layout, unique stage labels, valid stage lookup/forward moves, visibility/opacity, fresh instantiated identity and resource use. Descriptor instantiation precedes G checking: `Akzeptiert`/`AkzeptiertX`, footprints, ghost restrictions, all cost and user-logic duties are rechecked for every emitted instance. No blanket “template checked once” bypass. Use a deterministic key `(source ID, normalized typed actuals)`; cache only certificates at that key. A checked finite instance closure accounts for all referenced dependencies, rejects growing/cyclic type expansion, and includes instances reached only by contracts/constants/arrays. Code sharing additionally needs an explicit representation/meaning isomorphism; identical layouts alone cannot merge opaque types, marks or witness identities. |
| Generic preservation theorem | Define **new** `TemplateMeaning` by structural interpretation under a kind-correct substitution, using existing monomorphic `Ty`/G and `WrapperMeaning`; it is not defined as successful execution of `instantiateTemplate`. Prove substitution identity/composition, alpha invariance, and **new** `instantiateTemplate_sound`: every successful checked instance has exactly that interpreted type/value representation, predicate truth, body outcomes, effects/resources, costs and measure values under all related environments/worlds. For ordered linear wrappers prove injective stage-name encoding and preservation/reflection of allowed forward moves, `nach` resources and unique ownership. Transport generated IDs through declaration embeddings; prove the instantiated source-to-G diagram commutes, then apply existing `gabbro_ziel` to the accepted monomorphic unit. A value equality theorem alone does not preserve contracts or linearity. |

Non-linear `order` currently has no canonical value-operation rule; do not assign
it numeric order, mutable typestate or erasable decoration by analogy. Recommended
language decision: order remains a protocol on linear wrappers, including generic
instances. Until decided, reject non-linear ordered wrappers explicitly (also at
unused declarations) instead of allowing `uAliase` to discard the words. If the
owner requests copyable staged values, that needs an explicit value/stage
constructor and transition semantics with a separate `Spec`/cost review; this
design does not pretend existing `Res.marke` proves that different feature.

**Stage-0 consumption and connected acceptance.** Replace `FunctionMeaning`'s
single-expression equality with exact original `FnSig`/`SAnw` provenance,
`ConstElaborates`, checked wrapper instantiations and the generic const-call
theorem. `Scopes.functionMeaning` must expose this stronger result. Update
`constantFunction(s)`, `evaluationClauses`, `safeConstantName`/`SafeHull`,
`compileTimeSafe` and `Source.compileTime` together: every body, signature,
predicate and type/count consumer must resolve to the checked canonical call
hull; absent names and cycle revisits are not certificates of success.

In `DependentScopes.nextCandidates`/`resolveCandidate`/`discoverScopes`, discovery
remains untrusted. Re-elaborate every original body/contract/instantiation with
the final alias/constant environment, check all concrete calls again and retain
the existing signature stability/full scalar-fold/permutation checks. Extend
`ConstantOrder.dependencyDeclarations` beyond signature/call edges to body free
constants, local types, clauses, bounds and instance actuals, respecting lexical
shadowing. Check one mixed dependency graph; reject cycles even in unused
constants/arrays/aliases. No self-supporting fixed point may certify its own
signature or contract. Move the canonical dependency/const certificates into
grammatik for reuse, rather than leave the only semantics in Stage 0.

Thread those facts through `ConstantScopes.scopeMeaning`, `ConstantMeaning`,
`ArrayConstants.ArrayMeaning`, `Correctness.Normalization`,
`Elaboration.elabWithScopes`/`elabU_scopes`, `Compiler.Compiled`,
`CanonicalSourceProgram`/`compile_source_program` and `IRBild.irBild_correct`.
The source-to-value theorem must connect the exact literal/array initializer
consumed by `lowerAllg` and existing `lowE_ok`/`lowFun_spec`, including signed,
multiword and zero-length values; no per-program witness replaces this link.
Runtime `elabU` may keep removing const functions only after every const use is
certified; a surviving runtime call is a named refusal. Once integrated, remove
the superseded expression-only evaluator/collector path, including the nested
array path. The runner needs no C17 change merely to execute folded literals.

**Goal theorem, Spec and rebuild impact.** This design adds canonical elaboration
and a pure sublanguage judgment over unchanged G, not a new hardware premise or
a change to `Ziel`/`NutzerPflicht(A)`. No semantic change to `Spec.lean` is intended;
compile-time contract checks apply to actual constant calls and do not assert
universal contracts or runtime termination. Generic instances use the existing
monomorphic guarantees. The implementation commit must describe the new source
meaning and explicitly state this absence of a goal-statement change. Recheck
`Zielsatz/Kern/Beweis.ziel_aus`, `Zielsatz/Atomar/BeweisAtomar.gabbro_ziel`, SC
transfer, idle-root/link embeddings and D1 measure transport; no new proof case
in these theorems should arise unless implementation changes shared syntax or
acceptance fields. Keep exactly `propext`, `Classical.choice`, `Quot.sound`.
Extend GabbroV's `GvBruecke` source/export provenance where its represented
fragment changes; do not restore the retired source runtime.

Kern/Elab modules, parser constructors/traversals and every `UKonstFn` consumer
require a coordinated grammar rebuild by its single owner, followed by affected
Stage-0 compilation and the Lean guardian/layout/axiom checks. The full template
parser extension needs the owner's syntax decision and coordination with the
single authorized rebuild batch; it is not covered by the pure-export exception
alone. Use the current two-slot/memory policy; no such check was run for this
document. Avoid an import cycle: descriptors/purity syntax precede semantics,
semantic soundness imports G, and parser derivations import those modules;
the kernel never imports the parser or Stage 0.

**Witness and refusal matrix.** Every generic theorem above needs a `_zeuge`
whose source derivation, purity, termination, clause checks, instantiation and
actual pipeline premises hold jointly. Include a signed multi-parameter block
with locals/assignment/nested branches/early return; constant capture and name
shadowing; a nested call with different caller/callee ranges; a pure function
with true requires/ensures used by both a dependent signature and nested array;
an empty/nonempty/nested traversal with an accumulator; bounded retry with both
success and explicit overflow behavior; and one template instantiated at two
integer widths/counts and two distinct protocol stage lists, preserving opaque
and mark identity. Require a connected source-to-IR witness for each admitted
slice, not just descriptor evaluation.

Negative witnesses: effect hidden in a callee/unselected branch, unknown or
duplicate function, fallthrough/missing return, illegal local mutation, overflow,
zero division, bad cast, false/unevaluable requires and ensures, predicate-call
cycle, unused malformed const declaration, forward dependency cycle through a
contract/signature/instance, array-only unsafe call, exhausted evaluation work,
unbounded/open traversal, recursive SCC without totality/depth proof, invalid
retry overflow, wrong generic kind/arity, unresolved actual, stage-name
collision/backward move, opaque construction outside visibility, lost/duplicated
linear payload and non-linear order. Refuse unsupported aggregates/builtins by
name until C01/C13 supplies their generic meaning. Register each new diagnostic
sentence and poison probe when implementation introduces its refusal code.

**Staging and effort (engineering person-days, not measured build time).**

| Slice, in implementation order | Estimate | Completion gate |
|---|---|---|
| Canonical pure loop-free blocks, source relation, evaluator soundness and Stage-0 literal/array bridge | 6–10 | Generic source-to-value theorem is consumed by the compiled pipeline; old collector retired |
| Logical contracts and final-scope dependency/certificate integration | 3–5 | Both false-clause refusals and nested/dependent positive cases certified |
| Bounded traversal/retry and work/termination proofs | 3–5 | Generic finite-loop/control proof and connected witnesses |
| Existing wrappers plus full explicit type/value/order instantiation and preservation | 6–10 | Owner syntax/order decisions, finite instance closure, resource and body preservation |
| D1 runtime decreases binding (unchanged estimate) | 2–4 | Existing `MassPflicht`/termination theorem connected |

Full C17: **20–34 person-days**; remainder beyond D1 measures: **18–30**,
replacing the preliminary 10–20 remainder. Existing-wrapper checking is the
first generic slice; full parametric syntax is separately gated, not a reason
to delay block/contract semantics. Do not also charge the old optional 1–2 days.
With all other D5 package estimates unchanged, the overall full C estimate
becomes **245–414 person-days** (previously 237–404). Shared C01/C13/ABI work
remains charged there. Critical path is canonical source relation and final-scope
certification, then loop/control proofs and the owner-approved template grammar;
limited Lean slots and the coordinated rebuild affect elapsed time. Commit each
compiling implementation step; no helper-only stage closes C17.

**Owner questions, with recommendations.** (1) Approve canonical pure G block
evaluation, concrete compile-time requires/ensures and bounded loops as above;
keep recursion separately gated. (2) Confirm existing wrapper payload lists are
not retroactively formal binders, and approve explicit kinded template/application
syntax if genuine parametric types are desired; otherwise scope the first
wrapper slice to existing syntax and retain the application refusal. (3) Keep
`order` restricted to linear protocols, including instantiated wrappers; ask for
a separate semantic decision before copyable staged values. (4) Treat evaluator
work caps as explicit compilation resource refusals, independent of source
`costs`, with no implicit language bound of 64. These decisions change source
admission/meaning and must be recorded by the owner before enabling those rules.

Validation: source/name/path inspection and `git diff --check` only. **Zero new
language cases compiled or proved; no Lean file edited and no build run.**

## IR-03 merge of master `6444b5cc3` (2026-11-01)

Master (IR-01 const bounds, IR-02 wide kernels and mixed64 compare, IR-05 `wordConstant` tag bounds, IR-07
signed64 `shift`, IR-08 traversal, IR-09 locks/atomics) is merged into the full-ABI branch. Master's scalar
helpers (`wordConstant`, `scalarCompareL`, `engTest`/`intervalTestL`, `tagPayloadC` with word constants) are
kept; they run on the complete ABI: `lowE_ok` is `ValueOk` (the scalar relations are taken through
`ValueAt.word`), literals stay on `constWords`, `tagPayloadC` additionally requires a one-word payload
(`valueWords (.int lo hi) = 1`), `eng_width` is derived from `scalarFits`. Master's probes `ShiftProbe`,
`IntervalProbe`, `MixedProbe`, `TagProben` and `Aggregat/Proben` are migrated to `LayIn`/`LayDis`/`WeltAt` over
`ValueAt`. `StatementCost`/`EarlyExit` stay out of the root until the counted copy/return/store transports exist.

Measured: 294-module `Stage0` + `Stage0.Haupt` closure rebuilt; `Nachpruefung.lean` 336 theorems on
`propext`/`Classical.choice`/`Quot.sound` only (6 axiom-free), no `sorry`; layout check passes; all 168 textual
programs of `stage0/proben-ir` compile and execute (or are refused with the expected text) with 0 mismatches.
`grammatik/` untouched. Merge commit: `05cfd542b`.

## IR-03 `strGet` over any scalar index range (2026-11-01)

`strGet` of a string of capacity `n >= 2` now accepts every one-word index range (`scalarFits lo hi`, signed or
unsigned), not only `[0, n)`. `strGetWideL` (`Frame/StringGetCode.lean`) places a zero sentinel word after the
string span, evaluates the index behind it and clamps it branch-free to `n + (i <u n) * (i - n)`
(`strGetClamp`); the selection `selectFrameSpan` copies the byte word (padding or sentinel word is zero), so an
index below zero or at least `n` yields the model's zero byte, exactly `strGetW`. Generic theorems
(`Frame/StringGetOk.lean`): `ult_clamp`, `clamp_word`, `strGetClamp_ok`, `strClamped_byte`, `strGetWide_ok`,
`strGet_ok` (moved there from `StringOps`, `strGetLongL` deleted). Textual program `str-get-wide` (indices
inside, negative, equal to and beyond the capacity; signed and unsigned index types).

Measured: closure rebuilt (231 modules), `Nachpruefung.lean` 340 theorems on the standard axioms only (6
axiom-free), layout check passes, 169/169 textual programs.

## IR-03 narrowing `strWeit` of long strings (2026-11-01)

`strWeit q` of a string of capacity `n >= 2` to a smaller maximum `q < n` (`strTakeL`, `Frame/StringTakeCode.lean`):
`q >= 2` keeps the byte words in place and rewrites only the length word to `min len q` branch-free
(`strTakeLenL`); `q = 1` packs `0` or `256 + first byte` (`strTakePackL`); `q = 0` writes the empty word. Generic
theorems (`Frame/StringTakeOk.lean`): `strTake_encode` (the narrowed encoding is the new length word followed
by the byte words `1 .. q`), `take_len_word`, `bin_exact_ok` (a binary instruction with the exact footprint
`Agree fp d (d + 1)`), `strTakeLen_ok`, `strTakePack_ok`, `strTake_ok`, and `strWeit_ok` (moved there from
`String.lean`, now covering widening and narrowing of long strings). The surface language never narrows
(`string longer than the maximum` is refused by the elaborator), so no textual program reaches this lowering;
the model witnesses `Aggregat/Proben` (`narrow_semantics_zeuge`, `narrow_lowered_zeuge`) check the semantics
and that the lowering accepts narrowing to 2, 1 and 0 (and the wide-index `strGet`).

Measured: closure rebuilt (294 modules reachable from `Stage0`, `Stage0.Haupt`), `Nachpruefung.lean` 346 theorems
on the standard axioms only (6 axiom-free), layout check passes, 169/169 textual programs.

## IR-03 packed-to-long widening and `strEq` between short and long strings (2026-11-01)

Two forms, verified together in one rebuild (the surface `==` of a short and a long string first widens the short
operand, so the equality could only be exercised after the widening compiled):

- `strWeit m` of a string of capacity at most one to a long capacity `m >= 2` (`strExpandL`,
  `Frame/StringExpandCode.lean`): the scratch head computes the length word `[w <> 0]` and the first byte
  `(w - 256) * [w <> 0]`, `copyWords 2` places them (exact footprint), `constWords` writes the `m - 1` zero words.
  `expand_words` (the widened encoding), `strExpand_ok`; `strWeit_ok` moved to `StringExpandOk.lean` and now covers
  widening of short and long strings and narrowing.
- `strEq` of a string of capacity at most one and a long string, in either operand order (`strEqMixedL`,
  `Frame/StringEqMixedCode.lean`): the long string's length word and first byte are packed (`0` or `256 + byte`) and
  compared with the packed word, AND-ed with `len < 2`, branch-free. `pack_word`, `mixedEq_word` (the word
  identity by cases on both byte lists), `strEqMixedC_ok`, `strEqMixed_ok` (`strEqW_comm` for the swapped order);
  `strEq_ok` dispatches short, mixed and long. `span_len_read`/`span_byte_read` give the length and first byte word
  of a long span (used by narrowing, packing and the mixed comparison).

Textual programs `str-widen-short` (length, byte and zero words of widened `""`/`"A"`) and `str-eq-mixed` (both
operand orders, equal and unequal, empty and one-byte strings against longer ones). Model witnesses in
`Aggregat/Proben`; the former refusal witness for `strWeit 2` of a one-byte string is now an acceptance witness.

Measured: closure rebuilt (223 modules after the edits), `Nachpruefung.lean` 353 theorems on the standard axioms only
(6 axiom-free), layout check passes, 171/171 textual programs.

## IR-03 handback state (2026-11-01)

Branch `t3/central-value-abi`: master `ae716338a` merged (`cd8cf4d5d`) and current master `2d54e78f2` merged
(`c6ce18d84`, fast-forwardable: `master` is an ancestor). After both merges the whole Stage0 closure rebuilds, all 207
textual regressions in `stage0/proben-ir` pass, `Nachpruefung` and `gabbro_ziel` stay on the three standard axioms,
the layout check is clean and no file under 500 lines on master reaches 500. The four old probes in `stage0/proben`
(`echo`, `hello`, `threads`, `upper`) refused with "main takes parameters" at that point (activated by IR-12, see above). Earlier:
master `6444b5cc3` merged (`05cfd542b`), then `strGet` over any scalar index range,
`strWeit` narrowing, `strWeit` of short to long strings and `strEq` between short and long strings (commits above).

Open (exact):

- `strLt` on long strings (and between short and long): the planned form is an unrolled backward fold over
  the padded key sequence `x_k = [k < len] * (1 + byte_k)` with `res := (x_k <u y_k) | ((x_k == y_k) & res)`; its
  correctness needs `bytesLt as bs = lexLt (keys as) (keys bs)` and a descending induction over the scan code. Refused
  by its guard until then.
- `strCat` of strings whose combined capacity exceeds one: needs the dynamic-offset word store of the second
  operand (`storeFrameSpan` per word, preceded by zero-filling the extension) and the sum of the length words.
  Refused by its guard.
- IR-08 `StatementCost.lean` (5498 lines) and `EarlyExit.lean` (807 lines) are still outside the `Stage0` root: they
  depend on scalar-only copy, return and store transports and are not migrated to the complete value ABI.
- Ordinary records (canonical-model prerequisite); `getBytes`/`putBytes`/`shift` at the eight-byte limit (IR-02/IR-06).
- Not reachable from the surface language, hence witnessed on the model only: `arrSet` of arrays of more than one
  element and `strWeit` narrowing (the elaborator refuses a string longer than the maximum).
- The 500-line rule: `Ausdruck.lean` (about 620 lines), `Satz.lean` and `Anweisung.lean` exceed it as they did before
  this lane; they are the `lowE`/`lowS` mutual definitions and have not been split.

### IR-09 bounded inventory (base ae716338a, 2026-11-01)

Read against canonical `Kern/Syntax`, G/GX and the thread machine,
`Parser/Elab/Uebersetze{,Allg3}`, and the actual Stage0 `lowS`/`lowB`/`lowEnd`,
`Sperre/*`, `Anweisung/Atomar`, `BildSatz` and `IRBild` paths. Here **compiled +
connected theorem** means the existing sequential simulation with its stated
premises; it never means the missing concurrent GX refinement is proved.

| Owned form/aspect | Status and exact boundary | Connected theorem / prerequisite |
|---|---|---|
| Stmt `locks` (exclusive) | Compiled + connected theorem for admitted return-free bodies, including nesting, reason dispatch and loop `leave`/`next` cleanup. `retFreiB = false` or a missing body emitter refuses via `lowFunE`: `uses a form outside the IR fragment`. | `locks_ok`, `retFreiB_istZ`, mutual `lowS_ok`/`lowB_ok`/`lowEnd_ok`, `lowFun_spec`, image theorem and `irBild_correct`. `SyncOK` allows only free/mine locks and zero waiters. |
| Shared lock acquisition / RCU observation | Refused: `shared lock without G form`; no mode-aware canonical source admission. | Model C10; existing exclusive lock sugar and separate RW lemmas do not establish shared source semantics. Out of this bounded implementation. |
| Stmt `publish` | Compiled + connected theorem for represented scalar atomic/global values and the exact declared payload; scalar global-store path. | `lowS_ok` publish branch and ordinary world-store proof; image chain preserves existing `SichtOK`/gate premises. Multiword payload/value transport needs IR-03/06; concurrent release/publication preservation needs the missing concurrent proof. |
| Block `awaits` | Compiled + connected theorem as a scalar acquiring load with the exact declared payload and a compilable continuation. | `awaits_head`/`awaits_ok` in `lowB_ok`; `SichtOK` remains required. Multiword representation: IR-03. Concurrent visibility: missing concurrent proof. |
| Endblock `awaits` | Compiled + connected theorem with the same scalar/payload domain. | `endAwaits_case` in `lowEnd_ok`, then function/image chain; same IR-03/concurrent prerequisites. |
| Block `exchange` | Compiled + connected theorem for represented numeric updates and compilable continuations; emitted CAS retry loop. Canonical updates other than supported guarded values refuse as `exchange update body other than guarded values without G form` (or the single-value variant). | `ex_tail`/`exch_head`/`exch_ok` in `lowB_ok`; sequential proof takes the successful CAS path. Failed CAS under interference: missing concurrent proof. Wider representation: IR-03. |
| Endblock `exchange` | Compiled + connected theorem in the same scalar domain. | `endExchange_case` in `lowEnd_ok`; same representation, frontend-update and interference boundaries. |
| TopLevel `atomT` / ordinary atomic reads | Compiled + connected theorem for zero-initialized Bool/numeric atomics whose range contains zero, with exact payload declarations. Device-observed atomics refuse as `atomic observed by a device without G form` (excluded device scope). Other represented types remain limited by frontend/IR-03. | Canonical atomic-global export, global load/store proofs, checked source provenance and image chain; G/GX ordering refinement remains missing. |
| TopLevel `lockT` | Compiled + connected theorem for supported declarations with literal rank and no unsupported declaration clauses; masks other than `irqs` refuse as `lock masks something but irqs: no G form`; other unsupported shapes: `lock without G form: NAME`. Arena protection refuses as `arena under a lock without G form`. | `uSperre`, canonical checker and `LaySync`/`SyncOK` lock-word layout. Concurrent masking/ownership refinement remains missing; no hardware masking claim follows from sequential lock code. |
| TopLevel `rcuT` / reclamation | Refused: `item without G form`. | Model C10: domain, observation, grace and reclamation semantics/admission/export, then IR-07 lifetime and concurrent IR proof. No missing isolated RCU emitter can close this boundary. |
| TopLevel `concT`, `start {}` roots / multiple image threads | Compiled + connected **individual-thread** theorems: roots are collected, deduplicated and spawned before main on separate stacks, using real runner OS threads. Parameterized roots refuse as `ir: a root takes parameters`; entry/reason/argument integration belongs to IR-12/03. | `spawnC_ok`, `bild_ok`/`bild_wurzel_ok`, `irBild_correct`, existing `CloneOK`. Missing: simultaneous-thread simulation against GX/thread machine (`ir_parallel`), not a missing spawn emitter. |
| Contended lock wait / wake | Missing proof: actual `nimmC` already emits failed-CAS, waiter increments, `futexC` WAIT and retry; `gibC` emits WAKE. Existing proofs cover neither foreign ownership nor nonzero waiters. The compiler does not reject these runtime states; its sequential theorem excludes them via `SyncOK`. | `Runner.IR.Kern.ans` is arbitrary; `Runner.Mach` special-cases clone/exit, **not futex**. No existing named assumption specifies futex waiting, wakeup or memory preservation. Do not manufacture one. Selected smallest step: prove the actual failed-acquisition prefix reaches the wait branch with all three lock words unchanged, before any syscall. |
| Structural/concurrent `ir_parallel` | Missing: no Stage0 theorem relating a multi-thread IR run to existing GX/thread-machine boundaries/interleavings, including atomic retries, lock interference and ordering. | Existing runner SC/TSO simulations relate IR to machine execution; individual `Star`/`AgreeW` results are not this source-concurrency theorem. No full concurrent form is counted complete here. |

This inventory changes no model, source admission, emitter, ABI or named
assumption. Existing scalar refusals remain explicit; no RCU/shared-lock work,
IR-03 migration, grammar rebuild or concurrent-completion claim is authorized
by the selected bounded step.

The bounded implementation adds `Sperre/Contended.nimm_contended` to the
existing lock proof import chain. For arbitrary real code/frame/lock memory
satisfying `LE`/`LS`, a nonzero owner different from `meW` makes the actual
`nimmC` reach instruction 22 (the wait branch). The failed CAS returns the
foreign owner in scratch slot four; owner, recursion count and waiter count
remain unchanged, as do scratch slots from five on. The theorem holds for
every existing `Kern` relation and stops before waiter bookkeeping or a syscall.
It introduces no futex contract and does not extend `locks_ok`'s `SyncOK` domain.

`ContendedProbe.nimm_contended_zeuge` jointly supplies encoded instruction
bytes, writable frame/lock memory and all execution premises: this thread is
1, owner is 2, count is 3 and there are already 5 waiters. Execution reaches
byte PC 352, retains all three lock words, returns owner 2 in the CAS-result
slot and preserves the protected frame word 77. This witness is imported by
the existing `Sperre/Proben` module.

Measured in this worktree's private `.claude/ir09/lib` overlay: 159 Stage0 and
12 runner dependency modules pass direct checks, including the mutual
statement/block/endblock dispatcher, `lowFun_spec`, `IRBild` and `Haupt`.
Seven axiom audits (new theorem and memory witness, `locks_ok`, `lowS_ok`,
`lowFun_spec`, `irBild_correct`, cached `gabbro_ziel`) report exactly
`propext`, `Classical.choice`, `Quot.sound`. Six existing textual
source-to-IR-to-assembly regressions pass: lock-reason-dispatch and
atomic-payload-lock (42), sperre and atomar (208), start-roots (23), faeden (2).
The RCU probe still refuses with `item without G form`. Layout passes for all
1478 Lean files; both new Lean files are below 500 lines. Every Lean invocation
used the capped slot-2 lock with `ELAN_TOOLCHAIN` removed; grammar artifacts
were reused, with no grammar build or full guardian. This closes only the
foreign-owner acquisition prefix: full WAIT/WAKE, interference, ordering and
`ir_parallel` remain open, and no additional source-form family is claimed.

### IR-09 contended WAIT/WAKE sequential facts (base 2d54e78f2, 2026-11-01)

The owner explicitly authorized a named OS binding premise for futex, following
`CloneOK`/`TorOK`. `Runner.IR.FutexOK spurious` now states exactly the return
properties used here: a returning WAIT sees a different low 32-bit word or is
classified by the explicit `spurious` relation; a successful WAKE returns a
count at most the requested `n`. Negative WAKE error returns are allowed.
Interruptions, mismatch/error returns and a value changed back before return
can be classified as spurious. There is no eventual-return, release, scheduling
or fairness premise, no hardware assumption, and no Lean postulate.

`futex_prepare`, `futex_entry` and `futex_return` simulate the actual request
setup and syscall. Memory changes during a blocking call are **separate,
explicit client premises** (`LS` resume state and stable lock-word invariant),
not consequences of `FutexOK`. In particular the current `AgreeK` frame keeps
code, non-scratch frame words and the world unchanged across that boundary;
it is not the missing general source-world interference relation.

`add_waiters` proves the actual seven-instruction successful counter-CAS
iteration without interference inside that iteration. `LockInv` describes
stable free/held lock boundaries, including foreign owners and nonzero waiters,
with recursion and waiter counts below `2^62`. Its counter proofs require room
before increment and a registered waiter before decrement. `nimm_wait_entry` registers a waiter and reaches WAIT;
`nimm_wait_retry` consumes a supplied return, unregisters that waiter and jumps
to instruction **17**, the actual acquisition-CAS retry. `nimm_retry` either
returns to WAIT with the foreign owner intact or acquires a free lock.
`nimm_retry_acquired` finishes any finite actual retry history whose supplied
resume state is free; it does not prove eventual acquisition.

`gib_release` centralizes the last-release prefix through the waiter test.
`gib_waiters_entry` proves the nonzero-waiter branch reaches WAKE-one;
`gib_waiters_return` finishes it under an explicit response/frame premise and
leaves owner/count zero with the same waiter count. Returning WAITs remove their
own counter entries; WAKE itself does not decrement the counter.
`LockOK`/`SyncOK` can now specify waiter counts, and their frame/call/monotonicity
lemmas preserve those exact counts. Their defaults and the existing `locks_ok`
and source-to-image theorem domains still require zero waiters and free/mine
ownership, with all existing guarantees retained.

`WaitProbe` supplies encoded instruction bytes and writable real lock/frame
memory for acquisition after an explicit foreign release, a spurious unchanged
WAIT followed by a failed retry, WAKE with five waiters, and nonzero-waiter
`SyncOK` inherited by a callee. These are individual-thread `Star` facts.
Concurrent `ir_parallel`, interference inside counter CAS loops, general world
updates while blocked, ordering and progress remain outside this bounded proof;
no additional source-form family is counted complete.

The `lock-wait-wake` source regression uses bounded long critical sections on
two real assembly-runner OS threads. It complements the short `sperre` probe:
tracing the long probe exercises successful sleeping WAIT returns and WAKE-one,
while the short probe also exercises mismatch returns. This runtime evidence
is separate from the sequential component proofs and does not close `ir_parallel`.

## IR-02 wide integer operators in `lowE` (2026-11-01)

The verified wide kernels (`Arithmetik/Wide/*`) are now emitted by the actual expression lowering for integer
types of any width, with the generic theorem connected through `lowE_ok`, `lowE_top` and the equations. The
existing one-word emitters remain the fast path under their original guards; every case they refused is now
assembled from the shared operand placement instead of `none`.

- **Code below the proofs.** The 52 kernel code definitions moved unchanged into
  `Aggregat/WideInt/KernelCode.lean` (imports only `Hilfen`), because the proof modules import `Quant.Frame` and
  hence `Ausdruck.lean`. `Literal/Word` and `Literal/Eng` import the lemmas they use instead of a probe module,
  which removed the import path `Literal/Word -> Signed/Probe -> Divide/Probe -> BildLese -> ... -> Satz`.
- **Placement (`WideInt/Place.lean`).** First operand lowered at `d` and extended in place to the common width `k`
  (`wideExtendC`: sign extension exactly when the operand interval has a negative lower bound, zero extension
  otherwise), second operand lowered at `d + k` and extended, then the kernel at `d`; the result is the first
  `integerWords` limbs of the modular result. Widths: `arithWords` (operands and result), `signedArithWords`
  (`signedWords`: one sign limb more for nonnegative intervals), `compareWords` (`max signedWords + 1`, so the
  difference fits), `shiftWords` (also `h2 / 64 + 1`, so the count is below `64 k`; the count keeps its own limbs),
  `engWords`.
- **Generic proofs.** `Operands.wideBinary_ok` / `wideUnary_ok` prove the placement once against a kernel contract
  on actual memory with the exact footprint `Agree fp d K`; `Ring` (add, sub, mul, neg, and, or, xor), `Divide`
  (div, rem, sdiv, srem; the remainder is copied down by `withCopy_run`), `Compare` (lt, le by the swapped order and
  an `xor 1` instruction, eq), `Shift` (shl, shr with `shiftStages_bounds`) and `Eng` supply the contracts from
  the kernels' execution theorems. `lowE_ok` dispatches to them; `IntegerOps` now takes the operands as `ValueOk`
  hypotheses quantified over the destination slot.
- **sdiv/srem minimum / -1.** The model's result interval is `+-betragMax`, which holds the one out-of-range
  quotient; the kernel's modular limbs at the common width are its canonical encoding and the result type has
  the extra limb. No refusal is needed (`wide-sdiv-min`: `-2^127 / -1 = 2^127`).
- **Removed refusals:** `inUE`/`inWE`/`nichtMin` for div, rem, sdiv, srem, band, bor, bxor, shr; the one-word
  result and count guard of shl (now only the fast path); `scalarFits` for lt, le, eq and eng.
- **Counted layer.** `ExprCost.add` (IR-08's counted statement layer) covers only the one-word case and now says
  so with a `narrow` premise instead of `cases` on the wide branch; no counted wide cost exists.

Textual source -> IR -> assembly programs (`stage0/proben-ir/wide-*`): ring on constants, squares through a
64-bit parameter, unsigned and signed division of constants, order and negation, bit operators and shifts, plus
runtime-operand programs `wide-vars` (identities and order of 101-bit signed parameters), `wide-sdiv` (quotient and
remainder identity, exact quotient), `wide-sdiv-min` and `wide-bitvars` (bit identities, shifts by runtime counts,
division). `eng` has no textual form over a wide input (only the `update` body of an atomic exchange produces
it), so its acceptance witness is `WideInt/Proben.lowE_wide_eng_zeuge`.

Open (exact): the statement `narrow x to lo .. hi` of a value wider than 64 bits is still refused
(`uses a form outside the IR fragment`; its lowering is the scalar interval test, not `Expr.eng`); counted
(`StatementCost`/`EarlyExit`) wide costs.

Source-to-G export lane, step 1 (2026-11-01): fast-forwardable `24fcdda28992fba93537d3260d1b56dbc8b928b2` includes master `19947e92b`; ancestry checked. Complete 318-module closure, 252/252 IR regressions (63 refusals), standard axioms, clean layout/size checks. I/O 3/4: `upper` still expects the retired implicit `io.ein`/`io.aus` adapter; its source has no read/write gate, so the emitted image correctly exits without output. No grammar rebuild or model change.

Source-to-G export lane, batch 2 (2026-11-01), based on the checked step-1 merge
`24fcdda28992fba93537d3260d1b56dbc8b928b2` / documentation checkpoint `c6c4a6350`:
bounded A10 constant counts/ranks, checked scalar initializer G values and executable
zero expansions; A13 numeric slot membership and declared optional-self reach; A14
single-child tree filters/traversal and fixed lexical array INDEX domains; A16 all six
string comparisons. A17 is a typed same-region reference comparison bridge with genuine
value witnesses, not a completed source/provider package. Generic export/meaning/scope
and footprint laws are in ExportRelations/Quantifiers/Arrays/Comparisons, with seven
character-pinned source fixtures in ExportWitnesses2. `exported_batch2_ir_correct` and
its accepted nested-array image `_zeuge` connect the production compiler and
`compile_source_program` to `irBild_correct` without changing inherited memory/view,
call-depth or budget premises. Spec, G semantics and checker rules are unchanged.

The actual runner exposed the existing zero-filled image world: new nonzero scalar
initializer expressions preserve their canonical G values but are now precisely refused
by `Frontend.checkInitializers`, whose certificate is retained in Compiled and
CanonicalSourceProgram. No initialization is silently invented. The reach regression
initializes every relevant option edge explicitly, including its None end. Chain-field
binding, queue records, branching/consuming tree cases and reference provider realization
remain precise refusals. Wide array elements and numeric membership use the inherited
full-value ABI; no scalar path, width-one refusal or second execution backend was added.

Measured: 284/284 textual IR probes (81 intended refusals; 32 new probes), using actual
Lean `irBild` and the assembly runner; I/O 3/4, with the unchanged legacy `upper` adapter
expectation reported separately as at step 1. This branch does not contain the later
independent master rewrite of that fixture. The full Stage0 closure has 319 distinct
green modules: 317 before the host reboot, then all 30 affected source consumers and
15 initializer-guard dependents, including Stage0.Haupt and Nachpruefung. The final two
checks took 156.67 s and 479.90 s including slot waits; maximum Stage0 module RSS across
the closure was 4,406,784 KiB. The complete grammar build passed (2345 jobs); the final
110-module affected dependency batch took 1841.55 s including waits, peak cgroup memory
4,827,222,016 bytes, maximum module RSS 3,515,604 KiB. The final cached guardian grammar
build took 0.79 s. Every run used a no-swap memory scope, each Stage0 Lean check used
slot 1 with -j1/-DElab.async=false/-M4608 and a 5 GiB cap; grammar scopes measured available
memory after acquiring the same lock and reserved 2 GiB for the host.

The axiom audit found 13 goal statements (gabbro_ziel exactly the standard three), 434
Stage0/export statements on standard axioms and six axiom-free declarations. Static
check: 1452 Lean files, zero violations; after staging, layout checks all 1551 Lean files
with no folder over 20 entries. No master file previously below 500 lines reached 500;
Nachpruefung remains 499 lines. The Lean guardian uses its actual model/certificate/
coverage/runner stages plus the owner-required direct Stage0 closure and actual irBild
regressions; the cached native Stage0 compiler executable was not rebuilt. Logs and
resource metrics remain in ignored arbeitsprotokoll/export-work/.

All remaining Lean guardian stages passed: 36 certificates, generator coverage
(62,564 valid programs and 696 single-fault refusals), runner build/axioms and 20,023
CPU checks with zero differences. The resource-aware guardian result is red only for
the legacy upper I/O fixture; the direct axiom audit passed after correcting the
controller's parsing of wrapped lists, without repeating Lean checks.
### IR-09 catch-up through IR-03, IR-02 and IR-12 (2026-11-01)

The lane first merged `1652a7d0c` as `63dc7af56`, then caught master through
`19947e92b`. The complete-value ABI is retained: lock frame preservation uses
`ValueAt` and parameter/context word counts, with no scalar ABI restored.
The nonzero-reservation byte witness was ported to complete value spans and
cell-span disjointness and connected to the existing byte probes/audit.

The current connected closure has 324 Stage0 and 32 Runner modules. All were
checked in the private overlay; 283 affected Stage0 modules were rechecked for
the later master updates, including `Stage0`, `Stage0.Haupt` and
`Nachpruefung`. Four additional Runner modules (generator dependencies, main
and audit) pass. The audits report 413 Stage0 and 14 Runner assertions with no
foreign axioms; cached `gabbro_ziel` has exactly `propext`, `Classical.choice`,
`Quot.sound`. Grammar sources/artifacts were not rebuilt or changed.

All 219 standard textual IR probes pass: 174 emitted images execute with the
expected exit and 45 refusals have the expected text. The old I/O probes
`hello`, `echo`, `threads` now pass after the inherited IR-12 activation.
`upper` compiles and exits zero with empty output instead of `ABC`, matching
the master limitation documented above: its retired driver's implicit I/O
convention has no image binding. No new convention is assumed here.
The actual two-thread `lock-wait-wake` image exits 128; its trace has eight
successful sleeping WAIT returns and ten WAKE-one calls (eight return one,
two return zero). This evidence does not establish `ir_parallel`.

The forbidden-proof scan passes for 1448 Lean files and layout for 1547;
no master Lean file below 500 lines crosses that limit. Every Lean invocation
uses slot 1, the prescribed 4G/5G/no-swap scope, an unset `ELAN_TOOLCHAIN` and
`-j1 -DElab.async=false -M4608`. No full guardian or push is claimed.
An additional all-files check exposed old ABI type errors in the unimported
5498-line `Schleifen/StatementCost.lean` (including the `retWhyC` arity), then
ended with a Lean memory exception at the fixed cap. That separate cost module
is unchanged and outside the connected closure; it is not claimed green.
IR-09's concurrent coverage boundary remains the inventory's open
`ir_parallel`, ordering/interference, shared-lock and RCU work.

Fast-forwardable IR-09 integration checkpoint: `2c5226333` (master `19947e92b` is an ancestor, checked).

### IR-09 first structural concurrent refinement step (2026-11-01)

`ir_parallel` must map **every** finite `Runner.Mach.Tr M actI` of the
existing IR request machine (OS-thread starts from `cloneReq`, futex requests, reads/writes/CAS,
and the SC/TSO memory states) to a `RufErreichbarGX` run. The relation needs a
thread/root/stack map and per-thread code/continuation, complete `EnvAt`/`Kopf`
values, source call log, open-lock trace and remaining budgets; the common memory relation must
agree on the source carriers visible at each boundary. A finite IR prefix may
stutter in GX during scratch computation, failed CAS, waiter registration,
WAIT/WAKE and retry. A successful lock acquisition/release must match the
structured `RufSchrittG.dannLocks`/release boundary; a successful source atomic
operation must match its GX leaf with the observed old value and exact update.
Other-thread steps preserve private frames and stable non-atomic carriers;
shared atomics are presented through GX's existing `Tg` relation, never frozen
by a global `WeltAt` equality. TSO buffer drains and publication/acquisition
must be connected to the existing W ordering/visibility facts, not inferred
from the single-thread successful-CAS path. A pending WAIT is a suspended
request continuation, allowing other `Tr` threads to run; a returning syscall
alone supplies no scheduling or eventual-return claim.

Reuse the connected `Sim`/`Reach`/return cases and IR-03 complete-value ABI,
`locks_ok` and the contended `LS`/`LockInv` WAIT/retry/WAKE components,
`ex_tail`/`exch_ok`/`awaits_ok` and their payload/visibility premises, and
`spawnC_ok`/image-root setup. Their existing sequential statements remain
unchanged. In particular `SyncOK`'s free/mine condition is a local entry
condition, not a global concurrent invariant: foreign-owned locks require
`LockInv`, ownership from GX's open-lock traces and separate transient protocol
states between machine instructions. `AgreeK` footprints compose the private
frame rely; source stable-carrier preservation reuses `stabilS_relyX`,
`gx_aussen`, and `zielInvSA_schrittGX` from `Speichermodell/Atomar/AtomarLauf`.
This relation must be maintained at request-continuation granularity
(`Res IR.T` under `actI`), since other threads can run between the loads and
CAS of one IR instruction. Neither `Star` nor one complete `Sim` execution
can be treated as atomic; the existing existential single-thread simulations
are ingredients, not a backward refinement for arbitrary concurrent runs.

Assumptions remain the existing checked source/admission, user duties and
oracle/binding premises (including `CloneOK`, `TorOK`, exact layout, memory
permissions, stack/entry and visibility conditions), the existing runner
SC/TSO refinement premises and the explicitly named `FutexOK spurious` OS
binding premise. No fairness, eventual acquisition, scheduler behavior,
unchanged shared memory during WAIT or extra hardware premise is added.
Footprint preservation and counter-CAS retry/linearization are proof
obligations, not extra named assumptions. `FutexOK` must be applied to the
actual concurrent memory-answer relation at completion; its present sequential
instance does not itself establish this bridge.

The first component is `AgreeK.foreign_frame`: a foreign lock/scratch footprint
preserves permissions and every word/validity obligation of a disjoint local
`EnvAt`, with either address ordering permitted. The witness uses a three-word
array in one frame and real changed scratch/lock words in another. This is a
rely/guarantee frame lemma, not the full `ir_parallel` theorem; arbitrary shared
world updates, concurrent atomic retries, ownership/ordering and transient
lock-state refinement remain open. No new source-form completion is claimed.

Measured for this component: `Interference`, `Sperre.Proben`, `Stage0` and
`Nachpruefung` pass capped direct checks. The generic word/frame lemmas need
only `propext` and `Quot.sound`; the joint witness uses the three standard
axioms. The Stage0 audit now has 416 assertions with no foreign axioms or
duplicate entries. The import closure gains one Stage0 module (325 total).
The new file is 86 lines and the audit is 485; no existing sub-500-line file
crosses 500. The forbidden-proof scan passes for 1449 files, and layout passes
for 1548 tracked Lean files with at most 20 entries per folder. Source emission
is unchanged, so the textual/runner measurements above remain the measured
compiler behavior, including the inherited `upper` limitation. This completes
only the first frame component; the full concurrent refinement remains open.

### IR-10 complete-value calls and entry snapshots

Function frames are now computed once from the source signature, the complete
postcondition snapshot spans and loop-counter depth. The entry prelude first
relocates original parameters above the snapshot prefix, captures every required
entry span with the shared world-span loader, then establishes separate lexical
body parameters. The postcondition reads the preserved original parameters.
Normal returns keep the full result internal until guard 102 passes, then copy
the complete result into the canonical caller area, publish the status after
the shared normal/reason span, and maintain ReturnMirror. Reasons bypass ensures
as specified by the existing model. IR-12 startScratch stays above the canonical
parameter/result/status area.

EntrySnapshots.complete_at turns snapshots plus original parameters into an
ordinary typed EnvAt. lowEnsAt_ok therefore composes the same full-value
arithmetic/comparison kernels as lowE_ok, without a second scalar ABI or a
width-one gate. entryFrame_run and publishResult_run execute the actual entry
and return instructions; their joint witnesses use two distinct two-word old
values, a two-word parameter, and a three-word published result. Existing
copyValue_run/copyResult_run, constWords/constWords_ok, contextWords, returnWords,
ResultAt/ResultOk and ReturnMirror remain the common representation contracts.

Connected source forms are fnref, oldG, literal-indexed oldS, call/callInd,
ret/retWhy, bindCall/bindCallInd/bindCallElse, multiple old occurrences and
multiword parameters/results. The proof chain is lowE_ok/lowEnsAt_ok through
lowS_ok/lowB_ok/lowEnd_ok, lowFun_spec, bild_ok_u and Gabbro.Stage0.irBild_correct.

| IR-10 forms | Connected lowering theorem |
|---|---|
| Function declarations and recursion/depth | `lowFun_spec` |
| `fnref` | `fnref_ok` through `lowE_ok` |
| `oldG`, literal `oldS`, multiple complete snapshots | `entryIndex_ok`, `entryFrame_run`, `lowEnsAt_ok`, `lowEns_ok` |
| `call`, `callInd` | `callC_ok` / `lowInd_ok`, `indStmt_ok` |
| `ret`, `retWhy` | `ret_ok` / `retWhy_ok`, with `publishResult_run` for normal returns |
| `bindCall`, `bindCallInd`, `bindCallElse` (blocks and end blocks) | `blockCall_case` / `endCall_case`, `indBind_ok`, `callElse_ok` |
| Multiword arguments/results | Shared `lowA_ok`, `copyResult_run`, `receive_run`, `ResultAt` / `ResultOk` throughout the same chain |

In typed G, closed oldS indices support literals, widening, addition, subtraction,
multiplication and negation; the computed-index witness is kernel checked. The
frozen source exporter still refuses arithmetic indices with `index without G form`
before IR lowering (`old-slot-computed` measures that boundary). These computed
model cases are not counted as connected source cases. Parameter/result/current-state
dependent indices also still refuse because capture planning currently requires a
source-independent cell list. General result/current-state dependencies must select
the entry cell using the index evaluated at exit; naive entry evaluation is unsound.
Old-containing expressions outside the supported
arithmetic/Boolean postcondition fragment also refuse. Functions owing
invariant-return checks and indirect reason channels keep their explicit
existing gates; these belong to the separate invariant/interface packages.
No grammar or model semantics changed.

The already unimported IR-08 StatementCost/EarlyExit modules retain their separately
open ABI migration; they are outside the measured connected Stage-0 closure.

Measured in the IR-10 worktree: the complete 356-module Stage0/Stage0.Haupt/
Nachpruefung/Runner.Haupt closure passes direct sequential checks with private
artifact overlays. All 238 source regressions pass: 188 native IR executions,
four native I/O executions, and 46 expected compiler refusals. This includes
multiple distinct snapshots, equal-low/different-high snapshot values, normal
and failed multiword postconditions, indirect two-word calls/results, and reason
returns bypassing false ensures. The computed-source-index refusal is reported
separately from the successfully checked computed-G-index witness.

All 438 axiom audits pass (431 standard-axiom subsets and seven axiom-free
declarations); gabbro_ziel has exactly propext, Classical.choice and Quot.sound.
The layout check passes for all 1,559 tracked Lean files; no folder exceeds
20 entries, and no changed Lean file below 500 lines on master reaches 500.
Nachpruefung remains at 493 lines. No grammar source or model semantics changed;
the grammar was not rebuilt.

### Source-to-G export lane: IR-10 integration (2026-11-01)

Merged master `94fd5de41` into the batch-2 checkpoint `d75e6f754`. The complete-value
entry snapshots, call/return protocol and recursive Boolean postconditions from
IR-10 retain the source export bridge, initializer refusal and all additional
export audit entries. Imports and the lane histories are combined; no model or
grammar source changed during this catch-up, and grammar artifacts were reused.

Measured: all 141 affected modules (140 Stage0, including Stage0.Haupt and
Nachpruefung, plus Runner.IR.Futex) pass in dependency order in a private artifact
overlay. All 300 textual IR probes pass: 218 native image executions and 82 exact
expected refusals. All four native I/O probes pass, including master's rewritten
upper fixture. All 475 Stage0/export axiom audits pass (468 standard-axiom subsets,
seven axiom-free declarations), as do the 13 cached-model goal audits;
gabbro_ziel has exactly propext, Classical.choice and Quot.sound. The forbidden
proof scan passes for 1,471 files and layout for 1,570 tracked Lean files. No new
500-line violation; Nachpruefung is 498 lines. Every Lean invocation uses slot 1,
-j1/-DElab.async=false/-M4608 and a 4G/5G/no-swap scope. No grammar rebuild or push.
