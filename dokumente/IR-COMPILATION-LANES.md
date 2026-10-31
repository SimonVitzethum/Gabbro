# Gabbro-to-IR compilation lanes

**RESUMED (2026-10-31).** The owner authorized seven rounds with exactly two parallel Sol 6.1
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

| Round | Agent A | Agent B |
|---|---|---|
| 1 | IR-01 frontend and type coverage | IR-03 shared value representation and ABI |
| 2 | IR-02 integers and Booleans | IR-04 floating point |
| 3 | IR-05 options, sums and dispatch | IR-06 memory and references |
| 4 | IR-07 regions and ownership | IR-10 functions and contracts |
| 5 | IR-08 control and source budgets | IR-09 concurrency and RCU |
| 6 | IR-11 foreign calls and ASM bodies | IR-13 formats and generated constructs |
| 7 | IR-12 profiles and images | IR-14 compiler integration |

Start a round after integrating and checking its prerequisites. Each lane must implement its real compiler
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
source lowering. These waves do not raise the two-agent or one-global-Lean-check limits.

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
back to baseline extraction cannot bypass the check. Original runtime declarations remain present.
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
