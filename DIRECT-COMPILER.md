# Direct compiler: Lean model, optimisation, Rust and full translation validation

This is the central work order and progress record for the direct Gabbro-to-x86-64
compiler. Created on 2026-10-01 at Simon's request. Update it at every substantive
reviewed integration, changed scope, proved obligation, rejection or measured
milestone. Task files and committed reports contain the detailed evidence; this
record must distinguish completed proofs from running work and planned work.

The [detailed compiler design](DIRECT-COMPILER-DESIGN.md) specifies the planned instruction forms, invariant-derived optimisation rules, hardware scope and fast compilation/validation architecture. These are design requirements; the ledger below records implementation and proof status. <!-- x86-detailed-design -->

The [complete planned Lean optimiser specification](grammatik/OPTIMIZER.md) describes the shared IR, optimisation rules, invariant/effect premises, certificates, cost/concurrency guarantees, fast compilation and the proposed friend contributor handoff. It is a specification; the implementation and full validation chain remain OPEN. <!-- x86-optimizer-design -->

## Intended result

Compile Gabbro directly to x86-64 machine bytes, including linking, relocations,
entries and required runtime code. The selected validation route replaces the
C11-validation work order. The existing C backend remains operational during
implementation. Nothing here claims that the direct backend already emits a
fully validated executable.

First model and prove the relevant semantics, checks, compilation interfaces and
optimisations in **Lean 4**. Then implement the corresponding compiler, optimiser,
encoder, image construction and certificate production in **Rust**. Rust output
is checked by the Lean validation path: an emitter's annotations or certificates
are evidence to verify, never trusted conclusions.

The end condition is **generic full translation validation from the entire Gabbro
source text to the final executed binary bytes**, for every admitted program.
Acceptance must be derived from the source-computed full unit and duties, checked
optimisation/lowering steps, final relocated decoded instructions, actual loaded
mapping and all reachable executed bodies. No rules for particular examples or
function names. A mnemonic list, encode/decode round-trip, isolated helper or an
assumed simulation relation does not establish this end condition.

## Optimisation requirements

The initial package targets an **`-O3`-like optimisation scope**:

- Constant and copy propagation, dead-code elimination and common-subexpression elimination.
- Selective inlining with preservation of source call/return logs and contracts.
- Register allocation, private spills and peephole instruction selection.
- Loop-invariant motion and bounded unrolling.
- Selective SIMD after its generic source/target correspondence is proved.

Additional transformations should use what Gabbro actually proves: ranges,
regions, disjoint ownership, race freedom, stable protected memory and invariants
at their guaranteed locations. Examples are redundant-check removal, integer
strength reduction, alias separation and protected-load reuse. A fact at entry
cannot silently become a fact inside a writer or held section. Shared-memory
stability requires the actual global discipline, not a local token alone.

Every admitted optimisation must preserve values, faults, memory observations,
IEEE behaviour and control state, contracts, call logs, concurrent behaviour,
progress and the claimed budget/time bounds. Source budget accounting, target
machine work and hardware timing are separate proof obligations. SIMD and other
transformations stay refused where these obligations are unproved. Comparable
performance is a measurement target; no equivalence to GCC/Clang `-O3` is claimed.

## Lean-first sequence and remaining closure

1. Shared x86 vocabulary, modular integers/flags and actual permission-checked byte memory.
2. Instruction execution, independent byte decoder/encoder, checked images and relocations.
3. One source-linked typed IR, full source-computed units/duties and checked lowering.
4. Generic local/CFG optimisation validation, including invariant-derived rules.
5. Per-access target execution and x86-TSO refinement into existing W/GX concurrency.
6. Stack/ABI, entries, regions, runtime, binding bodies and all reachable executable code.
7. IEEE/control-state correspondence, source budget accounting and target work/time transfer.
8. Generic closing validator soundness, finite/infinite execution coverage, witnesses and negative probes.
9. Rust implementation of the reviewed Lean interfaces, then full integrated validation and performance measurement.

This is an implementation sequence with parallel independent modules, not a
claim that steps 1–8 are complete. W/GX and `gabbro_ziel` supply the existing
source-side concurrency framework; the actual target refinement is still required.
Aligned/narrow accesses, tearing, LOCK/RMW, fences, retries and access grouping need
proved correspondence. Enabledness must not be advertised as fairness or eventual
completion. No memory-safety, race, contract, cost or lock guarantee is weakened.

OS access, runtime and binding contracts are user logic with implementation proofs.
Only named silicon, device and timing behaviour belongs to hardware assumptions.
All executed support bytes must be covered, including any unavoidable handwritten
entry code. File offsets, virtual addresses, load bias and relocation operands must
be checked against the final image and executed mapping.

The stopped Rust codec lane 280 retains its draft. Existing unwired Rust vocabulary
is historical groundwork. Further Rust backend work waits for the relevant reviewed
Lean models; a whole source-to-final-byte acceptance theorem remains **OPEN**.

## Agent and review workflow

Use local isolated OpenCode Go `opencode-go/muse-spark-1.3-contributor` authors and
independent reviewers, with **at most 20 active model processes in total**. The
same cap includes repairs and reviews. Lean builds use the global queued wrappers.

An independent reviewer receives a clean committed candidate snapshot pinned by
its full commit hash, the task and actual check output. It records ACCEPT or
concrete REPAIR findings. Repairs return to the author and invalidate the previous
review. Integration requires the exact-candidate verdict, a green local build and
the unchanged standard axiom set of `gabbro_ziel`:
`propext`, `Classical.choice`, `Quot.sound`. Source-syntax claims need jointly
inhabited non-degenerate witnesses. No `sorry`, admitted theorem or new axiom.

The coordinator performs scheduling, mechanical transfer, build gates and this
ledger. Semantic review by the coordinator is a fallback after demonstrated agent
blockage. Failed integration checks return to agents; they never become automatic
acceptance. Completed clones are removed only after checked integration; reports,
review evidence and tasks remain in Git.

## Current work ledger

<!-- X86-PROGRESS:BEGIN -->
Last ledger refresh: **2026-10-01 11:26 UTC**. This is an operational snapshot, not a proof of the full chain.

| Owner | Work | State | Independent reviewer | Evidence |
|---|---|---|---|---|
| 269 | Emitter scope inventory | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-269.md) |
| 270 | Integer and flag semantics | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-270.md) |
| 271 | Byte memory semantics | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-271.md) |
| 272 | Pilot instruction execution | Merged after review/checks | 296: Merged after review/checks | [report](messung/muse/MUSE-REPORT-272.md) |
| 273 | Rust target vocabulary | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-273.md) |
| 274 | TSO to existing concurrency model | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-274.md) |
| 275 | SSA and optimisation validation architecture | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-275.md) |
| 276 | Final image ABI and loader contract | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-276.md) |
| 277 | Generic source and user-duty bridge | Merged after review/checks | Historical coordinator review; see report | [report](messung/muse/MUSE-REPORT-277.md) |
| 278 | Floating point and cost preservation | Merged after review/checks | 295: Merged after review/checks | [report](messung/muse/MUSE-REPORT-278.md) |
| 279 | Pilot byte codec and generic round-trip | Merged after review/checks | 297: Merged after review/checks | [report](messung/muse/MUSE-REPORT-279.md) |
| 280 | Pilot Rust encoder and decoder | Stopped: Lean first; draft retained | Historical coordinator review; see report | [task](lanes/280.md) |
| 281 | Independent foundation and byte-contract review | Merged after review/checks | 295: Merged after review/checks | [report](messung/muse/MUSE-REPORT-281.md) |
| 282 | Integer families beyond the pilot | Merged after review/checks | 298: Merged after review/checks | [report](messung/muse/MUSE-REPORT-282.md) |
| 283 | Checked byte image and loaded memory | Merged after review/checks | 299: Merged after review/checks | [report](messung/muse/MUSE-REPORT-283.md) |
| 284 | Executable target TSO over real byte memory | Merged after review/checks | 300: Merged after review/checks | [report](messung/muse/MUSE-REPORT-284.md) |
| 285 | Mathematical carry and signed-overflow characterisation | Merged after review/checks | 301: Merged after review/checks | [report](messung/muse/MUSE-REPORT-285.md) |
| 286 | Width-aware IEEE target data and f32 bridge evidence | Merged after review/checks | 302: Merged after review/checks | [report](messung/muse/MUSE-REPORT-286.md) |
| 287 | One typed IR and source-linked lowering foundation | Agent working | 303: scheduled | [task](lanes/287.md) |
| 288 | Invariant-derived optimisation on actual source semantics | Merged after review/checks | 304: Merged after review/checks | [report](messung/muse/MUSE-REPORT-288.md) |
| 289 | Disjoint byte-memory commutation | Merged after review/checks | 305: Merged after review/checks | [report](messung/muse/MUSE-REPORT-289.md) |
| 290 | Packed integer lane model for future SIMD | Merged after review/checks | 306: Merged after review/checks | [report](messung/muse/MUSE-REPORT-290.md) |
| 291 | Checked relocation arithmetic and byte patching | Merged after review/checks | 307: Merged after review/checks | [report](messung/muse/MUSE-REPORT-291.md) |
| 292 | Independent source and invariant trust-boundary review | Merged after review/checks | 308: Merged after review/checks | [report](messung/muse/MUSE-REPORT-292.md) |
| 293 | Independent concurrency granularity and target bridge review | Merged after review/checks | 308: Merged after review/checks | [report](messung/muse/MUSE-REPORT-293.md) |
| 294 | Independent optimiser and full-binary obligation review | Merged after review/checks | 308: Merged after review/checks | [report](messung/muse/MUSE-REPORT-294.md) |
| 309 | Stack frames and ABI memory obligations | Merged after review/checks | 313: Merged after review/checks | [report](messung/muse/MUSE-REPORT-309.md) |
| 310 | Call-log obligations for source inlining | Merged after review/checks | 314: Merged after review/checks | [report](messung/muse/MUSE-REPORT-310.md) |
| 311 | Range-justified integer strength reduction | Merged after review/checks | 315: Merged after review/checks | [report](messung/muse/MUSE-REPORT-311.md) |
| 312 | Checked target regions and allocation ceiling | Merged after review/checks | 316: Merged after review/checks | [report](messung/muse/MUSE-REPORT-312.md) |
| 317 | Single pilot instruction access extraction | Merged after review/checks | 318: Merged after review/checks | [report](messung/muse/MUSE-REPORT-317.md) |
| 319 | Byte-memory fetch decode and actual instruction step | Merged after review/checks | 320: Merged after review/checks | [report](messung/muse/MUSE-REPORT-319.md) |
| 323 | Detailed instruction optimisation and fast compilation design | Merged after review/checks | 324: Merged after review/checks | [report](messung/muse/MUSE-REPORT-323.md) |
| 325 | High runtime performance and feasible hardware-profile design revision | Merged after review/checks | 326: Merged after review/checks | [report](messung/muse/MUSE-REPORT-325.md) |
| 327 | Safety-first broad practical-performance design prioritisation | Merged after review/checks | 328: Merged after review/checks | [report](messung/muse/MUSE-REPORT-327.md) |
| 329 | Muse organisation and dependency ownership plan | Merged after review/checks | 332: Merged after review/checks | [report](messung/muse/MUSE-REPORT-329.md) |
| 330 | Muse merge-owner for independently approved safety-first design | Merged after review/checks | 333: Merged after review/checks | [report](messung/muse/MUSE-REPORT-330.md) |
| 331 | Complete Lean optimiser specification and friend handoff | Merged after review/checks | 334: Merged after review/checks | [report](messung/muse/MUSE-REPORT-331.md) |
| 335 | Practical-performance Lean wave A1: NarrowOps | Committed candidate; review/integration pending | 373: Committed candidate; review/integration pending | [task](lanes/335.md) |
| 336 | Practical-performance Lean wave A2: MulDiv | Merged after review/checks | 374: Merged after review/checks | [report](messung/muse/MUSE-REPORT-336.md) |
| 337 | Practical-performance Lean wave A3: ShiftLogic | Merged after review/checks | 375: Merged after review/checks | [report](messung/muse/MUSE-REPORT-337.md) |
| 338 | Practical-performance Lean wave A4: ControlFlow | Merged after review/checks | 376: Committed candidate; review/integration pending | [report](messung/muse/MUSE-REPORT-338.md) |
| 339 | Practical-performance Lean wave A5: LockedOps | Committed candidate; review/integration pending | 377: Committed candidate; review/integration pending | [task](lanes/339.md) |
| 340 | Practical-performance Lean wave A6: ScalarFloat | Agent working | 378: scheduled | [task](lanes/340.md) |
| 341 | Practical-performance Lean wave B1: AccessList | Committed candidate; review/integration pending | 379: Committed candidate; review/integration pending | [task](lanes/341.md) |
| 342 | Practical-performance Lean wave B2: OverlapRefusal | Merged after review/checks | 380: Merged after review/checks | [report](messung/muse/MUSE-REPORT-342.md) |
| 343 | Practical-performance Lean wave B3: SpillPrivate | Merged after review/checks | 381: Merged after review/checks | [report](messung/muse/MUSE-REPORT-343.md) |
| 344 | Practical-performance Lean wave B4: FenceDrain | Committed candidate; review/integration pending | 382: Committed candidate; review/integration pending | [task](lanes/344.md) |
| 345 | Practical-performance Lean wave C1: TableLayout | Committed candidate; review/integration pending | 383: Committed candidate; review/integration pending | [task](lanes/345.md) |
| 346 | Practical-performance Lean wave C2: GateStub | Committed candidate; review/integration pending | 384: Agent working | [task](lanes/346.md) |
| 347 | Practical-performance Lean wave C3: CostSummary | Committed candidate; review/integration pending | 385: Committed candidate; review/integration pending | [task](lanes/347.md) |
| 348 | Practical-performance Lean wave C4: EntryState | Committed candidate; review/integration pending | 386: Agent working | [task](lanes/348.md) |
| 349 | Practical-performance Lean wave C5: ValidatorSkeleton | Waiting for accepted dependencies | 387: scheduled | [task](lanes/349.md) |
| 350 | Practical-performance Lean wave C6: AtomicPayload | Agent working | 388: scheduled | [task](lanes/350.md) |

Every merged helper retains its own `CUTS` and report. An ACCEPT verdict covers the
exact delivered claim; it never certifies the unfinished compiler or whole binary.
<!-- X86-PROGRESS:END -->

## Validation and publication record

- Earlier integrated foundation checks: full Rust suite **1468 passed, 0 failed,
  1 ignored**; emission check **338/338 translated**, **53 end-to-end comparisons**
  and **2 reverse probes**, exit 0. ASan was unavailable in that emission run.
  These measurements preceded the later Lean modules; they are historical,
  not a full source-to-x86 validation result.
- Each integrated Lean lane has its local merge build and goal-axiom gate. Detailed
  author/reviewer results are in the linked committed reports. Fresh whole-tree
  checks for the implementation at `77e6f362` completed on 2026-10-01: full
  Lean build **375 jobs, 0 errors**; Rust **1468 passed, 0 failed, 1 ignored**;
  emission **338/338 translated, 53 end-to-end comparisons, 2 reverse probes**,
  exit 0. ASan remains unavailable and was not counted as passing. The goal
  axiom probe reports exactly `propext`, `Classical.choice`, `Quot.sound`.
  Subsequent documentation/report-only commits do not change the checked code.
- Push only checked master after required local checks, outgoing secret-pattern
  inspection and a remote-ancestry check. Never force-push or publish lane branches.

## Append-only milestone history

- 2026-10-01: selected direct x86-64 final-byte validation; updated the active
  documents in `38f97c18`. The previous C11 route is retained as historical evidence.
- 2026-10-01: established shared canonical pilot vocabulary in `09eed365`.
- 2026-10-01: user required Lean modelling first, invariant-derived and `-O3`-like
  optimisation, many independent agent reviews and complete source-to-binary validation.
  Stopped Rust codec 280 without discarding its draft.
- 2026-10-01: scheduled eighteen Lean implementation owners, architecture audits,
  exact-candidate reviewers and dependent byte/access coupling tasks. This allocation
  is a work plan, not a count of completed models or currently active processes.
- 2026-10-01: lane **269**, Emitter scope inventory, integrated after its applicable review and checks. Commit `44fbb7e5`. [Evidence](messung/muse/MUSE-REPORT-269.md). <!-- x86-merged:269 -->
- 2026-10-01: lane **270**, Integer and flag semantics, integrated after its applicable review and checks. Commit `82b7da29`. [Evidence](messung/muse/MUSE-REPORT-270.md). <!-- x86-merged:270 -->
- 2026-10-01: lane **271**, Byte memory semantics, integrated after its applicable review and checks. Commit `d1bd60d6`. [Evidence](messung/muse/MUSE-REPORT-271.md). <!-- x86-merged:271 -->
- 2026-10-01: lane **272**, Pilot instruction execution, integrated after its applicable review and checks. Commit `ff323a08`. [Evidence](messung/muse/MUSE-REPORT-272.md). <!-- x86-merged:272 -->
- 2026-10-01: lane **273**, Rust target vocabulary, integrated after its applicable review and checks. Commit `229cb13e`. [Evidence](messung/muse/MUSE-REPORT-273.md). <!-- x86-merged:273 -->
- 2026-10-01: lane **274**, TSO to existing concurrency model, integrated after its applicable review and checks. Commit `c4f2155b`. [Evidence](messung/muse/MUSE-REPORT-274.md). <!-- x86-merged:274 -->
- 2026-10-01: lane **275**, SSA and optimisation validation architecture, integrated after its applicable review and checks. Commit `40a8479e`. [Evidence](messung/muse/MUSE-REPORT-275.md). <!-- x86-merged:275 -->
- 2026-10-01: lane **276**, Final image ABI and loader contract, integrated after its applicable review and checks. Commit `d842b987`. [Evidence](messung/muse/MUSE-REPORT-276.md). <!-- x86-merged:276 -->
- 2026-10-01: lane **277**, Generic source and user-duty bridge, integrated after its applicable review and checks. Commit `a3fc6f88`. [Evidence](messung/muse/MUSE-REPORT-277.md). <!-- x86-merged:277 -->
- 2026-10-01: lane **278**, Floating point and cost preservation, integrated after its applicable review and checks. Commit `10d6547b`. [Evidence](messung/muse/MUSE-REPORT-278.md). <!-- x86-merged:278 -->
- 2026-10-01: lane **281**, Independent foundation and byte-contract review, integrated after its applicable review and checks. Commit `a9bd7373`. [Evidence](messung/muse/MUSE-REPORT-281.md). <!-- x86-merged:281 -->
- 2026-10-01: lane **282**, Integer families beyond the pilot, integrated after its applicable review and checks. Commit `abdeda30`. [Evidence](messung/muse/MUSE-REPORT-282.md). <!-- x86-merged:282 -->
- 2026-10-01: lane **283**, Checked byte image and loaded memory, integrated after its applicable review and checks. Commit `28065fd4`. [Evidence](messung/muse/MUSE-REPORT-283.md). <!-- x86-merged:283 -->
- 2026-10-01: lane **284**, Executable target TSO over real byte memory, integrated after its applicable review and checks. Commit `927574ce`. [Evidence](messung/muse/MUSE-REPORT-284.md). <!-- x86-merged:284 -->
- 2026-10-01: lane **285**, Mathematical carry and signed-overflow characterisation, integrated after its applicable review and checks. Commit `0bd0c3e6`. [Evidence](messung/muse/MUSE-REPORT-285.md). <!-- x86-merged:285 -->
- 2026-10-01: lane **286**, Width-aware IEEE target data and f32 bridge evidence, integrated after its applicable review and checks. Commit `8950b811`. [Evidence](messung/muse/MUSE-REPORT-286.md). <!-- x86-merged:286 -->
- 2026-10-01: lane **289**, Disjoint byte-memory commutation, integrated after its applicable review and checks. Commit `06c05f62`. [Evidence](messung/muse/MUSE-REPORT-289.md). <!-- x86-merged:289 -->
- 2026-10-01: lane **292**, Independent source and invariant trust-boundary review, integrated after its applicable review and checks. Commit `001061d4`. [Evidence](messung/muse/MUSE-REPORT-292.md). <!-- x86-merged:292 -->
- 2026-10-01: lane **293**, Independent concurrency granularity and target bridge review, integrated after its applicable review and checks. Commit `49eddf88`. [Evidence](messung/muse/MUSE-REPORT-293.md). <!-- x86-merged:293 -->
- 2026-10-01: lane **294**, Independent optimiser and full-binary obligation review, integrated after its applicable review and checks. Commit `9029ed95`. [Evidence](messung/muse/MUSE-REPORT-294.md). <!-- x86-merged:294 -->
- 2026-10-01: lane **295**, Independent review of 278,281, integrated after its applicable review and checks. Commit `d9f1b372`. [Evidence](messung/muse/MUSE-REPORT-295.md). <!-- x86-merged:295 -->
- 2026-10-01: lane **296**, Independent review of 272, integrated after its applicable review and checks. Commit `08e5e6c3`. [Evidence](messung/muse/MUSE-REPORT-296.md). <!-- x86-merged:296 -->
- 2026-10-01: lane **298**, Independent review of 282, integrated after its applicable review and checks. Commit `e8faf0ee`. [Evidence](messung/muse/MUSE-REPORT-298.md). <!-- x86-merged:298 -->
- 2026-10-01: lane **299**, Independent review of 283, integrated after its applicable review and checks. Commit `87741b71`. [Evidence](messung/muse/MUSE-REPORT-299.md). <!-- x86-merged:299 -->
- 2026-10-01: lane **300**, Independent review of 284, integrated after its applicable review and checks. Commit `287f1f30`. [Evidence](messung/muse/MUSE-REPORT-300.md). <!-- x86-merged:300 -->
- 2026-10-01: lane **301**, Independent review of 285, integrated after its applicable review and checks. Commit `1c4f4532`. [Evidence](messung/muse/MUSE-REPORT-301.md). <!-- x86-merged:301 -->
- 2026-10-01: lane **302**, Independent review of 286, integrated after its applicable review and checks. Commit `0de7edc7`. [Evidence](messung/muse/MUSE-REPORT-302.md). <!-- x86-merged:302 -->
- 2026-10-01: lane **305**, Independent review of 289, integrated after its applicable review and checks. Commit `3cfe1cbd`. [Evidence](messung/muse/MUSE-REPORT-305.md). <!-- x86-merged:305 -->
- 2026-10-01: lane **308**, Independent counter-review of source concurrency and binary audits, integrated after its applicable review and checks. Commit `ddcc9f22`. [Evidence](messung/muse/MUSE-REPORT-308.md). <!-- x86-merged:308 -->
- 2026-10-01: fresh publication checks passed for implementation `77e6f362`: Lean (375 jobs), Rust (1468 passed), emission (338 translations/53 comparisons/2 reverse probes), and the standard goal axioms. ASan was not run.
- 2026-10-01: moved this central record to root `DIRECT-COMPILER.md`; relocated
  design, completed-work and tutorial documents into `dokumente/`; renamed the
  unchanged licence addendum to root `LICENSE-ADDENDUM.md`. Updated readers,
  tutorial checks and generated licence-notice references. Archived unused local
  assistant output and duplicate proof work copies with their contents preserved.
  Fresh Lean, Rust and emission checks after these path changes passed before publication.
- 2026-10-01: independent cleanup reviewer 322 found two stale emitted-C notice
  pins after the licence-file rename. Mechanically refreshed both pins against
  the actual fresh emitter (1570/1465 bytes); proof statements and negative
  witnesses remain unchanged. Full Lean rebuild passed (375 jobs, 0 errors);
  the byte guardian passed all four speech probes and both actual pins
  (3035 bytes compared).
- 2026-10-01: user requested immediate master publication once Lean is green.
  After root cleanup `4aad806a`, Rust passed 1468 tests (0 failures, 1 ignored)
  and emission passed 338 translations, 53 comparisons and 2 reverse probes.
  The pin-only repair then passed the complete Lean rebuild and CTEXT guardian;
  Rust/emitter implementation is unchanged by that repair. ASan was not run.
- 2026-10-01: lane **279**, Pilot byte codec and generic round-trip, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-279.md). <!-- x86-merged:279 -->
- 2026-10-01: integration of candidate(s) [291] failed the local proof/build gate after independent review 307; no failing candidate was merged. Author repair and a fresh exact-commit review are required. <!-- x86-gate-rejection:307 -->
- 2026-10-01: checked master `552f0ec8` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:552f0ec8a56a15661ba22c8b5d5016694d5793d7 -->
- 2026-10-01: lane **297**, Independent review of 279, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-297.md). <!-- x86-merged:297 -->
- 2026-10-01: lane **290**, Packed integer lane model for future SIMD, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-290.md). <!-- x86-merged:290 -->
- 2026-10-01: lane **306**, Independent review of 290, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-306.md). <!-- x86-merged:306 -->
- 2026-10-01: lane **291**, Checked relocation arithmetic and byte patching, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-291.md). <!-- x86-merged:291 -->
- 2026-10-01: lane **307**, Independent review of 291, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-307.md). <!-- x86-merged:307 -->
- 2026-10-01: lane **309**, Stack frames and ABI memory obligations, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-309.md). <!-- x86-merged:309 -->
- 2026-10-01: lane **313**, Independent review of 309, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-313.md). <!-- x86-merged:313 -->
- 2026-10-01: lane **310**, Call-log obligations for source inlining, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-310.md). <!-- x86-merged:310 -->
- 2026-10-01: lane **314**, Independent review of 310, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-314.md). <!-- x86-merged:314 -->
- 2026-10-01: lane **311**, Range-justified integer strength reduction, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-311.md). <!-- x86-merged:311 -->
- 2026-10-01: lane **315**, Independent review of 311, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-315.md). <!-- x86-merged:315 -->
- 2026-10-01: publication batch checks passed for `ce698d8f`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **322**, Independent root cleanup and English filename review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-322.md). <!-- x86-merged:322 -->
- 2026-10-01: checked master `1c415d29` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:1c415d29989d42c49ccabc731831239e49499d96 -->
- 2026-10-01: lane **312**, Checked target regions and allocation ceiling, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-312.md). <!-- x86-merged:312 -->
- 2026-10-01: lane **316**, Independent review of 312, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-316.md). <!-- x86-merged:316 -->
- 2026-10-01: lane **323**, Detailed instruction optimisation and fast compilation design, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-323.md). <!-- x86-merged:323 -->
- 2026-10-01: lane **324**, Independent detailed compiler design review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-324.md). <!-- x86-merged:324 -->
- 2026-10-01: publication batch checks passed for `fa7aef61`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **317**, Single pilot instruction access extraction, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-317.md). <!-- x86-merged:317 -->
- 2026-10-01: checked master `785b8fc3` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:785b8fc3337fbc086b19923b407d5adc9f2d1a5d -->
- 2026-10-01: lane **318**, Independent review of 317, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-318.md). <!-- x86-merged:318 -->
- 2026-10-01: lane **321**, Independent central compiler document review, integrated after its applicable review and checks. Commit `55f533ac`. [Evidence](messung/muse/MUSE-REPORT-321.md). <!-- x86-merged:321 -->
- 2026-10-01: lane **325**, High runtime performance and feasible hardware-profile design revision, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-325.md). <!-- x86-merged:325 -->
- 2026-10-01: lane **326**, Independent high-performance hardware-design revision review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-326.md). <!-- x86-merged:326 -->
- 2026-10-01: publication batch checks passed for `c1527ce9`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **288**, Invariant-derived optimisation on actual source semantics, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-288.md). <!-- x86-merged:288 -->
- 2026-10-01: checked master `2e19f7de` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:2e19f7de163e375eac258e13fac55868f4e9bcaa -->
- 2026-10-01: lane **304**, Independent review of 288, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-304.md). <!-- x86-merged:304 -->
- 2026-10-01: publication batch checks passed for `6c15db3a`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **319**, Byte-memory fetch decode and actual instruction step, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-319.md). <!-- x86-merged:319 -->
- 2026-10-01: checked master `82e7efb5` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:82e7efb53e7793269d110a320f130e0119f123a8 -->
- 2026-10-01: lane **320**, Independent review of 319, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-320.md). <!-- x86-merged:320 -->
- 2026-10-01: publication batch checks passed for `ad1a6e2a`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **330**, Muse merge-owner for independently approved safety-first design, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-330.md). <!-- x86-merged:330 -->
- 2026-10-01: checked master `7b932d72` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:7b932d727443a5f62ad6716bc3362de78c3957bb -->
- 2026-10-01: lane **327**, Safety-first broad practical-performance design prioritisation, integrated after its applicable review and checks. Commit `0dbd217b`. [Evidence](messung/muse/MUSE-REPORT-327.md). <!-- x86-merged:327 -->
- 2026-10-01: lane **333**, Independent exact merge-owner candidate review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-333.md). <!-- x86-merged:333 -->
- 2026-10-01: documentation-only publication at `f3bda6f0` retains the successful complete local Lean, Rust and emission checks at `ad1a6e2a`; source/build files are unchanged. Goal axioms checked again. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **328**, Independent safety-first practical-performance scope review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-328.md). <!-- x86-merged:328 -->
- 2026-10-01: checked master `610d0cfb` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:610d0cfb20a6ff8064bb9186c3a109d9a0a72e80 -->
- 2026-10-01: lane **331**, Complete Lean optimiser specification and friend handoff, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-331.md). <!-- x86-merged:331 -->
- 2026-10-01: lane **334**, Independent complete optimiser specification review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-334.md). <!-- x86-merged:334 -->
- 2026-10-01: documentation-only publication at `95a4871f` retains the successful complete local Lean, Rust and emission checks at `ad1a6e2a`; source/build files are unchanged. Goal axioms checked again. Full source-to-binary validation remains OPEN.
- 2026-10-01: checked master `a52b229b` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:a52b229b1f6ccc38157a437594ddf3c4dc5756f1 -->
- 2026-10-01: lane **329**, Muse organisation and dependency ownership plan, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-329.md). <!-- x86-merged:329 -->
- 2026-10-01: checked master `159269ed` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:159269ed9567fda9e3b0fadf303ddf238c4d0fe2 -->
- 2026-10-01: lane **332**, Independent organisation and ownership plan review, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-332.md). <!-- x86-merged:332 -->
- 2026-10-01: documentation-only publication at `cc400110` retains the successful complete local Lean, Rust and emission checks at `ad1a6e2a`; source/build files are unchanged. Goal axioms checked again. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **343**, Practical-performance Lean wave B3: SpillPrivate, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-343.md). <!-- x86-merged:343 -->
- 2026-10-01: checked master `f737a6f0` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:f737a6f04c22dfdd9499532e0535ad119cf2e56d -->
- 2026-10-01: lane **381**, Independent exact-candidate review of 343 SpillPrivate, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-381.md). <!-- x86-merged:381 -->
- 2026-10-01: publication batch checks passed for `a8ba748c`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **342**, Practical-performance Lean wave B2: OverlapRefusal, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-342.md). <!-- x86-merged:342 -->
- 2026-10-01: checked master `b5267bd4` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:b5267bd4e371bc56f7f1e4360de56e91b46c3397 -->
- 2026-10-01: lane **380**, Independent exact-candidate review of 342 OverlapRefusal, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-380.md). <!-- x86-merged:380 -->
- 2026-10-01: publication batch checks passed for `1f533c8b`: complete local Lean, Rust and emission checks plus the standard goal axioms. Full source-to-binary validation remains OPEN.
- 2026-10-01: lane **336**, Practical-performance Lean wave A2: MulDiv, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-336.md). <!-- x86-merged:336 -->
- 2026-10-01: checked master `250d09c7` published to origin/master after local checks, outgoing secret-pattern inspection and remote ancestry verification. <!-- x86-published:250d09c736c02db4ca3354f9dbdc1800dc7dc35d -->
- 2026-10-01: lane **374**, Independent exact-candidate review of 336 MulDiv, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-374.md). <!-- x86-merged:374 -->
- 2026-10-01: lane **337**, Practical-performance Lean wave A3: ShiftLogic, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-337.md). <!-- x86-merged:337 -->
- 2026-10-01: lane **375**, Independent exact-candidate review of 337 ShiftLogic, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-375.md). <!-- x86-merged:375 -->
- 2026-10-01: lane **338**, Practical-performance Lean wave A4: ControlFlow, integrated after its applicable review and checks. Recorded with the integration commit containing this entry. [Evidence](messung/muse/MUSE-REPORT-338.md). <!-- x86-merged:338 -->
<!-- X86-HISTORY -->

## Detailed references

- [Active translation-validation plan](dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md) and [work order](dokumente/AUFTRAG-UEBERSETZUNGSVALIDIERUNG.md).
- [Lean-first allocation](dokumente/x86/LEAN-ZUERST.md), [wave history](dokumente/x86/WELLE-A.md) and [canonical byte contract](dokumente/x86/BYTE-PILOT.md).
- [IR/optimisation obligations](dokumente/x86/IR-VALIDIERUNG.md), [full source bridge](dokumente/x86/QUELLBRUECKE.md) and [emitter inventory](dokumente/x86/EMITTER-INVENTAR.md).
- [TSO/W/GX bridge](dokumente/x86/TSO-GX-BRUECKE.md), [image/ABI coverage](dokumente/x86/IMAGE-ABI.md) and [IEEE/time obligations](dokumente/x86/FLOAT-ZEIT.md).
- [Source/invariant audit](dokumente/x86/REVIEW-QUELLE-INVARIANTEN.md), [concurrency audit](dokumente/x86/REVIEW-TSO.md) and [optimisation/binary audit](dokumente/x86/REVIEW-OPT-BINAER.md).

- 2026-10-01: fast compilation is an explicit design priority, including mandatory
  Lean validation. [Author 323](lanes/323.md) is preparing a separate root English
  instruction, invariant-optimisation and compiler-speed design;
  [reviewer 324](lanes/324.md) checks the exact committed candidate independently.
  No speed measurement or expanded native instruction support is claimed.

- 2026-10-01: the instruction and invariant design is integrated after independent
  review 324. The latest user priority is high runtime performance with a feasible
  complete selected architectural hardware model, alongside fast compilation and
  full mandatory validation. [Author 325](lanes/325.md) revises the detailed design;
  [reviewer 326](lanes/326.md) independently checks its exact candidate.
  No measured runtime or compiler speed, expanded ISA support or whole-binary proof
  is claimed.

- 2026-10-01: latest scope priority: broad important practical performance, with
  safety above marginal final improvements. The user’s approximate “last 10%” is
  qualitative prioritisation, not reduced proof coverage or a measured performance
  guarantee. [Author 327](lanes/327.md) clarifies essential and deferred instruction
  families; [reviewer 328](lanes/328.md) checks the exact plan independently.
  Full mandatory source/final-byte validation and fast accepted compilation remain
  requirements; the full chain remains OPEN.

- 2026-10-01: user authorised up to 40 concurrent Muse processes today, including
  organising and merge-owner agents, returning to 20 on later days. Author 329
  prepares concrete dependency/ownership allocation; merge owner 330 performs the
  actual local merge of independently reviewed design 327, followed by independent
  merge review 333. Author 331 writes the complete planned optimiser specification
  in `grammatik/OPTIMIZER.md`, reviewed by 334, with an isolated proposed friend
  rule-library handoff. No friend work or 40 simultaneously active processes is
  claimed. Source/final-byte validation remains mandatory and the full chain OPEN.

- 2026-10-01: the agent-organised next Lean wave is registered from the independently
  reviewed [work allocation](dokumente/x86/WORK-ALLOCATION.md): authors 335–350
  and paired reviewers 373–388, with 349 waiting for accepted layout/gate producers.
  Shared source/target models and friend-owned optimisation paths remain protected;
  no additional ISA support or full correspondence is claimed by task registration.
  The global cap is 40 today including reviewers/organisers/merge owners.
- 2026-10-01, 11:01 UTC: measured 11,223 integrated Lean lines in 20 x86 modules
  over 2.93 wall hours from the first Lean model process: about 3.84 k lines/hour.
  Counts include definitions, proofs, comments and documented cuts; unreviewed
  drafts are excluded. Setup, reviews, repairs and queued checks are included.
  This is not a benchmark of 40 simultaneously active agents or completed full
  validation; the full source-to-binary chain remains OPEN.
