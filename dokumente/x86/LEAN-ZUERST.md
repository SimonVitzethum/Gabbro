# Lean first — complete source-to-binary model and optimisation

Simon, 2026-10-01: model everything in Lean with agents first. The final
objective remains generic full Gabbro source-to-actual-binary translation
validation, with the -O3-like starter package and additional transformations
justified by Gabbro guarantees. No program-specific acceptance rules.
Binding closure plan: `dokumente/x86/COMPILER-SCHLUSSPLAN.md` (§§1–6).

The unmerged Rust codec lane 280 is stopped; its draft and logs are preserved.
No further Rust/native backend work is scheduled until the relevant Lean
models and their generic proof interfaces are reviewed. Existing unwired Rust
vocabulary stays as recorded historical groundwork; nothing uses it to admit
a native binary.

Active Lean owners:

| Lane | Module | Concrete first deliverable |
|---|---|---|
| 272 | `X86/Ausfuehrung.lean` | Real canonical pilot instruction state transitions |
| 279 | `X86/Codec.lean` | Actual byte decode/encode with generic round-trip and consumption |
| 282 | `X86/Ganzzahl.lean` | Remaining integer arithmetic/division/shift families |
| 283 | `X86/Bild.lean` | Decided file-to-virtual mapping and actual loaded byte memory |
| 284 | `X86/TSO.lean` | Executable FIFO buffers/forwarding/flush over canonical memory |
| 285 | `X86/FlagBeweis.lean` | Mathematical signed overflow and carry characterisation |
| 286 | `X86/Gleitprofil.lean` | Width/control checks, IEEE bit facts and explicit f32 gap evidence |
| 287 | ~~`X86/IR.lean`~~ superseded, report-only | Single typed IR ~~and actual source-linked lowering fragment~~ — SUPERSEDED by `DIRECT-LOWERING-DECISION.md` (594/606 merged): no persistent SSA IR, source-anchored blocks instead; see `COMPILER-SCHLUSSPLAN.md` §0 |
| 288 | `X86/InvariantenOpt.lean` | Source-semantic rewrite proofs using correctly scoped invariants |

These bounded first tasks do not model or validate the full language yet.
Next dependent work closes aligned atomic/LOCK accesses and TSO-to-W/GX;
image decoding/control targets/relocations and ABI/entries; source-computed
full units/duties; runtime/templates; target/source budget and machine-work
transfer; and optimiser families. Constant/copy propagation, DCE/CSE,
inlining, allocation/peepholes, LICM, unrolling and SIMD each require a
generic checked rule and explicit preservation of faults, FP state, source
call logs, memory observations, progress and all claimed bounds.

Additional optimisation opportunities include proved range-check removal,
strength reduction, ownership-based alias separation, stable protected loads
and private-memory SIMD. Range/ownership/invariant evidence is source-computed
and proved at the actual location. No assumption that an invariant holds
inside a running writer or arbitrary held section; no inferred ensures; no
local-only token argument for shared memory. Pending correspondence never
admits an optimisation.

The closing validator must bind the entire source-computed unit to decoded
final bytes, loaded mapping, entries and every reachable executed body. A
round-trip, a generic helper or a schematic simulation premise closes no
source-to-binary chain. OS/runtime/binding logic is user logic; only silicon,
device behaviour and named timing bounds belong to hardware assumptions.

At most 20 active Contributor model processes, including reviewers. Private
clones/caches, checked isolation, one queued Lean build globally, independent exact-candidate agent review
before integration, standard goal axioms. Every uncovered form is explicit;
no guarantee is weakened to turn a build green.

## Additional parallel proof and review owners

| Lane | Module/document | Task |
|---|---|---|
| 289 | `X86/SpeicherKommutation.lean` | Actual disjoint-store/frame commutation for future private spills |
| 290 | `X86/Vektor.lean` | Packed integer lane arithmetic and actual memory carriage |
| 291 | `X86/Relokation.lean` | Checked rel32/abs64 arithmetic and final-byte operand/data patching |
| 292 | `REVIEW-QUELLE-INVARIANTEN.md` | Independent source-unit, duty and scoped-invariant audit |
| 293 | `REVIEW-TSO.md` | Independent target-access granularity/concurrency/progress audit |
| 294 | `REVIEW-OPT-BINAER.md` | Independent optimisation and full-binary closure audit |

The initial Lean-first tranche has twelve Lean implementation owners (272,
279, 282–291) and three independent review owners (292–294). Model processes
are bounded to20 including any repair/review sessions; completed owners are
rotated into dependent work after review. Direct source lowering, runtime/ABI,
full W/GX simulation, complete instruction-family encoding and global
optimiser/cost soundness remain required follow-up tasks, not implied by
these foundations. Transfer/integration stays with the coordinator after
independent findings are resolved and local checks pass.

## Independent exact-candidate reviews

Simon requests substantive checks by agents first; coordinator review is a
fallback when agents cannot resolve a finding. Lanes 295–307 review pinned
committed snapshots independently from the authors: 295 reviews the completed
float/time and foundation-review documents; 296–307 review respectively
272, 279 and 282–291. Each report names the exact candidate commit and records
ACCEPT or concrete REPAIR findings. A stale review cannot admit a changed
candidate. Copies stay in each reviewer's private scratch; authors keep their
owned clones. Transfer/integration is mechanical after the agent verdict and
local merge checks. The coordinator resolves scheduling/build/import mechanics;
semantic fallback is reserved for a demonstrated agent blockage.

## Further independent Lean owners

309 models actual stack-frame/ABI memory operations; 310 proves source-call-log
reconstruction needed for inlining; 311 proves range-justified strength
reductions against actual source semantics; 312 models checked target region
allocation and ceilings. Their exact-candidate reviewers are 313–316.
This schedules sixteen Lean implementation owners, three broad independent
reviewers and one current completed-candidate reviewer (up to20 concurrent
models). As authors finish, their review sessions replace them under the same
20-process cap. No Rust codec work is resumed.

## Counter-review of architecture audits

Lane 308 independently counter-reviews the exact committed source/invariant,
concurrency and optimiser/full-binary audits from 292–294. Those historical
baseline reports retain their dated claim boundaries. New bounded helper
modules do not establish any full-chain theorem. Their transfer follows the
same pinned-candidate ACCEPT gate as implementation work.

If an integration build or proof gate fails after an ACCEPT, the candidate
remains unmerged. Its author receives the actual gate output for repair and
a fresh independent review follows any changed commit. Semantic coordinator
fallback requires a demonstrated inability of agents to resolve the finding.

## First dependent coupling tasks

317 owns the single target access-footprint extraction linked to the actual
pilot instruction transitions; 318 independently reviews it. 319 couples
permission-checked fetch from actual instruction memory to the existing byte
decoder and instruction step; 320 independently reviews it. The coordinator
starts each author only after its accepted dependencies are merged, and all
model processes share the same 20-slot ceiling. This brings the scheduled
Lean implementation owners to eighteen. These coupling lemmas still leave
full source lowering, the W/GX refinement, runtime/ABI and optimisation/time
closure open.
