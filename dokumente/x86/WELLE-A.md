# Direct x86-64 validation — wave A

*Started 2026-10-01 by Simon's instruction; SUPERSEDED capacity note:
coordinate at most **15** `opencode-go/muse-spark-1.3-contributor` agents
(authoritative since 2026-10-01, see `dokumente/x86/COMPILER-SCHLUSSPLAN.md`
§0). The "20" first written here is historical. All execution and builds are local.*

## Shared contract

The target is the active translation-validation plan, with an initial optimisation package:
constant/copy propagation, dead-code elimination, common subexpressions, selective inlining,
register allocation, peephole instruction selection, loop-invariant motion, bounded unrolling
and selective SIMD. These are generic mechanisms; no acceptance or compiler rule depends on
an example or function name. Actual performance must be measured. Preserve faults, IEEE
behaviour, concurrent observations, progress and cost guarantees.

`grammatik/Grammatik/X86/Typen.lean` is the canonical pilot vocabulary. Namespace:
`Gabbro.Grammatik.X86`. The 16 registers are in their architectural encoding order.
`Byte`, `Wort` and `Adresse` are BitVec 8/64/64. Memory includes byte contents and explicit
read/write/execute permissions. Arithmetic is modular at machine level; source-side range and
fault behaviour still need correspondence. `Flags.af = none` is undefined, not false.

The pilot supports only the `Befehl` constructors in that file. Displacements are signed
32-bit values; relative control flow uses the address AFTER the decoded instruction. Instruction
length belongs to validated decoding, not an untrusted emitter annotation. Loads/stores use
base-register plus sign-extended displacement. Do not independently invent another register,
instruction, byte-memory or source-concurrency model. Propose required extensions in the report.

The Rust mirror belongs under `crates/gabbro-check/src/x86/`. It is initially an internal
foundation with no CLI/native-execution acceptance claim. The new mechanism remains unwired
until its relevant Lean part and correspondence are reviewed. Existing C behaviour stays green.

Instruction-level sequential helpers do not establish concurrent atomicity. A memory-changing
instruction witness is required; per-access TSO and alignment/tearing correspondence remain
separate obligations. W/GX and the existing goal theorem remain the source-side model.

## Owners and deliverables

| Lane | Owner files | Deliverable |
|---|---|---|
| 269 | `dokumente/x86/EMITTER-INVENTAR.md` | Exhaustive source/emitter/runtime-path inventory, widths/orders and target obligations |
| 270 | `grammatik/Grammatik/X86/Wort.lean` | Modular integer operations, architectural flag helpers and generic lemmas |
| 271 | `grammatik/Grammatik/X86/Speicher.lean` | Permission-checked little-endian reads/writes, frame and read-after-write facts |
| 272 | `grammatik/Grammatik/X86/Ausfuehrung.lean` | Real pilot instruction state transitions, memory-changing witnesses and explicit gaps |
| 273 | `crates/gabbro-check/src/x86/{mod.rs,typen.rs}`, `lib.rs` module export | Canonical Rust mirror and checked architectural register/width conventions |
| 274 | `dokumente/x86/TSO-GX-BRUECKE.md` | Existing-model audit, exact refinement obligations and granularity counterexamples |
| 275 | `dokumente/x86/IR-VALIDIERUNG.md` | Shared SSA/certificate architecture and legality requirements for starter optimisations |
| 276 | `dokumente/x86/IMAGE-ABI.md` | Byte-image/layout/relocation/entry contract and whole-executable-code coverage |
| 277 | `dokumente/x86/QUELLBRUECKE.md` | Source-computed judgement/duties reuse and generic source-to-target closing interface |
| 278 | `dokumente/x86/FLOAT-ZEIT.md` | IEEE/SSE mapping, timing/progress obligations and supported-profile boundaries |

Only these owned files, the lane report and the prescribed Lean umbrella import may be edited.
The coordinator owns Typen.lean, central integration, plan/status/number ledgers and final reviews.
No diagnostic, poison-probe or example numbers are allocated in wave A; these tasks add no new
source-language construct or checker rule. Do not touch MARKE_EMIT or existing C templates.

## Gates and next wave

Every task begins with HARD RULES. Keep isolated local clones without a remote, private scratch
space and warm caches. Use the existing queued build wrappers; run only one Lean build globally.
No sorry/admit/native_decide/new axiom/unsafe. Prove generic claims and give joint non-degenerate
witnesses; record a blockage rather than replacing it with a premise. No theorem-only mini-models
that cannot affect actual machine memory. Report exact definitions, commands, results and cuts.

Wave B depends on reviewed shared foundations: encoder/decoder and their round-trip, source
lowering and certificates, per-access TSO refinement, ABI/image construction, optimiser families
and independent review. The limit is 20 active model processes including reviewers. Starting a
lane or obtaining a green helper lemma does not close a binary validation chain.

## Initial execution status

The canonical vocabulary passed the full local Lean build (366 jobs, zero errors), committed
as `09eed365`. Nine Go Contributor lanes are running (269–271 and 273–278); lane 272 waits
for reviewed arithmetic/memory helpers. All nine checked their actual tool working directory,
Git toplevel and branch against their own clone before resuming work.

The launcher uses explicit `--dir` plus matching PWD; process cwd alone was insufficient for
opencode in this environment. The first start was stopped before any lane commit, two partial
owned Lean files were preserved into their correct clones, and master was restored unchanged.
Every task now refuses an isolation mismatch before edits or branch changes. Continuations
use explicit session IDs; they never continue the last session across parallel clones.

Coordinator state: `.claude/muse-arbeit/x86/state/`; logs: local
`/home/simon/Dokumente/gabbro-muse/logs/NN.log`. These are operational records, not proof verdicts.

## Reviewed foundation milestone and next execution wave

Merged locally after coordinator review: word/flags (270), byte memory (271),
and the repaired Rust vocabulary (273). The integrated Lean build and goal
axiom checks passed; the source goal still uses only propext, Classical.choice,
Quot.sound. The Rust lane's permission-revocation regression is repaired and
its full suite passed (1468 passed, zero failed, one ignored); coordinator
integration checks are being run separately. None of these is a complete
source-to-byte chain. Remaining wave-A designs are still under review.

Lane 272 now runs against the merged word/memory helpers. Wave B reserves:

| Lane | Owner files | Deliverable |
|---|---|---|
| 279 | `X86/Codec.lean`, additive umbrella import | Actual canonical bytes, decoder, generic round-trip and length/refusal facts |
| 280 | `x86/codec.rs`, additive `x86/mod.rs` export | Untrusted Rust byte encoder/decoder and independently pinned architecture probes |
| 281 | `dokumente/x86/REVIEW-GRUNDLAGEN.md` | Independent arithmetic/memory/Rust-vocabulary/encoding-contract review |

The byte encoding contract is `BYTE-PILOT.md`. Parallel implementations share
that contract and the canonical types. The checked Lean decoder will remain
the trust path; Rust remains unwired. At most 20 active Contributor model
processes, including review and repair sessions. Independent reviews do not
replace the later two complete-goal verdicts.

## User steering: Lean first

Simon requested complete Lean modelling before further Rust implementation,
including the -O3-like package, invariant-derived extra optimisations and
complete Gabbro-to-binary validation. See `LEAN-ZUERST.md` for owned modules
and dependency order. Lane 280 is stopped with its unmerged draft preserved;
272/279 continue, and 282–288 are Lean-only owners. The integrated foundation
passed the full Rust suite (1468/0/1 ignored), full Lean (368 jobs), standard
goal axiom check, and emission regression (338/338, 53 execution comparisons;
ASan unavailable and not counted as passed). Those checks establish the
foundation regression state, not a complete native validation chain.
