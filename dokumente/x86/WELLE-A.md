# Direct x86-64 validation — wave A

*Started 2026-10-01 by Simon's instruction: coordinate at most 20
`opencode-go/muse-spark-1.3-contributor` agents. All execution and builds are local.*

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
