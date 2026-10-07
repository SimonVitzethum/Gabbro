# ARM-PLAN.md — the AArch64 direction (decided by Simon, 2026-10-07)

**Decision.** All work on the x86-64 hardware model stops. The files stay in the tree
(`grammatik/Grammatik/X86/`, `DIRECT-COMPILER*.md`); nothing is deleted and nothing new is
added there. The selected next target is **AArch64 (Armv9-A)**. The reason is effort: the x86
hardware model was too laborious to complete.

**Basis.** The Arm architecture specification as Sail models:
`rems-project/sail-arm` (`arm-v9.4-a`, 37 `.sail` files, about 466,000 lines, derived from
Arm's ASL by the ASL-to-Sail translation, BSD-3-Clause-Clear) and the Sail compiler and
libraries `rems-project/sail`. Both are cloned read-only (not into the repository, not into
`/tmp`) at `/home/simon/Dokumente/gabbro-arm/src/{sail,sail-arm}`. What the model gives: the
sequential semantics of the A64 instructions, system registers and exceptions. **What it does
not give: multicore.** The memory interface of Sail Arm (`interface.sail`, `mem.sail`) emits
single-thread memory events; the relaxed-memory behaviour of several cores is added here, in
Lean.

**Measured facts (2026-10-07).**
- `sail-arm/arm-v9.4-a` has Isabelle and Coq snapshots but **no generated Lean** (only
  `lean/ArmExtras.lean`). Sail has a Lean backend (`sail/src/sail_lean_backend`, `sail/lib/lean`),
  and its libraries contain `concurrency_interface`.
- The Sail compiler is OCaml (opam); **it is not installed on this machine**. Until it is, the
  sequential semantics are ported by hand, each definition citing the Sail source file and line
  it translates, so a later Sail-generated Lean can be compared one to one.

**Layout.** `arm/` is a separate small Lake project (Lean 4.33.1, no mathlib, no dependency),
built with `./arm-bau` and `./arm-probe <file>` (three builds at a time). It will be linked to
`grammatik/` (the goal theorem, W / GX) when the model is complete. Folders: `Arm/Mem`
(multicore and the memory model), `Arm/Isa` (sequential instructions), `Arm/Sail` (the bridge to
the Sail source), `Arm/Lit` (litmus tests). Shared vocabulary: `arm/Arm/Basic.lean` (frozen).

**The 15 agents** (each in its own shell and clone `/home/simon/Dokumente/gabbro-arm/work/NN`,
branch `arm/NN`, personal task `lanes/arm/NN.md`, report `REPORT-NN.md`):

| | Topic |
|---|---|
| 01-05 | GabbroV: start duty, wider elaborated fragment, traversal membership, tree parent consistency, disjunctive posts and call chains |
| 06-10 | Multicore: events and executions, the axiomatic model, litmus tests, exclusives and atomics, barriers and acquire/release |
| 11-15 | Sequential Sail Arm: integer, loads and stores, branches and system, floating point and SIMD, decoder and coverage ledger plus the Sail-to-Lean bridge |

When the model is complete, the same agents move on to the compiler. Up to two Sonnet 5.5
agents check what in Gabbro itself is not yet Arm-compatible.

**Order.** The findings of the language-gap reports (`messung/SPRACHLUECKEN*.md`) are NOT done
now; they come after GabbroV and the hardware model.

**Honesty.** Nothing here is implemented yet. A Lean port of Sail semantics is self-consistency
with the Sail text, not a hardware correspondence; vendor-undefined behaviour stays free.

## C emitter archive (2026-10-07)

The C11 backend (`crates/gabbro-check/src/emit.rs`, `certemit.rs`, `schablonen.rs`, `tearing.rs`,
`crates/gabbro-cli/src/treiber.rs`, `laufzeit/`, `bibliothek/`, `instrumente/pruefe-emission.sh`) is
archived as legacy evidence: git tag `archiv/c-emitter-2026-10-07` and a tarball outside the repo
(`gabbro-arm/archiv/c-emitter-2026-10-07.tar.gz`). It stays in the tree because the checker, the
examples and the AArch64 compatibility work (Sonnet C) still build on it; the direct AArch64
compiler replaces it as the target, and nothing new is added to the C backend beyond ARM
compatibility fixes.

## Direction fixed (Simon, 2026-10-07): C backend deprecated

The emitted C11 backend is DEPRECATED. The planned path is the AArch64 Gabbro **native compiler**
with **translation validation** (source -> model -> final AArch64 bytes, checked in Lean). No new
work goes into the C backend (no new C templates, no C-side audits); known C-backend defects are
recorded as legacy (for example the page-return helper wrap, `messung/ARM-KOMPATIBILITAET-C.md`
F2). The C emitter archive above is the reference for its last state.
