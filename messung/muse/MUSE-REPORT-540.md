# Muse Report 540: OS-independent and freestanding target architecture

## What was done

Design-only lane. Two deliverables, no Lean/Rust code, no model changes:

1. Created `dokumente/x86/TARGET-PORTABILITY.md` (proposed architecture):
   one canonical IR/executor/validation chain with three separated concerns
   (hardware instruction profile, declarative ABI/image/entry profile,
   program-supplied environment bindings); hosted vs freestanding modes;
   executable and relocatable outputs with ELF/PE-COFF/Mach-O/raw as planned
   examples (explicitly not implemented); stack/red-zone/shadow-space/
   callee-save/TLS/unwind rows where used; syscall-gate vs ordinary
   extern-call bindings; pre-stack entries; interrupt/device/context state;
   relocation/load-bias/final-mapping checks; closure boundary (validated
   domain vs outside, three external-body obligations, refusal of unresolved
   obligations); per-profile acceptance gates (generic obligations,
   memory-changing positive witness, negative probes, budget/concurrency/FP
   compatibility, eventual Rust tests); profile-covering cache keys with
   validation on the fast path; practical dependencies (accepted bounded
   helpers vs open proofs); add-an-OS checklist; capability-refusal rule;
   guarantee and friend-reserved-file boundaries.
2. Added concise linked section `## 12. Target portability` to
   `DIRECT-COMPILER-DESIGN.md`, pointing to the new document. No other
   edits to that file; `DIRECT-COMPILER.md` (central ledger) untouched.

## Exact names of new definitions/theorems

None. This lane adds no Lean definitions, lemmas, theorems, checker rules,
diagnostics, or probes, per the task (design only, no new Lean/Rust code or
custom model).

## Checks

- `git diff --check`: clean (no whitespace errors).
- Local links verified by reading: sibling links (`IMAGE-ABI.md`,
  `QUELLBRUECKE.md`, `IR-VALIDIERUNG.md`), parent links
  (`../../DIRECT-COMPILER.md`, `../../DIRECT-COMPILER-DESIGN.md`,
  `../../grammatik/Grammatik/X86/*.lean`, `../../grammatik/OPTIMIZER.md`,
  `../PLAN-UEBERSETZUNGSVALIDIERUNG.md`), and the new forward link
  `dokumente/x86/TARGET-PORTABILITY.md` from the design doc all resolve to
  existing files.
- Section consistency: design doc previously ended at `## 11`; the addition
  is `## 12`, no renumbering, no collision.
- No `./lean-bau` run: no Lean files were touched, so no Lean build was
  owed for this documentation-only change (per the task: do not invent a
  required full build for documentation-only changes). No `./cargo-pruef`
  run: no Rust files touched.

## What remains open

- Everything in the new document is PROPOSED: gate-stub correspondence
  (no accepted `GateStub` Lean module exists today; lane 346 work is
  pending), per-access TSO-to-W/GX refinement, full-unit source
  computation, lowering/optimisation certificates, budget/work and time
  transfer, FP/hardware correspondence, template x86 instances, linking
  image step.
- Independent review by reviewer 541 (scheduled, not run by this lane).

## Anything in the task believed wrong

- Nothing wrong. One note: the task text asks to "read actual ... GateStub"
  as if it existed; I verified by glob that no `grammatik/Grammatik/X86/Gate*.lean`
  file is accepted today, so the document records GateStub as pending lane-346
  work rather than citing it as an existing helper. No weakening follows from
  this; it is booked as an open proof obligation.
