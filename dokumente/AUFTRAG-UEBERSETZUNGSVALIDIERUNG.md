# Assignment: translation validation — source to validated x86-64 bytes

*Revised 2026-10-01 by Simon's decision. This replaces the C11 validation assignment.
Read this file first, then [the active plan](PLAN-UEBERSETZUNGSVALIDIERUNG.md) §§0–5.
The current compiler still emits C; the direct backend and its validator are planned.*

## 1. The deliverable

Build a generic Lean-checked chain from source text to the final x86-64 image. Lean computes
the model program and its user duties from the source, validates the decoded image against that
program, and applies the existing goal theorem. The Rust backend and its certificates are
untrusted. Validate actual executable bytes, layout, relocations and entries; an assembly listing
or a proof that stops before assembly/linking is not the deliverable.

Every theorem and checker rule must apply to arbitrary supported source texts. Per-program
witnesses demonstrate that the theorem is useful, but cannot define acceptance. Preserve every
existing safety, concurrency, contract and cost guarantee. Unsupported cases cause refusal.
The selected path removes the C compiler from the intended trust base; it has not done so today.

## 2. Reuse instead of rebuilding

- Lean parser/elaborator and source-computed duties: `grammatik/Grammatik/Parser/`,
  `bruecke/Bruecke/Quelle.lean`; GabbroV: `programmlogik/`.
- Existing concurrent source model: `grammatik/Grammatik/Speichermodell/`, especially
  `Sicht.lean`, `MaschineW.lean`, `GXMaschine.lean`, `AtomarW.lean`.
- Goal statement and proof: `grammatik/Grammatik/Zielsatz/Spec.lean` and
  `BeweisAtomar.lean`. Read `SchwachX`, `ZielX`, `GabbroZiel` and the named gap list.
- Generic correspondence/certificate architecture and abstract ticket-lock proofs may supply
  reusable techniques. C-specific semantics and closing theorems remain C-specific evidence.

W / GX already support the source-side weak-memory and shared-atomic reasoning. Prove that
EVERY permitted execution of the generated x86 image refines that model. Choose a per-access
TSO-to-W-to-GX relation, or a direct TSO-to-GX relation preserving all required properties.
Neither x86-TSO correspondence nor concrete lock/runtime correctness follows automatically
from the existing model theorem. The old C `DRFSC` premise cannot stand in for this proof.

## 3. First work package and gates

1. Inventory ALL source operations and emitter/runtime paths, including widths, atomics,
   hardware access and generated entry code. Do not define coverage by example binaries.
2. Write the fixed machine profile: instruction encodings, byte memory, TSO access events,
   layouts, stack/ABI, flags, traps and the relation to the existing source model. Explicitly
   distinguish coherent RAM from MMIO/DMA. Review this before adding a large instruction set.
3. Deliver a generic pilot validator through final bytes for integer data, memory, control
   and calls, with a non-degenerate witness and altered-byte rejection probes. Check every
   relocation, executable target and data layout used by that pilot.
4. Prove atomic-order and lock mappings early. Cover ordinary access footprints, tearing and
   alignment, CAS success/failure, store buffers, retry loops and publication. No implicit
   atomicity for a whole emitted sequence. Preserve progress for infinite executions too.
5. Extend the generic mechanism to floating point, regions, runtime/entries, linking and
   performance profiles; each extension requires its Lean semantics and correspondence first.

Use 64-bit execution, retain narrow data operations, and prefer a small semantic core with
proved extensions. Legacy execution modes, x87 and MMX are outside the initial profile.
Do not promise maximum performance from an instruction-count minimum. Do not change the source
language's memory-ceiling or termination policy to make the backend easier.

A first package is complete when its generic decoder/refinement statements and validator are
proved, its witness passes, its planted defects fail, and its missing coverage is listed.
It must not report the whole language or concurrent binaries verified on that basis.

## 4. Rules and coordination

- No `sorry`, `admit`, `native_decide` or new axiom. The goal theorem retains exactly
  `propext`, `Classical.choice`, `Quot.sound`; new lemmas use at most those standard axioms.
- No weakening to obtain a proof. Changes to `Zielsatz/Spec.lean` require the existing reviewed
  statement-change process; do not modify it merely to avoid a target-side obligation.
- Source and model guarantees stay generic; examples and function names are off the trust path.
- OS services and runtime/binding routines are user logic with checked implementations and
  contracts, not hardware assumptions. Only hardware behaviour stays a named assumption.
- Coordinate before changing `Zielsatz/`, `programmlogik/`, source parser/exporters or shared
  compiler files. Keep the current C backend and its regression guardians working.
- Local builds only. Use the project's lane wrappers where applicable. Run relevant Lean,
  Rust and emission checks for implementation changes; no red merge or push.
- Documents, comments and commit messages are English. Commit through `./commit.sh`.

## 5. Measurement and hand-in

Report the generic statements proved, supported semantic/encoding families, final-byte binding,
positive witnesses and rejected mutations, with commands and explicit gaps. Source coverage
comes from the implementation inventory; corpus counts diagnose coverage but do not prove a
universal claim. `instrumente/zaehle-kette.py` and `pruefe-cformen.py` still measure C evidence.
Do not relabel their output as x86 validation.

Update `TODO.md` §2, the active plan and the theorem map for each delivered proof. Keep PRs
small and reviewable. The former C line/token/cost estimates are not an estimate of this work;
measure the generic pilot before scheduling the full backend and proof chain.
