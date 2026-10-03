# ARBEITSPLAN-AKTUELL — standing dynamic work plan for compiler/hardware closure

*Owner: planner lane 1098 (this file) plus `MUSE-REPORT-1098.md`.
Status: organisation only — no implementation, no proof, no closure claim.
Central progress record: `DIRECT-COMPILER.md`.
Scope records: `DIRECT-COMPILER-DESIGN.md` (essential/deferred scope),
`dokumente/x86/HARDWARE-INTEGRATION-COVERAGE.md` (producer/consumer states, lane 732),
`dokumente/x86/FULL-COMPILER-WORK-PLAN.md` (lane 744, once integrated).*

## Cycle 2026-10-03 (planner 1098)

Base: `03491267` (merge of reviewer 974). No `ARBEITSPLAN-AKTUELL.md` existed
in this base, so this file starts here; earlier planner cycles (e.g. lane 1099)
left no committed section in this clone.

### 1. Committed state read from this clone (not from live private registry)

The live coordinator registry (`manifest.json`, `state/`, `dispatch.json`,
`watch.json`, task-brief audits B01–B11) is private to the coordinator and was
NOT visible from this clone. The states below rest on committed evidence only:
`DIRECT-COMPILER.md` history entries, committed `lanes/*.md` prompts (present
= not finally integrated; absent = merged or removed), `git log`, and the
`grammatik/Grammatik/X86/` tree. The coordinator MUST re-check the live
registry at registration (PIDs, holds, blocking lists may have moved).

Accepted and integrated in this base (consumers now available as dependencies):
720/721 (integer bytes to shared TSO execution), 728/729 (IDT/TSS descriptor
layer), 730/731 (SIB/RIP-relative addresses to actual effects), 738/739
(fault ordering across fetched accesses), 824/974 (decode-to-execution
closing through the common dispatcher, bounded ACCEPT), 860/1010 (optimiser
constant folding), plus compact/fence/CAS/FP rows 746–785 with reviewers
896–939, 704/705 (port bus, after one gate rejection), 710/711 (PR-1 review),
714/715 (PR-2 ISA review). Full source-to-final-bytes validation remains OPEN;
every `DIRECT-COMPILER.md` publication entry says so.

Gate-rejected, repair required (coordinator resume of the owning author lane
with a fresh exact-commit review — NEVER a new author on the same file):
698/699 (shift/rotate widths), 718/719 (unified dispatch
`HardwareDecodeDispatch.lean`), 722/723 (LOCK to buffers
`ConcurrentAtomicExecution.lean`). Rejection entries in `DIRECT-COMPILER.md`
lines 1122–1124 say: "Author repair and a fresh exact-commit review are
required. No failing candidate was merged."

Gate-rejected with NO lane file left in this base (752/902, 757/907,
759–768/909–918): repair ownership is unclear from committed state. The
coordinator confirms from the live registry whether a repair lane already owns
this work before proposing anything adjacent.

Still registered / active — disjointness boundary for this wave (OWN ONLY
lines read 2026-10-03): 672 (HELD: `HardwareInterrupts.lean`), 690
(`Vector256HardwareForms.lean`), 696 (`ByteWidthHardwareForms.lean`), 698
(`ShiftWidthHardwareForms.lean`), 708 (`LongModeReturnHardwareForms.lean`),
718 (`HardwareDecodeDispatch.lean`), 722 (`ConcurrentAtomicExecution.lean`),
724 (`ConcurrentFloatingExecution.lean`), 726 (`PagedMemoryHardware.lean`),
734 (`ControlRegisterHardwareForms.lean`), 736
(`ContextStateHardwareForms.lean`), 740/741 (PR-2 Lean repair patch),
742/743 (PR-2 Rust repair patch), 744 (full-compiler work plan, unaccepted),
1094/1096 (pool tools). Held lanes 672/673/684/685 are never touched and no
hold is cleared by any proposal below (no TOCTOU).

### 2. Wave proposal of this cycle: 6 authors + 6 exact reviewers (12 slots)

Twelve of the 15 model slots; 3 slots stay free for the 698/718/722 repair
resumes and for 744/745 landing. All six authors are Lean-kind, mutually
disjoint by owned file, depend ONLY on already-accepted modules (never on
unmerged 718/722/724/726/734/736/690/708/696/698 APIs), and can run in
parallel. Integration in any order; serial checked publication unchanged.

- **P1-A — defined auxiliary-carry rows (F-AF slice).** New
  `X86/AuxiliaryCarryRows.lean`. Over accepted 720 (`ConcurrentIntegerExecution`),
  692 (`ArchitecturalFlags`), 666 (`IntegerHardwareForms`): per admitted
  integer row either the defined AF value or a proved non-observability lemma
  consumed by every flag consumer. The `af : Option Bool` abstraction is never
  cited as a defined hardware result.
- **P1-B — port/device execution on the common machine (F-DEV slice).** New
  `X86/DeviceCommonExecution.lean`. Over accepted 704 (`DeviceBusHardwareExecution`),
  694 (`MemoryTypeHardwareExecution`), 728 (`InterruptDescriptorHardware`):
  ordered IO events, privilege/IOPL/TSS outcomes, generic device-response
  interface; RAM TSO inheritance refused by construction (preserve the 694
  enforcement).
- **P1-C — close the accepted consumers through the common dispatcher.** New
  `X86/ComposeAcceptedConsumers.lean`. Over accepted 824 (`ComposeDecodeExec`),
  720, 730 (`AddressedHardwareExecution`), 738 (`ExceptionPriorityHardware`),
  728: one fetched-execution theorem composing the accepted integer, address,
  fault-priority and descriptor rows on `HwMaschine` (660). No import of any
  unaccepted consumer; missing width/LOCK/FP/paging rows stay explicit
  pending extensions, never assumed.
- **P2-D — realised per-access footprints for the 720 integer rows.** New
  `X86/IntegerAccessFootprints.lean`. Over accepted 720, 738 and the accepted
  TSO/word modules: footprint lemmas for every realised 720 access feeding the
  mandatory F-6B typed-carrier TSO bridge; 128-bit/shared-row atomicity limits
  stay explicit.
- **P2-E — binary32 fetched steps with a lifting API for consumer 724.** New
  `X86/ScalarFloat32FetchedSteps.lean`. Over accepted 702
  (`ScalarFloat32HardwareForms`), 730, 720 (memory discipline), 668/682
  (kernel/control inputs): fetched binary64-style execution for `S32Op` rows
  on per-core FP state, CVTSD2SS narrowing witness required,
  sticky/payload CUTS stay OPEN. DEFINES the lifting API; never imports the
  unaccepted 724 module.
- **P2-F — packed-integer fetched steps with a dispatch-slot API.** New
  `X86/VectorIntegerFetchedSteps.lean`. Over accepted 686
  (`VectorIntegerHardwareForms`), 720, 730: fetched execution preserving the
  proved saturate-vs-mask divergence (`vecShlQ_satt_vs_maske`), 128-bit access
  non-single-copy-atomic, shared vector stores refused until the 6B bridge
  rules them. DEFINES the slot API; never imports unaccepted 718/724.

Full register-ready texts (title, kind, owned paths, dependencies, priority,
task text, review text) are in `MUSE-REPORT-1098.md`. NO lane numbers there —
the coordinator allocates live IDs at registration.

### 3. Explicit non-goals of this wave (with reason)

- 698/718/722 repairs: same-file ownership; coordinator resume only.
- 752/757/759–768 follow-up: ownership unclear in this base; confirm live first.
- Interrupt delivery / F-RET: needs held 672 plus active 708/726/734 — blocked.
- F-6B full bridge and closing validator: premature until 722/724 accepted.
- F-AVX: needs active 690/736 — blocked.
- SYSCALL/SYSRET byte forms: documented next-wave candidate (accepted 728
  descriptors as base, 708/726/734 inputs as honest-pending interfaces).
- PR-2 Lean/Rust repairs: registered 740–743 — no duplicate.
- Friend-reserved optimiser files and 684-owned instruments/docs: untouched.
- 744-dependent pipeline validation: 744 unaccepted — no 744 API assumed.
- Benchmark/GCC-O3 measurement: needs an accepted pipeline — premature.
- AMD provenance / silicon proof: none claimed anywhere.

### 4. Handoff to the next planner cycle

Resume the planner when the queue runs low or when 744/745 lands, a repair
resumes, or a hold clears. Re-read the live registry first; registration state
is not inferable from this file. Next expected inputs: 744 acceptance (unlocks
pipeline integration wave), 718/722/698 repair outcomes (unlock F-6B slices and
dispatch-dependent rows), 724/726/734/736 acceptance (unlock F-B32/F-VEC
plug-in, F-RET staging, F-AVX).
