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
registry at registration (PIDs, holds, blocking lists may have moved) AND
re-verify the §1 disjointness statements against the post-`03491267` delta:
tip `b040b155` (merge 975) was unavailable in the planner clone (lane fetch
is denied), so new merges, newly registered owned paths, newly cleared/added
holds, and the 698/718/722 repair plus 744/745 landing state at registration
time are gating inputs, not assumptions.

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

## Cycle 2026-10-04 (planner 1112)

Base: `7f81b2c6` (docs: track the direct compiler Lean-first validation work;
lane files `lanes/1112.md`, `lanes/1113.md` registered here). This clone
verifies branch `muse/1112`. Organisation only — no implementation, no proof,
no closure claim. Full source-to-final-bytes validation remains OPEN; every
`DIRECT-COMPILER.md` publication entry says so.

### 1. Committed state read from this clone (live registry NOT visible)

The live coordinator registry (`manifest.json`, `state/`, `dispatch.json`,
`watch.json`, PIDs, dispatcher queue/backoff, watch gate errors, B01–B11
blocking lists) is private to the coordinator: `.claude/` does not exist in
this clone, so NONE of it was readable here. Task-brief audits B01–B11 are
likewise not in the tree (only the committed audit-batch lanes `1061`
(B08) / `1062` (B09) exist as prompts). Everything below rests on committed
evidence only: `git log` (merge commits), `DIRECT-COMPILER.md` history and
register table, committed `lanes/*.md` prompts (present = not finally
integrated; absent = merged or removed), committed
`messung/muse/MUSE-REPORT-*.md`, and the `grammatik/Grammatik/X86/` tree at
`7f81b2c6`. The coordinator MUST re-check the live registry at registration
(PIDs, holds, queue, blocking lists may have moved) AND re-verify the
disjointness statements against the post-`7f81b2c6` delta (lane fetch is
denied from this clone, so newer merges, newly registered owned paths and
newly cleared/added holds are gating inputs, not assumptions).

1100-wave A–F outcomes (cycle-1 wave of planner 1098), from committed state:

- **A — defined auxiliary-carry rows (1100 author / 1101 review): MERGED**
  (`071d4a37`, `657d178e`; `DIRECT-COMPILER.md` `x86-merged:1100`,
  `x86-merged:1101`; file
  `grammatik/Grammatik/X86/AuxiliaryCarryRows.lean` in tree;
  `messung/muse/MUSE-REPORT-1100.md` / `-1101.md`). Covers the admitted
  720 load/store rows on the AF non-observability leg only; the report
  names the follow-up explicitly (ADD/SUB/NEG families need their own
  `AuxDefined` constructors) — see §3 for why it is NOT proposed here.
- **B — port/device execution on the common machine (1102 / 1103):
  MERGED** (`3e8d2f1f`, `43211329`; `x86-merged:1102`, `x86-merged:1103`;
  `DeviceCommonExecution.lean` in tree; reports `-1102.md` / `-1103.md`).
  F-DEV as scoped (depends on accepted 704 + 694) is thereby delivered;
  its CUTS (hardware correspondence, pending responses enumerated never
  answered, no TSO/GX simulation, no source/ABI/budget link) names no
  follow-up against accepted-only modules — no follow-up proposed.
- **C — compose accepted consumers (1104 / 1105): MERGED** (`e74989df`,
  `df46d5fa`; `x86-merged:1104`, `x86-merged:1105`;
  `ComposeAcceptedConsumers.lean` in tree; reports `-1104.md` /
  `-1105.md`). Nine pending families stay explicit pins
  (`breite696/698`, `lock722`, `fp724`, `seiten726`, `steuer734`,
  `kontext736`, `avx690`, `rueck708` — the ninth is the width split);
  which bytes each family will accept stays with the owning lanes.
- **D — realised per-access footprints (1106 author / 1107 review):
  NOT LANDED in this clone.** Both lane files are still present
  (registered/active); no `MUSE-REPORT-1106.md` / `-1107.md` exists in
  `messung/muse/` or the clone root, and `IntegerAccessFootprints.lean`
  is absent from the tree. Outcome (working / awaiting review /
  repair) is unknown from committed state. Coordinator owns it under
  the same-file rule (resume 1106 on the same file, never a new lane);
  §2 proposes nothing on that path.
- **E — binary32 fetched steps with lifting API (1108 / 1109): MERGED**
  (`646172c4`, `fc5b465e`; `x86-merged:1108`, `x86-merged:1109`;
  `ScalarFloat32FetchedSteps.lean` in tree; reports `-1108.md` /
  `-1109.md`). This is the API side for consumer 724, not the F-B32
  plug-in (needs accepted 724) — still blocked, see §3.
- **F — packed-integer fetched steps with dispatch-slot API (1110 /
  1111): MERGED** (`d6f693a4`, `61eb1e8b`; `x86-merged:1110`,
  `x86-merged:1111`; `VectorIntegerFetchedSteps.lean` in tree; reports
  `-1110.md` / `-1111.md`). Slot API for 718, not the F-VEC plug-in
  (needs accepted 718 + 724) — still blocked, see §3.

**Umbrella-import gap (finding):** all five merged 1100-wave files exist
in the tree, but `grammatik/Grammatik.lean` at `7f81b2c6` imports NONE of
them (each author report records the lane permission gate denying the
edit and leaves the one line as merge action; later `Grammatik.lean`
merges such as 885 did not add them either). Consequences: (a)
`./lean-bau` does not cover the five files in this clone; (b) §2 authors
import them by full module path (`Grammatik.X86.<Name>` — the files
exist, so this resolves) and MUST NOT edit `Grammatik.lean`; (c) the
coordinator lands the five import lines through the merge-script union
before or with the §2 integrations, and re-verifies coverage with
`./lean-bau`. If origin/master already carries the lines (this clone
cannot fetch), (c) is already done — re-check at registration.

Still registered / active — disjointness boundary for this wave (OWN
ONLY lines read 2026-10-04 in this clone): 672/673 (HELD:
`HardwareInterrupts.lean`), 684/685 (external-path tooling, not
hardware), 690/691 (AVX2 forms), 696/697 (8/16/32-bit widths), 698/699
(shift/rotate widths, gate-rejected repair), 708/709 (long-mode
return), 718/719 (unified dispatch, gate-rejected repair), 722/723
(LOCK to buffers, gate-rejected repair), 724/725 (coherent FP), 726/727
(paging), 734/735 (control registers + syscall MSR), 736/737 (context),
740/741 (PR-2 Lean repair), 742/743 (PR-2 Rust repair), 744/745
(full-compiler work plan), 1094/1095 + 1096/1097 (pool tools), 1106/1107
(footprints), 1112 (this planner), 1113 (exact review of this cycle).
Held lanes are never touched and no hold is cleared by §2
(no TOCTOU). `FULL-COMPILER-WORK-PLAN.md` does not exist in this clone
(744 unaccepted). `instrumente/upstream-pr-2-lean.patch` does not exist
(740 repair not delivered as a file here). Local refs are only `master`
and `muse/1112`: no `feat/*` branch is fetchable from this clone, and
lane fetch is denied — PR merge-verify stays blocked-on-fetch, see §3.

Accepted-only dependency surface used by §2 (all umbrella members at
`7f81b2c6` unless noted): `Codec`, `Byteschritt`, `HardwareExecution`
(660), `ConcurrentIntegerExecution` (720), `AddressedHardwareExecution`
(730), `ExceptionPriorityHardware` (738), `InterruptDescriptorHardware`
(728), `ComposeDecodeExec` (824), `ComposeAcceptedConsumers` (1104 —
merged file, umbrella line pending per the gap above), `AuxiliaryCarryRows`
(1100), `DeviceCommonExecution` (1102), `ScalarFloat32FetchedSteps`
(1108), `VectorIntegerFetchedSteps` (1110), `OptDceDead` (865+1015),
`OptDceStore` (866+1016), `ValidatorSkeleton` (349+387). No X86 module
imports `OptDceDead`/`OptDceStore` today (validator-side DCE admission
is genuinely open). Friend-reserved `OptimizationRules.lean` /
`OptimizationWitnesses.lean` are never touched.

### 2. Wave proposal of this cycle: 3 authors + 3 exact reviewers (6 slots)

Six of the 15 model slots; the rest stay with the coordinator for the
1106/1107 outcome, the 698/718/722 repair resumes, the 744/745 landing
and live-queue backfill. All three authors are Lean-kind, mutually
disjoint by owned file, depend ONLY on the accepted-only surface above
(never on unmerged 718/722/724/726/734/736/690/708/696/698 APIs and
never on the unmerged 1106 file), and can run in parallel. Integration
in any order; serial checked publication unchanged. NO lane numbers
below — the coordinator allocates live IDs at registration.

- **W1-A — compose the newly accepted rows beside the 1104 closing
  (integration).** New `X86/ComposeExtendedConsumers.lean`. Over merged
  1100 (AF non-observability per admitted row), 1102 (device common
  steps with TSO refusal + UC ordering), 1108 (S32 fetched steps +
  lifting interface), 1110 (packed-integer fetched steps + slot
  interface) beside accepted 1104 (`ComposeAcceptedConsumers`) and 824
  (`ComposeDecodeExec`): per-new-row fetched-execution coexistence
  with `composeAccepted_gesamt` on the common discipline (same or
  disjoint-address witness machines; no second dispatcher, no restated
  consumer lemma), plus proof that all 1104 `PendingFam` pins stay open
  (none of the four new rows belongs to a pending family; adding a
  family without a pin must still be a type error). The unmerged 1106
  footprints are NOT consumed. Targets: `extendedRows_coexist` (each
  new row's fetched agreement runs without breaking the 1104 closing)
  and `extendedRows_luecken_bleiben` (pending pins preserved +
  four-row classification). ZEUGE: joint witness reusing the four
  lanes' reached memory-changing runs on disjoint addresses, plus
  planted probes: a pending-family byte claimed covered (refused by
  `decide`), a shared vector store claimed single-copy-atomic
  (refused). CUTS: per-access TSO→W/GX simulation, `valX86_sound`
  and the closing theorem stay OPEN (F-6B, blocked until 722/724
  accepted); no source/ABI/entry/budget claim.
- **W1-B — SYSCALL/SYSRET trap-entry gating over accepted checks
  (hardware slice).** New `X86/SyscallTrapEntryGating.lean`. Over
  accepted 728 (`InterruptDescriptorHardware`, DPL/privilege reuse
  precedent: 1102 `dev_dpl_verweigert_software`), 738
  (`ExceptionPriorityHardware`), 720 (memory discipline) and the
  `Codec`/`Byteschritt` fetch discipline on 660 (`HardwareExecution`):
  first a checked decoder census for `0F 05` (SYSCALL) / `0F 07`
  (SYSRET) over the accepted `decodeExt`/codec rows — rows with no
  accepted decoder get explicit refusal pins (`decodeExt = none` by
  `decide`), never invented rows; then the trap-entry gate contract
  (CPL gate via accepted 728 privilege fields, trap-vs-fault order via
  738 or explicit pending where 738 is silent, fetched-step hook
  running the gate on the common discipline). MSR/return/paging legs
  stay explicit pending refusals naming their owning lanes
  (734/708/726), DEFINING the slot those lanes plug into (1108/1110
  precedent) and never importing their files. NO producer-form work:
  no MSR semantics, no return forms, no page walks, no parallel
  privilege model (1102 §-finding: IDT gates and IO bitmaps are
  different tables — the same discipline applies here). Targets:
  `syscallGate_stimmt` (gate contract per fetched trap row) and
  `syscallGate_offen_bleibt` (pending legs refused, owners named).
  ZEUGE: joint witness with a refused wrong-CPL gate and a refused
  SYSRET-with-unaccepted-return-state pin beside one admitted
  gate-shaped fetched step. CUTS: F-RET delivery, paging, MSR effects
  and silicon correspondence stay OPEN. ADJACENCY RISK (for reviewer
  1113 and the coordinator): semantic neighbours 708/734 are
  registered with their own mandates (`LongModeReturnHardwareForms`,
  `ControlRegisterHardwareForms`); this task forbids producer areas by
  construction, but veto it on any overlap the live task texts show.
- **W1-C — validator-side DCE admission on the non-reserved path
  (optimiser/validator slice).** New `X86/ValidatorDceAdmission.lean`.
  Over accepted 865/1015 (`OptDceDead`: pure + dead-confirmed removal
  preserves `execBlock` outcome) and 866/1016 (`OptDceStore`) with
  accepted 349/387 (`ValidatorSkeleton.valX86`) plus
  `DecodingCoverage`/`Byteschritt` re-decoding: the validator
  RECOMPUTES purity/deadness from the accepted rule vocabulary (no
  trusted annotation, no rival purity predicate, no forked
  evaluator), and proves (T1) `dceZugelassen_bleibt` — a removal
  satisfying the accepted side conditions preserves
  admission-relevant bytes (a removed op's bytes were never a decoded
  start the admission relies on — re-decided coverage — or the block
  is explicitly refused); (T2) `dceVerweigert_laut` — the DESIGN §7
  failure cases stay refused at validator level: faulting FP
  (`0.0/0.0` hiding `logik bereich`), spin/wait-load removal
  (REVIEW-OPT-BINAER §2: DCE never removes a spin/wait load), and
  exit-edge preservation per block map. Friend-reserved
  `OptimizationRules`/`Witnesses` are never touched; the work is the
  validator check, not the rule library. ZEUGE: joint witness with an
  admitted pure-dead-local removal beside two refused probes (spin
  load, `0.0/0.0`) on reached fetched runs. CUTS: `valX86_sound`,
  the full closing validator and the budget-stop link stay OPEN
  (CE-1: no theorem connects a deleted op to a preserved exhaustion
  stop); no compile-latency or GCC-ratio claim.

Full register-ready texts (title, kind, owned paths, dependencies,
priority, task text, review text) are in `MUSE-REPORT-1112.md`. The
coordinator registers them as-is (IDs allocated live) or vetoes W1-B
on the stated adjacency risk.

### 3. Explicit non-goals of this wave (with per-candidate blocker)

- 1100-wave D follow-up: 1106/1107 still registered, outcome unknown in
  this clone — coordinator resume of 1106 on the same file on REPAIR,
  integration of the exact candidate on ACCEPT. Never a new lane on
  `IntegerAccessFootprints.lean` (no overlapping writer).
- 698/718/722 repairs: gate-rejected authors repair on their own
  files with fresh exact-commit reviews (coordinator resume only).
  Never new lanes on `ShiftWidthHardwareForms`,
  `HardwareDecodeDispatch`, `ConcurrentAtomicExecution`.
- 744/745 pipeline integration: 744 unaccepted
  (`FULL-COMPILER-WORK-PLAN.md` absent) — direction (2) is respected:
  nothing is proposed that assumes a 744 API.
- PR-1/PR-2 merge-verify authors: 740–743 repairs stand registered;
  no `feat/*` branch exists in local refs and lane fetch is denied, so
  there is nothing read-only-verifiable to verify against —
  blocked-on-fetch per direction (3). Propose them only after a fetch
  shows the branches.
- F-B32 plug-in: needs accepted 724 (724 lane file present,
  unaccepted; 1108 delivered only the lifting API). Blocked.
- F-VEC plug-in: needs accepted 718 + 724 (both unaccepted; 718 in
  repair). Blocked.
- F-RET delivery: needs 672 (HELD) + 708/726/734 (active). Blocked;
  W1-B stages only the accepted-checks gate, never the delivery.
- F-AVX: needs accepted 690 + 736 (both active). Blocked.
- F-6B typed-carrier TSO bridge and closing validator: needs
  722/724 (+720/738 facts) — premature until the repairs and 724 land.
- Defined-AF arithmetic rows (ADD/SUB/NEG `AuxDefined`
  constructors, named as follow-up in MUSE-REPORT-1100): needs a
  fetched arithmetic-row consumer — accepted 720 connects load/store
  rows only (`concLoadMaschine`/`concStoreMaschine`). Blocked until
  such a consumer exists; proposing it now would manufacture its own
  premise.
- Interrupt delivery / held work (672/673), external-path tooling
  (684/685), pool tools (1094–1097), friend-reserved optimiser files:
  untouched. No hold cleared, no instrument/doc owned elsewhere
  edited.
- Benchmark/GCC-O3 measurement and fast-compile telemetry: need an
  accepted pipeline — premature (no measured speed is claimed
  anywhere). AMD provenance / silicon proof: none claimed anywhere.

Direction (4) reconciliation: SYSCALL/SYSRET is proposed as the
accepted-checks gate slice W1-B (not the byte forms, which belong to
registered 708/734); the DCE validator non-reserved path is proposed
as W1-C (rule lemmas 865/866 accepted, no module connects them to the
validator); F-DEV already landed via 1102/1103 (no duplicate); F-B32
remains blocked on accepted 724 (1108 was the API side, not the
plug-in). Direction (5) is respected by proposing 3 substantive pairs
instead of filler: the remaining slots belong to the coordinator's
live backfill (1106/1107 outcome, repair resumes, 744 landing), not to
invented work.

### 4. Handoff to the next planner cycle

Resume the planner when the §2 wave is registered (reviewer 1113
verdict), when 1106/1107 resolves, when 744/745 lands, when a repair
resumes, or when a hold clears. Re-read the live registry first. Next
expected inputs: 1113 verdict on this cycle (especially the W1-B
adjacency call), 1106/1107 outcome (unlocks footprint consumers for
the F-6B facts), 744 acceptance (unlocks the pipeline integration
wave), 718/722/698 repair outcomes, 724/726/734/736 acceptance
(unlock F-B32/F-VEC plug-ins, F-RET staging, F-AVX).

