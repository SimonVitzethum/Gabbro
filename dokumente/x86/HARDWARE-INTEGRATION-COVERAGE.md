# Hardware integration and executable coverage — selected x86-64 model

*Owner: lane 732 (organisation only). Owned file per `lanes/732.md`.
Status: PROPOSED organisation, not an implementation or a proof.
Nothing here claims any source-to-final-bytes chain is closed.
Central progress record: `DIRECT-COMPILER.md`.
Scope record: `dokumente/x86/HARDWARE-MODEL-COMPLETION.md` (lane 678).
Design scope: `DIRECT-COMPILER-DESIGN.md` sections 2A/2D/3–6.
Measured source baseline in this clone: `9fc15bf4`
(`docs: track the direct compiler Lean-first validation work`).
No in-flight candidate was inspected: producer clones were not accessed;
in-flight states below come from the committed registry in
`DIRECT-COMPILER.md` and the committed task prompts in `lanes/`.*

## 0. What this document is for

The scope matrix (lane 678) records per-family WHAT is proved and what stays
OPEN. This document records the integration mechanics: for every accepted
constructor/form row, WHERE its bytes execute, whether that execution runs
through the ONE common architecture, and which scheduled consumer closes the
remaining gap. Columns per row:

- **Real codec**: actual byte decoder/encoder over real bytes (file, entry
  theorems) — never encode-equality alone.
- **Manual provenance**: recorded Intel SDM heading/page in the producer
  report; `.tmp/HARDWARE-REFERENCES/` is gitignored and clone-local, so no
  provenance file exists in this clone — provenance lives in the committed
  producer reports and each module's CUTS.
- **Canonical evaluator**: actual effect function reusing canonical helpers
  (`Wort`, `Ganzzahl`, `logikFlags`, `Gleitprofil` kernel, `stepExt`).
- **Common fetched dispatcher**: whether the row executes through the shared
  `HwMaschine`/`HwSchritt` composition
  (`grammatik/Grammatik/X86/HardwareExecution.lean`) via fetched bytes.
- **TSO/per-access effects**: buffered-issue/forward/flush treatment, word
  grouping, atomicity posture.
- **Control/fault/flags**: raw observable register/flag/FP/fault treatment.
- **Joint reached witness**: memory-changing reached run plus planted
  refusal probes.
- **Tests/review evidence**: merged report and reviewer.

Verdict per row: **executed** (bytes run through the common machine),
**produced** (codec + evaluator + own witness proved, common-machine
connection pending), **in flight**, or **missing**.
Producer work (byte rows) versus consumer work (unified dispatch and common
execution) is distinguished in every row: an ACCEPT verdict on a producer
covers its exact delivered claim only.

## 1. The common architecture (consumer foundation, accepted)

`HardwareExecution.lean` (902 lines, lane 660, reviewed by 661) defines
`HwKern` (per-core data, no memory), `HwMaschine` (one shared `Speicher`,
per-core data, per-core TSO buffers, one `HwProfil`, per-core
`BereitProfil`), projections with proved agreement
(`projZustand_speicher`, `projFp_speicher`, `kerne_ein_speicher`,
`tsoAnsicht_speicher`, `tsoAnsicht_puffer` at `:63-79`), `HwWf` with
`hwWf_aus_zugelassen` (`:95`), `HwSchritt` with cases `reg`/`lade`/
`gibAus`/`spuele`/`fehler` (`:173-190`), the computable register step
`hwByteschrittReg` with `hwByteschrittReg_rechtfertigt` justifying
`HwSchritt.reg`, and the joint witness `hwWit_zeuge` joining 11 closed
facts with an actual shared-memory drain 0 → 42 (`:795` region).
Crucially, `HwSchritt.reg` steps through `stepExt` over the OLD
`ExtendedExecution` dispatcher only (`:174-176`); every newer producer
family needs a consumer lane to reach this machine. The `HwAdapter`
extension points (`:815-854`: `adapterLocked662`, `adapterInteger666`,
`adapterFp668`, `adapterFault670`, `adapterInterrupt672`) are typed over
the OLD event vocabularies (`SperrBefehl`, `ExtInstr`, `FpDecodiert`,
`MulDivDecodiert`, `Unit`) — two of them are register-path plugs, three
are explicit refusals awaiting their producers.

## 2. Constructor/form/observable matrix

### Row P0 — pilot 14 forms (accepted foundation)

Codec: `Codec.lean` round trip for all 14 forms. Evaluator: `Ausfuehrung.lean`
per-form step equations. Dispatcher: **executed** — `decodeExt`/`stepExt`/
`fetchExt`/`extByteschritt` in `ExtendedExecution.lean` (828 lines) plus
`hwByteschrittReg` on `HwMaschine`. TSO: byte-issue discipline via
`issueListe`/`hwWortAusgabe` (eight byte issues, never SC `write64`);
aligned-word single-copy grouping stays with consumer 720. Flags: pilot
`Flags` with `af : Option Bool`. Witness: store-changing reached runs,
`realisiert_fuss_abdeckung` over all 14 forms (`AccessExecution.lean`).
Review: lanes 272/279/296.

### Row I1 — practical integer widths (producer 666 accepted; 696/698/700)

- Accepted: `IntegerHardwareForms.lean` (1544 lines, lane 666, reviewed
  667). `IntHwOp` (`:24`), evaluator `intHwWert` reusing canonical
  `Ganzzahl`/`ShiftLogic` producers (`:33`, imports `:10-18`), flags via
  `logikFlags` (`intHwFlagsLogik`, `:58`; `inthw_logik_af_none`, `:68`),
  b32 zero-upper merge (`inthw_b32_clears`, `:103`), b64 full agreement
  (`inthw_b64_agrees`, `:73`), encoder `encodeIntHw` (`:161`),
  decoders `decodeIntHwModrm`/`decodeIntHwF7`/`decodeIntHwNach`/
  `decodeIntHw` (`:213-264`), round trips (`:285-291`),
  fetched steps `intHwByteschritt`/`intHwImmByteschritt` over `Zustand`
  (`:976-985`). Verdict: **produced** — own fetched step over `Zustand`,
  NOT yet stepped on `HwMaschine`; consumer 720 owns that connection.
- Accepted: `MulDivWidthHardwareForms.lean` (2058 lines, lane 700,
  reviewed 701). `WdBreite` (`:29`), divide refusals at zero/overflow
  (`divWeitU32_verweigert_bei_null`, `divWeitU32_verweigert_bei_ueberlauf`,
  `:107-113`), `WdBefehl` (`:211`). Immediate-IMUL round trip stays in
  CUTS (`:762`); divide rows stay refused as essential OPEN per header
  (`:8`). Verdict: **produced**; consumer 720 (width accesses) and 738
  (divide fault priority).
- In flight: 696 (8/16/32-bit arithmetic and moves,
  `ByteWidthHardwareForms.lean`, agent working) and 698 (width-selected
  shifts/rotates, `ShiftWidthHardwareForms.lean`, agent working).
  Partial-register (8/16-bit) versus 32-bit zero-upper semantics for the
  NEW byte rows is decided by these producers, not assumed.

### Row I2 — LOCK atomics and fences (producer 662 accepted; consumer 722)

Accepted: `LockedInstructionExecution.lean` (1144 lines, lane 662,
reviewed 663). `LockForm` (`:34`), `LockAnweisung` (`:64`), encoder
`encodeLock` (`:73`), decoder `decodeLock` (`:187`), round trips for
XADD/CMPXCHG (`:240-252`), full step `lockSchrittVoll` over its OWN
`LockMaschine` (`:333`), fetched `lockByteschritt` (`:658`). Imports
reuse canonical `TSO`, `LockedOps`, `WordAtomicity`, `ExtendedExecution`,
`FeatureProfile` (`:18-27`) — no second TSO invented. Verdict:
**produced** — own machine, own fetched loop; the `HwMaschine` bridge
(prior drain, one aligned atomic access, failed-CAS permission
semantics, interleaved observers) is consumer 722, which must project
through the existing RMW evaluator, never a desired equality. Recorded
obstruction (not a defect): `cas_fehlschlag_stottert` in `LockedOps.lean`
— the failure path stutters and proves nothing about failed-path access
rules; 722 resolves it per the manual or leaves the row refused.

### Row I3 — scalar FP binary64 (producer 668 accepted; consumer 724)

Accepted: `ScalarFloatHardwareForms.lean` (2203 lines, 73 defs,
148 theorems, lane 668, reviewed 669). Encoders `fpHwEncodeArithRR/RM`,
`fpHwEncodeUcomiRR/RM`, `fpHwEncodeCvtsi/Cvtt`, `fpHwEncodeMovsdRR/Lade/
Speichere` (`:68-125`), length lemmas (`:133-154`), decoders
`fpHwDecodeReg/MemForm/Rest` (`:190-247`). Reuses the accepted IEEE
kernel. CUTS (`:2091`): NaN payloads class-level only, sticky MXCSR
bits unmodelled, raw-bit fidelity OPEN. Verdict: **produced**; consumer
724 derives fetched binary64 execution on per-core FP state with shared
buffered memory, preserving XMM upper lanes and raw MXCSR control.

### Row I4 — scalar FP binary32 (producer 702 accepted; NO consumer scheduled)

Accepted: `ScalarFloat32HardwareForms.lean` (1853 lines, lane 702,
reviewed 703). `S32Op` (`:163`), `s32Rechne` routing every arithmetic
form to the ACCEPTED binary32 kernel
(`Gleitprofil.fadd32/fsub32/fmul32/fdiv32`, `:155-159`, `:168`),
width conversions through the kernel (`:236-248`), distinguishing
witnesses (`s32_eins_plus_zwei`, `s32_plusnull_minusnull`,
`s32_subnormal_waechst`, `s32_eins_durch_null_unendlich`,
`s32_null_durch_null_nan`, `s32_stallt_bei_2hoch24`,
`s32_f64_steigt_weiter` at `:185-231`). No duplicated float
interpreter: the f32-vs-f64 counterexample is reused, not re-proved
(`:8-11`). CUTS (`:1805`): sticky-flag accumulation and silicon
correspondence OPEN. Verdict: **produced** — and the ONLY accepted
producer family with no scheduled consumer: lane 724 explicitly
defers binary32 plugging ("future binary32 ... producers plug in
later"). Follow-up F-B32 is proposed in §5.

### Row I5 — packed SSE2 integer (producer 686 accepted; NO consumer scheduled)

Accepted: `VectorIntegerHardwareForms.lean` (2348 lines, 151 theorems,
lane 686, reviewed 687). `IntVecOp` (`:32`), encoder `encodeIntVec`
(`:90`), lane evaluators `vecShlQ`/`vecShrQ` with proved
SATURATE-not-MASK semantics (`vecShlQ_satt_vs_maske`, `:226-229` —
a checked divergence from masked-count scalar semantics, flagged here
so no consumer silently unifies them), decoders `decodeIntVecReg/Imm/
Mem/Nach` (`:267-361`), `decodeIntVec` (`:425`), round trips from
`:438`. Legacy upper bits beyond 128 unmodelled (CUTS `:2249`).
Verdict: **produced**; SSE-integer execution on the common machine is
likewise deferred by 724 ("future ... SSE integer ... plug in later").
Follow-up F-VEC is proposed in §5.

### Row I6 — indirect/compact control (producer 680 accepted; consumer 718)

Accepted: `IndirectControlHardwareForms.lean` (1581 lines, lane 680,
reviewed 681). `IndForm` (`:64`), `indLen` (`:74`), short-target
`kurzZiel` (`:87`), encoders `encodeIndReg/encodeIndMem/encodeJmpKurz/
encodeJccKurz` (`:112-133`), manual record `indirektHandbuch` (`:53`).
Imports reuse `ControlFlow` and `EffectiveAddress` (`:16-17`).
Verdict: **produced**; consumer 718 unifies its decoder into the tagged
dispatch, and validator-side target-set discipline (M140, N575–N577)
stays a 6B consumer obligation, not claimed here.

### Row I7 — MXCSR control (producer 682 accepted; consumer 724)

Accepted: `FpControlHardwareForms.lean` (1311 lines, lane 682, reviewed
683). `MxcsrBefehl` (`:32`), `MxcsrDec` (`:39`), `MxcsrAusgang` (`:50`),
profiles `mxcsrProfilModern`/`mxcsrProfilAlt` (`:73-76`),
`mxcsrSteuerungOk` with refusal theorem (`:94-105`).
Verdict: **produced**; consumer 724 (control state on per-core FP state)
and 736 (MXCSR_MASK/reserved handling in save/restore).

### Row I8 — CPUID/XGETBV (producer 688 accepted; consumers 690/736)

Accepted: `CpuFeatureHardwareForms.lean` (1234 lines, lane 688,
reviewed 689). `CpuForm` (`:115`), `cpuLen` (`:121`), `cpuEncode`
(`:126`), `decodeCpuFeature` (`:131`), pilot-refusal pins
(`pilot_verweigert_cpuid/xgetbv`, `:176-181`), LOCK-prefix refusals
(`:186-191`), clone-local manual record in CUTS (`:13`, `:1180`).
No host probing, no AMD snapshot. Verdict: **produced**; enabled-state
consumers are 690 (AVX2, waiting on accepted dependencies) and 736
(context, XCR0/component checks or explicit pending).

### Row I9 — RFLAGS defined/undefined (producer 692 accepted; consumers 720/724)

Accepted: `ArchitecturalFlags.lean` (lane 692, reviewed 693). Imports
canonical `Wort`/`Ganzzahl`/`Ausfuehrung`/`ShiftLogic`/`MulDiv`/
`FlagDependencies` (`:34-42`) — flag identities proved against the same
helpers the evaluators use, so no forked flag semantics. Verdict:
**produced**; consumed by 720 (integer flag effects on the common
machine) and 724 (conversion flags). The AF=none abstraction stands as
a named abstraction, never as proof of a defined hardware AF result;
consumer F-AF (defined-AF rows or proved non-observability, §5) still
needs an owner after 720 lands.

### Row I10 — ports/devices (producer 676 accepted; 694 accepted; 704 pending)

- Accepted: `DeviceHardwareForms.lean` (1363 lines, lane 676, reviewed
  677). `IoBreite`/`IoDir`/`PortQuelle`/`IoOp`/`IoDec` (`:26-49`),
  encoder `encodeIo` with length proofs (`:94-126`), decoder `decodeIo`
  (`:138`), twelve round trips (`:183-231`). CUTS (`:377`, `:473`):
  hardware correspondence OPEN; **no `TSOZustand` buffer ever carries a
  device byte** — device traffic is refused from the RAM TSO rule by
  construction.
- Accepted: `MemoryTypeHardwareExecution.lean` (1440 lines, lane 694,
  reviewed 695). UC profile `decktUc`/`istUc` (`:48-69`), `MmioMaschine`
  with `busFortschritt` (`:661`), non-UC instructions reuse `stepExt`
  (`:691-732`, never a second integer executor),
  `mmioByteschritt` (`:786`), reached witnesses (`:1075-1094`).
- Candidate pending review: 704 (`DeviceBusHardwareExecution.lean`,
  exact review 705). Verdict: port/device rows are **produced**
  (codec + UC machine); common-machine port execution waits for 704
  acceptance. MMIO must never inherit WB-RAM ordering — enforced by
  the 694 construction, to be preserved by 704's reviewer.

### Row I11 — faults (producer 670 accepted; consumers 726/738)

Accepted: `HardwareFaults.lean` (530 lines, lane 670, reviewed 671).
`ArchFehler` (`:31`), `klassifiziereMulDiv` with `halt_ist_de`
(`:43-48`), `klassifiziereExt` with the 660 adapter
(`adapter660_klasse`, `:60-67`), canonical check `istKanonisch`/
`adrKlasse` (`:84-90`). The adapter classifies only; delivery belongs
to 672/708. Verdict: **produced**; consumers 726 (paging faults) and
738 (fault priority across fetched accesses). 738 must not choose #PF
arbitrarily where the 726 control input is missing — interface or
honest pending, never a fiat choice.

### Row I12 — addresses (producer 664 accepted; consumer 730)

Accepted: `AddressEncoding.lean` (lane 664, reviewed 665) + prior
`EffectiveAddress.lean`/`BranchLayout.lean`. Verdict: **produced**;
consumer 730 binds actual instruction length/next-RIP and canonical
register values to real producer access effects (SIB, RIP-relative,
REX/rbp-r13/rsp-r12 restrictions, overflow/wrap/canonical rules).
Legacy narrower decoders must not be cited as full-address proof —
730 proves the adapter or states the obstruction.

### Row I13 — coherent composition (consumer foundation 660 accepted)

See §1. Verdict: **executed** for the old dispatcher vocabulary;
**awaiting producer plug-in** for every row above via 718–724.

## 3. What is in flight or waiting (registry state, not inspected)

- Committed candidate, review/integration pending: 672 interrupts
  (`HardwareInterrupts.lean`, reviewer 673), 704 port bus (reviewer
  705). Neither is accepted; 718–738 must not import them — their
  prompts forbid it, and 728 exports the descriptor layer 672 will
  consume once accepted.
- Agent working: 696 (8/16/32-bit rows), 698 (shift/rotate widths).
- Waiting for accepted dependencies: 690 (AVX2 integer forms),
  708 (long-mode interrupt/system return).
- Scheduled consumers: 718 unified dispatch; 720 integer→TSO;
  722 LOCK→buffers; 724 FP→coherent; 726 paging; 728 IDT/TSS;
  730 address adapter; 734 control registers/MSR; 736 context
  save/restore; 738 fault ordering. Reviewers 719/721/723/725/727/
  729/731/735/737/739 are paired per the registry.
- Organisation: this lane (732, reviewer 733).

## 4. Contradiction, duplication and assumption audit

Findings from reading the accepted tree (exact locations, no new proofs):

1. **No contradictory accepted semantics at evaluator level.** New
   evaluators reuse canonical helpers: `intHwWert` via `Ganzzahl`/
   `ShiftLogic` (`IntegerHardwareForms.lean:10-18,33`);
   `s32Rechne` via the accepted binary32 kernel
   (`ScalarFloat32HardwareForms.lean:155-159`); non-UC path via
   `stepExt` (`MemoryTypeHardwareExecution.lean:691-732`); flag
   identities via shared helpers (`ArchitecturalFlags.lean:34-42`).
   The one proved semantic DIVERGENCE is intentional and pinned:
   vector shifts saturate where scalar counts mask
   (`vecShlQ_satt_vs_maske`, `VectorIntegerHardwareForms.lean:226`);
   consumers 718/720 must not unify these rows.
2. **Parallel fetched-step loops exist — unification is the 718
   duty, not a second executor.** Today each family owns a byte loop:
   `extByteschritt`/`hwByteschrittReg` (660), `intHwByteschritt`
   (666), `lockByteschritt` (662), `mmioByteschritt` (694). Lane 718
   is explicitly tasked with "no second competing executor" and a
   proved obstruction plus checked discriminator if unification is
   unsafe. A further parallel loop outside 718 would be a duplicate
   interpreter and must be refused at review.
3. **Named abstractions that must not be cited as completion.**
   (a) `af : Option Bool` (`Typen.lean`): AF=none is an abstraction,
   never a defined-AF proof. (b) `cas_fehlschlag_stottert`
   (`LockedOps.lean`): failure stutter, never full failed-path access
   rules. (c) `hwWortAusgabe` (eight byte issues):
   grouping evidence, never an SC single-copy claim. (d) `osXmm : Bool`
   (`FeatureProfile.lean:42-63`): readiness bit, never a
   CPUID/XCR0/OSXSAVE proof — 690/736 close it or it stays OPEN.
   (e) Codec round trips: self-consistency, never hardware fidelity.
4. **No undocumented assumption found in the read modules.**
   Hardware-assumption discipline (named silicon/device/timing only;
   OS/kernel/scheduler as user logic) is stated per module CUTS;
   `.tmp/HARDWARE-REFERENCES/` provenance is clone-local by `.gitignore`
   design and recorded per producer report — reviewer duty is to check
   that each report names its manual heading, not to re-assert facts here.

## 5. Actionable uncovered rows and disjoint follow-up proposals

The scheduled set 718–738 already covers dispatch, integer/LOCK/FP
common execution, paging, descriptors, addresses, control registers,
context and fault priority. The following rows are covered by NO
scheduled lane — each is a narrow disjoint follow-up with its
dependency gate:

- **F-B32 — binary32 plug into coherent FP execution.** Depends on
  accepted 724. Lift `S32Op` rows through the 724 lifting API; reuse
  the kernel routing (`ScalarFloat32HardwareForms.lean:155-159`);
  CVTSD2SS narrowing witness required; sticky/payload CUTS stay OPEN.
- **F-VEC — packed-integer plug into coherent execution.** Depends on
  accepted 724 (memory discipline) and 718 (dispatch slot). Preserve
  the saturate-vs-mask divergence (§4.1); 128-bit access stays
  non-single-copy-atomic; shared vector stores refused until the 6B
  TSO bridge rules them.
- **F-AF — defined auxiliary-carry rows.** Depends on accepted 720.
  Per admitted integer row, either the defined AF value or a proved
  non-observability lemma consumed by every flag consumer; no flag
  consumer may be weakened to fit.
- **F-DEV — port/device execution on the common machine.** Depends on
  accepted 704 and 694. Ordered IO events, privilege/IOPL/TSS outcomes,
  generic device-response interface; RAM TSO inheritance refused.
- **F-RET — system-return/interrupt-delivery closure.** Depends on
  accepted 672, 708, 726, 728, 734. Delivery through checked
  descriptors and translated stacks on `HwMaschine`; nested delivery
  retains memory/TSO/FP obligations or is refused by a checked gate.
- **F-AVX — AVX2 dispatch and context extension.** Depends on accepted
  690 and 736. VEX rows gated per named CPU profile with
  CPUID/XCR0/context proofs; scalar remains where gates do not close.
- **F-6B — typed-carrier TSO bridge and closing validator.**
  Prerequisite: 6A item-4 model facts (aligned-word atomicity table,
  LOCK unit, fence drain, tearing, fault-vs-observer order) proved by
  720/722/724/738. Per-access x86-TSO → W simulation consuming those
  facts, composed with preserved `schwach_ist_gX`; then `valX86_sound`
  and the source-to-final-loaded-byte theorem. Mandatory follow-on,
  never a parking lot for essential model rows.

## 6. Required integration dependency sequence

1. 718 (dispatch over the eight accepted decoder families named in
   `lanes/718.md`; no unmerged imports) and 730 (address adapter) and
   692-consumed flag rows can integrate in any order — none edits
   another author's module.
2. 720 (needs 730 for full memory forms; missing 696/698 width rows
   stay explicit pending extensions), 722 (needs 730 for full LOCK
   forms; failed-path rules per manual), 724 (needs 682/688 as
   control/enabled inputs; binary32/vector plug-ins deferred to
   F-B32/F-VEC).
3. 726 (needs 734 control-state fields for CR bits; paging modes
   beyond selected 4-level/4KiB stay explicit) and 728 (descriptor
   layer for 672/708) enable 738 (priority relation; paging input as
   interface or honest pending).
4. 734 (control registers/MSR from the actual entry/runtime
   inventory) and 736 (save/restore; AVX2 parts wait for 690).
5. F-B32/F-VEC/F-AF/F-DEV/F-RET/F-AVX as above, then F-6B.
6. Publication stays serial and checked: green `./lean-bau`,
   standard `gabbro_ziel` axioms, joint non-degenerate witnesses,
   poison plus positive probes, key-scan gate. No review bypasses any
   gate; no completion percentage is computed from module or line
   counts.

## 7. Workforce note (15 useful agents, no filler)

The scheduled consumer wave (718–738 plus reviewers) plus in-flight
696/698 and waiting 690/708 already spans dispatch, four execution
integrations, paging, descriptors, addresses, control, context, fault
priority and organisation. If the queue empties, §5 follow-ups
(F-B32/F-VEC/F-AF/F-DEV/F-RET/F-AVX, each disjoint by owned file and
dependency gate) are substantive closure work — never decorative
recounts of this matrix. Counts in this document (lines, theorems)
locate evidence; they measure nothing about completion.

*CUTS (organisation lane 732): no Lean definitions, theorems, decoders,
evaluators, simulations or validator claims are proved here. Accepted
states rest on the named merged reports and their independent reviews;
in-flight and scheduled states rest on the `DIRECT-COMPILER.md`
registry and committed `lanes/` prompts. Manual provenance is recorded
in producer reports and module CUTS, not re-asserted here. The 6B
follow-on (typed-carrier TSO→W/GX bridge, image/ABI/entry/budget
connection, closing validator, Rust backend) remains OPEN and
mandatory; it is separated from the hardware model, not dropped.*
