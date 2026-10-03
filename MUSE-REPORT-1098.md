# MUSE-REPORT-1098: standing dynamic planner cycle 2026-10-03

Lane 1098, clone `/home/simon/Dokumente/gabbro-muse/a1098`, branch `muse/1098`
(verified: `git branch --show-current` = `muse/1098`, toplevel matches).
Organisation only: no Lean/Rust/source file touched, so `./lean-bau` state is
unchanged from base `03491267` (last publication batch in `DIRECT-COMPILER.md`
reports complete Lean + Rust + emission + standard `gabbro_ziel` axioms green;
full source-to-binary validation remains OPEN everywhere).

Owned deliverables: `dokumente/x86/ARBEITSPLAN-AKTUELL.md` (created — it did
not exist in this base; first dated cycle section added) and this report.

## 1. What I did

Read the committed state available from this clone: `DIRECT-COMPILER.md`
history (lines 1050–1198: all 2026-10-02/03 integrations, gate rejections and
publications), `dokumente/x86/HARDWARE-INTEGRATION-COVERAGE.md` (lane 732, §5
follow-ups F-B32/F-VEC/F-AF/F-DEV/F-RET/F-AVX/F-6B with dependency gates),
`lanes/744.md` + `lanes/745.md` (full-compiler plan organisation + its exact
review, both still registered = 744 unaccepted), `dokumente/x86/
UPSTREAM-PR-1-OPTIMIZER-REVIEW.md` (verdict: no MUST-FIX) and
`UPSTREAM-PR-2-ISA-REVIEW.md` (verdict: REJECT as-is; repair lanes 740–743
registered), `DIRECT-COMPILER-DESIGN.md` section map (essential/deferred
scope), OWN ONLY lines of every committed `lanes/*.md` prompt, `git log`, and
the `grammatik/Grammatik/X86/` tree (155 modules; none of the six proposed
files exists).

NOT available in this clone: the live coordinator registry (`manifest.json`,
`state/`, `dispatch.json`, `watch.json`, PIDs, dispatcher queue/backoff,
watch gate errors, task-brief audits B01–B11). De-duplication below rests on
committed prompts + `DIRECT-COMPILER.md`; the coordinator MUST re-check live
holds, blocking lists and worker identities at registration.

## 2. Prioritisation applied (coordinator direction for this cycle)

1. Common-machine/hardware closure first: all six authors connect accepted
   producer rows to the accepted `HwMaschine`/`HwSchritt` (660) world or feed
   it directly. No new detached helper inventory: every author theorem is a
   fetched-bytes execution, footprint, ordering or defined-observable claim
   with a reached memory-changing witness and planted refusal probes.
2. Pipeline integration after 744/745: proposal P1-C composes only accepted
   consumers (no 744 API assumed). Genuine source-to-byte validation beyond
   that waits for the accepted 744 plan — stated as non-goal, not faked.
3. PR1/PR2 repair completion: 740–743 already registered; no duplicate
   proposed. PR-1 needs no repair (review found no MUST-FIX).
4. Backfill with substantive disjoint work: P2-D/E/F are unblocking slices
   (F-6B footprints; lifting/slot APIs that 724 and the 718-repair consume)
   defined against accepted-only modules, each with honest pending gates.

Hard constraints honoured: at most 8 authors (6 proposed + 6 reviewers = 12
slots, 3 left for 698/718/722 repair resumes and 744/745 landing); Lean-first,
all Lean-kind; exact independent reviewer for every author (full review texts
below); no overlap with registered owned paths (§1 list in
ARBEITSPLAN-AKTUELL.md); friend-reserved `OptimizationRules.lean` /
`OptimizationWitnesses.lean` untouched; held lanes 672/673/684/685 untouched,
no hold cleared, no `HardwareInterrupts.lean` import anywhere; no second
executor/interpreter; no desired-simulation premise; no named-program closure.

## 3. Register-ready wave proposal (NO lane numbers — coordinator allocates)

Shared author gates (repeat in every registration): HARD RULES preamble;
`./lean-probe` after every step, `./lean-bau` green before finish; no `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe`; no `Prop`-typed premise; every
premise used; standard `gabbro_ziel` axioms preserved (`#print axioms` per
main theorem); joint non-degenerate `_zeuge` for every target theorem (reached
run with a memory-changing step + at least one table some function writes;
malformed-byte/fault/control-state/overlap refusal probes planted); CUTS block
listing exactly what stays OPEN; English only; `MUSE-REPORT-<ID>.md`; commit
via `arbeitsprotokoll/.commitmsg` + `./commit.sh`; additive
`grammatik/Grammatik.lean` import only (six authors touch that one line —
integrate serially); never touch `Spec.lean`, goal theorem, emitter, checker,
friends' files, or another lane's module.

---

### AUTHOR PROPOSAL A (priority P1, kind lean)

- Title: Defined auxiliary-carry rows for admitted integer execution (F-AF slice)
- Owned paths: `grammatik/Grammatik/X86/AuxiliaryCarryRows.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-<ID>.md`
- Depends on (all accepted): 720 `ConcurrentIntegerExecution.lean`, 692
  `ArchitecturalFlags.lean`, 666 `IntegerHardwareForms.lean`, 660
  `HardwareExecution.lean`. Must NOT import any unaccepted module.
- Task text: For every integer row the accepted 720 consumer connects to
  shared TSO execution, prove in the NEW module either (i) the DEFINED
  hardware AF value as a theorem over the same canonical helpers the
  evaluators use (`Ganzzahl`/`ShiftLogic`, reusing the 692 flag identities —
  never a forked flag semantics), or (ii) a proved non-observability lemma
  showing the row's AF value cannot reach any flag consumer (consumed by every
  flag consumer: the lemma must be imported, not worked around). The
  `af : Option Bool` abstraction (`Typen.lean`) stays a named abstraction and
  is never cited as a defined hardware AF result; no flag consumer is weakened
  to fit. Fetched-bytes execution of at least one representative row runs on
  `HwMaschine` through the accepted 720 connection (reuse it, do not rebuild
  it). Targets: `auxCarry_definiert_alle` (per-row defined-or-unobservable
  disjunction over the exact admitted 720 row set) and
  `auxCarry_byteschritt` (fetched execution agreement). ZEUGE: joint
  `<name>_zeuge` for both targets on one non-degenerate program (a function
  writing a table, a reached run with a memory-changing step), plus one
  planted probe refusing an AF claim over an unadmitted row and one refusing a
  flag-consumer bypass. CUTS must name every row left without a defined value
  and why. Read first: `ConcurrentIntegerExecution.lean`,
  `ArchitecturalFlags.lean` (`:34-42` helper reuse),
  `IntegerHardwareForms.lean` (`intHwFlagsLogik`, `inthw_logik_af_none`),
  `HardwareExecution.lean` (`HwSchritt`, adapter duties), 732 §4.3(a) on the
  AF abstraction. If a defined value is unprovable for a row, that row keeps
  an explicit pending extension — never a fiat value, never a weakened consumer.
- Review text (report-only reviewer, OWN ONLY `MUSE-REPORT-<ID>.md`): exact
  CANDIDATE: author HEAD (full pinned hash). Reproduce the admitted-row
  inventory against accepted 720 and check every row is covered by (i) or (ii)
  with no third case; check flag-helper reuse (`Ganzzahl`/`ShiftLogic`/692
  identities) and forbid any local AF redefinition; check no flag consumer was
  weakened (diff consumer call sites); check the fetched-execution theorem
  steps through the accepted 720 connection and `HwSchritt` (no second
  executor, no desired-equality premise); check joint `_zeuge`
  non-degeneracy and both refusal probes fail-then-pass; check CUTS honesty;
  check `Grammatik.lean` diff is the one import line. Exactly one VERDICT:
  ACCEPT or REPAIR with precise evidence and file/line repairs.

### AUTHOR PROPOSAL B (priority P1, kind lean)

- Title: Port and device execution on the common machine (F-DEV slice)
- Owned paths: `grammatik/Grammatik/X86/DeviceCommonExecution.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-<ID>.md`
- Depends on (all accepted): 704 `DeviceBusHardwareExecution.lean`, 694
  `MemoryTypeHardwareExecution.lean`, 728 `InterruptDescriptorHardware.lean`,
  660 `HardwareExecution.lean`. Must NOT import any unaccepted module.
- Task text: Lift the accepted port/device rows (676 codecs, 694 UC machine,
  704 bus with IO permissions) onto `HwMaschine` in the NEW module: ordered IO
  event trace over fetched port/device bytes, privilege/IOPL/TSS outcomes
  derived through the accepted 728 descriptor layer (reuse its definitions,
  never a parallel descriptor model), and a GENERIC device-response interface
  (explicit pending responses stay refused by a checked gate, never answered
  by fiat). Preserve the 694 construction: NO `TSOZustand` buffer ever carries
  a device byte — prove the refusal (device traffic excluded from the RAM TSO
  rule by construction) as a theorem, and prove MMIO never inherits WB-RAM
  ordering. Targets: `deviceCommon_byteschritt` (fetched port/device step on
  `HwMaschine`), `deviceCommon_tso_verweigert` (device-byte TSO exclusion),
  `deviceCommon_mmio_ordnung` (no WB ordering inheritance). ZEUGE: joint
  witness on a non-degenerate program with a reached memory-changing run, plus
  planted probes: a device byte offered to the RAM TSO rule (refused), an
  unprivileged port access under a denying descriptor (refused), a pending
  device response consumed as an answer (refused). CUTS: hardware
  correspondence stays OPEN (as in 676/694), pending responses enumerated.
  Read first: `DeviceBusHardwareExecution.lean`, `MemoryTypeHardwareExecution.lean`
  (`:48-69` UC profile, `:661` bus progress, `:691-732` non-UC reuse),
  `InterruptDescriptorHardware.lean` permission rows, `HardwareExecution.lean`,
  732 rows I10 + §4.2 (no second executor).
- Review text: exact CANDIDATE author HEAD. Check the three targets against
  the accepted 694/704 constructions (no rebuilt bus, no second TSO); check
  the TSO-exclusion theorem really covers every device-byte path (no bypass
  via MMIO rows); check privilege outcomes come from 728 definitions (diff
  against parallel models); check generic-response gate refuses (not answers)
  pending cases; check joint `_zeuge` non-degeneracy + three probes;
  CUTS honesty; one-line import. VERDICT: ACCEPT or REPAIR with evidence.

### AUTHOR PROPOSAL C (priority P1, kind lean)

- Title: Close the accepted consumers through the common dispatcher
- Owned paths: `grammatik/Grammatik/X86/ComposeAcceptedConsumers.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-<ID>.md`
- Depends on (all accepted): 824 `ComposeDecodeExec.lean`, 720, 730
  `AddressedHardwareExecution.lean`, 738 `ExceptionPriorityHardware.lean`, 728,
  660. Must NOT import unaccepted 718/722/724/726/734/736/690/708/696/698.
- Task text: Compose ONE fetched-execution closing theorem over `HwMaschine`
  from already-accepted pieces in the NEW module: the 824 decode-to-execution
  closing as the dispatch backbone, the 720 integer→TSO rows, the 730 address
  adapter (SIB/RIP-relative/canonical register values bound to real access
  effects), the 738 fault-priority relation across fetched accesses, and 728
  descriptor/stack-selection inputs where entry-adjacent rows need them. Every
  not-yet-accepted producer family (width rows 696/698, LOCK 722, FP 724,
  paging 726, control 734, context 736, AVX2 690, returns 708) stays an
  EXPLICIT pending extension enumerated in CUTS — never imported, never
  assumed, never closed by a premise shaped like the conclusion. No second
  competing executor: reuse `decodeExt`/`stepExt`/`extByteschritt` (575/660
  line) and the 824 composition lemmas. Targets:
  `composeAccepted_gesamt` (fetched bytes → `HwSchritt` runs for the accepted
  row set with 738 priority respected) and `composeAccepted_luecken`
  (exact enumeration of the pending families as a checked datatype the theorem
  threads through, so a silent widening is a type error). ZEUGE: joint witness
  on a non-degenerate program (table-writing function, reached
  memory-changing run spanning an integer access + an address computation +
  a fault-priority decision), plus planted probes: a width-row byte (pending,
  refused), a LOCK byte (pending, refused), an FP byte (pending, refused).
  Read first: `ComposeDecodeExec.lean` (824 claim boundary: bounded ACCEPT),
  `ConcurrentIntegerExecution.lean`, `AddressedHardwareExecution.lean`,
  `ExceptionPriorityHardware.lean`, `InterruptDescriptorHardware.lean`,
  `HardwareExecution.lean`, 732 §6 steps 1–2 (integration sequence).
- Review text: exact CANDIDATE author HEAD. Check the backbone really is the
  accepted 824 composition (no re-proved rival); check the pending datatype
  covers exactly the unaccepted families (compare against the §1 active list —
  no missing family, no accepted family misfiled as pending); check no
  unaccepted import in the file (grep the import block); check priority
  relation is the 738 one (not a fiat order); check joint `_zeuge`
  spans all three row kinds + three probes; CUTS honesty; one-line import.
  VERDICT: ACCEPT or REPAIR with evidence.

### AUTHOR PROPOSAL D (priority P2, kind lean)

- Title: Realised per-access footprints for the connected integer rows (F-6B feed)
- Owned paths: `grammatik/Grammatik/X86/IntegerAccessFootprints.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-<ID>.md`
- Depends on (all accepted): 720, 738, 660, plus accepted
  `WordAccessGrouping.lean`, `WordAtomicity.lean`, `TSOHistory.lean`
  (650/651), `VectorFootprints.lean` (pattern reference only — integer rows,
  not vector rows). Must NOT import unaccepted modules.
- Task text: Prove realised footprint lemmas for EVERY access the accepted
  720 consumer realises on shared TSO execution: per-access address/length/
  direction/carrier facts derived from the actual 720 fetched steps (consume
  them, never restate them), grouped per the accepted word-grouping table,
  ordered per the accepted 738 priority relation, and projected per the
  accepted 650/651 TSO-history→W transition (preserve `schwach_ist_gX`; the
  missing target leg is NOT assumed — this module feeds precise facts to the
  future F-6B bridge, it is not the bridge). 128-bit/shared-row accesses stay
  explicitly non-single-copy-atomic; fault-vs-observer order follows 738 or
  stays pending where 738 is silent. Targets: `intFootprint_vollstaendig`
  (every realised 720 access has its footprint lemma) and
  `intFootprint_wort_ordnung` (grouping + priority agreement). ZEUGE: joint
  witness on a non-degenerate program with a reached run containing two
  overlapping realised accesses resolved per the proved order, plus planted
  probes: a footprint claimed for an unrealised (pending-family) row
  (refused), a single-copy claim over a 128-bit access (refused). CUTS: the
  per-access x86-TSO→W/GX simulation, `valX86_sound` and the closing theorem
  stay OPEN (F-6B, blocked until 722/724 accepted). Read first:
  `ConcurrentIntegerExecution.lean` realised-access set,
  `ExceptionPriorityHardware.lean`, `WordAccessGrouping.lean`,
  `WordAtomicity.lean`, `TSOHistory.lean`, 732 §5 F-6B prerequisite list.
- Review text: exact CANDIDATE author HEAD. Check completeness claim against
  the exact realised-access set of accepted 720 (enumerate, no gap, no extra);
  check grouping/priority reuse accepted tables (no local rival table); check
  `schwach_ist_gX` preserved and no target-leg premise smuggled in; check
  joint `_zeuge` has two overlapping accesses + two probes; CUTS honesty
  (no bridge claim); one-line import. VERDICT: ACCEPT or REPAIR.

### AUTHOR PROPOSAL E (priority P2, kind lean)

- Title: Binary32 fetched steps with a lifting API for the FP consumer (724 unblock)
- Owned paths: `grammatik/Grammatik/X86/ScalarFloat32FetchedSteps.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-<ID>.md`
- Depends on (all accepted): 702 `ScalarFloat32HardwareForms.lean`, 730,
  720 (shared-buffer memory discipline), 668 `ScalarFloatHardwareForms.lean`,
  682 `FpControlHardwareForms.lean`, 660. DEFINES the lifting API for 724;
  never imports the unaccepted 724 module.
- Task text: Derive fetched binary32 execution for the accepted `S32Op` rows
  on per-core FP state with shared buffered memory, reusing the accepted
  binary32 kernel routing (`s32Rechne` via `Gleitprofil.fadd32/fsub32/fmul32/
  fdiv32`) and the 724-style control inputs (MXCSR profiles from 682,
  preserving XMM upper lanes and raw MXCSR control). Required: CVTSD2SS
  narrowing witness distinguishing f32-vs-f64 (reuse, not re-prove, the 702
  counterexample pattern). Sticky-flag accumulation, NaN payloads and silicon
  correspondence stay OPEN in CUTS. Export a SMALL explicit lifting interface
  (named definitions, exact signatures) that consumer 724 can import once
  accepted; document each signature's contract so a shape mismatch with 724 is
  a loud type error, not silent drift. Targets: `s32Fetched_schritt` (fetched
  step agreement per `S32Op` row), `s32Fetched_narrowing` (CVTSD2SS witness),
  `s32Fetched_lift_schnittstelle` (interface inhabitation: every signature has
  a proved provider). ZEUGE: joint witness on a non-degenerate program
  (table-writing, reached memory-changing run with an arithmetic row AND a
  conversion row), plus planted probes: a narrowing claimed without the
  witness (refused), a sticky-flag accumulation claim (refused), an XMM-upper
  clobber (refused). Read first: `ScalarFloat32HardwareForms.lean`
  (`:155-159` kernel routing, `:185-231` distinguishing witnesses, `:1805`
  CUTS), `FpControlHardwareForms.lean`, `ScalarFloatHardwareForms.lean`
  encoder/decoder shapes, 732 rows I3/I4 (724 defers binary32 — this module is
  the deferred plug-in source, not a second 724).
- Review text: exact CANDIDATE author HEAD. Check kernel routing reuse (no
  duplicated float interpreter); check narrowing witness really separates
  f32/f64; check XMM-upper/MXCSR preservation theorems; check lifting
  interface signatures are provided AND used inside the module (no dead
  interface); check no 724 import; joint `_zeuge` + three probes; CUTS
  honesty; one-line import. VERDICT: ACCEPT or REPAIR.

### AUTHOR PROPOSAL F (priority P2, kind lean)

- Title: Packed-integer fetched steps with a dispatch-slot API (718-repair/724 unblock)
- Owned paths: `grammatik/Grammatik/X86/VectorIntegerFetchedSteps.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-<ID>.md`
- Depends on (all accepted): 686 `VectorIntegerHardwareForms.lean`, 720
  (memory discipline), 730, 660. DEFINES the dispatch-slot API; never imports
  unaccepted 718/724.
- Task text: Derive fetched packed-integer execution for the accepted
  `IntVecOp` rows on the common machine discipline: lane evaluators reused
  from 686 (`vecShlQ`/`vecShrQ` with the PROVED saturate-not-mask semantics —
  preserve `vecShlQ_satt_vs_maske`; no consumer may unify these rows with
  masked-count scalar semantics), memory rows through the accepted 720/730
  discipline, 128-bit access explicitly non-single-copy-atomic, shared vector
  stores refused by a checked gate until the 6B TSO bridge rules them. Legacy
  upper bits beyond 128 stay unmodelled (CUTS, as in 686). Export a SMALL
  explicit dispatch-slot interface (tag discriminator + slot lemmas over the
  eight accepted decoder families named in `lanes/718.md`) that the 718-repair
  and 724 can consume; document the saturate-vs-mask divergence AT the
  interface so a unifying consumer is a loud type error. Targets:
  `vecFetched_schritt` (fetched step agreement per `IntVecOp` row),
  `vecFetched_satt_erhalten` (divergence preserved through fetching),
  `vecFetched_slot_schnittstelle` (slot interface inhabitation). ZEUGE: joint
  witness on a non-degenerate program (reached memory-changing run with a
  lane-shift AND a memory row), plus planted probes: a masked-count reading
  of a vector shift (refused), a shared vector store claimed executable
  (refused), a 129th-bit dependence claim (refused). Read first:
  `VectorIntegerHardwareForms.lean` (`:226-229` divergence, `:267-425`
  decoders, `:2249` CUTS), `lanes/718.md` (eight decoder families in scope),
  732 rows I5 + §4.1/§4.2 (no unification, no second executor).
- Review text: exact CANDIDATE author HEAD. Check evaluator reuse (no rival
  vector semantics); check divergence theorem blocks unification (attempt the
  unifying rewrite and show it fails); check 128-bit/shared-store limits are
  theorems, not comments; check slot interface covers the eight 718 families
  and is provided+used; check no 718/724 import; joint `_zeuge` + three
  probes; CUTS honesty; one-line import. VERDICT: ACCEPT or REPAIR.

## 4. Integration order and slot budget

Authors A–F are mutually independent (disjoint files, accepted-only deps) and
may run in parallel: 6 authors + 6 reviewers = 12 of 15 slots. Reserve 3 slots
for (i) 698/718/722 repair resumes (same-file ownership — coordinator resume,
not new lanes), (ii) 744/745 landing and its pipeline-integration follow-up,
(iii) coordinator/organisation overhead. Publication stays serial and checked:
green `./lean-bau`, standard axioms, joint witnesses, probes, key-scan gate —
no review bypasses any gate. `Grammatik.lean` one-line imports from six
authors integrate serially at publication.

## 5. Explicit non-goals (proposed work that was considered and refused)

- 698/718/722 repairs as new-author work: same-file ownership forbids it;
  coordinator resume only. 752/757/759–768: lane files absent in this base,
  ownership unclear — confirm live registry before any adjacent proposal.
- F-RET / interrupt delivery: needs HELD 672 + active 708/726/734. Blocked;
  no hold-clearing, no `HardwareInterrupts.lean` import (TOCTOU).
- F-6B full bridge / `valX86_sound` / closing validator: premature until
  722/724 accepted (732 §5 prerequisite). Proposal D feeds it; it does not
  claim it.
- F-AVX: needs active 690/736. Blocked.
- SYSCALL/SYSRET byte forms: next-wave candidate (base: accepted 728;
  708/726/734 inputs as honest-pending interfaces, never imports).
- Dead-store-elimination validator (OPTIMIZER.md §3.4): considered as a 7th
  author; deferred to keep 3 slots free for repairs + 744 landing. Next-wave
  candidate with PR-1 certificate pattern on a non-reserved path.
- PR-2 Lean/Rust repairs: registered 740–743. PR-1: no MUST-FIX found.
  No duplicates proposed.
- 744-dependent source-to-byte validation: 744 unaccepted; nothing proposed
  that assumes its APIs. Proposal C is accepted-consumers-only by design.
- Benchmark / GCC-O3 80/95/>110 measurement and compile-latency telemetry:
  needs an accepted pipeline — premature; targets restated as requirements,
  never as results.
- 684-owned instruments/docs, friend-reserved optimiser files, `Spec.lean`,
  goal theorem, emitter/checker: untouched by every proposal.

## 6. Evidence index (all inside this clone)

- Integration/merge + gate-rejection + publication record:
  `DIRECT-COMPILER.md` lines 1050–1198 (base HEAD `03491267` contains them).
- Producer/consumer states, CUTS locations, F-* dependency gates:
  `dokumente/x86/HARDWARE-INTEGRATION-COVERAGE.md` §§1–6.
- 744 scope + 745 review shape: `lanes/744.md`, `lanes/745.md`.
- PR states: `dokumente/x86/UPSTREAM-PR-1-OPTIMIZER-REVIEW.md` (no MUST-FIX),
  `dokumente/x86/UPSTREAM-PR-2-ISA-REVIEW.md` (REJECT as-is, §8 MUST-FIX;
  repairs 740–743 registered per `lanes/740.md`, `lanes/742.md` titles).
- Ownership boundary: OWN ONLY lines of `lanes/{672,684,690,696,698,708,718,
  722,724,726,734,736,740,742,744,1094,1096}.md` (read 2026-10-03).
- Absence proofs: `grammatik/Grammatik/X86/` listing has none of the six
  proposed files; `dokumente/x86/ARBEITSPLAN-AKTUELL.md` did not exist before
  this turn; `lanes/{752,757,759–768}.md` absent (repair ownership unclear).
- Design scope: `DIRECT-COMPILER-DESIGN.md` §§2A/2D/3–6 headers.

## 7. What I believe is wrong or risky in the task/inputs

- The task names `dokumente/x86/ARBEITSPLAN-AKTUELL.md` ("extend") and the
  accepted 744 `FULL-COMPILER-WORK-PLAN` as inputs; neither exists in this
  base. I created the former with its first cycle section and treated the
  latter as pending (no proposal assumes it). If the coordinator holds newer
  committed states, my §1 snapshot needs a live refresh — flagged in both
  deliverables rather than guessed.
- The B01–B11 task-brief blocking lists are not in the repo; de-duplication
  here rests on committed prompts + publication history. Registration-time
  re-check is mandatory, stated twice above.
- Six authors editing `grammatik/Grammatik.lean`'s import block will conflict
  at merge; the merge procedure's import-union rule covers it, but the watch
  should integrate them serially (noted in §4).
- Proposal C's pending-datatype (`composeAccepted_luecken`) duplicates the
  732 §5 follow-up list in Lean form; if 732 is revised, C must track it.
  The reviewer text covers the comparison but a stale 732 would silently
  age C's completeness claim — coordinator should re-pin 732 at C's
  registration.

No Lean theorems added by this lane: no `_zeuge` obligation arises for lane
1098 itself. ./lean-bau not re-run (no `grammatik/`, Rust, or instrument file
touched by this lane; docs-only turn).
