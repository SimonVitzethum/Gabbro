# MUSE-REPORT-1112: Standing dynamic work planner, cycle 2

Clone verified: `/home/simon/Dokumente/gabbro-muse/a1112`, branch
`muse/1112` (via `git branch --show-current`; tree clean per
`git status --short`). Base `7f81b2c6`. Organisation only: the only
files touched are `dokumente/x86/ARBEITSPLAN-AKTUELL.md` (dated
cycle-2 section appended) and this report. No Lean, Rust, instrument,
or lane file touched; no model launched; no merge/push/fetch.

## What was done

Read from committed state in this clone (the live coordinator
registry is absent here — `.claude/` does not exist — so manifest
lanes/statuses, state files, inventory counts, dispatcher
queue/backoff, watch gate errors and B01–B11 blocking lists were NOT
readable; §5 records this as a standing limitation, not a silent
assumption):

- `dokumente/x86/ARBEITSPLAN-AKTUELL.md` cycle-1 section (planner
  1098, base `03491267`).
- `git log` merge commits for the 1100 wave: `071d4a37` (1100),
  `657d178e` (1101), `3e8d2f1f` (1102), `43211329` (1103),
  `e74989df` (1104), `df46d5fa` (1105), `646172c4` (1108),
  `fc5b465e` (1109), `d6f693a4` (1110), `61eb1e8b` (1111).
- `DIRECT-COMPILER.md` history tail + register table rows for 865/866
  (DCE rules, merged with reviews 1015/1016) and the 1100-wave
  `x86-merged` entries.
- Committed `messung/muse/MUSE-REPORT-1100/1101/1102/1103/1104/1105/
  1108/1109/1110/1111.md` (full reads of the five author reports for
  outcomes and CUTS-mined follow-ups).
- Committed `lanes/*.md` title + OWN ONLY lines (39 lanes) for the
  disjointness boundary.
- Scope records: `DIRECT-COMPILER-DESIGN.md` §§2D/6/7 (essential vs
  deferred, SYSCALL trap §6-exclusions, DCE row §7), `dokumente/x86/
  HARDWARE-INTEGRATION-COVERAGE.md` §§1/2/4/5/6 (producer/consumer
  states, F-B32/F-VEC/F-AF/F-DEV/F-RET/F-AVX/F-6B gates, integration
  sequence), `dokumente/x86/REVIEW-OPT-BINAER.md` §2 (DCE never
  removes a spin/wait load; CE-1 budget-stop cut).
- Tree facts at `7f81b2c6`: `grammatik/Grammatik/X86/` contains the
  five merged 1100-wave files; `grammatik/Grammatik.lean` imports
  NONE of them (but imports `Codec`, `Byteschritt`,
  `HardwareExecution`, `ConcurrentIntegerExecution`,
  `AddressedHardwareExecution`, `ExceptionPriorityHardware`,
  `InterruptDescriptorHardware`, `ComposeDecodeExec`,
  `ValidatorSkeleton`, `OptDceDead`, `OptDceStore`); no X86 module
  imports `OptDceDead`/`OptDceStore`; `FULL-COMPILER-WORK-PLAN.md`
  and `instrumente/upstream-pr-2-lean.patch` are absent; local refs
  are only `master` and `muse/1112`.

## 1100-wave A–F outcomes (committed state)

- A (1100/1101, AF rows): MERGED. B (1102/1103, device common):
  MERGED — F-DEV delivered, no follow-up. C (1104/1105, compose):
  MERGED. D (1106/1107, footprints): NOT LANDED — lane files present,
  no report, no tree file; outcome unknown here; coordinator resume
  only. E (1108/1109, S32 + lifting API): MERGED — API side only,
  F-B32 plug-in still blocked on accepted 724. F (1110/1111, vec-int
  + slot API): MERGED — F-VEC plug-in still blocked on 718 + 724.

## Findings

1. **Umbrella-import gap.** The five merged 1100-wave files exist but
   are not imported by `grammatik/Grammatik.lean` at `7f81b2c6`
   (each author report leaves the line as merge action). So
   `./lean-bau` does not cover them here. §2 authors import them by
   full module path and never edit `Grammatik.lean`; the coordinator
   lands the five lines via the merge-script union and re-verifies
   with `./lean-bau`. Re-check at registration whether
   origin/master already carries them.
2. **No Lean-checkable planner output.** This lane adds no theorem and
   no Lean file; the HARD RULES inhabitation clause (rule 13) has no
   target (no premise over program syntax is stated anywhere in §2).

## Register-ready wave (NO lane numbers; coordinator allocates)

Three author + three exact-review pairs, mutually disjoint by owned
file, accepted-only dependencies, parallelisable, any integration
order. At most the six slots; remaining capacity belongs to the
coordinator's live backfill (1106/1107 outcome, 698/718/722 resumes,
744 landing) — no filler proposed.

### AUTHOR-1 — ComposeExtendedConsumers (integration, priority HIGH)

- Kind: Lean author.
- Owned paths: `grammatik/Grammatik/X86/ComposeExtendedConsumers.lean`,
  `MUSE-REPORT-<id>.md`.
- Depends (accepted/merged only): `AuxiliaryCarryRows` (1100),
  `DeviceCommonExecution` (1102), `ScalarFloat32FetchedSteps` (1108),
  `VectorIntegerFetchedSteps` (1110), `ComposeAcceptedConsumers`
  (1104), `ComposeDecodeExec` (824), `HardwareExecution` (660).
  Import the 1100-wave modules by full module path
  (`Grammatik.X86.<Name>`); NEVER edit `grammatik/Grammatik.lean`
  (the five umbrella lines land via the merge-script union).
  NEVER import `IntegerAccessFootprints` (unmerged 1106),
  `ConcurrentFloatingExecution` (724), `ConcurrentAtomicExecution`
  (722), `HardwareDecodeDispatch` (718), or any 726/734/736/690/708/
  696/698 module.
- Priority: HIGH (first genuine integration of the newly accepted
  rows; unblocks nothing else, breaks nothing).
- Full task: In the NEW module prove fetched-execution coexistence
  of the four newly accepted rows with the accepted 1104 closing on
  the common discipline. Read first: the four merged modules'
  fetched-agreement theorems (`auxCarry_byteschritt`,
  `deviceCommon_byteschritt`, `s32Fetched_schritt`,
  `vecFetched_schritt`), `ComposeAcceptedConsumers.lean`
  (`composeAccepted_gesamt`, `composeAccepted_luecken`,
  `PendingFam`), `ComposeDecodeExec` composition lemmas. Define no
  second dispatcher and restate no consumer lemma: reuse each row's
  fetched agreement and the 1104 closing. TARGET-1
  `extendedRows_coexist`: each of the four rows' fetched steps runs
  on the common discipline (same or disjoint-address witness
  machines) without breaking `composeAccepted_gesamt`. TARGET-2
  `extendedRows_luecken_bleiben`: every 1104 `PendingFam` pin stays
  open — classify all four new rows as belonging to NO pending
  family, keep the exhaustiveness shape so a family added without a
  pin is a type error. ZEUGE: joint witness reusing the four lanes'
  reached memory-changing runs on disjoint addresses, plus planted
  probes: a pending-family byte sequence claimed covered (refused by
  `decide`) and a shared vector store claimed single-copy-atomic
  (refused). CUTS: per-access x86-TSO to W/GX simulation,
  `valX86_sound` and the source-to-final-loaded-byte closing theorem
  stay OPEN (F-6B, blocked until 722/724 accepted); no source, ABI,
  entry, budget, or call-log claim. Checks: `./lean-probe` after
  each piece, `./lean-bau` green before finish, standard
  `gabbro_ziel` axioms only, no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`, every premise used, English only. Leave
  the one-line umbrella import for the merger. Commit through
  `./commit.sh` with the coordinator-provided trailer; finish with
  the report (exact theorem names, last `./lean-bau` line, open
  items, anything believed wrong in this task).

### REVIEW-1 — exact-candidate review of AUTHOR-1 (report only)

- Kind: Lean exact review, report-only. Owned paths:
  `MUSE-REPORT-<id>.md` only. No source changes.
- Depends: the exact pinned AUTHOR-1 HEAD (coordinator provides the
  hash) + the same accepted modules.
- Full review text: Independent exact author-HEAD review of the
  pinned AUTHOR-1 candidate. Check: (a) all four new rows consumed
  with no gap and no extra (enumerate against the four merged
  modules); (b) the 1104 closing reused, never restated — no rival
  dispatcher, no forked consumer lemma; (c) every 1104 `PendingFam`
  pin preserved and still exhaustive; the four-row classification
  proved, and no pin silently closed; (d) joint `_zeuge` reuses four
  reached memory-changing runs on disjoint addresses plus both
  planted refusals (pending-family byte, shared-store atomicity),
  decided, not assumed; (e) no unaccepted import anywhere
  (deny-list: 1106/724/722/718/726/734/736/690/708/696/698 files);
  (f) CUTS honesty — no bridge, validator, source, or budget claim;
  (g) one-line umbrella import noted for the merger;
  (h) `#print axioms` within standard `gabbro_ziel` set, no banned
  tactic/axiom, every premise used. Exactly one VERDICT: ACCEPT or
  REPAIR with a precise repair list (file, theorem, failed check,
  evidence). English report-only clean commit through `./commit.sh`.

### AUTHOR-2 — SyscallTrapEntryGating (hardware slice, priority MEDIUM-HIGH)

- Kind: Lean author.
- Owned paths: `grammatik/Grammatik/X86/SyscallTrapEntryGating.lean`,
  `MUSE-REPORT-<id>.md`.
- Depends (accepted only): `InterruptDescriptorHardware` (728 —
  reuse the accepted DPL/privilege checks per the 1102 precedent,
  never a parallel privilege model), `ExceptionPriorityHardware`
  (738), `ConcurrentIntegerExecution` (720, memory discipline),
  `Codec` + `Byteschritt` fetch discipline, `HardwareExecution`
  (660). NEVER import `LongModeReturnHardwareForms` (708),
  `PagedMemoryHardware` (726), `ControlRegisterHardwareForms` (734),
  `HardwareInterrupts` (672, HELD), or any 718/722/724/736/690/696/
  698 module. NEVER edit `grammatik/Grammatik.lean`.
- Priority: MEDIUM-HIGH (stages the accepted-checks gate for F-RET;
  delivery itself stays blocked).
- Full task: In the NEW module build the SYSCALL/SYSRET trap-entry
  gate over accepted checks only. Read first: accepted 728
  privilege/DPL theorems (as reused by 1102:
  `dev_dpl_verweigert_software` pattern), 738 priority relation
  (where it is silent, stay pending — never invent an order), 720
  fetched memory discipline, accepted `decodeExt`/codec rows. Step
  1 — checked decoder census: enumerate accepted decoder coverage
  for `0F 05` (SYSCALL) / `0F 07` (SYSRET); every row with no
  accepted decoder gets an explicit refusal pin (`decodeExt = none`
  by `decide`); no row invented. Step 2 — gate contract: CPL gate
  via accepted 728 privilege fields, trap-vs-fault order via 738
  (or explicit pending pin where 738 is silent), one fetched-step
  hook running the gate on the common discipline. Step 3 — pending
  legs: MSR state (734), return forms (708) and paging translation
  (726) stay explicit pending refusals naming their owning lanes;
  this module DEFINES the slot they plug into (1108/1110
  precedent). NO producer-form work: no MSR semantics, no return
  forms, no page walks, and — per the 1102 finding that IDT gates
  and IO bitmaps are different tables — no routing of the gate
  through a wrong accepted check. TARGET-1 `syscallGate_stimmt`
  (gate contract per fetched trap row); TARGET-2
  `syscallGate_offen_bleibt` (pending legs refused, owners named).
  ZEUGE: joint witness with a refused wrong-CPL gate and a refused
  SYSRET-with-unaccepted-return-state pin beside one admitted
  gate-shaped fetched step with a real state change. CUTS: F-RET
  delivery, paging, MSR effects, silicon correspondence, TSO/GX
  bridge and source/budget claims stay OPEN. Checks as AUTHOR-1
  (probe per piece, bau green, standard axioms, no banned
  tactics, every premise used, English). Leave the umbrella import
  for the merger. Commit through `./commit.sh`; finish with the
  report.
- ADJACENCY NOTE (not a premise): registered lanes 708
  (`LongModeReturnHardwareForms.lean`) and 734
  (`ControlRegisterHardwareForms.lean`, whose title covers syscall
  MSR byte effects) own the neighbouring producer areas. This task
  forbids those areas by construction, but the coordinator and
  REVIEW-2 veto on any overlap the live task texts show.

### REVIEW-2 — exact-candidate review of AUTHOR-2 (report only)

- Kind: Lean exact review, report-only. Owned paths:
  `MUSE-REPORT-<id>.md` only.
- Depends: the exact pinned AUTHOR-2 HEAD + the same accepted
  modules.
- Full review text: Independent exact author-HEAD review of the
  pinned AUTHOR-2 candidate. Check: (a) accepted-only imports —
  deny-list the files of 708/726/734/672/718/722/724/736/690/696/
  698 (exact paths, no prefix tricks); (b) decoder census complete:
  every `0F 05`/`0F 07` claim resolves to an accepted decoder row
  or a `decide` refusal pin — no invented row; (c) the CPL gate
  reuses accepted 728 checks (no parallel privilege model, no
  IDT-gate/IO-bitmap confusion); (d) 738 order reused where it
  speaks, explicit pending pin where it is silent; (e) MSR/return/
  paging legs refused with correct owning lane numbers, slot-shaped
  for 708/734/726 (no producer semantics smuggled in); (f) joint
  `_zeuge` with both refusals and one admitted state-changing step;
  (g) CUTS honesty — no delivery, paging, MSR, silicon, bridge, or
  source claim; (h) axioms standard, no banned tactic, every premise
  used. Rule on the ADJACENCY NOTE: compare against the live
  708/734 task texts; any producer-area overlap (MSR semantics,
  return forms, page walks) is REPAIR with the overlapping theorem
  named, however green the build. Exactly one VERDICT: ACCEPT or
  REPAIR with a precise repair list. English report-only clean
  commit.

### AUTHOR-3 — ValidatorDceAdmission (optimiser/validator slice, priority MEDIUM)

- Kind: Lean author.
- Owned paths: `grammatik/Grammatik/X86/ValidatorDceAdmission.lean`,
  `MUSE-REPORT-<id>.md`.
- Depends (accepted only): `OptDceDead` (865+1015), `OptDceStore`
  (866+1016), `ValidatorSkeleton` (349+387), `DecodingCoverage`,
  `Byteschritt` re-deciding. NEVER touch the friend-reserved
  `OptimizationRules.lean` / `OptimizationWitnesses.lean`; this is
  the validator check, not the rule library. NEVER edit
  `grammatik/Grammatik.lean`.
- Priority: MEDIUM (first validator-side consumer of the accepted
  DCE rule lemmas; no module connects them today).
- Full task: In the NEW module prove validator-side admission for
  DCE-rewritten blocks. Read first: the accepted rule side
  conditions (`OptDceDead`: pure — no token/atomic/call/check/stop/
  trap-capable FP — plus dead confirmed; `OptDceStore`), the
  `ValidatorSkeleton.valX86` admission shape, `DecodingCoverage`
  re-decision lemmas, REVIEW-OPT-BINAER §2 obligations. The
  validator RECOMPUTES purity/deadness from the accepted rule
  vocabulary — no trusted annotation, no rival purity predicate, no
  forked evaluator. TARGET-1 `dceZugelassen_bleibt`: a removal
  satisfying the accepted side conditions preserves
  admission-relevant bytes (re-decided coverage: the removed op's
  bytes were never a decoded start the admission relies on — or the
  block is explicitly refused). TARGET-2 `dceVerweigert_laut`: the
  DESIGN §7 failure cases stay refused at validator level —
  faulting FP (`0.0/0.0` hiding `logik bereich`), spin/wait-load
  removal, exit-edge preservation per block map. ZEUGE: joint
  witness with an admitted pure-dead-local removal beside two
  refused probes (spin load, `0.0/0.0`) on reached fetched runs
  with real state change. CUTS: `valX86_sound`, the full closing
  validator and the budget-stop link stay OPEN (CE-1: no theorem
  connects a deleted op to a preserved exhaustion stop); no
  compile-latency and no GCC-ratio claim. Checks as AUTHOR-1.
  Leave the umbrella import for the merger. Commit through
  `./commit.sh`; finish with the report.

### REVIEW-3 — exact-candidate review of AUTHOR-3 (report only)

- Kind: Lean exact review, report-only. Owned paths:
  `MUSE-REPORT-<id>.md` only.
- Depends: the exact pinned AUTHOR-3 HEAD + the same accepted
  modules.
- Full review text: Independent exact author-HEAD review of the
  pinned AUTHOR-3 candidate. Check: (a) rule-lemma reuse — purity/
  deadness recomputed from the accepted `OptDceDead`/`OptDceStore`
  vocabulary, no rival predicate, no forked evaluator, no trusted
  annotation; (b) all three failure-case probes refused by `decide`
  (faulting `0.0/0.0`, spin/wait load, exit-edge break); (c) the
  admitted case is a genuine reached run with a real state change,
  never an empty or unchanged run; (d) friend-reserved files
  untouched (verify no edit outside the two owned paths);
  (e) CUTS honesty — no `valX86_sound`, no closing-validator, no
  budget-stop and no speed claim; (f) no unaccepted import, axioms
  standard, no banned tactic, every premise used. Exactly one
  VERDICT: ACCEPT or REPAIR with a precise repair list. English
  report-only clean commit.

## Explicit non-goals (per-candidate blockers; see plan §3)

No new lane is proposed for: 1106/1107 footprints (registered,
coordinator same-file resume); 698/718/722 repairs (coordinator
resume on the same files, never new lanes); 744/745 pipeline
integration (744 unaccepted — direction (2) respected, nothing
assumes a 744 API); PR-1/PR-2 merge-verify authors (740–743
registered, but no `feat/*` branch in local refs and lane fetch
denied — blocked-on-fetch per direction (3)); F-B32 plug-in
(needs accepted 724); F-VEC plug-in (needs accepted 718 + 724);
F-RET delivery (needs HELD 672 + active 708/726/734); F-AVX (needs
690 + 736); F-6B bridge + closing validator (needs 722/724);
defined-AF arithmetic rows (needs a fetched arithmetic-row
consumer — accepted 720 covers load/store only); held lanes,
external-path tooling, pool tools, friend files (untouched);
benchmark/GCC-O3 measurement (needs an accepted pipeline).

Direction (4) reconciliation: SYSCALL/SYSRET enters as the
accepted-checks gate slice AUTHOR-2 (byte forms belong to
registered 708/734); the DCE validator non-reserved path enters as
AUTHOR-3 (rules 865/866 accepted, unconnected); F-DEV already
landed via 1102/1103 (proposing it again would be a duplicate);
F-B32 stays blocked on accepted 724. Direction (5): 3 substantive
pairs, no filler — remaining slots are the coordinator's live
backfill, not invented work.

## Verification

- No Lean, Rust, instrument, or guardian file changed or created:
  `./lean-bau`, `./lean-probe`, `./cargo-pruef`,
  `./emission-pruef` and `pruefe-*.py` have nothing new to check.
  (A full 500-job `./lean-bau` from a planner lane would only
  contend the shared build lease without verifying anything I
  wrote.)
- `git status --short` clean before edits; `git branch
  --show-current` = `muse/1112`; only the two owned files are
  modified (verified on commit via `git status` + staged diff).

## Task feedback (things believed wrong or missing)

1. Direction (4) names F-DEV as a next-slice candidate, but F-DEV
   as scoped (depends on accepted 704 + 694) already landed via
   merged 1102/1103. Recorded as delivered, not re-proposed; only
   genuinely open sub-slices would justify a follow-up, and the
   1102 CUTS names none against accepted-only modules.
2. "Read the LIVE registry" cannot be fulfilled from a lane clone
   by construction: `.claude/` (manifest, states, dispatch/watch,
   B01–B11) is absent here and lane fetch/network is denied. All
   outcome and disjointness statements above are committed-state
   only (base `7f81b2c6`) and the coordinator must re-verify them
   at registration. If cycle-3+ planners should see live state, the
   coordinator needs to publish a read-only snapshot into the tree.
3. The HARD RULES ZEUGE vocabulary ("a table some function writes")
   has no literal meaning at the hardware layer; four merged author
   reports already record the mapping to written memory bytes. No
   weakening was proposed anywhere in §2 on this account.
4. No `TARGET STATEMENT` was given, so rule 12 has no target; no
   premise over program syntax is stated, so rule 13 has no
   trigger. Nothing was weakened.

## What remains open

Commit this report + the plan section through `./commit.sh`
(staged only, trailer
`Co-Authored-By: muse-agent-1112 <muse-agent-1112@noreply.invalid>`);
reviewer 1113 then rules ACCEPT/REPAIR on the exact candidate;
registration, umbrella-import landing, and all live-state
re-verification belong to the coordinator, not this lane.
