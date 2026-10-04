# Next dependency-aware proof wave (lane 401)

*Owner: lane 401. Owns only this file plus `MUSE-REPORT-401.md`.
Status: work plan, not a proof. Full source-to-final-bytes validation remains OPEN.
No model, goal, checker, emitter or ledger change is made or claimed here.
Historical snapshot note (2026-10-04): module/line counts (§0: "27 modules")
and in-flight lists below describe the 2026-10-01 tree; for compiler closure
the binding plan is `dokumente/x86/COMPILER-SCHLUSSPLAN.md`, ledger state is
`DIRECT-COMPILER.md`. Counts here are not re-typed measurements.*

**Capacity policy (authoritative): at most 15 managed Muse model processes
permanently, including reviewers, organisers and repairs.** Target useful steady
utilisation is 15, never above. Registration/queueing is not running. This
supersedes every older 20/40 statement (including WORK-ALLOCATION §7 slot
arithmetic and DIRECT-COMPILER.md workflow notes, which are historical).

## 0. What is stable (accepted foundations this wave builds on)

- Goal and concurrency: `gabbro_ziel` over GX with exactly
  `propext, Classical.choice, Quot.sound`; `PrueferX`/`AkzeptiertSpecX`,
  `NutzerPflichtA`, `schwach_ist_gX`, W/GX legs. Nothing in the goal moves.
- Canonical pilot vocabulary `grammatik/Grammatik/X86/Typen.lean`
  (`Gabbro.Grammatik.X86`): 16 registers in architectural encoding order,
  `Byte`/`Wort`/`Adresse` as `BitVec 8/64/64`, `Breite`, `Flags`
  (`af : Option Bool`), per-byte `Speicher` with R/W/X bits, `Zustand`,
  exactly 14 `Befehl` constructors, `Decodiert`.
- Merged helpers (27 modules, ~14.4 k lines): `Wort`, `Speicher`,
  `Ausfuehrung`, `Codec`, `Byteschritt`, `Bild`, `TSO`, `Zugriffe`, `Stapel`,
  `Regionen`, `Gleitprofil`, `InvariantenOpt`, `AufrufOpt`,
  `SpeicherKommutation`, `Relokation`, `Ganzzahl`, `FlagBeweis`, `Vektor`,
  plus `AccessList`, `SpillPrivate`, `OverlapRefusal`, `MulDiv`, `ShiftLogic`,
  `ControlFlow`, `LockedOps`, `StaerkeReduktion`. (`AccessList.lean:264`
  "admit only findings" is review prose, not a Lean `admit`; no `sorry`/`admit`
  tactic or new `axiom` was found in the merged X86 modules.)
- In flight, not foundations: 287 (single typed IR; reviewer 303 scheduled),
  340 ScalarFloat (author working, reviewer 378 scheduled), 335/344/345/346/
  347/348 NarrowOps/FenceDrain/TableLayout/GateStub/CostSummary/EntryState
  (committed candidates, reviews pending), 349 ValidatorSkeleton (WAITING for
  accepted layout/gate producers), 350 AtomicPayload (candidate, review
  scheduled). Friend-reserved `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` are OFF LIMITS; the optimiser spec is owner 331.

## 1. Triage of the provisional 416-435 reserve (all currently Scheduled, none running)

Verdict codes: KEEP (start in seed order) / DELAY (blocked or no consumer yet) /
COMBINE (merge into one module) / RESCOPE (narrow to remove overlap).

| Lane | Topic | Verdict | Reason |
|---|---|---|---|
| 416 | EffectiveAddress | KEEP, tier 1 | Real consumer: pilot load/store `effAddr`, C1 layout, C2 stubs. Separates modular address arithmetic from nonwrapping region ranges. |
| 417 | ConditionalMove | KEEP, tier 1 | Consumer: ControlFlow CMOVcc follow-up, AufrufOpt lowering. Register-only select with fault preservation is a genuine closer. |
| 418 | BitScan | DELAY | No BSF/TZCNT constructor in the 14-form pilot, no consumer in the single architecture. Pure `Wort` arithmetic without a target form. Revisit only when a native form is admitted. |
| 419 | BitCount | DELAY | Same as 418: no POPCNT form, no consumer. |
| 420 | ByteSwap | DELAY | Same as 418/419: no BSWAP form; involution over words is `Wort`-level. If all three unblock later they return as ONE combined `BitOps` module, not three. |
| 421 | WordAtomicity | KEEP, tier 1 | Direct consumer: TSO bridge per-access work. Must prove frame/disjoint facts or honestly expose the unclosed bridge; never assert word atomicity from eight byte writes. |
| 422 | ReleaseAcquire | KEEP, tier 1 | Direct consumer: TSO/GX bridge acquire-release obligation from actual `TSO` + GX definitions. |
| 423 | BranchLayout | KEEP, tier 2 | Consumer: C5 validator + `Relokation`/`Bild`. rel32 bounds/layout facts for existing encodings only; rel8 stays a cut. |
| 424 | FeatureProfile | RESCOPE, tier 3 | Overlaps C3 CostSummary (347) and 434 HardwareAssumptions. Keep only as the fail-closed admission-decision predicate; cost aggregation belongs to 434, schemas to C3. |
| 425 | FloatExceptions | KEEP, tier 2 | Consumer: A6 ScalarFloat (340, still working). Status/guard/observation fact against the binary64 source model; no fastmath/FMA. |
| 426 | VectorFootprints | KEEP, tier 2 | Consumer: selective-SIMD admission gate (new row N14 below). Footprint/tail/disjointness only, no store-atomicity claim. |
| 427 | RegisterInterference | KEEP, tier 2 | Consumer: register allocation per OPTIMIZER.md. Fail-closed interference certificates over actual pilot reads/writes. |
| 428 | ParallelMoves | COMBINE into 427 | movReg64 scheduling facts belong in the same allocation-correctness module as 427. One module, one review; frees a slot. |
| 429 | CodeImmutability | KEEP, tier 1 | Consumer: fetch/decode (`Byteschritt`) + C5 validator. Disjoint-store preserves decode, overlapping store refuses. Core final-image cut. |
| 430 | ValidationCache | DELAY (high-risk) | Reuse certificates risk trusting Rust-supplied conclusions. Consumer (C5 skeleton, lane 349) is itself WAITING. Revisit only after 349 lands, scoped as pure input-equality congruence. |
| 431 | ValidationBudget | DELAY | Overlaps C3 CostSummary (347, candidate pending review). Fuel-limited traversal waits for the accepted cost schema; otherwise two schemas diverge. |
| 432 | RegionSeparation | KEEP, tier 2 | Consumer: `Regionen`/C1 layout + new row N18. Finite pairwise separation checker over actual regions/footprints. |
| 433 | ObservationProjection | KEEP, tier 2 | Consumer: validator soundness (new row N6). Target observation projection with real faults/stops; no hidden-channel equivalence. |
| 434 | HardwareAssumptions | KEEP, tier 2 | Consumer: cost/time transfer (new rows N5/N17). Selected-profile assumption records + conservative step-cost aggregation from actual finite runs. |
| 435 | DecodingCoverage | KEEP, tier 2 | Consumer: C5 validator. Entry-byte coverage from the actual decoder, not encoder round-trip alone. Complements (not duplicates) `Codec` round-trip. |

Net effect: 13 KEEP (427 absorbs 428), 1 RESCOPE, 5 DELAY (418/419/420 as a group,
430, 431). No slot is filled with a replacement topic until §2 rows are seeded;
delayed lanes stay registered but unscheduled, their numbers reserved.

## 2. Audits 404-415: findings feed, not proofs

The twelve adversarial audits (ARITHMETIC-FLAGS, MEMORY-RANGES,
DECODE-BOUNDARY, FINAL-IMAGE, WEAK-MEMORY, INVARIANT-LIFETIME, CALL-ABI,
DYNAMIC-REGIONS, FLOAT-SIMD, BUDGET-OBSERVATIONS, SOURCE-FOOTPRINT,
END-TO-END-TRUST, reviewers 484-495) produce prioritized repair/bridge tasks,
never closing theorems. Routing rule: each ACCEPTED audit finding is filed by
the coordinator as either (a) a repair against a merged module (returns to the
module owner lane if still open, else a repair lane), (b) a new refusal/negative
case for the owning proof row in §3, or (c) a CUTS amendment. An audit that
confirms a helper "correct within its stated claim" closes nothing and opens
nothing. Audits never substitute for the paired exact-candidate reviews of
proof lanes.

## 3. Next wave: 22 nonoverlapping necessary deliverables

Each author owns ONLY the named new module plus `MUSE-REPORT-<N>.md` (and the
one additive umbrella import). No existing central file, no friend path, no
second IR, no second executor. Every target theorem quantifies over arbitrary
values/programs; source-syntax premises get a JOINT non-degenerate `_zeuge`
(a table some function writes; a reached run with a memory-changing step).
Every row carries a planted refusal/negative case, explicit CUTS and standard
`#print axioms`. Rows marked WAITING define only their non-gated half.

Conventions per row: PATH (new owned file) / USES (existing
definitions/consumer) / DEP (what must land first) / TARGET (main obligation) /
WITNESS+ (positive joint case) / WITNESS- (negative/refusal case) /
REVIEW (paired reviewer).

**Concurrency closers (bridge legs from WORK-ALLOCATION §1):**

- **N1** `X86/TearingRefusal.lean`. USES `Speicher` coefficients,
  `OverlapRefusal`, consumer TSO bridge. DEP: none (runs now). TARGET: aligned
  multi-byte agreement + proved refusal of unaligned/cross-carrier shared
  multi-byte access (tearing correspondence stays OPEN in CUTS). WITNESS+:
  aligned 8-byte store/load round-trip changing memory. WITNESS-: torn
  concurrent split read refused by the Bool. REVIEW: 518.
- **N2** `X86/BridgeRead.lean`. USES `TSO.loadByte`, `Zugriffe.zugriff`,
  `AccessList.accessList`, consumer TSO-GX bridge L-read/view legs. DEP: B1
  AccessList (merged). TARGET: per-access forward simulation for target loads
  into W reads. WITNESS+: single-byte load simulated with memory change.
  WITNESS-: local-drain-as-foreign-drain shape has no simulation (OBS-5 proved
  limitation cited). REVIEW: 519.
- **N3** `X86/BridgeWrite.lean`. USES `TSO.issueByte/flushKern`,
  consumer L-write/step/run legs. DEP: B1 merged. TARGET: per-access forward
  simulation for target stores + FIFO order facts. WITNESS+: two-core
  store-buffer trace with ordered flush changing memory. WITNESS-: foreign
  buffer drained by a local fence is unprovable (stated non-theorem). REVIEW: 520.
- **N4** `X86/CasBound.lean`. USES `LockedOps` LOCK shapes, `CostSummary`
  (C3) schema. DEP: A5 LockedOps (merged), C3 candidate (schema only).
  TARGET: single-LOCK-op = constant-cost shape; CAS-loop = unbounded shape with
  NO constant bound claimed (O-cas-cost closer). WITNESS+: locked add with
  bounded cost; retry loop with attempt counter changing memory. WITNESS-:
  constant bound claimed over a retry site refused. REVIEW: 521.
- **N5** `X86/BudgetSim.lean`. USES `Budget.Op.cost`, `KostenG.kostenTiefF`,
  C3 `kostenSummeOk`. DEP: C3 (347) accepted first; SCFG parts WAITING on 287.
  TARGET: source-step to target-work simulation fragment for counted steps;
  `budget_simulation` full form stated OPEN, never derived by re-summing.
  WITNESS+: one counted step class expanded with honest spill/fence counts on
  a memory-changing run. WITNESS-: unbounded-retry site behind a constant
  bound refused. REVIEW: 522.

**Final-image / validator closers:**

- **N6** `X86/ImageCoverage.lean`. USES `Bild.geladen`, `Byteschritt.geholt`,
  consumer `valX86_sound` (C5 skeleton 349). DEP: C5 non-gated half; full
  soundness WAITING on 287 + TSO coupling. TARGET: every executed byte derives
  from the validated image (reachability coverage obligation). WITNESS+:
  minimal image prefix executed to a memory store. WITNESS-: execution from an
  unlisted mapping refused. REVIEW: 523.
- **N7** `X86/JumpTableCert.lean`. USES `ControlFlow` direct-target theorem,
  `Bild.kanonischBereich`, consumer A4/indirect control. DEP: A4 merged.
  TARGET: jump-table certificate shape (bounded table, entries are decoded
  starts or listed entries). WITNESS+: dispatched indirect jump landing on a
  certified entry, memory changed. WITNESS-: computed target into
  mid-instruction refused. REVIEW: 524.
- **N8** `X86/HandlerEntry.lean`. USES `Stapel.ausgerichtet16`, `Bild` entries,
  consumer C4 EntryState + validator. DEP: C4 (348) accepted. TARGET: trap-return
  and kernel-handoff state obligations the C4 predicates name but do not prove
  (save/restore bytes validated, IF discipline). WITNESS+: entry predicate on a
  concrete loaded prefix with validated save area. WITNESS-: entry with
  unsaved touched XMM refused. REVIEW: 525. (Does not duplicate 348: C4 states
  predicates, N8 proves the trap/handoff transfer facts against validated bytes.)
- **N9** `X86/StackUnwind.lean`. USES `Stapel.Rahmen/Belegung`,
  `Regionen`, consumer validator + Stapel. DEP: none. TARGET: frame-chain
  well-formedness + guard-page facts for actual pilot push/pop/call/ret.
  WITNESS+: nested call/return restoring rsp16 with a memory store. WITNESS-:
  return to a non-executable or guard address refused. REVIEW: 526.

**Source / contract closers:**

- **N10** `X86/GateCallee.lean`. USES gate declaration shape (N063-N066),
  `Bild`, consumer IMAGE-ABI obligation (c). DEP: C2 (346) caller half.
  TARGET: callee-side contract obligations (register/clobber/errno discipline
  at the boundary); kernel behaviour named only. WITNESS+: gate stub pair with
  distinct registers and decoded errno channel. WITNESS-: forged int->ptr at a
  gate site refused (M140). REVIEW: 527. (Complements, not duplicates, C2.)
- **N11** `X86/PayloadResidue.lean`. USES `AkzeptiertSpecX/FussSX`,
  consumer C6 AtomicPayload + QUELLBRUECKE. DEP: C6 (350) checker half.
  TARGET: plain-payload hand-off residue proof (guarded transfer leaves no
  observable residue to an unguarded reader). WITNESS+: guarded handoff with a
  memory-changing run through the guard discipline. WITNESS-: unguarded
  payload read without residue proof refused. REVIEW: 528.
- **N12** `X86/SpawnPublish.lean`. USES `TSO.zaunBereit`, `FenceDrain` local
  facts, consumer B4/OBS-5 publication. DEP: B4 (344) local half. TARGET:
  spawn/join/handler visibility (publication) lemma: what the spawner flushed
  before spawn is visible after join. WITNESS+: two-thread publish/join with
  memory changed on both sides. WITNESS-: join visibility without a fence on
  the publishing path refused. REVIEW: 529.
- **N13** `X86/ContractSites.lean`. USES `AufrufOpt.InlinePflicht`,
  `Zugriffe`, consumer SCFG lowering (287 interface when accepted). DEP: 287
  interface; non-gated half (site shapes over actual `Stmt`/`Endblock`) runs
  now. TARGET: call-site contract application at actual entry/return values
  (no `forall rho`/`forall v` weakening). WITNESS+: inlined call preserving
  the call log with a memory-changing run. WITNESS-: contract applied at
  quantified-away values refused (stated as inadmissible shape). REVIEW: 530.

**Width / float / SIMD gates:**

- **N14** `X86/SimdGate.lean`. USES `Vektor`, 426 footprints, `OverlapRefusal`,
  consumer selective-SIMD lowering. DEP: 426 accepted. TARGET: decided SIMD
  admission gate (lane separation + alignment/tearing + flag treatment proved
  per site). WITNESS+: admitted packed op over disjoint lanes changing memory.
  WITNESS-: overlapping-lane or cross-carrier packed store refused. REVIEW: 531.
- **N15** `X86/F32Refusal.lean`. USES `Gleitprofil`, consumer A6 ScalarFloat
  (340). DEP: none (runs now; feeds 340 before it closes). TARGET: proved
  refusal evidence for the f32 bridge (double-rounding paragraph as a decided
  refusal predicate, not prose). WITNESS+: f64 path accepted under
  `mxcsrGueltig`. WITNESS-: every `float` (f32) node refused at the bridge.
  REVIEW: 532.
- **N16** `X86/DecodeFault.lean`. USES `Ausfuehrung.schritt`, `MulDiv`
  trapping checks, consumer bridge fault leg. DEP: A2/A6 merged/working.
  TARGET: fault preservation catalogue (div-by-zero/overflow → `hardware`
  stop; faulting CMOV-memory keeps its untaken-path fault). WITNESS+:
  trapping division reaching the named stop class. WITNESS-: trapping op
  marked pure for motion refused. REVIEW: 533.

**Cost / time / observation closers:**

- **N17** `X86/TimeTransfer.lean`. USES 434 cost aggregation, source `ZeitAb`,
  consumer FLOAT-ZEIT §8. DEP: 434 accepted; hardware cycle bounds DEFERRED in
  CUTS. TARGET: target-work to source-time transfer skeleton (waiting
  exclusions need exact source correspondence). WITNESS+: bounded run with
  aggregated cost matching the admitted bound. WITNESS-: exclusion without
  source correspondence refused. REVIEW: 534.
- **N18** `X86/RegionFresh.lean`. USES `Regionen.reserviere/initialisiere`,
  432 separation, consumer arena/gate lowering. DEP: 432 accepted. TARGET:
  fresh-disjoint external region proofs per allocation (no int->ptr anywhere).
  WITNESS+: two reservations proved disjoint with stores to both. WITNESS-:
  overlapping reservation refused; number-derived address refused. REVIEW: 535.
- **N19** `X86/CallArgPass.lean`. USES `Stapel`, `Zugriffe`, C2 stub shapes,
  consumer GateStub/lowering. DEP: C2 (346) accepted. TARGET: argument-passing
  facts (register/stack slots, caller/callee-save discipline) for actual pilot
  call shapes. WITNESS+: call with stacked argument arriving intact, memory
  changed. WITNESS-: clobbered live argument across a call without
  save/restore refused. REVIEW: 536.
- **N20** `X86/StutterAudit.lean`. USES `Ausfuehrung`/`Byteschritt` steps,
  consumer bridge + audit 413 findings. DEP: audit 413 output (feeds negative
  cases). TARGET: decided zero-cost-stutter audit lemma (which steps may
  stutter at zero cost without hiding behaviour). WITNESS+: failure-as-stutter
  step preserving observations. WITNESS-: cost-carrying retry hidden behind a
  zero-cost premise refused. REVIEW: 537.

Reserve rows (activate only on audit findings or dependency unblock, numbers
from the coordinator registry at activation):

- **R1** `X86/CacheCongruence.lean`: the safe remainder of delayed 430
  (pure input-equality congruence), only after C5/349 lands. REVIEW: 538.
- **R2** `X86/TraversalFuel.lean`: the safe remainder of delayed 431
  (timeout/refusal-never-acceptance), only after C3/347 schema accepted.
  REVIEW: 539.

Non-overlap check: N1-N20 touch no 335-350 or 416-435 owned path, no friend
file, no second IR (N13 cites the 287 interface, never redefines it), no
duplicated executor (all steps reuse `Ausfuehrung.schritt`/`Byteschritt`/
`TSO` transitions).

## 4. Deterministic scheduling and backfill under the 15-cap

Priority tiers (seed in order, never exceed 15 live model processes):

1. Finish open candidates first: 340 author + 378 review, 335/344/345/346/347/
   348 + 373/382/383/384/385/386 reviews, 349/350 + 387/review. These occupy the
   first free slots; nothing in §3 seeds until a slot frees.
2. Tier-1 §1 KEEPs (416/417/421/422/429) + N1/N15 (dependency-free closers),
   each with its paired reviewer, in §1/§3 seed order.
3. Tier-2 rows as dependencies land (423/425/426/427/432/433/434/435, then
   N2/N3/N4/N6/N7/N9/N11/N13-non-gated/N14/N16/N18).
4. Gated halves (N5/N8/N10/N12/N17/N19 + WAITING parts) activate only when the
   named DEP is accepted; the coordinator checks DEP state at seed time.
5. Audits 404-415 run at most 3 concurrently (they are read-heavy and
   finding-producing, not proof-producing); their findings route per §2.
6. Repairs pre-empt new seeds: a REPAIR verdict on any lane returns its author
   slot to the author; the paired reviewer re-checks the new exact commit.

Backfill rule: when any lane commits its report (done) or stalls on a
documented dependency (WAITING), its slot goes to the next unblocked seed in
tier order. No sleeping placeholder agents: a lane that has no unblocked work
item commits its partial green state + report and exits; the slot is refilled,
never held warm. No duplicate tasks: the registry refuses a seed whose owned
path or target obligation is already assigned to a live lane.

## 5. Honest counting: PIDs, wrappers and stop conditions

- A counted process is a live OpenCode model loop executing an assigned lane
  task in that lane's clone. The coordinator registry records
  `lane -> clone path -> model PID -> role -> state` at launch; the published
  count is the number of registry rows with state `running`, reconciled
  against live PIDs before every status line.
- NEVER counted: `./lean-bau`/`lake` builds, `./cargo-pruef`, emission checks,
  `pruefe-*.py` guardians, log watchers, merge/publish wrappers, completed
  lanes, queued (not yet launched) lanes. Wrappers are build evidence, not
  model work; quoting them as utilisation is forbidden.
- The count drops honestly when: (a) all unblocked seeds are running and the
  rest wait on named dependencies (287 IR, C3 schema, C5 skeleton, audit
  output); (b) the build queue serialises Lean checks (one global Lean build);
  (c) the provider or machine limits launches. The status line then states the
  live count, the blocker for each idle slot class, and the next unblock
  event -- it never rounds up to 15.
- With paired review, steady state is ~6 author+reviewer pairs + 1 organiser =
  13; the remaining 2 slots absorb repairs and audit bursts. Depth-first
  finishing beats breadth: do not seed tier-3 work while tier-1 reviews are
  pending.

## 6. Lane-number allocation (proposed, registry confirms)

Authors N1-N20 + R1-R2 propose lanes **496-517**; paired reviewers propose
**518-539** (reviews 464-495 are already reserved for the 404-435 pairs).
No lane launches until the coordinator registry confirms its number is unique
and its owned path unassigned. Reviewers receive the author's exact commit
hash; a changed commit invalidates the verdict and needs a fresh review.

---

*CUTS: plan only. No Lean module, no validator, no refinement, no cost
transfer and no image acceptance is proved here. Tier ordering assumes the
§0 foundation state as read on 2026-10-01; if 287/340/344-348 change state,
§4 tier 1 re-seeds first. 418/419/420/430/431 verdicts (DELAY) are reversible
on the stated unblock events. Full source-to-binary validation remains OPEN.*
