# Audit: BUDGET-OBSERVATIONS (lane 413)

*Owner: lane 413. Owns only this file plus `MUSE-REPORT-413.md`.
Adversarial implementation audit over the accepted tree as-read 2026-10-01
(base `0b3132b7`). Line numbers below are as-read and may drift.
No Lean, Rust, checker, Spec, goal, emitter or canonical-model change is
made or claimed here. Full source-to-final-byte validation remains OPEN.*

Scope: source budget-stop/cost transfer, target faults/stop observations,
hardware waiting assumptions, observable call/I/O channels, and the hunt
for zero-cost stutter premises that could hide behavior. Evidence is
file/theorem/line-pinned, with two fresh reproduced Lean probes kept
private in `.tmp/` (`probe413_budget.lean`, `probe413_stops.lean`, both
`./lean-probe` 0 errors). Existing decided probes are cited by name where
they already pin a fact; they are not re-claimed.

Out of scope (not duplicated): the three independent audits
`REVIEW-GRUNDLAGEN.md`, `REVIEW-TSO.md`, `REVIEW-OPT-BINAER.md`,
`REVIEW-QUELLE-INVARIANTEN.md` and counter-review 308. This document
covers only budget, stops, waiting, observations and stutter.

Method: read `Ausfuehrung.lean`, `Byteschritt.lean`, `LockedOps.lean`,
`TSO.lean` (fence/CUTS section), `MulDiv.lean`, `InvariantenOpt.lean`,
`AufrufOpt.lean`, `SpillPrivate.lean`, `SpeicherKommutation.lean`,
`AccessList.lean`, `Fortschritt.lean` (stop classes), `FLOAT-ZEIT.md`
(time/cost doctrine), `WORK-ALLOCATION.md` (pending rows). Confirmed by
tree search: no `CostSummary`, `GateStub`, `FenceDrain` or
`ValidatorSkeleton` module exists yet (lanes 344-349 are registered
candidates, not merged foundations).

---

## 1. Verdicts up front

**No false theorem and no hidden unsoundness was found.** Every module
examined states its zero-cost / no-transfer / no-halt limitation in its
own `CUTS`, and the limitations are real limitations, not prose covering
a wrong lemma. The audit therefore reports **consumer gaps and one
concrete undercounting risk**, not repairs to accepted proofs:

- The single load-bearing risk is **E1**: failed-CAS stutter carries no
  cost anywhere, and `lockKosten` counts only successful locked ops. Any
  future work bound that sums shape costs without a per-site attempt
  bound undercounts a spin loop without bound. `LockedOps` itself is
  correct (it proves unboundedness); the obligation lands on the
  pending C3 cost-summary certificate (lanes 347/385).
- The second real gap is **E3**: check elimination removes counted
  source steps with no cost delta. Again the module books it as OPEN;
  the obligation lands on the same C3 consumer.
- Everything else in §5 is either correct-with-explicit-CUTS or a named
  OPEN bridge (budget simulation, observation projection, gate stubs,
  stop correspondences) already allocated to lanes 340/344-349/385/433.

## 2. Source budget-stop/cost transfer: target side absent (OPEN, allocated)

**A1. No target step threads a budget or a cost.**
Reproduced structurally (`.tmp/probe413_budget.lean`, `./lean-probe`
0 errors):

- `schritt : Decodiert → Zustand → Option Zustand`
  (`Ausfuehrung.lean:69`)
- `byteschritt : Zustand → ByteAusgang` (`Byteschritt.lean:70`)
- `casSchritt : Adresse → Wort → Wort → Nat → TSOZustand → Option (TSOZustand × Bool)`
  (`LockedOps.lean:83-84`)
- `lockKosten : SperrBefehl → Nat`, `casKosten : Nat → Nat`
  (shape counts only, `LockedOps.lean:98-107`)

against the source side (`.tmp/probe413_stops.lean`, 0 errors):

- `RufSchrittG : {D} → Programm D → Orakel D → Nat → RufMaschineG D → Faden → RufMaschineG D → Prop`
  (the `Nat` is `passes`, the model budget)

So `segZaehleX`/`kostenTiefF` have no target quantity to transfer to
yet: `targetWork`, `expandBound`, `kostenSummeOk` and
`budget_simulation` are schemas in `FLOAT-ZEIT.md` §8.1, all OPEN.
This is the documented state, not a finding against any module.
Consumer: pending C3 author 347 + reviewer 385.

**A2. Check elimination changes budget timing — booked, not hidden.**
`InvariantenOpt.lean:517` CUTS: "cost/ghost-budget transfer (removing a
check changes budget timing)". The proved equalities
(`exec_pruefung_wahr`, `exec_ite_wahr`, `exec_pruefung_inv`,
lines 215-268) transfer traces exactly but carry no cost delta; see E3
for the concrete consequence. Correct within the stated claim.

**A3. Inlining cost recomputation deferred — booked, not hidden.**
`AufrufOpt.lean:255` CUTS: "Bounds/depth and budget timing are
separate preserved obligations (decreases/depth discipline, cost model)
and are not touched here." The `InlinePflicht` structure (lines 127-144)
pins contracts at actual values but no cost field. Correct within the
stated claim; consumer is the same C3 certificate, which must recompute
`kostenTiefF` over the inlined body.

## 3. Target faults/stop observations: disciplined, with two OPEN mappings

**B1. `verweigert` is absence of transition, never halt. Positive.**
`Byteschritt.lean:58-64` deliberately provides NO halt constructor;
both refusal directions are proved (`byteschritt_verweigert_ohne_fetch`,
`byteschritt_verweigert_ohne_schritt`, lines 195-208); CUTS
(`Byteschritt.lean:452`) states termination OPEN and `laufBytes` fuel exhaustion
answering `weiter`. A consumer that needs normal termination (empty
caller on `ret`, thread end) must build it in the closing-validator
layer (pending lane 349). No repair in this module.

**B2. `hardwareHalt` names the source stop class without mapping it.
Correct within claim, mapping OPEN.**
`MulDiv.lean:159-163` header: "`hardwareHalt` (the divide-error trap ...
i.e. the `hardware` stop class), ... the DIV/IDIV-to-`hardware`
correspondence itself is OPEN." Reproduced
(`.tmp/probe413_stops.lean`): `md_div_halt`, `verweigert_heisst_halt`
prove guard/trap agreement and the never-pure policy (`rein_ohne_halt_mul`),
never a source-stop implication. The CUTS (`MulDiv.lean:521`) repeats that
the name does not prove the mapping. This is exactly the honest posture;
the bridge task (target trap → `FortschrittG` `hardware` disjunct) is
unallocated follow-up work after lane 340/349.

**B3. Target refusals cover permissions/length only — consistent with
doctrine, float/budget/contract refusals absent.**
`schritt` returns `none` only on bad length or failed
permission-checked access (`Ausfuehrung.lean:69-72`, all
`*_verweigert` lemmas). There is no target refusal for float range,
budget exhaustion or contract breach, which matches `FLOAT-ZEIT.md` §3:
a float range failure must lower to user-logic refusal
(`Logik.bereich`), never to a new hardware stop. Since the pilot
`Befehl` has no float constructor at all, nothing yet needs that
lowering; lane 340 (ScalarFloat, working) is the producer. No action.

**B4. Profile admission vs hardware fault line drawn correctly.
Positive.** `AccessList.lean:238` CUTS (admission sentence at 265): a `luecke`/refusal is
"validator/profile admission, never an invented hardware fault."
`MulDiv.lean:270-277` keeps the same discipline (refused image is
refused, never executed; guard mirrors the divide check). No module
invents a silicon fault from a validator decision.

## 4. Hardware waiting assumptions: honestly absent

**C1. No fairness, no progress, no timing — stated, not smuggled.**
`TSO.lean:551` CUTS: "No fairness, progress or timing claim: spins, CAS
retries, flush liveness and cycle costs are out of scope; any
`FortschrittG` or `ZeitAbX` transfer is OPEN." `LockedOps.lean:82`
("Stutter is safety-only: no progress or cost follows") and the proved
`cas_schleife_unbeschraenkt` (lines 272-277) refuse exactly the inference
this audit hunts for. Target lock-take spinning and flush liveness are
unmodelled; the attempt-bound obligation belongs to C3 (per-site proved
attempt bounds, `FLOAT-ZEIT.md` §8.1). Lane 344 (FenceDrain, pending)
covers only the local-drain facts, not liveness.

**C2. Local fence limit proved as limitation. Positive.**
`zaunBereit` gates on the empty own buffer only (`TSO.lean:85`);
`zaun_kein_fremd_drain` proves a local fence never drains foreign
buffers, with `zaun_fremd_issue`/`zaun_fremd_flush` pinning the
boundary. The OBS-5 boundary is a proved non-theorem, not a gap hidden
in prose. No waiting assumption is available for a consumer to lean on,
which is the safe direction.

## 5. Observable call/I/O channels: no target counterpart yet (OPEN, allocated)

**D1. Source call logs have no target projection.**
Source: every `RufSchrittG` step is log-silent or one real call/return
event with actual values (`rufSchrittG_logSchritt`,
`AufrufOpt.lean:99-113`); inlined calls re-emit ghost pairs preserving
`FolgeLog` (`geistRekon_folge`, lines 55-84). Target: `call32`/`ret`
move RIP and the stack only (`schritt_call32_erfolg`,
`schritt_ret_erfolg`, `Ausfuehrung.lean:351-379`) and emit no event;
`Zugriffe.lean` extracts per-instruction access records but no call
log. So no statement yet governs which machine calls must preserve
`FolgeG` order or contracts. The ghost mechanism is source-to-source
only. Consumer: pending observation-projection work (reserve lane 433,
"ObservationProjection") together with the 287 IR interface. No repair
in `AufrufOpt` or `Ausfuehrung`.

**D2. Gate/syscall I/O channels entirely unmodelled at target.**
No `GateStub` module exists (lane 346 pending,
`WORK-ALLOCATION.md:250`); the pilot `Befehl` has no syscall/gate
instruction form. At source, gates are user logic with contracts
(DIRECT-COMPILER design: OS access is user logic, never a hardware
assumption). The consequence is two-sided. First, every externally
observable channel of a real binary (OS writes, map/unmap answers,
thread creation) has no target event at all, so no statement yet
says which machine interactions must preserve contracts or order.
Second, region answers arrive exactly through these gates (memory
from outside comes as a REGION through a `syscall`/`extern` item,
never from a number): the future stub must bind the extent
obligation to the answer, not just emit an event. Consumer: lane
346 (stub shapes plus extent binding) together with 433 (which of
the stub crossings are observable). No repair anywhere in the
accepted tree; nothing there claims a gate form.

---

## 6. Zero-cost stutter hunt: three real edges, no hidden behavior

Every examined step that costs nothing either proves it changes
nothing or books the transfer as OPEN. The three edges below are
the complete list found; all three land on the same consumer.

**E1. Failed-CAS stutter has no cost linkage (load-bearing for any
work bound).** `casSchritt` failure returns the unchanged state
with `false` (`LockedOps.lean:83-96`); `cas_fehlschlag_stottert`
(line 249) proves bytes and buffers unchanged. Cost enters only
through `casKosten versuche = versuche + 1` (line 107), whose
argument the caller supplies: NO theorem connects the number of
executed failed `casSchritt` stutters to `versuche`, and
`cas_schleife_unbeschraenkt` (lines 272-277) proves no constant
bounds the retry count. A work bound that sums shape costs over a
retired trace without a per-site proved attempt bound therefore
undercounts every spin loop, without bound. The module is honest
about this (line 82: "Stutter is safety-only: no progress or cost
follows"; lines 98-107: "a syntactic shape count, never a cycle
or latency bound"). The missing linkage is already booked:
`FLOAT-ZEIT.md` §8.1 (lines 767-771) requires "retry sites carry
proved attempt bounds". Severity: none for safety (stutter is
proved), high for any future timing claim.

**E2. `lockKosten` does not cover CAS.** The shape count has two
arms only, `.xadd64` and `.mfence` (lines 100-104); a CAS attempt,
successful or not, contributes nothing to `lockKosten` (its cost
shape is the attempts-parameterised `casKosten`). A consumer
summing `lockKosten` over retired locked ops silently drops every
CAS. Same consumer as E1 (C3, lanes 347/385): either extend the
shape function with a CAS arm or state the exclusion next to the
attempt accounting. Small, but exactly the silent drop this audit
hunts for.

**E3. Check elimination removes counted source steps with no cost
delta.** `exec_pruefung_wahr`, `exec_ite_wahr`,
`exec_pruefung_inv` (`InvariantenOpt.lean:215-268`) transfer
traces exactly while the eliminated check's source steps vanish;
no cost-delta lemma accompanies them, and the CUTS (line 517)
books "cost/ghost-budget transfer (removing a check changes
budget timing)" as OPEN. Same for inlining (A3): the inlined body
must have `kostenTiefF` recomputed, not inherited. Same
consumer (C3).

**Hunted and NOT found:** no premise of the form "this step costs
nothing, trust us" hiding a memory change (every zero-cost step
proves byte-equality or is ghost-only); no `verweigert` read as
progress (both refusal directions proved,
`Byteschritt.lean:195-208`); no invented silicon fault behind a
validator refusal (B4); no fairness or liveness smuggled through
`zaunBereit` (C2 proves the boundary). One remark: `laufBytes`
fuel exhaustion answers `weiter` (B1), so a consumer counting
`weiter` outcomes as retired work overcounts fuel stops as
progress; the closing-validator layer (lane 349) must tag or
separate fuel-`weiter` from step-`weiter`.

---

## 7. Prioritized bridge tasks (nothing in §§2-6 is a repair)

**P1 (high, blocks any timing claim): C3 cost summary must close
E1-E3.** Owner: author lane 347, reviewer 385
(`WORK-ALLOCATION.md:250-261`). Acceptance: per-site proved
attempt bounds (`FLOAT-ZEIT.md` §8.1), executed-stutters to
`versuche` linkage (E1), CAS coverage in the shape sum (E2), and
recomputed `kostenTiefF` after elimination/inlining (E3/A3).
Until then no work bound exists; nothing accepted claims one.

**P2 (blocks observability claims): projection of call logs and
gate channels.** Owner: reserve lane 433 (ObservationProjection,
`DIRECT-COMPILER.md:200`) on the accepted 287 IR interface, with
346 for stub shapes. Acceptance: which machine calls preserve
`FolgeG` order, which gate crossings are observable, extent bound
to region answers. Until then `FolgeG` and contracts stop at the
source boundary; nothing accepted claims otherwise.

**P3 (blocks end-to-end stop claims): stop correspondences.**
Three mappings, all OPEN: target trap to `FortschrittG`
`hardware` disjunct (B2; named in `MulDiv.lean:159-163`, mapping
assigned by that file's CUTS to "bridge lane 277", which has no
row yet in `WORK-ALLOCATION.md` — allocation gap worth closing);
normal-termination constructor in the validator layer (B1, lane
349); machine-work-to-budget simulation (A1, phase-B
`budget_simulation`, `FLOAT-ZEIT.md` §8.1 lines 696-705).
Profile-vs-fault discipline (B4) constrains all three: validator
refusals must never arrive as `hardware`.

**P4 (doctrine, not a gap): waiting stays unmodelled.** No task
unless a `ZeitAbX` transfer is claimed; then the claim needs
named hardware waiting assumptions, with lane 344 (local drain
facts only) and C3 attempt bounds as prerequisites.

**Explicit non-tasks.** `Byteschritt` needs no halt constructor;
`MulDiv` needs no mapping proof inside its naming file;
`AufrufOpt`/`InvariantenOpt` need no cost field inside their
equality/ghost results; `TSO` needs no fairness; `AccessList`
needs no fault behind `luecke`. Each file's CUTS already says
so; "repairing" any of them inside its own claim would be scope
creep, not a fix.

---

## 8. Evidence log and CUTS of this audit

Reproduced probes (private, `.tmp/`, never committed):
`probe413_budget.lean` — `./lean-probe` 0 errors (re-run
2026-10-01): target step types take no budget/cost argument;
shape costs compute (`lockKosten (.xadd64 ..) = 1`,
`casKosten 5 = 6`); failed CAS is proved stutter.
`probe413_stops.lean` — `./lean-probe` 0 errors (re-run
2026-10-01): `RufSchrittG` threads `passes`, `byteschritt` takes
none; `md_div_halt`/`verweigert_heisst_halt` proved, never a
source-stop implication.

Tree facts re-checked 2026-10-01 at base `0b3132b7`: no
`CostSummary`, `GateStub`, `FenceDrain` or `ValidatorSkeleton`
module under `grammatik/Grammatik/X86/`; lane 433 reserved in
`DIRECT-COMPILER.md:200`; lanes 340/344-349 and reviewer 385 in
`WORK-ALLOCATION.md:163-275`; `FLOAT-ZEIT.md` §3 (float refusal
is user logic, lines 164-182) and §8.1 schemas OPEN (lines
660-705, 767-771).

CUTS of this audit: this document proves no Lean theorem and
changes no code, model, checker, statement or proof. Every claim
is a pointer claim (file/theorem/line at the stated base) plus
the two reproduced probes above. Line numbers may drift with
later merges. OPEN here by design: whether C3 attempt bounds
will use syntactic retry caps, semantic progress arguments or
profile admission (a C3 design choice, not audited); whether
gate crossings count as observable (a 433 design choice); the
full final-byte validation chain (phase-B work).