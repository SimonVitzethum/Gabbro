# Direct lowering decision: existing source model versus additional SSA

*Owner: lane 594. Scope: this document plus `MUSE-REPORT-594.md` only.
No Lean, checker, goal, emitter, or optimiser file is changed by this lane.
Status: architecture decision for review (reviewer: lane 606). It governs
follow-up compiler tasks once accepted; until then it is a proposal.*

## 0. Question and method

Simon's question: can the direct x86-64 backend lower from the existing
typed source model (`grammatik/Grammatik/Syntax.lean` + `Semantik.lean`)
or from `programmlogik/Gabbro/Body.lean` plus its established source
bridge (`bruecke/Bruecke/Quelle.lean`, `Pflichten.lean`, `Simulation.lean`),
without adding another SSA IR — and if so, what is the smallest reusable
representation and what are the concrete lowering contracts?

Method: read the real definitions in this clone at base `0044c258`
(`Syntax.lean`, `Semantik.lean`, `Body.lean`, `bruecke/Bruecke/Quelle.lean`),
the private snapshots `.tmp/overnight-context/IR287-DRAFT.lean` and
`SourceMemory570-CANDIDATE.lean` (never another clone), and the committed
architecture docs `dokumente/x86/IR-VALIDIERUNG.md`, `QUELLBRUECKE.md`,
`CONNECTION-PLAN.md`. No new IR, interpreter, or axiom is created here.
No source file is changed.

## 1. What the candidates actually are

### 1.1 Candidate A: typed source syntax + `exec` (the goal's own semantics)

- Syntax: `Deklaration` (`Syntax.lean:114`), `Ty` (`Typen.lean:35`),
  `Expr D Γ Λ τ` (`Syntax.lean:342`), `Stmt D V l Γ Λ Λ'`
  (`Syntax.lean:455`), `Block` (`Syntax.lean:533`), `Endblock`.
- State: `World D` (`Semantik.lean:79`: slots, globals, trace),
  `Env D Γ`, outcomes `Ausgang` / `EndAusgang`.
- Execution, the single semantic path of the goal theorem:
  `eval` (`Semantik.lean:214`), `execStmt` (`Semantik.lean:699`),
  `execBlock` (`Semantik.lean:788`), `execEnd` (`Semantik.lean:880`),
  fuelled `exec` (`Semantik.lean:952`).
  The table-write step reuses `World.schreibSlot` (unfolded by
  `execStmt_assignSlot`, the exact operation the SourceMemory570
  candidate reuses).
- Goal binding: `Zielsatz.Einheit` (`P`, `S`, `Q`, `starts`, `sp0`),
  `NutzerPflicht` / `NutzerPflichtA`, `PrueferX` / `AkzeptiertSpecX`,
  `gabbro_ziel` over GX. Anything the validator accepts must refine to
  THIS execution; there is no alternative source semantics on the trust
  path.

### 1.2 Candidate B: `Gabbro.Body` plus the duty bridge (human-proof language)

- `programmlogik/Gabbro/Body.lean`: `Value` (int/bool/absent/present/
  reason/tagged), `Stmt` (`Body.lean:966`: `let`, assignment, `if`,
  `match`-over-option, `return`, plus call/loop desugaring, wrapping
  stores, `narrow` as `ite`), `State` (places to values, `let` bindings),
  `exec : Env -> List Stmt -> State -> Outcome` (`Body.lean:1357`).
- By its own header: NO heap model, NO separation logic, NO pointers,
  NO concurrency. Sequential reading only; races, frames, aliasing, and
  overflow live in the checker passes (`M104`, `E005`/`E008`, `R007`,
  `K008`/`K009`), not in this execution.
- Bridge (`bruecke/Bruecke/`): `zuBody` (body of `f` as `Body` sees it),
  `preExpr` / `postU` / `meetsU` (duty statement), `Pflichten src`,
  `nutzer_aus_quelle` / `nutzerA_aus_quelle` (`Quelle.lean:144/156`) via
  `bruecke_nutzer` (`Simulation.lean`). This supplies premise (b) for
  the goal theorem from human-written duty files.
- Coverage ceiling (read from `QUELLBRUECKE.md` §1.4, confirmed against
  `Pflichten.lean`): `zuBody` returns `none` (refusal, never a weaker
  body) for `assignB`, `assignTabB`, lock open/close, `alt`/`erg` outside
  `ensures`, bool returns, arithmetic inside `ensures`, bool slot reads,
  unknown operators. Atomics, locks, gates, regions, handlers, arenas
  are outside the bridged fragment. The bridge is therefore a
  duty-statement path for premise (b), not a compiler input language:
  it refuses exactly the constructs a backend must lower.

### 1.3 Candidate C: IR287 draft SSA/CFG (private snapshot, uncommitted)

The snapshot is a substantial second language (~1400 lines in the
snapshot): `IROrd` (plain/atomic; fences, locks, RMW explicitly not
modelled), `IRSort` (val/tok), `IROp D` (const/fetch/mov/add/sub/cmp/
store/setvar/push/pop with source anchors), `IRPhi`, `IRTerm`
(halt/br/cond), `IRBlock`/`IRGraph`, `IRState` (world + vars + ssa +
toks + label/pred), `irStepOp` (re-implements `Zahl.add`/`sub` and calls
the real `World.schreibSlot` for stores), `irStepBlock`, fuelled
`irRun`, decided checker `irWF` (unique labels, entry present, token
phi coverage, use/definition dominance via recomputed `domSets`,
depth/token threading, `b.label < tgt` edge order), derivation evidence
`FragE`/`FragS`/`FragB`, lowering `lowerE`/`lowerB`/`lowerGraph`, and
execution facts (`ssaGet_push`, `runList_append`, `runList_stable`,
`runPhisTok`, agreement `varsAgree`/`memEq`).

Covered fragment (stated in its own header): integer arithmetic,
bind/assignment, memory write, conditional flow, with a generic
correspondence to `eval`/`execStmt`/`execBlock`. Explicit cuts in the
same file: no calls, no loops (loop-free graphs only — labels strictly
grow along edges), no fences/locks/RMW, `noBindB` forbids `bind` under
an `ite` branch, stores carry an empty static resource list. It is a
real SSA construction with a real interpreter (`irRun`) and a real
checker (`irWF`) — i.e. a second semantics, a second executor, and a
second WF notion alongside `exec` and the checker.

### 1.4 Candidate D (reference point): direct AST-to-block lowering contracts

No persistent IR file. Lowering is a checked relation from
source-anchored instruction blocks to decoded bytes, reusing the
SourceMemory570-candidate pattern: small generic representation
interface (`zahlWort`/`wortZahl` + `repOk` range/width/region Bool +
`layoutOk`/`regionDisjunkt` from `TableLayout`/`Regionen`) with source
writes through `execStmt`/`World.schreibSlot` and target writes through
`write64`/`read64`. CFG, dataflow, and allocation facts are
validator-recomputed checked claims over the block list (the
`IR-VALIDIERUNG.md` §4.2 discipline), not a stored graph with its own
`irRun`.

## 2. Comparison on the five asked criteria

| Criterion | A: typed `Syntax`/`exec` | B: `Body` + bridge | C: extra SSA IR (IR287 shape) |
|---|---|---|---|
| Proof reuse | Full: the goal theorem, `schwach_ist_gX`, `PrueferX`, `NutzerPflichtA`, and the QUELLBRUECKE schema (`valX86_sound`, `schluss_x86`) are already stated over this execution. Every connection lane (559–575) consumes it. | Partial: reuses premise (b) only (`nutzer_aus_quelle`). Contributes nothing to code shape, layout, decoding, TSO, or cost legs; refuses backend-relevant constructs. | Negative: duplicates `exec` as `irRun`, then owes a new correspondence (`irRun` vs `execStmt`/`execBlock`) per fragment extension, plus checker soundness for `irWF`, plus a bridge from IR graphs to bytes. Each is a new proof obligation that A already discharges by construction. |
| One semantic path | Yes: exactly one executor (`execStmt`/`execBlock`/`execEnd`/`exec`). No second interpreter to keep in lockstep. | No: `Body.exec` is a second, deliberately weaker executor (sequential core only). Using it as compiler input would fork the semantic path and then need a Body-to-bytes correspondence that does not exist. | No: `irRun` is a third executor. The snapshot already duplicates `Zahl` arithmetic, variable environments (`varsAgree` vs `Env`), and memory writes, with its own fuel, token, and phi-resolution rules. |
| `-O3`-like / invariant optimisations | Sufficient as the reference: `IR-VALIDIERUNG.md` already places all nine starter optimisations in the untrusted middle arrow with checked certificates (layers A/B/C) validated against source-computed `P`/`GX` judgements. Optimisation legality needs recomputed dataflow facts + token threading + duty binding, not a persistent IR file. The friend-reserved `OptimizationRules.lean` / `OptimizationWitnesses.lean` stay untouched under every option. | Insufficient: `Body` has no widths, no token, no ordering, no FP modes, no costs, no footprints. Nothing an optimisation certificate must check (overlap, atomicity, lock regions, FP control status, stop classes) is representable. | Convenient but not required: a shared vocabulary helps certificate writers, but the snapshot's vocabulary is smaller than what certificates need (no calls, loops, atomics, locks, FP, costs) and bigger than what validation needs (its own interpreter + WF + dominators must then be trusted or re-proved). The certificate interface (§2 of `IR-VALIDIERUNG.md`) already standardises claims about before/after block pairs + bytes without requiring `IR.lean` to exist. |
| Compilation / validation speed | Fastest trust path: validator checks are `decide`-settled Bools over finite block lists (`repOk`, `layoutOk`, `lowerOk`-style, `check_C`, `layoutOk`), reusing the existing `korrOk` precedent. No fixpoint in the trusted code beyond what the validator recomputes structurally; Rust hints (bitsets, dominator trees, alias answers) stay hints. | Irrelevant to speed: the bridge runs once per source for duties, not per lowering or per optimisation step. It adds no validation cost but also carries no lowering information. | Slowest to close: every new construct needs a `FragE`/`FragS`/`FragB` derivation extension, a `lowerE`/`lowerB` case, an `irWF` rule, execution-fact lemmas, and correspondence proofs — before any byte is validated. The snapshot's dominator iteration (`domSets`: `blocks.length + 1` steps) and phi/token bookkeeping are extra trusted machinery with no byte-level payoff. |
| Maintenance | Smallest: one semantics to extend (standing rule: every new construct gets G semantics + checker side + Body bridge + correspondence together). No lockstep between two executors. | Small but disjoint: `zuBody`/`postU` coverage grows with the duty fragment, independently of lowering. Keeping it as the duty language costs nothing; promoting it to compiler input would couple every backend change to the human-proof fragment. | Largest: every language or machine extension touches three places (source semantics, IR, byte semantics) plus two correspondences (source-IR, IR-bytes) instead of one (source-bytes via checked lowering). CONNECTION-PLAN M4 already books the cost: with `IR.lean` absent, lanes 570/572/573/574 carry explicit representation interfaces instead — and stay unblocked. |

## 3. Decision

**Use the existing typed source model (candidate A) as the single
reusable source representation. Do not add a persistent SSA IR. Keep
`Body` plus its bridge as the duty-statement path only. Preserve the
IR287 draft unchanged as design input; do not commit it as `IR.lean`.**

Concretely:

1. THE source representation is the typed AST the goal theorem already
   speaks: `Deklaration`, `Programm D`, `Expr`/`Stmt`/`Block`/`Endblock`,
   `World`/`Env`, `execStmt`/`execBlock`/`execEnd`/`exec`, plus the
   source-computed unit `Einheit D` (`einheitAllg` shape, generalised
   per QUELLBRUECKE §3 as coverage grows). No new source-level
   representation is introduced.
2. Lowering is NOT a new language with its own runner. It is a checked
   relation from source-anchored blocks to validated bytes, in the
   SourceMemory570 pattern: a small generic representation interface
   (`repOk`-style admission Bools + `layoutOk`/`regionDisjunkt` +
   value mappings like `zahlWort`/`wortZahl`) with source steps through
   `execStmt`/`World.schreibSlot` and target steps through the accepted
   byte/memory definitions (`Speicher.read/write`, `Codec.decode`,
   `Byteschritt`, `Ausfuehrung.schritt`, `TSO.issueByte/loadByte`).
   Rust prints of layouts, maps, and certificates are hints re-decided
   in Lean, never premises.
3. CFG, dataflow, and register facts live as validator-recomputed
   checked claims over explicit block/edge lists (dominators,
   availability, liveness, token threading, colouring maps), per
   `IR-VALIDIERUNG.md` §§2–4 — without a stored `IRGraph`, without
   `irRun`, without `irWF` as trusted code. The analyses may reuse
   IR287's algorithms as untrusted implementation guidance; their
   soundness is proved against `exec` and the byte semantics, not
   against `irRun`.
4. `Body` stays exactly where it is: the human duty language behind
   `Pflichten src` / `meetsU` / `bruecke_nutzer`. It is not a compiler
   input, not a lowering source, and not a certificate vocabulary.
5. The IR287 draft is preserved (see §7), not deleted and not
   committed. Its reusable ideas are listed in §7; its interpreter,
   WF checker, and fragment datatype are not adopted.
6. Removing the extra SSA stage removes no source-to-bytes proof
   obligation: the delivered closing theorem stays `schluss_x86` with
   `valX86_sound` derived inside the chain (QUELLBRUECKE §4), now with
   the lowering leg stated directly between source-anchored blocks and
   decoded bytes instead of detoured through `IRGraph` acceptance.

## 4. Lowering contracts (what gets proved, with real names)

### 4.1 Contract L1: representation admission (per slot/region)

- Checked Bool: `repOk ty base len off` (SourceMemory570 pattern:
  range `0 <= lo`, `hi < 2^64`, width (`.int`, never bool/sums/FP/
  pointers), region `off + 8 <= len`, `base + off + 8 <= 2^64`).
  Generalises per width/object with `TableLayout.layoutOk`,
  `Regionen.regionDisjunkt`, `Speicher` frame lemmas. Rust layout hints
  via `hinweisOk`, re-decided, never trusted.
- Value mapping: `zahlWort` / `wortZahl` with roundtrip
  `zahlWort_wortZahl` (needs both bounds: `hLo` for `toNat` inversion,
  `hHi` for `ofNat` modulo identity). Each new width/kind gets its own
  mapping + roundtrip; lossy cases (`Int.toNat` clipping, `BitVec.ofNat`
  wrap) are refusals, not premises.
- Success criterion: generic preservation theorems
  (source-write/target-`write64` agreement + disjoint-carrier
  commutation) over arbitrary values, with a jointly inhabited
  memory-changing source/run witness and overlap/out-of-range/width
  refusals. Owner: accepted SourceMemory570 interface (lane 570 +
  reviewer 588); consumers: 567/573/574 per CONNECTION-PLAN §2.

### 4.2 Contract L2: statement lowering (source-anchored blocks to bytes)

- Shape: for each covered `Stmt`/`Block` form, a lowering relation
  `lowerOk`-style (`E`-anchored, never a free initial graph):
  source step `execStmt s σ ρ` agrees with the fetched-byte run
  (`Byteschritt.byteschritt` + `Ausfuehrung.schritt`) on admitted
  slots, with footprint `Zugriffe.zugriff` realised (not merely
  computed) and token/order consequences derived.
- First implementable fragment: exactly what 570 + 568 already cover —
  one `.int lo hi` slot stored as one little-endian 8-byte word,
  integer arithmetic/bind/assignment/memory-write/conditional-flow
  lowered to the 14 accepted pilot forms, with `TableLayout` admission.
  Success criterion: a joint source-table-to-bytes witness (a table
  some function writes; a reached run with a memory-changing step)
  plus planted refusals (overlap, out-of-range index, width mismatch,
  truncated/corrupt bytes, non-executable fetch).
- producers: `execStmt`, `execBlock`, `World.schreibSlot`,
  `TableLayout.layoutFuer/slotAufz`, `Codec.decode`,
  `Byteschritt.fetchDekodiert/gehalt/byteschritt`,
  `Ausfuehrung.schritt`, `Zugriffe.zugriff` + `erfolg_*` realised
  facts. Consumers: validator adapter (M1 follow-up), 571/572/573/574.

### 4.3 Contract L3: control (branches, calls/returns, entries, stops)

- Branch/call/return lowering maps CFG edges to validated
  displacements (`Relokation.rel32Fuer/patchRel32`,
  `BranchLayout` length facts, `Bild` sites) with re-decoding of
  patched bytes (lane 561 pattern) and stack-frame proofs
  (`Stapel`, `StackUnwind`, `CodeImmutability`) from executable-memory
  bytes — never from an emitter annotation.
- Entries bind the FULL unit (`hE : E = einheitAllg u P hn`
  explicitly until the M1 validator adapter closes full `E`-identity),
  with entry obligations from checked mapping + source start/binding
  duties (`EntryState`, `GateStub.torOkB`, `Bild`), OS/binding
  contracts as user logic, loader logic as checked `Laufzeit` premises,
  silicon/timing as the only named hardware premises.
- Budget/stop leg: source/target halves with explicit representation
  interface + real store + exhaustion + stutter/progress argument
  (lane 572 pattern). No free CAS-retry bound (O-cas-cost stays open);
  no unrecorded-oracle-read closure (OBS-5 stays open toward a
  reviewed `Spec.lean` diff if ever moved).
- Success criterion: nested-call run from executable bytes with
  correct return word + RSP restoration; wrong/unchecked-entry,
  guard/code-overlap, and exhaustion refusals; ghost call/return
  events for inlining (direct and indirect) preserving `FolgeG`.

### 4.4 Contract L4: concurrency (per-access TSO to W/GX)

- Per-access store/load relations from the accepted 567 history/view
  projection + 570 representation to actual W steps (`RufSchrittW`),
  reusing `schwach_ist_gX` only once real W execution is derived.
  Byte-level `Sicht` projection alone is never presented as a
  full-carrier claim; tearing/forwarding/fence/LOCK behaviour follows
  the lane-274 per-access table (O-access, O-align, O-spill, O-lock,
  O-ord, O-enable), with `kein_lock_schritt` keeping LOCK claims
  refused until a LOCK step is modelled.
- Success criterion: FIFO order, stutter bookkeeping, two-core joint
  memory-changing witnesses, tearing/foreign-drain/stale refusals,
  atomic-rely duties (`NutzerPflichtA` value sets) preserved as sets.

## 5. Analysis requirements (validator-recomputed, never trusted)

- CFG: explicit labelled blocks + one terminator each (branch/cond/
  call/return/stop-trap), predecessor lists, reducible shape;
  irreducible input refused. Dominators, reachability, and edge maps
  recomputed structurally over the finite block list.
- Dataflow: forward availability/reaching-definitions/invariance and
  backward liveness recomputed by the validator from the graph with
  proved transfer functions; Rust bitsets are worklist hints only.
  Each rewrite/motion site cites a recomputed fact; memory-token
  re-threading decides order, and every load elimination/motion
  additionally cites ownership, held-lock stability, or immutability
  (whole-unit where required) — local disjointness alone never moves
  a shared access across publication, fences, or acquire/release.
- Registers: colouring map SSA-name to register-or-spill with
  recomputed interference, fresh private spill objects (never
  address-taken, in no source extent), token-threaded spill accesses,
  callee-saved save/restore on every path, dead-flags discipline.
  Freshness implies disjointness implies commutation against the
  per-access TSO relation (the §3-item-5 lemma, proved once
  generically against the lane-274 memory relation).
- Refusal surface (each with a planted-defect probe that fails
  closed): truncated/corrupt/overlong decode, non-executable or
  guard-overlapping fetch, out-of-range relocation, overlapping or
  unadmitted layout, width/signedness/unknown-ness mismatch (loud
  `narrow` guard kept, never dropped), trapping-op motion or deletion,
  atomic-order weakening, fence/lock-region motion, FP reassociation
  or cross-mode motion, cost-sum mismatch, missing ghost events,
  missing remainder/tail path, unvalidated external code via a bare
  declaration.

## 6. Dependency / consumer table (real names)

| Producer (accepted) | Consumed by | Through interface |
|---|---|---|
| `Syntax.Expr/Stmt/Block/Endblock`, `Semantik.eval/execStmt/execBlock/execEnd/exec`, `World.schreibSlot` | every lowering/validator lane; L1–L4 | the single semantic path; no second executor |
| `bruecke/Bruecke/Quelle`: `uebersetzeAllg`, `declOf`, `lowerAllg`, `uOf`, `einheitAllg`, `Pflichten`, `nutzer_aus_quelle`, `nutzerA_aus_quelle` | validator closing (`schluss_x86` premises hU/hE/hN) | T3 parse fidelity + duty bridge, reused unchanged |
| `AtomarW.schwach_ist_gX`, `PrueferX`, `NutzerPflichtA`, `gabbro_ziel` | L4, closing theorem | selected concurrency foundation; not rebuilt |
| `X86.Typen`, `X86.Codec.decode/encode`, `X86.Byteschritt`, `X86.Ausfuehrung.schritt` | 559–566, L2/L3 | canonical byte vocabulary + fetched execution |
| `X86.Speicher`, `X86.Regionen`, `X86.TableLayout`, `X86.Zugriffe`, `X86.BranchLayout`, `X86.Bild`, `X86.Relokation` | 560/561/568/570, L1–L3 | layout, footprints, relocation with re-decoding |
| `X86.TSO` + `Sicht`/`W` defs via 567 `TSOHistory` projection | 573/574 (wait ACCEPTED 567 + ACCEPTED 570) | byte-TSO history/view interface (stable, published by 567) |
| 570 `SourceMemory` (`repOk`, `zahlWort`/`wortZahl`, preservation) | 567/571/572/573/574, L1/L2/L4 | THE small representation interface; extended per width, never replaced by an IR |
| 559–566 codec helpers + 568 `AccessExecution` + 569 `StackExecution` | 575 `ExtendedExecution` (waits ACCEPTED 559–566) | one selected-profile byte-facing path; dispatch stated, `decode`/`schritt` never rewritten |
| 571 `EntryExecution` + 572 `BudgetExecution` obstruction | validator adapter (M1 follow-up, proposed next wave) | full-`E` identity, entry/budget/stutter legs |
| Validator adapter (new file, unassigned): `valX86 E bild` over FULL unit + generic `valX86_sound` | `schluss_x86` (delivered theorem) | the only public closing claim; internal composition lemma labelled as such |

First implementable fragment (no IR needed): extend the accepted
570 representation along L1 with one more admitted width/object,
connect one more `Stmt` form along L2 to its already-decoded pilot
bytes, and carry both through the 568 realised-footprint pattern.
Each step ships its joint memory-changing witness, its planted
refusals, precise CUTS, and standard `#print axioms`.

## 7. Migration and ownership plan (IR287, optimiser friend, docs)

- IR287: the author lane (287, still running per the last measured
  snapshot) finishes its committed candidate; reviewer 303 judges the
  exact candidate on its own terms. Whether or not it is accepted, no
  follow-up task adopts `IR.lean` as a second semantics. On acceptance,
  its reusable algorithms (token threading, anchor discipline, pure-
  expression lowering shape, WF checks as validator checks) migrate as
  UNTRUSTED implementation guidance into validator-adapter work; its
  `irRun`, `irWF`-as-trusted-code, and `Frag*` derivation datatypes do
  not migrate. The old draft file/snapshot is preserved, never
  deleted; this document records the decision so a future lane does
  not re-fork it silently.
- Optimiser friend: `grammatik/Grammatik/X86/OptimizationRules.lean`
  and `OptimizationWitnesses.lean` stay reserved and untouched; the
  complete planned optimiser specification stays in
  `grammatik/OPTIMIZER.md`. Optimisation certificates speak about
  before/after block pairs plus decoded bytes through the §4/L1–L4
  contracts, never about `IRGraph` acceptance.
- Central docs: on acceptance of this decision, the coordinator (not
  lanes) records the outcome in `DIRECT-COMPILER.md` history and points
  follow-up compiler tasks at §§3–6 above. Lane files after this one
  must cite this decision before proposing any new representation.
- Ownership: validator adapter (M1: `valX86 E bild` + `valX86_sound`
  shape), one width/object extension of L1, one statement form of L2,
  and the 573/574 per-access legs are four disjoint follow-up tasks
  with the same closure rule as CONNECTION-PLAN §0 (real execution
  evidence, joint witness, planted refusal, standard axioms, exact
  CUTS). No overlapping writers of the representation interface:
  extensions add rows to `repOk`-style tables; they do not fork them.

## 8. CUTS

This document proves nothing and adds no Lean, Rust, or build claim.
Open until proved: the validator adapter (`valX86 E bild`,
`valX86_sound`, `schluss_x86`), every L1 width/object row beyond the
accepted 570 fragment, every L2 statement form beyond the covered
fragment, the L3 entry/budget/stutter legs, the L4 per-access TSO–W/GX
simulation, LOCK/fence execution, the per-access concurrent
equivalence for eligible atomics, the generic vector correspondence
(no SIMD admitted before it), ghost-event call-log preservation, ghost
source-budget accounting (or proved separation with transfer), and
lane-278 timing bounds. Full-source unit computation beyond
`einheitAllg` fragment defaults stays open per QUELLBRUECKE §3. Model
process counts are not progress; only accepted exact-candidate
reviews move work to integration.
