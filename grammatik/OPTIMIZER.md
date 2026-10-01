# Gabbro optimiser: complete specification (Lean folder)

*Lane 331, 2026-10-01. Status: SPECIFICATION / PLAN, not an implementation
and not a proof. Nothing here claims any optimisation is implemented,
admitted, or validated end to end. Central progress record:
[DIRECT-COMPILER.md](../DIRECT-COMPILER.md). Detailed design:
[DIRECT-COMPILER-DESIGN.md](../DIRECT-COMPILER-DESIGN.md). All
source-to-final-binary closure remains OPEN.*

*Scope of this file: the full optimiser design for the direct x86-64
compiler — interfaces, rule inventory, certificates, pipeline, pass order,
verification register, and the friend-contributor handoff. Normative Lean
sources live under [Grammatik/X86/](Grammatik/X86/); this file adds no
definitions and changes no guarantee. English file and identifier names.*

*Link convention: this file sits in `grammatik/`, so `../X` means the
repository root and `Grammatik/X86/*.lean` means the Lean model files.*

*Inspected 2026-10-01 (this lane): `Grammatik/X86/` contains 20 accepted
Lean modules (`Typen`, `Wort`, `Ganzzahl`, `Speicher`, `SpeicherKommutation`,
`Zugriffe`, `Ausfuehrung`, `Byteschritt`, `Codec`, `Bild`, `Relokation`,
`Regionen`, `Stapel`, `TSO`, `FlagBeweis`, `Gleitprofil`, `Vektor`,
`InvariantenOpt`, `AufrufOpt`, `StaerkeReduktion` — 11,223 lines total);
there is NO `IR.lean`, NO `OptimizationRules.lean`, NO
`OptimizationWitnesses.lean` in the tree. The shared typed IR is lane 287's
task ([287.md](../lanes/287.md)) and is PENDING, not accepted. Anything
below that consumes the IR is therefore PROPOSED against a frozen-interface
dependency. Reviewer: lane 334 ([334.md](../lanes/334.md)).*

*Update 2026-10-01 (friend handoff, first delivery, PENDING REVIEW): the two
reserved files now exist —
[OptimizationRules.lean](Grammatik/X86/OptimizationRules.lean) and
[OptimizationWitnesses.lean](Grammatik/X86/OptimizationWitnesses.lean). They
implement the §11.4 starting set over the ACTUAL source syntax (no IR, §11.5):
certificates, executable Lean validators and their generic soundness for
constant folding, range-decided check removal, entailed `narrow`, target-word
strength reduction and the §9 pass-order check. §13 lists exactly what is
proved and what is not. The statement above ("there is NO
`OptimizationRules.lean`") is the lane-331 inspection and stays as history.*

## 0. Reading guide and claim boundary

1. This document is a plan. Every section marked PROPOSED needs Lean
   modelling, generic proofs over the real source model, and independent
   review before any Rust code is built.
2. Sections marked ACCEPTED describe only what is already checked in:
   helper lemmas over real source semantics (`InvariantenOpt`,
   `AufrufOpt`, `StaerkeReduktion`), canonical target vocabulary
   (`Typen`, `Wort`, `Ganzzahl`, `Speicher`), per-byte execution
   (`Ausfuehrung`, `Byteschritt`), codec/image/relocation (`Codec`,
   `Bild`, `Relokation`), stack/regions (`Stapel`, `Regionen`), TSO
   model (`TSO`), flag proofs (`FlagBeweis`), FP profile
   (`Gleitprofil`), SIMD data foundation (`Vektor`), access footprints
   (`Zugriffe`), commutation facts (`SpeicherKommutation`).
3. Performance sections select among already-valid translations only.
   Tuning data never weakens a proof obligation, never admits an
   unproved form, and never changes FP, concurrency, contract, cost or
   lock semantics (safety priority, per standing instructions).
4. No per-program rules exist: every rule is generic over all source
   texts, with statements computed from the source, never trusted from
   a print. No rule mentions a particular function, variable, or
   example name.
5. No measured speed, throughput, RSS, LOC, or benchmark promise appears
   in this file. Unknown numeric limits are marked MEASURE-THEN-CHOOSE.

## 1. Scope and trust path (ACCEPTED goal + PROPOSED optimiser)

### 1.1 What the optimiser may assume (ACCEPTED)

| # | Item | Source |
|---|---|---|
| G1 | Goal theorem `gabbro_ziel` over model G/GX with standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) | [Zielsatz/Spec.lean](Grammatik/Zielsatz/Spec.lean), [BeweisAtomar.lean](Grammatik/Zielsatz/BeweisAtomar.lean) |
| G2 | User logic = `LogikPflicht` + `StartPflicht` for every budget; runtime/OS/binding contracts are user logic, proved, never assumed | [Spec.lean](Grammatik/Zielsatz/Spec.lean) header block, standing instruction 2026-09-30 |
| G3 | Only named hardware behaviour is an assumption (`HardwareAnnahmen`); silicon/device/timing beyond the named list is NOT CLAIMED | [Spec.lean](Grammatik/Zielsatz/Spec.lean) header |
| G4 | Source semantics = real `execStmt`/`exec` over `Expr`/`Stmt`/`Block`/`Endblock`; worlds come from execution, never from metadata | [Semantik.lean](Grammatik/Semantik.lean) |
| G5 | Source concurrency = W / GX; atomics carry the ATOMIC RELY (`PrueferX`, `NutzerPflichtA`, `ZielFX`/`ZielX`) | [BeweisAtomar.lean](Grammatik/Zielsatz/BeweisAtomar.lean) |
| G6 | Checker verdict = Lean `Bool` `Akzeptiert`; the Rust checker is evidence, the Bool is the claim | [Akzeptiert.lean](Grammatik/Zielsatz/Akzeptiert.lean) |

### 1.2 What the optimiser must preserve (PROPOSED obligation list)

Every admitted optimisation preserves, for every accepted source unit:

1. Values of all executions (finite and infinite runs).
2. Faults: every source fault still faults, at a source-blamed place,
   through the declared channel (`or R` / reason), in source order.
3. Memory observations, including concurrent observations under GX/TSO.
4. IEEE float behaviour (see §3.9, §5.5): no reassociation, no free FMA,
   no width change, NaN payload/stickiness preserved where observed.
5. Control state: flags, MXCSR, condition outcomes (see §3.10).
6. Contracts at their place: entry/return/`ruhe`/holder, with actual
   values — never `forall`-away quantified, never compiler-guessed
   `ensures` (see §4.5).
7. Call logs and `FolgeG` order, including inlined calls via ghost
   reconstruction (see §4.6).
8. Concurrent behaviour: race freedom, lock discipline, visibility,
   synchronisation, interrupt-deadlock obligations (see §5).
9. Progress classes and stop kinds (hardware / flag / budget /
   `nieZurueck`); no fairness or termination invented (see §6).
10. Source budget refusal/channel/order/call logs (see §6).

### 1.3 Trust path (PROPOSED)

```
accepted source unit (full text)
  -> source-computed obligations (generic theorems over the source,
     computed in Lean from the source, not trusted from Rust prints)
  -> ONE shared typed IR (lane 287, PENDING; §2)
  -> untrusted Rust candidate passes + certificates (evidence only)
  -> executable Lean Bool validators (proved sound, §7)
  -> lowered/decoded final x86-64 bytes in a checked image (§8)
  -> revalidation of fetched bytes against the loaded mapping (OPEN)
```

Parameters in: full accepted `Einheit D`, duties (`NutzerPflichtA`),
named hardware assumptions `Q`, budget. Results out: either a validated
optimised image (with certificate) or REFUSAL. There is no third outcome
"optimised but unchecked". A missing certificate, a wrong certificate,
or a timed-out optional pass yields refusal or the conservative route
(§7.6), never a warning.

### 1.4 Current helper vs plan state (ACCEPTED inventory)

| Helper file | Covers | Does NOT cover |
|---|---|---|
| [InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean) (550 lines) | executable rewrites on source syntax + correspondence over `eval`/`execBlock`: literal folding helpers (`alsLitOpt`, `litLeBool`, `litEqBool`, `isWahrAll`), branch pruning at decidable conditions | full CFG/GVN/LICM; memory rules; any IR |
| [AufrufOpt.lean](Grammatik/X86/AufrufOpt.lean) (288 lines) | inlining ghost obligation: `GeistAntwort`, `geistPaar` (entry/return pair with ACTUAL `rho`/`v`/`s0`/`s1`), `FolgeLog` preservation lemmas | physical inlining decision, budget transfer for inlined bodies |
| [StaerkeReduktion.lean](Grammatik/X86/StaerkeReduktion.lean) (296 lines) | `mul`/`div`/`rem` by `2^k` to shifts/masks (`shlW`, `shrW`, `maskW`, `mod_pow2_and_mask`) with nonneg/never-zero/width side conditions; `sdiv`/`srem` REFUSED | reassociation, FMA, float reduction, vector reduction |
| [Wort.lean](Grammatik/X86/Wort.lean) (407 lines) / [Ganzzahl.lean](Grammatik/X86/Ganzzahl.lean) (584 lines) | canonical `Wort` (BitVec 64) arithmetic, `trunc`/`sext`, `addB`/`subB`/`xorB`/`andB`/`orB`, checked div/rem, masked shifts, `Bedingung` tests, flag definitions (AF `none` = undefined, never false) | source range/fault bridge (lane 277 business) |
| [Speicher.lean](Grammatik/X86/Speicher.lean) (761 lines) / [SpeicherKommutation.lean](Grammatik/X86/SpeicherKommutation.lean) (342 lines) / [Zugriffe.lean](Grammatik/X86/Zugriffe.lean) (696 lines) | permission-checked little-endian byte memory, `Fuss` byte footprints, single-owner per-instruction access extraction (`Zugriff`), commutation facts | atomicity for unaligned concurrent use; TSO visibility; grouping |
| [Ausfuehrung.lean](Grammatik/X86/Ausfuehrung.lean) (869 lines) / [Byteschritt.lean](Grammatik/X86/Byteschritt.lean) (510 lines) / [Codec.lean](Grammatik/X86/Codec.lean) (806 lines) | 14-form pilot instruction execution, byte step, independent encode/decode | full ISA; SIMD/FP instructions; LOCK/RMW |
| [Bild.lean](Grammatik/X86/Bild.lean) (578 lines) / [Relokation.lean](Grammatik/X86/Relokation.lean) (669 lines) / [Regionen.lean](Grammatik/X86/Regionen.lean) (631 lines) / [Stapel.lean](Grammatik/X86/Stapel.lean) (673 lines) | checked images, relocations, regions, stack/ABI fragments | final linked-image closure; all reachable-bytes coverage |
| [TSO.lean](Grammatik/X86/TSO.lean) (622 lines) | per-core FIFO store buffers, forwarding, flush onto canonical `Speicher`, local-fence readiness, byte-level `Sicht` link | aligned multi-byte atomicity; LOCK RMW; cross-granularity W/GX simulation (OPEN) |
| [FlagBeweis.lean](Grammatik/X86/FlagBeweis.lean) (550 lines) | flag-level correspondence facts | full condition-code optimisation licence |
| [Gleitprofil.lean](Grammatik/X86/Gleitprofil.lean) (653 lines) | MXCSR checks (RNE, FTZ/DAZ off, masks), per-context FP state, f32/f64 projection, f32-vs-f64 counterexample, NaN/sticky/SSE gaps | hardware correspondence; any FP optimisation admission |
| [Vektor.lean](Grammatik/X86/Vektor.lean) (651 lines) | packed-integer data/operation foundation (128-bit, lane widths, two-chunk memory carriage); NO `Befehl` extension, NO FP SIMD | SIMD optimisation admission (refused until correspondence proved) |

Exact cuts: no shared IR exists; no optimisation certificate format
exists; no validator `Bool` exists; no lowering from full source exists;
no TSO-to-GX refinement exists; no budget/time transfer exists. §12
lists every open obligation.

## 2. IR, effects and control interface (PROPOSED, blocked on lane 287)

### 2.1 Identity: one shared typed SSA IR

There is exactly ONE intermediate representation for optimisation. It is
the typed SSA/control-flow representation of lane 287's task
([287.md](../lanes/287.md)), consumed by every later certificate. No
second IR (no "optimiser IR" beside a "lowering IR"), no per-pass syntax,
no source-program-specific syntax (no rule mentions one program's names).
Until lane 287's interface is frozen and accepted, all downstream work
reuses the actual source syntax (`Expr`/`Stmt`/`Block`) plus the accepted
helpers of §1.4. Inventing a parallel IR while waiting is forbidden
(see §11.5).

Required IR content (acceptance checklist for the frozen interface):

| Element | Requirement |
|---|---|
| Types/widths | every value carries its source type and target width (`Ty` × `Breite`); widths from [Typen.lean](Grammatik/X86/Typen.lean); no widthless temporaries |
| SSA + CFG | explicit control labels, edges, terminators; definition/use references; block arguments with φ-nodes; computed dominators (checked, not trusted) |
| Effect nodes | explicit nodes for memory read/write, atomic access (per-width ordering token), lock acquire/release, call (with callee identity + actual args), budget consume, fault/stop (`or R` channel, `nieZurueck`) |
| Region ownership | every memory node names its region; footprints as byte sets reusing `Fuss` ([Speicher.lean](Grammatik/X86/Speicher.lean)); alias relations explicit (§2.3) |
| Source anchors | every node carries its source-unit anchor (function, statement index) for contract-place (§4) and call-log (§4.6) reconstruction |
| Well-formedness | decided graph predicate (`Bool`): closed uses, typed φ-nodes, single terminator per block, reachable exit or declared-divergent |
| Checked interpretation | executable interpretation over actual memory-changing operations (memory writes really change the canonical `Speicher`); a semantics that cannot change memory is not a semantics |

### 2.2 Semantic relation (PROPOSED)

The IR semantics must cover, jointly:

- registers (the 16 `Register` of [Typen.lean](Grammatik/X86/Typen.lean)),
  flags (`Flags`, AF `Option`-undefined), FP control (`MXCSR` per
  [Gleitprofil.lean](Grammatik/X86/Gleitprofil.lean));
- memory (canonical `Speicher`, permission-checked, little-endian);
- observable concurrency events (per-access events compatible with the
  `Zugriff` extraction of [Zugriffe.lean](Grammatik/X86/Zugriffe.lean)
  and the TSO buffers of [TSO.lean](Grammatik/X86/TSO.lean));
- contracts and source call logs (`RufEreignisF`, `rufAt`,
  `FolgeLog`/`FolgeG`);
- finite AND infinite runs (divergence is a behaviour, not an absence);
- stopping and budget faults (source budget vs machine work, §6);
- target work/time transfer obligations (§6.4).

Refinement may stutter (several target steps per source step) but must
not invent fairness or termination: enabledness of a target step is not a
promise it eventually runs. Infinite source runs map to infinite target
runs with the same observable events; a pass that turns divergence into
a fault (or vice versa) is unsound.

### 2.3 Effects, footprints, alias relations (PROPOSED)

- Each memory/atomic/call/lock node publishes its footprint: read set,
  write set (byte sets over regions, reusing `Fuss`), ordering token,
  may-fault flag, may-block flag.
- Alias relation is a proved three-state answer per pair:
  `Disjoint` (proved, with the proof obligation named), `Same`,
  `Unknown`. Only `Disjoint`-proved pairs commute (§3.7); `Unknown`
  blocks motion. There is no "probably disjoint".
- Invalidation rules: any call to an external callee (unknown body),
  any lock release/acquire boundary, any atomic release/acquire, and any
  region hand-over invalidates cached facts over the callee-visible
  footprint (§4.3). Facts carry their validity scope; scope expiry is a
  checked condition, not a comment.
- Only one shared effect system: no invented parallel executors (no
  second evaluator that "also runs the program") and no parallel
  checkers (one validator `Bool` per pass, §7).

## 3. Optimisation inventory and rule table (PROPOSED rules, ACCEPTED helpers noted)

Conventions for every row: PATTERN (syntactic input shape) → FACT SOURCE
(where the justifying fact comes from) → SCOPE (where the fact is valid)
→ CONDITIONS (effect/fault/flag/call/cost gates) → CERTIFICATE (exact
content + recomputed checks) → REFUSAL/COUNTEREXAMPLE (what fails, with a
concrete program sketch). Status is one of: ACCEPTED-HELPER (proved Lean
lemma exists), PROPOSED (specified here, unproved), REFUSED (admission
explicitly withheld), PROVED-PENDING-REVIEW (certificate + validator `Bool`
+ generic soundness + joint witness + poison probes in the reserved files,
§13; not yet independently reviewed, so NOT accepted).

### 3.1 Constant/copy folding and checked arithmetic

| # | Rule | Status |
|---|---|---|
| C1 | literal `lit a ⊕ lit b` → `lit (a⊕b)` where `⊕` is total at the type (bool ops, int add within proved range) | ACCEPTED-HELPER (`alsLitOpt`, `litLeBool`, `litEqBool` in [InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean)); general integer/boolean fold PROVED-PENDING-REVIEW (`foldInt`, `foldBool`, §13) |
| C2 | copy `x = y; …x…` → substitute where `y` is SSA-single-def, same type/width, no intervening write to `y` | PROPOSED |
| C3 | checked op with Decidable side condition proved `true` (e.g. `x ≤ y` by `litLeBool`) → unchecked body with the check retained as a ghost precondition | ACCEPTED-HELPER (`isWahrAll`, `holdsBool` in [InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean)) |

Example (C1): `lit 2 + lit 3` folds to `lit 5`. Fact source: literal
syntax itself. Certificate: the two input literals + recomputed
`decide (2 + 3 = 5)`. Counterexample/refusal: `lit 2^63 + lit 1` at
`signed 64` does NOT fold silently — the overflow fault is a behaviour;
folding it away drops a source fault. It folds only with the overflow
channel preserved (C4).

| # | Rule | Status |
|---|---|---|
| C4 | wrapping vs checked arithmetic selected exactly by the source range/type: `M102`/`M137` side conditions carried by the syntax decide | PROPOSED (bridge owned by lane 277; helpers in [Wort.lean](Grammatik/X86/Wort.lean)/[Ganzzahl.lean](Grammatik/X86/Ganzzahl.lean)) |

### 3.2 SCCP / CFG simplification

| # | Rule | Status |
|---|---|---|
| S1 | `if isWahrAll(c) = true then A else B` → `A` (condition kept as ghost) | ACCEPTED-HELPER (truth checker + correspondence in [InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean)); exact decider incl. `not`/false side + condition fold PROVED-PENDING-REVIEW (`constBool?`, `foldBool`, §13) |
| S2 | unreachable block (no predecessor after S1) removed; φ-nodes re-typed | PROPOSED |
| S3 | sparse conditional propagation of C1 facts along decided edges | PROPOSED (local part — deciding a condition from constants and operand TYPE ranges — PROVED-PENDING-REVIEW, `constBool?`, §13) |

Refusal: S1 fires only when `isWahrAll` returns `true` by recomputation
in the validator. A condition that is "true by contract" without a
decided literal proof does not prune — that would be a compiler-guessed
`ensures` (§4.5).

### 3.3 GVN / CSE

| # | Rule | Status |
|---|---|---|
| V1 | textually identical pure expressions (`a+b`, `a+b`) → one computation, one name | PROPOSED |
| V2 | value-numbered reuse across blocks under dominator + no intervening invalidation | PROPOSED |

Conditions: the reused expression must be pure (no memory/atomic/call/
fault node inside — a faulting expression reused twice faults once, not
twice, which changes behaviour). Certificate: value number + dominator
proof + purity recomputation. Counterexample: `x = a[i] + b; y = a[i] +
b` does NOT merge the loads — that is §3.7 business (memory), and with
a concurrent writer between them the two reads may differ.

### 3.4 Dead code / dead stores

| # | Rule | Status |
|---|---|---|
| D1 | pure computation with no live use → removed | PROPOSED |
| D2 | store to a location provably never read again (whole-unit footprint, §4.4) → removed | PROPOSED |

D2 gate: "never read again" needs the whole-unit writer footprint plus
the concurrency discipline — a store observed by another thread, a
device (MMIO), or a lock-protected reader is live. Flags-live is part of
liveness: removing the last writer of a flag a later `Bedingung` reads
is miscompilation (see §10.4 test `flagslive`).

### 3.5 Bounds / narrow / overflow checks

| # | Rule | Status |
|---|---|---|
| B1 | redundant bounds check removed where the range fact at THIS program point (SSA version, §4.2) entails the access inside the extent | PROPOSED (read-free check decided by type ranges: PROVED-PENDING-REVIEW, `dropCheck`, §13) |
| B2 | `narrow` kept unless the source range already fits the target width at this version | PROVED-PENDING-REVIEW (`narrowEntailed`, §13) |
| B3 | overflow check removed only under a proved-impossible overflow (range entailment, recomputed) | PROPOSED (the explicit `where`-check form: PROVED-PENDING-REVIEW, `dropCheck`, §13) |

Counterexample (B1): `p[i]` checked against extent `n` at entry, then
`i := i + k` inside a loop, then `p[i]` unchecked — the entry fact does
not cover the later SSA version. Removing the second check is refused;
the certificate must name the SSA version and the entailment proof.

### 3.6 Strength reduction

| # | Rule | Status |
|---|---|---|
| R1 | `x * 2^k` → `x << k` for nonneg `x` (source range proves `0 ≤ x`), `k < width` | ACCEPTED-HELPER ([StaerkeReduktion.lean](Grammatik/X86/StaerkeReduktion.lean): `shlW`, side conditions); certified target-word selection PROVED-PENDING-REVIEW (`checkStrength`, §13) |
| R2 | `x / 2^k` → `x >> k` for nonneg `x`, divisor never zero (`2^k ≠ 0` by `k` bound) | ACCEPTED-HELPER (`shrW` + divisor lemma); certified selection PROVED-PENDING-REVIEW (§13) |
| R3 | `x % 2^k` → `x &&& (2^k - 1)` (`maskW`, `mod_pow2_and_mask`) | ACCEPTED-HELPER; certified selection PROVED-PENDING-REVIEW (§13) |
| R4 | signed `sdiv`/`srem` → shift: REFUSED (truncation ≠ shift for negative numerators) | REFUSED (in the helper file itself; the validator refuses it by construction, `checkStrength_sdiv`/`_srem`, §13) |
| R5 | reassociation `(a+b)+c → a+(b+c)`, FMA formation, float strength moves | REFUSED (§3.9) |

Example (R1): `x * 8` with `x : u32 in 0 .. 100` → `x << 3`. Fact
source: the declared source range at this SSA version. Certificate: the
range fact + `decide (8 = 2^3)` + `decide (3 < 64)` + nonneg proof.
Counterexample: `x * 8` with `x : s32` possibly negative does NOT
reduce under R1; signed-negative multiplication is not a left shift.

### 3.7 Alias / commutation / load reuse

| # | Rule | Status |
|---|---|---|
| A1 | two accesses with proved-`Disjoint` footprints commute / the first load reuses across the second | PROPOSED over [SpeicherKommutation.lean](Grammatik/X86/SpeicherKommutation.lean) facts |
| A2 | load after store to `Same` address, no intervening invalidation → forward stored value | PROPOSED |
| A3 | any pair answering `Unknown` → no motion, no reuse | REQUIRED (absence of a rule, enforced by the validator) |

Counterexample (A1): `a[i]` and `b[j]` with `a ≠ b` as NAMES but no
proved region disjointness (both derived from one region, or one behind
a pointer of unknown origin) do NOT commute. Name inequality is not
disjointness. The certificate carries the disjointness proof (distinct
regions, or disjoint proved ranges inside one region, §2.3).

### 3.8 LICM

| # | Rule | Status |
|---|---|---|
| L1 | loop-invariant pure computation hoisted to preheader | PROPOSED |
| L2 | invariant load hoisted only with proved no-store-to-footprint inside the loop + no fault-order change + no concurrency-observation change | PROPOSED |

L2 gates (all must hold): the hoisted load must not fault where the
loop might never reach it (fault-order change: hoisting a faulting load
above a loop that exits early introduces a fault the source never had);
the load must not cross a lock/atomic/call boundary that invalidates
it; the loop bound trip-count reasoning uses only proved facts, never a
timeout. Unrolling (§3.12) interacts: hoist first, then unroll, never
the reverse without revalidation.

### 3.9 Floating point (bridge incomplete — default REFUSE)

Status: the FP bridge is incomplete. [Gleitprofil.lean](Grammatik/X86/Gleitprofil.lean)
gives the target profile (MXCSR RNE, FTZ/DAZ off, masks set, per-context
state, f32/f64 projection, the f32-vs-f64 counterexample, NaN/sticky/SSE
gaps) but NO hardware correspondence and NO optimisation admission.

| # | Rule | Status |
|---|---|---|
| F1 | exact-IEEE folds at one width with RNE proved (e.g. `1.5 + 2.5 → 4.0` in f64, recomputed in the kernel Float model) | PROPOSED (narrow: literal-only, one width, RNE precondition) |
| F2 | reassociation, distribution, FMA formation/contraction, `x*2 → x+x` in floats | REFUSED |
| F3 | narrowing/widening `f32 ↔ f64` motion | REFUSED (the file's own counterexample: `f32` vs `f64` differ observably) |
| F4 | NaN-payload or exception-flag-dependent rewrites | REFUSED (sticky flags + SSE gaps unmodelled) |

### 3.10 Flags / peepholes / address selection / branch layout / allocation interaction

| # | Rule | Status |
|---|---|---|
| P1 | flag-consumer fusion (`cmp; jcc` → fused test where `Bedingung` evaluation over the REAL flag defs agrees) | PROPOSED over [FlagBeweis.lean](Grammatik/X86/FlagBeweis.lean) + [Wort.lean](Grammatik/X86/Wort.lean) flag defs |
| P2 | address-mode selection (`base + i*scale + disp` formation) with no-wrap proof | PROPOSED |
| P3 | branch layout (fall-through, alignment) that changes no semantics, only code positions | PROPOSED (positions revalidated against final image, §8.7) |
| P4 | allocation interaction: spill/fill insertion is semantics-preserving by construction (private spill slots, §9.5) | PROPOSED |

Hard gates: AF-`none` (undefined) is never treated as false; a peephole
that reads an undefined flag is refused. `CMOV`-with-memory reads BOTH
sides' memory: `cmov cc, [mem], reg` can fault even when the condition
is false — predicating a faulting load behind `cmov` does NOT remove
the fault. Division is never "speculated": no hoisting, no
reordering, no zero-divisor motion. Shift counts mask (`& 63` / width
mask): a shift-by-64 is not a shift-by-64. Signed division is not a
shift (R4). A shared-atomic reread is not stable: two reads of one
atomic may return different values — no local token makes them equal
(§5.3).

### 3.11 Inlining / devirtualisation (legal entries, call ghosts)

| # | Rule | Status |
|---|---|---|
| I1 | direct call to a known body inlined with ghost pair spliced at the site (entry + return with ACTUAL `rho`/`v`/`s0`/`s1`), `FolgeLog` preserved | PROPOSED over ACCEPTED-HELPER ([AufrufOpt.lean](Grammatik/X86/AufrufOpt.lean): `geistPaar`, `geistPaar_laenge`, order lemmas) |
| I2 | devirtualisation (indirect → direct) only through a legal-entry proof (the callee set at this call site is proved singleton) | PROPOSED |
| I3 | inlining that drops contracts, budget consumption, or the reason channel | REFUSED |

I1 certificate: callee identity + actual argument env + ghost pair +
order proof + budget transfer (§6.3). Inlining budget: the inlined
body still consumes its source budget; inlining must not make an
over-budget program fit by forgetting the call cost.

### 3.12 Bounded unroll / tails

| # | Rule | Status |
|---|---|---|
| U1 | loop unrolled by factor `k` with proved trip-count multiple-or-remainder structure (remainder loop retained) | PROPOSED |
| U2 | tail-call / tail-jump with stack discipline preserved ([Stapel.lean](Grammatik/X86/Stapel.lean)) | PROPOSED |

Caps are MEASURE-THEN-CHOOSE (§9.7): no invented constants in this
file. Unrolling preserves the source budget refusal: unrolling a loop
whose source budget refuses at iteration `n` still refuses at `n`
(§6.3).

### 3.13 SIMD (planned — default REFUSE)

[Vektor.lean](Grammatik/X86/Vektor.lean) is data operations only: no XMM
file, no `Befehl` extension, no FP SIMD. Admission needs, jointly:
source correspondence per lane, fault order across lanes (first-faulting
lane matches scalar order), tearing rules for concurrent observers,
budget transfer, and vector-tail handling (remainder elements identical
to scalar). Until all are proved: every SIMD optimisation is REFUSED
(`simdFreigabe` closed). Scalarisation direction is allowed only as the
conservative route (§7.6): packed code the validator cannot check is
replaced by checked scalar code, never the reverse.

### 3.14 Rule-table scheduling, dependencies, status summary

Dependency order (a later pass may assume only validated output of an
earlier pass + recomputed facts, never its logs):

```
C1/C2 (fold/propagate) -> S1/S2/S3 (simplify CFG) -> V1/V2 (GVN/CSE)
  -> B1/B2/B3 (check removal, needs range facts at versions)
  -> R1/R2/R3 (strength, needs ranges) -> A1/A2 (alias motion)
  -> L1/L2 (LICM) -> I1/I2 (inline) -> U1/U2 (unroll/tails)
  -> P1..P4 (peephole/select/layout/alloc) ; F* refused; SIMD refused
```

Each pass lists: input pattern, fact source + validity scope, gate
conditions, certificate schema + recomputed checks, refusal example,
status. "No ensuring contracts from compiler guesses" (§4.5) and "no
hard refusal into warning" apply to every row: a failed gate refuses
the rewrite (or the whole compilation if the pass is required), it never
downgrades to a warning.

## 4. Invariant-fact lifetime (PROPOSED, over ACCEPTED location model)

Facts come from source invariants at guaranteed locations. The location
model (entry / return / `ruhe` / holder-observed / lock moves) is part of
the goal statement ([Spec.lean](Grammatik/Zielsatz/Spec.lean): `VertragAmOrtG`,
`InvAmOrtG`, `InvAmGrundG`, `InvRuheG`, `InvSichtG`, `SperrWechselG`,
`SperrSichtG`); the optimiser reuses it and adds nothing.

### 4.1 Fact homes

| Location | Fact valid | Example |
|---|---|---|
| function entry | `requires` with actual entry values | `requires 0 <= n` gives `0 ≤ n` at entry block only |
| function return | `ensures` with actual result | `ensures result <= lenof(buf)` at return site only |
| idle root (`ruhe`) | `InvRuheG`: wherever no writer runs | global quiescent facts usable between threads' writer windows |
| holder-observed (`InvSichtG`) | observed by the holder alone | lock holder's view inside the section |
| lock moves (`SperrWechselG`/`SperrSichtG`) | at every lock move | hand-over facts |
| no-writer windows | invariants wherever no writer runs | stable-memory reuse (§4.3) |

### 4.2 Writer blackout and SSA versions

Inside a running writer or a held section, global invariants are NOT
available (NOT CLAIMED list in [Spec.lean](Grammatik/Zielsatz/Spec.lean)).
Consequences for facts:

- Every range/alias/stable fact is versioned by SSA definition: a fact
  about version `x_3` says nothing about `x_4` after a writer step.
- A fact at entry cannot silently become a fact inside a writer or a
  held section. The certificate names the SSA version; the validator
  rechecks the version is the fact's version.
- Continuous lock holding extends a holder-observed fact across the
  held region only; releasing the lock ends it (lock-move facts take
  over).

Generic SAFE example: `requires 0 <= i <= n` at entry, no writer of
`i`/`n` before the bounds check at block B with versions `i_1`,`n_1` →
check at B removable, certificate cites entry versions + no-writer
proof over the path entry→B.

Generic INVALID counterexample: same `requires`, but a call to an
external callee (unknown body) sits between entry and B → the call may
write `i` through a shared reference → the entry fact is dead at B.
Removing the check is refused. The callee-effect invalidation (§2.3)
is what catches it.

### 4.3 External-callee invalidation

A call whose body is unknown (external, indirect without legal-entry
proof, or not yet summarised — §7.7) invalidates every cached fact over
its visible footprint: all regions it can name, all globals, all
memory reachable from its actual arguments. After such a call, range
facts restart from `ensures` (actual return values) and region
footprints, never from pre-call versions. This is a checked
invalidation: the validator recomputes the visible footprint from the
call node and rejects certificates that reuse pre-call versions.

### 4.4 Whole-unit writer footprint

Dead-store removal (D2) and stable-load reuse need the whole-unit
writer footprint: for each region/table, the set of functions that may
write it, computed from the full source unit (generic, source-computed,
§7.5). Immutable (`const`/never-written-after-init) and provably
private (no reference escapes the function — no int→ptr/fn-ptr
conversion exists to smuggle it out, standing rule) regions get
disjointness proofs for free; everything else needs per-pair proof.
A `static mut` buffer shared with another thread is never "private".

### 4.5 No compiler-guessed contracts

The compiler never derives `ensures`. A fact is usable only if (a) it
is a source `requires`/`ensures`/invariant at its guaranteed place
with actual values, (b) a literal computation (`isWahrAll`-style), or
(c) a previously validated certificate's conclusion. Optimiser
"knowledge" from profiling, heuristics, branch history, or "this usually
holds" is not a fact and never appears in a certificate. A hard refusal
(a check that cannot be proved redundant) stays a refusal; it is never
turned into a warning to "optimise anyway".

### 4.6 Call ghosts carry actuals

Per [AufrufOpt.lean](Grammatik/X86/AufrufOpt.lean): an inlined call's
ghost pair uses the ACTUAL argument environment `rho`, the ACTUAL
result/reason value, and the ACTUAL entry/return worlds `s0`/`s1`.
`geistPaar_laenge` (length 2) and the `FolgeLog` order lemmas are the
checked shape. A ghost with quantified-away parameters (`forall rho`)
or a dropped return event breaks `FolgeG` and is refused. Never
named-program special rules: ghosting applies to every inlined call by
the same generic construction.

## 5. Concurrency and per-width atomics (PROPOSED; TSO bridge OPEN)

Source model: GA/GA-runs/GX/W per [BeweisAtomar.lean](Grammatik/Zielsatz/BeweisAtomar.lean)
(ATOMIC RELY). Target model: per-core FIFO byte store buffers over
canonical memory per [TSO.lean](Grammatik/X86/TSO.lean) (`TSOZustand`:
memory + per-core buffers; oldest-first flush; youngest own-buffer
forwarding; local fence ready iff own buffer empty).

### 5.1 The bridge is OPEN

The per-access x86-TSO refinement into W/GX does NOT exist. Reusing W/GX
lemmas for target steps without the bridge is unsound and forbidden.
What exists: byte-level helpers (not word-atomic proofs), one proved
target-side link to `Sicht` (`Lesbar`/`Frisch` at bytes,
[TSO.lean](Grammatik/X86/TSO.lean) §8), and the precise cross-granularity
obligation. Until the bridge is proved, concurrency-affecting
optimisations run under the conservative discipline of §5.2–§5.4.

### 5.2 What stays put (no motion across)

No optimisation moves, removes, merges, or reorders across:

- any atomic access (any width, any ordering);
- any lock acquire/release (lock discipline + `SperrWechselG` order);
- any fence;
- any call that may synchronise (unknown body ⇒ may synchronise);
- any MMIO/device access (separate profile, §5.6);
- any interrupt enable/disable or handler Tad.

In particular: `racefree ⇒ remove all fences` is NOT a rule. Race
freedom of the source (DRF-SC) is a source property; fences carry the
target visibility that the bridge (OPEN) has not yet transferred.
Removing them "because the source is race-free" deletes the thing the
missing proof still owes.

### 5.3 Per-width atomic rules

- RMW (read-modify-write) sequences are indivisible units: no pass
  splits,CSEs across, or hoists out of an RMW. CAS keeps its retry
  loop; the retry count is not a constant cost and termination of the
  retry is not promised (no "CAS always succeeds eventually" rewrite).
- Ordering tokens are preserved exactly: `acquire` stays `acquire`,
  `release` stays `release`, `seqcst` stays `seqcst`. No strengthening
  ("stronger is safe") without the bridge — stronger can deadlock
  where weaker progressed (interrupt-deadlock obligations,
  `KernHaltE` in the goal).
- A shared-atomic reread is NOT stable: `x := load(a); y := load(a)`
  may observe different values. No GVN/CSE across two atomic reads,
  no "local token" fact makes them equal.
- Bytewise helpers prove byte facts only: the per-byte TSO link says
  nothing about aligned multi-byte single-copy atomicity or LOCK RMW
  (explicitly OPEN in [TSO.lean](Grammatik/X86/TSO.lean) §7).

### 5.4 Local reasoning limits

- A local fence drains the OWN core buffer only — never a foreign
  buffer. "Fence here orders thread B's stores" is not a rule.
- A fact proved under one core assignment does not transfer to another
  (`keinKernHalt` is over every core assignment in the goal).
- Stuttering refinement (§2.2) covers interleaving granularity, not
  fairness: no pass assumes a thread's buffered store becomes visible
  "soon".

### 5.5 FP under concurrency

FP state is per-context ([Gleitprofil.lean](Grammatik/X86/Gleitprofil.lean)).
MXCSR is not shared memory: no atomicity, no cross-thread visibility
rules apply to it. A context switch preserves it; the optimiser never
moves MXCSR writes across calls that may switch context.

### 5.6 MMIO / device profile (separate)

Device accesses have their own ordering profile (device protocol order,
not TSO): never merged, never removed, never reordered, never
speculated, faults always preserved. The profile itself (which regions
are MMIO, what order the device needs) comes from the source-declared
binding contracts (user logic), never from optimiser heuristics.

## 6. Budget, stops, work, time (PROPOSED)

Three separate quantities, three separate obligations:

| Quantity | Meaning | Decided by |
|---|---|---|
| source budget | abstract execution fuel; refusal is a behaviour (`FortschrittG` stop kinds: hardware / flag / budget / `nieZurueck`) | source semantics + duties |
| machine work | actual target steps/bytes executed | target execution ([Ausfuehrung.lean](Grammatik/X86/Ausfuehrung.lean), [Byteschritt.lean](Grammatik/X86/Byteschritt.lean)) |
| hardware time | silicon/device/timing behaviour | named hardware assumptions ONLY |

### 6.1 Source-stop correspondence

Every source stop kind must correspond to a target behaviour:

- budget refusal → target refuses through the same channel, same
  order, same call logs (early fault stays early: an optimisation that
  moves a faulting operation above the budget check changes the
  refusal point and is unsound);
- flag/hardware stops → preserved by §§3.10/5.6;
- `nieZurueck` (never-returns) → the target does not return either
  (no "optimised the infinite loop into a return").

### 6.2 Machine work vs source budget

Cheaper code is no licence to extend source acceptance: if the source
refuses (budget exhausted), the target refuses — even if the optimised
target "could have" continued. Conversely, optimisation work (compile
time, validator fuel) is accounted separately and never debited from
the source budget. Resuming costs alone (restarting after a stop)
prove nothing about the stopped run; the correspondence is per-run,
not per-resume.

### 6.3 Inlining / unrolling / early faults / dead calls

- Inlined bodies consume their source budget at the inline site (§3.11:
  the call cost is not forgotten).
- Unrolled iterations consume per-iteration budget; unrolling a loop
  that refuses at iteration `n` still refuses at `n` (§3.12).
- Early faults (a fault before the budget check in source order) stay
  early; dead-call elimination (removing a call whose result is unused)
  is allowed only if the call is proved fault-free, effect-free, and
  log-free — a call with a ghost obligation (§4.6) is never dead.

### 6.4 Target work/time transfer (OPEN)

The transfer lemmas (machine work bounds source budget consumption;
hardware time bounds machine work under named assumptions) do NOT exist
yet. Until they do: no optimisation claims a time bound, no tuning
table is a correctness premise (§9.7), and "faster binary" is a
measurement (§10.6), never a proof step.

## 7. Certificates and checker architecture (PROPOSED)

### 7.1 Shape: untrusted candidates, proved Bool checks

```
source-computed assumptions (Lean, from the source text)
  + untrusted Rust candidate (pass output + certificate blob)
  -> executable Lean Bool validator per pass (proved sound once, generically)
  -> accept (with validated output) | refuse (or conservative route, §7.6)
```

Names in this section are PROPOSED (no such definitions exist in the
tree today): `OptCert` (certificate ADT per pass), `pruefeOpt`
(executable `Bool` checker), `optSound` (generic soundness: `pruefeOpt
c = true → refinement holds`), `QuellAnnahmen` (source-computed
assumption bundle). They are interface sketches, not claims — the
reviewer must check no sentence below is written as if they already
existed.

### 7.2 Certificate content per pass (exact, recomputed)

| Pass | Certificate carries | Validator recomputes |
|---|---|---|
| fold (C1–C4) | input literals + result literal + range side proof | `decide` on the literal equation + range entailment |
| simplify (S1–S3) | condition + `isWahrAll`-style truth trace | re-runs the truth `Bool` (cf. [InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean): nothing trusted from Rust) |
| GVN/CSE (V1–V2) | value numbers + dominator path + purity trace | dominator check + purity re-derivation |
| DCE (D1–D2) | liveness summary + footprint non-observation proof | liveness recomputation incl. flags/concurrency/device |
| checks (B1–B3) | SSA versions + range entailment | entailment `decide` at the cited versions |
| strength (R1–R3) | range fact + `2^k` shape + width bound | `decide (d = 2^k)`, `decide (k < width)`, nonneg proof |
| alias (A1–A2) | disjointness/sameness proof | region/range proof recheck |
| LICM (L1–L2) | invariance trace + no-store/no-fault/no-sync proof | loop-body scan + fault-order check |
| inline (I1–I2) | callee identity + actuals + ghost pair + order proof | `geistPaar`-shape recheck + `FolgeLog` preservation |
| unroll (U1–U2) | trip-count structure + remainder loop | arithmetic recheck |
| peephole (P1–P4) | flag/address proofs per §3.10 gates | flag-def + no-wrap recomputation |

### 7.3 Soundness, not simulation-premise

Each validator `Bool` gets ONE generic soundness lemma proved in the
Lean kernel: `pruefeOpt c = true →` the output refines the input per
§2.2 (values, faults, observations, IEEE, control, contracts, logs,
concurrency, progress, budget). The refinement is DERIVED from the
`Bool`, never assumed as a simulation premise ("assume the pass is
correct, then…"). No `native_decide`, no trusted Rust verdict, no
unchecked SMT: everything the soundness proof depends on is either a
kernel-checked Lean proof or a recomputed `Bool`.

### 7.4 Graph maps, renames, analyses, obligation reuse

Certificates name explicit node maps (input node → output node),
register/region renames, and the analyses they depend on (dominators,
liveness, footprints, range facts). Source obligations (contracts,
`FolgeG` legs, budget) are REUSED from the source unit, never
re-proved: the certificate shows the output still discharges exactly
the obligations the source computed. Renames are checked total and
injective on live names; dangling references refuse.

### 7.5 Whole-unit obligations: summaries, linking, image

Reusable checked function proofs carry global summaries (may-write set,
may-call set, contract reuse). Linking checks summaries at every call
edge (callee summary ⊇ actual behaviour — computed from the callee
source, not its claim). Final-image obligations (every executed byte
validated, relocations resolved, load mapping matches — cf.
[Bild.lean](Grammatik/X86/Bild.lean)/[Relokation.lean](Grammatik/X86/Relokation.lean))
are never skipped: a per-function validated result with an unchecked
link is a refusal.

### 7.6 Negative default + conservative route

A wrong certificate (failed `Bool`) refuses by default. Where a
conservative route exists it is listed per pass and is itself validated:
scalarise instead of vectorise (§3.13), keep the check instead of
removing it (§3.5), keep the call instead of inlining (§3.11),
`seqcst` instead of a weaker ordering is NOT a conservative route
(§5.3 — stronger can deadlock). Optional optimisation impossible ⇒
valid conservative output, never a warning, never unchecked output.
Required validation failed ⇒ refuse the compilation.

### 7.7 No per-program handwritten proofs

Certificates are produced by Rust code and checked by the generic
`Bool`; no human writes a per-program Lean proof on the trust path.
Per-program Lean files may exist as witnesses (off the trust path,
per standing instruction 2026-09-30) but the validator must accept
WITHOUT them. Reusable checked function proofs (§7.5) are generic
lemmas with joint `_zeuge` witnesses (§10.1), not per-program files.

## 8. Fast compilation + validation pipeline (PROPOSED)

Mandatory validation is on the hot path: the pipeline must compile
fast INCLUDING the Lean checks. Design (all PROPOSED, none implemented):

### 8.1 Compact representation

Typed IR with interned IDs (functions, blocks, nodes, regions as small
integers), arena allocation per function, structural sharing of types
and footprints. No pretty-printing on the hot path; certificates are
compact binary-able structures with a Lean-readable projection for
audit.

### 8.2 On-demand shared analyses with invalidation

One copy each of: dominators, loop forest, liveness (incl. flags),
range facts (versioned), alias answers, footprints, call graph. Each
analysis carries an explicit revision + dependency set; a pass that
writes memory/renames/hoists bumps exactly the revisions it
invalidates. Passes never cache facts across an invalidation boundary.
Stale-fact use is a validator-detected refusal, not a miscompile risk.

### 8.3 Deterministic bounded work

Deterministic worklists (fixed order, no hash-iteration), explicit fuel
per pass (bounded inlining depth, bounded unrolling factor, bounded
layout relaxation rounds). Linear-scan allocation with bounded
improvement rounds; spills go to provably private slots (checked:
slot never named by any other fact). Module/function parallelism is
allowed only with deterministic results (same input → same bytes);
nondeterministic scheduling that changes output bytes is forbidden.

### 8.4 Caching (untrusted, checked)

Cache key: source-contract hash + effect-summary hash + callee-summary
hashes + hardware/ABI profile + proof-schema version + optimiser
version. Cache hits are UNTRUSTED: the cached certificate re-runs the
validator `Bool` before acceptance. Cache schema bump on any validator
change. No cache hit skips the final fetched-bytes revalidation (§8.7).

### 8.5 Timeouts and fallback

Every OPTIONAL pass has a timeout/fuel cap: on expiry, deterministic
fallback to the fully certified route (unoptimised but validated
output for that unit — §7.6). REQUIRED validation has no fallback:
failure refuses. No silent pass-skipping: the certificate records which
passes ran, and the validator checks the recorded pipeline matches an
admitted sequence (§9).

### 8.6 Warm Lean batching (PROPOSED)

Amortise Lean startup: batch validator runs per module in one Lean
process, keep a warm worker with the project `.lake` cache, share
elaborated validator definitions across units. Full-accepted latency
(time to validated bytes) and unvalidated-bytes latency are measured
and reported SEPARATELY (§10.6) — a fast pipeline that skips checks
is not a fast validated pipeline. No assumed linear complexity for
symbolic/entailment checks: range/entailment solving is bounded-decide
with a fuel cap; overflow falls back to keeping the check.

### 8.7 Final revalidation

After relocation and load: revalidate the FETCHED bytes (decoded from
the final image at final addresses, cf. [Codec.lean](Grammatik/X86/Codec.lean)
round-trip + [Bild.lean](Grammatik/X86/Bild.lean)) against the validated
IR: every executed byte covered, file offsets/virtual addresses/load
bias/relocation operands checked against the executed mapping,
including runtime/binding/entry bytes (no unchecked entry stubs).
A mismatch refuses, however late.

## 9. Standard pass ordering (PROPOSED)

Rationale per pass: why it runs here, what it enables, what would break
if it ran earlier. All numeric caps MEASURE-THEN-CHOOSE (unknown now;
no invented benchmarks in this file).

| Order | Pass | Rationale | Cap (proposed kind) |
|---|---|---|---|
| 1 | fold/propagate (C,S) | canonicalises syntax so later analyses see literals, not expressions | fuel: bounded rewrite rounds |
| 2 | CFG simplify | fewer blocks ⇒ smaller dominators/liveness; must precede GVN | fuel: bounded |
| 3 | GVN/CSE (pure only) | removes redundancy before range/alias work prices it | value-number table bound |
| 4 | check removal (B) | needs stable ranges + clean CFG; before motion so LICM sees unchecked bodies | entailment fuel |
| 5 | strength reduction (R) | needs ranges from (4); rewrites arithmetic GVN just numbered | `k < width` (exact, not tuned) |
| 6 | alias motion/load reuse (A) | needs footprints + whole-unit writers; after arithmetic is final | alias-query budget |
| 7 | LICM (L) | needs invariance over final bodies + alias answers from (6) | hoist size bound |
| 8 | inlining (I) | late: inlining earlier would explode every analysis above; ghost + budget transfer checked here | depth + size growth bound |
| 9 | unrolling/tails (U) | after inline (trip counts final); before allocation (body shape final) | unroll factor bound |
| 10 | peephole/select/layout/alloc (P) | last: machine shapes, positions, registers; revalidated vs image | layout rounds, improvement rounds |

Essential portable set (always on): scalar integer/fold/simplify/GVN/
DCE/check-removal/strength/alias/LICM/inline/unroll/peephole + SSE2 and
a selected AVX2 integer profile (after its correspondence is proved —
currently OPEN, so scalar-only until then). Deferred expensive set:
aggressive vectorisation, interprocedural range propagation beyond
summaries, profile-guided layout — admitted only with their own
correspondence proofs. Runtime quality target: good O3-like code;
SAFETY stands above the last marginal gains — the final ~10% of
benchmark performance that needs unsound-by-default tricks (speculative
faulting motion, ordering weakening, FP reassociation) is explicitly
NOT pursued (qualitatively not needed, per steering). Tuning tables are
never a correctness premise: a wrong table costs performance, never
correctness.

## 10. Verification register and test matrix (PROPOSED)

### 10.1 Generic statements + joint witnesses

Every validator soundness lemma and every rule-correctness theorem is
generic (`∀` over full source/IR syntax where it applies) and carries a
joint `_zeuge` companion: ALL premises instantiated JOINTLY on a
NON-DEGENERATE program — at least one table some function writes, and
(for run statements) a reached run with at least one memory-changing
step. A witness over a declaration with no tables or an empty run does
not count (HARD RULES §13). If a witness cannot be built, that is a
finding (premises may be contradictory) — report it, do not weaken the
witness.

### 10.2 Poison certificates and positive probes

Per pass, both directions: poison certificates (wrong certs the
validator MUST refuse: stale SSA version, cross-invalidated fact,
dropped ghost event, weakened ordering, invented `ensures`, faulting
motion, undefined-flag read, `cmov`-memory fault dropped, div
speculated, shift-count mismatch, atomic reread merged, check removed
without entailment, FP reassociation) and positive probes (legal
optimisations the pipeline MUST accept and validate). A pass with only
positive tests is unreviewed.

### 10.3 Required test rows

| Row | What it pins |
|---|---|
| `flagslive` | flag producers survive to their `Bedingung` consumers; no DCE across flag defs |
| `faultorder` | faulting motion refused (LICM hoist above early exit, `cmov`-memory, div speculation) |
| `alias` | name-inequality ≠ disjointness; `Unknown` blocks motion |
| `locks/calls` | no motion across lock/atomic/fence/may-sync call; ghost pairs exact |
| `budget` | over-budget source still refuses after inline/unroll/cheapening; stop kinds preserved |
| `fp` | reassociation/FMA/width-change refused; RNE literal fold accepted |
| `vectortail` | remainder elements identical to scalar; unprovable vector ⇒ scalar route |
| `relocation` | final-address decode matches validated IR; load bias/operands checked |
| `profile/cache` | wrong tuning table still correct (slower only); stale cache rechecked, never trusted |
| `cachedirty` | invalidated analysis revisions never reused across a write boundary |

### 10.4 Project gates (unchanged)

Full-project Lean build stays green (`./lean-bau`); goal keeps exactly
`propext`, `Classical.choice`, `Quot.sound` (`#print axioms
gabbro_ziel`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`pruefe-saetze.py` ratchet unchanged; emission counters re-measured by
the merger, not by lanes. Nothing in this file claims existing tests
finish the whole proof — they are the floor, not the ceiling.

### 10.5 Dependency graph and proof-completion gates

```
IR frozen+accepted -> rule helpers (done: C/S/R/call-ghost) ->
  per-pass cert+Bool+soundness -> TSO bridge -> budget/time transfer ->
  FP admission (narrow) -> SIMD admission -> closing validator soundness ->
  finite+infinite coverage -> Rust implementation -> integrated validation
```

No gate is skippable: Rust implementation starts only after the Lean
interface it implements is reviewed and accepted; integrated validation
only after all gates are green. Reviewer pins the exact commit of each
gate; agent merge and green publication follow the serial checked
process (one merge at a time, master green before push).

### 10.6 Measurement (UNKNOWN now)

Complexity and cold/warm/incremental throughput, RSS, and code quality
are UNKNOWN at the time of writing — no numbers are promised here.
When measured: use emitter-construct coverage (which source constructs
lower+validate, over the corpus), not examples-only; report
cold/warm/incremental separately; report validated-bytes latency vs
unvalidated-bytes latency separately (§8.6). No measured speed or LOC
promise exists in this file.

## 11. Friend-contributor handoff (PROPOSED)

### 11.1 What the friend can own

A generic optimisation rule/proof library AGAINST THE FROZEN SHARED IR:
rule statements, certificate schemas, validator `Bool`s, soundness
proofs, `_zeuge` witnesses, poison/positive probes. This is practical
separate work: it touches only the reserved files (§11.2) plus new
proof-only helpers it adds itself, and it composes with lane 287's IR
through the frozen interface.

### 11.2 Reserved English files (NOT YET EXISTING — do not link as present)

- `Grammatik/X86/OptimizationRules.lean` — rule statements + certificate
  schemas + validator `Bool`s (PROPOSED, reserved for the friend).
- `Grammatik/X86/OptimizationWitnesses.lean` — `_zeuge` companions +
  poison/positive probe theorems (PROPOSED, reserved for the friend).

Muse lanes do NOT edit these paths (standing instruction). They did not
exist in the tree when lane 331 wrote this section. Since the first
friend delivery (2026-10-01, §13) both files exist; they are PENDING
REVIEW, not accepted, and their content is listed in §13.

### 11.3 What the friend does NOT own

Central IR (lane 287), TSO bridge, encoder/image, root umbrella
(`Grammatik.lean`), `Zielsatz/Spec.lean`, shared invariant interface,
pass scheduling, pipeline/caching, Rust implementation. These stay with
the coordinator/lanes; the friend waits for the frozen IR interface
rather than inventing a second IR (§11.5).

### 11.4 Starting order and acceptance contract

Start: arithmetic/constant-fold/strength-reduction rules against the
ACTUAL existing helpers ([Wort.lean](Grammatik/X86/Wort.lean),
[Ganzzahl.lean](Grammatik/X86/Ganzzahl.lean),
[StaerkeReduktion.lean](Grammatik/X86/StaerkeReduktion.lean),
[InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean)) — inspect live
flags, faults, overflow behaviour first. Then: CSE/LICM/inlining rules
only after the shared IR + effects + source-cost interface is accepted.

Proof-acceptance contract per deliverable: generic statement, kernel-
checked proof, joint non-degenerate `_zeuge` with a real
memory-changing run, poison + positive probes, queued wrappers only
(`./lean-bau`, `./lean-probe`), no axioms/`sorry`/`native_decide`, no
hardcoded programs (no per-function-name lemmas), concrete
counterexample for each refusal the rule claims.

### 11.5 While waiting for the IR

Do NOT invent a second IR. Useful waiting work that needs no IR:
extend the accepted helper families (more literal/fold lemmas in the
style of [InvariantenOpt.lean](Grammatik/X86/InvariantenOpt.lean), more
range-justified reductions in the style of
[StaerkeReduktion.lean](Grammatik/X86/StaerkeReduktion.lean)), more
`geistPaar`-style ghost lemmas, more probe/poison programs. Anything
shaped like an IR goes into a clearly marked PROPOSED scratch file of
its own, never into the reserved paths, and is rebased onto lane 287's
interface when frozen.

### 11.6 Submission mechanics

Private clone, local branch, no push to shared master; submit commits
or a patch for independent review + serialised merge (reviewer checks
§10 gates per deliverable). No external messages are sent by this lane,
no friendship credentials are needed or used. Effort scope: modelling
the interface + rule library is practical separate work; closing the
ENTIRE optimiser pipeline (all of §§2–10 proved + Rust + integrated
validation) is larger and is not what this handoff asks.

The friend is not claimed to have started; no start date, no name, and
no delivered line is asserted anywhere in this file.

## 12. Open obligations and implementation phase order

### 12.1 Obligation register (all OPEN unless marked ACCEPTED)

| # | Obligation | Depends on |
|---|---|---|
| O1 | shared typed IR frozen + accepted (lane 287) | source syntax/semantics (ACCEPTED) |
| O2 | per-pass certificates + validator `Bool`s + generic soundness | O1 |
| O3 | lowering full source → IR, checked, with refusal catalogue | O1 |
| O4 | per-access target execution + x86-TSO refinement into W/GX | [TSO.lean](Grammatik/X86/TSO.lean) + W/GX (ACCEPTED helpers only) |
| O5 | stack/ABI/entries/regions/runtime/binding coverage of all reachable bytes | [Stapel.lean](Grammatik/X86/Stapel.lean)/[Regionen.lean](Grammatik/X86/Regionen.lean) fragments |
| O6 | IEEE/control-state correspondence | [Gleitprofil.lean](Grammatik/X86/Gleitprofil.lean) profile only |
| O7 | source budget accounting + machine-work/hardware-time transfer | source `FortschrittG`/stop model (ACCEPTED) |
| O8 | closing validator soundness + finite/infinite coverage + witnesses + negative probes | O2–O7 |
| O9 | Rust implementation of reviewed Lean interfaces | O1–O8 (Lean first) |
| O10 | full integrated source-to-final-bytes validation + performance measurement | O9 |

### 12.2 Phase order

Lean first, later Rust: no Rust optimisation code is written before its
Lean interface (rule schema + certificate + validator + soundness shape)
is reviewed and accepted. The current C11 backend stays operational and
is untouched by this plan; its validation proofs remain legacy evidence.
The selected target is direct x86-64 machine bytes; the C lemmas do not
discharge the x86 obligations.

### 12.3 No hidden NOT-CLAIMED guarantees

This file adds no guarantee to the goal statement. Termination and
waiting bounds, stack depth, weak memory beyond DRF-SC, unguarded
payloads, floats beyond the kernel IEEE model, starvation freedom,
invariants inside a running writer/held section, and CPU-silicon claims
beyond the named hardware assumptions stay NOT CLAIMED per
[Spec.lean](Grammatik/Zielsatz/Spec.lean). The optimiser preserves
claimed guarantees; it proves none about silicon.

## 13. First friend delivery: the rule library over source syntax (PROVED-PENDING-REVIEW)

*2026-10-01. Files:
[OptimizationRules.lean](Grammatik/X86/OptimizationRules.lean) (rules,
certificates, validators, soundness) and
[OptimizationWitnesses.lean](Grammatik/X86/OptimizationWitnesses.lean)
(joint `_zeuge` witnesses, positive and poison probes). Both are imported
by the umbrella `Grammatik.lean`. Nothing here is accepted until an
independent review pins it (§10.5).*

### 13.1 Why source syntax and not an IR

Lane 287's IR is not frozen (§2.1), and §11.5 forbids a second IR. Every
rule therefore acts on the real typed source syntax (`Expr`/`Stmt`/`Block`)
and is proved against the real semantics (`eval`/`execStmt`/`execBlock`).
When the IR is frozen, these rules are the reference the IR-level rules
must agree with; nothing here has to be thrown away.

### 13.2 The refinement relations

| Name | Meaning | Why this strength |
|---|---|---|
| `ExprEquiv e e'` | `e'.orte = e.orte` and `eval` equal in every world and environment | value equality alone would let a rule delete a READ event; the race-freedom legs are stated over the event trace |
| `StmtEquiv` / `BlockEquiv` | identical `Ausgang` under EVERY oracle, loop budget and call handler | the whole `Ausgang` carries world, trace, environment, returns, reasons, `logik` stops (incl. budget refusal) and `hardware` stops (§1.2 items 1–3, 9, 10) |

Both are reflexive (the conservative route, §7.6) and transitive (passes
chain, §3.14).

### 13.3 Rules, certificates, validators

| Rule (§3) | Validator | Fact source, recomputed in Lean | Soundness |
|---|---|---|---|
| C1 integer fold | `foldInt` | `constInt?`: literals and every pure integer operator, each arm the SAME operation `eval` uses (incl. `sdiv`/`srem` as values) | `foldInt_sound` (via `constInt?_sound`, `constInt?_orte`) |
| C1/S3 condition fold | `foldBool` | `constBool?`: constants, `<`/`<=`/`=` decided by operand TYPE ranges (`bounds`), `and`/`or`/`not`; refused if the condition reads anything | `foldBool_sound` (via `constBool?_sound`) |
| S1/B1/B3 check removal | `dropCheck` | condition read-free and decided `true` | `dropCheck_sound` |
| B2 entailed `narrow` | `narrowEntailed` | the operand's type range lies inside the target range; the `narrow` becomes a widening `bind` | `narrowEntailed_sound` |
| R1–R3 strength (target words) | `checkStrength` | right operand the constant `2^k`, left operand nonnegative by type, range (and for `mul` the product) below `2^64`, `k ≤ 64` for the mask | `checkStrength_sound`: `shlW`/`shrW`/`&&& maskW` on the encoded left operand reads back as the source value |
| R4 | `checkStrength` | — | `checkStrength_sdiv`, `checkStrength_srem`: always refused |
| placement | `applyExpr`, `applyStmt`, `applyBlock` | certificate = rule + path (`head`/`rest`, `ite` branches, `locks` body, expression positions) | `applyExpr_sound`, `applyStmt_sound`, `applyBlock_sound` (one mutual theorem by recursion on the certificate) |
| conservative route (§7.6) | `applyOrKeep` | refused ⇒ input unchanged | `applyOrKeep_sound` |
| pipeline order (§§8.5, 9) | `applyPipeline` | passes in §9 rank order and every certificate uses only rules of the pass it is filed under | `applyPipeline_sound`, `applyPipeline_order` |

A certificate never carries a value, range or proof the validator trusts:
it says only WHERE and WHICH rule. The validator recomputes every fact.

Mapping to the §7.1 sketch names: `OptCert` is `ExprCert`/`StmtCert`/
`BlockCert` (plus the shift count of `checkStrength`); `pruefeOpt` is
`applyExpr`/`applyStmt`/`applyBlock`/`checkStrength`/`applyPipeline`;
`optSound` is the family of `*_sound` theorems. The validators are
`Option`-valued rather than `Bool`-valued: the source syntax has no
decidable equality (its terms carry proofs), so instead of comparing a
Rust output with a Lean recomputation, Lean REBUILDS the output from the
input and the certificate, and `none` is the refusal. The untrusted Rust
side (§7.1) then only has to emit what Lean rebuilt. `QuellAnnahmen` is
not needed by these rules: all their facts come from the source text.

Why range facts from TYPES are version-exact (§4.2): a source value
outside its type does not exist (`Typen.lean` §2), and the range belongs
to the expression itself. A variable keeps its declared type for every
value ever assigned to it, so a fact read off its type cannot go stale
across a writer step. No `requires`/`ensures`/invariant is consulted,
so §4.5 (no compiler-guessed contracts) holds by construction.

### 13.4 Witnesses and probes (§§10.1, 10.2)

The joint witness `pipeline_zeuge` runs the whole chain on a program over
`InvariantenOpt.wD` (one table, written by its contract): a range-decided
check, an entailed `narrow`, a store of the narrowed variable and a store
of `2 + 3`. The certified pipeline (fold → drop check → widen `narrow`)
is accepted (`wPipe_accepts`), the optimised and source runs have the same
outcome, and that run moves the slot from `0` to `5`. Every generic
theorem of §13.3 has its own `_zeuge`.

Poison probes (the validators MUST refuse, each checked by computation):
a fold that would delete a slot read although the condition is decided
(`foldBool_refuses_read`, `dropCheck_refuses_read`); an undecided check;
a check decided `false`; an unentailed `narrow`; an integer fold of a
variable; a rule at the wrong type; float comparisons (no FP rule exists);
a certificate path into the wrong shape; signed division; a multiplier
that is not a power of two; a possibly negative operand (§3.6's
counterexample); a product that may wrap 64 bits; a wrong shift count;
a pipeline out of §9 order; a fold certificate filed under the
check-removal pass.

### 13.5 What this delivery does NOT do

- No IR: V1/V2, D1/D2, A1/A2, L1/L2, I1/I2, U1/U2, P1–P4 still wait for
  lane 287 (§11.4).
- Certificate paths reach `cons`/`bind`/`pruefung`/`narrow` continuations,
  `ite` branches, `locks` bodies and expression positions of `ite`,
  `assignSlot`, `assignVar`, `assignGlob`, `pruefung`, `bind`, `narrow`.
  Loops, match arms, calls and the other binders are not reachable yet;
  a certificate pointing there is refused.
- Branch elimination is not a block rewrite: a decided condition folds to
  `true`/`false` exactly; dropping the dead branch is a lowering step.
- A decided condition that reads memory is refused, not optimised.
- Strength reduction certifies the WORD operation, not encoded bytes,
  registers or the final image (§8.7, O3/O5 stay OPEN).
- No FP rule (F1 included), no SIMD, no concurrency/TSO, budget/time or
  call-log transfer beyond exact single-thread `Ausgang` equality.
- No Rust: §12.2 (Lean first) is respected; the Rust certificate producer
  comes after review.

---

## CUTS (honest)

- This file is documentation only: no Lean definition, no theorem, no
  validator `Bool`, no certificate schema is implemented or proved here.
- The shared IR does not exist (lane 287 pending); every section that
  consumes it (§§2, 6.4, 7, 8, 9, 10, O1–O10) is plan, not inventory.
- Accepted helpers are exactly §1.4's table (20 X86 modules, 11,223
  lines); nothing in §§2–12 upgrades a PROPOSED/REFUSED/OPEN item to
  accepted.
- No TSO-to-GX refinement, no budget/time transfer, no FP/SIMD
  admission, no lowering, no closing validator exists at the time of
  writing.
- No performance numbers, no throughput/RSS/latency data, no benchmark
  comparison exists in this file; §10.6 records the unknowns.
- Relative links were checked against the tree on 2026-10-01:
  `../DIRECT-COMPILER.md`, `../DIRECT-COMPILER-DESIGN.md`,
  `../lanes/287.md`, `../lanes/334.md`, `Grammatik/X86/*.lean` and
  `Grammatik/Zielsatz/Spec.lean` all resolve; the two reserved friend
  files were deliberately NOT hyperlinked because they did not exist
  then. Since the first friend delivery (§13) they exist and are linked
  from §13 and the update note at the top.
- Inspected, not merely repeated: the headers and key definitions of
  `InvariantenOpt` (`alsLitOpt`, `litLeBool`, `isWahrAll`, `holdsBool`),
  `AufrufOpt` (`GeistAntwort`, `geistPaar`, `geistPaar_laenge`),
  `StaerkeReduktion` (`shlW`, `shrW`, `maskW`, `mod_pow2_and_mask`),
  `Typen` (`Register`, `Breite`, `Flags`, `Bedingung`), `TSO`
  (`TSOEintrag`, `TSOZustand`), `Wort`/`Ganzzahl`, `Speicher`
  (`lesbar8`, `read64`), `Zugriffe` (`Zugriff`), `Gleitprofil`
  (`MXCSR`, `mxcsrRundungRNE`), `Vektor` (128-bit, lane widths); line
  counts per X86 module; absence of `IR.lean`,
  `OptimizationRules.lean`, `OptimizationWitnesses.lean`.
