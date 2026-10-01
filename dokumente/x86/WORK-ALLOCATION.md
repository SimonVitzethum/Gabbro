# Next Lean-only wave: dependencies, allocation and safe parallel work (lane 329)

*Owner: lane 329. Owns only this file plus `MUSE-REPORT-329.md`.
Status: work plan, not a proof. Full source-to-final-bytes validation remains OPEN.
No model, goal, checker, emitter or ledger change is made or claimed here.*

Cap basis: the user authorised up to **40** concurrent Muse processes for today
2026-10-01 (authors, reviewers, organisers, mergers), returning to 20 afterwards.
All execution and builds are local. Safety outranks marginal performance; every
accepted optimisation and every emitted byte needs mandatory validation; the
compiler must stay fast. Runtime/OS/binding code is user logic with contracts;
only named silicon, device and timing behaviour is a hardware assumption.

## 0. What is stable (accepted foundations this wave builds on)

- Goal and concurrency: `gabbro_ziel` over GX with exactly
  `propext, Classical.choice, Quot.sound`; `PrueferX`/`AkzeptiertSpecX`,
  `NutzerPflichtA`, `schwach_ist_gX`, W/GX legs. Nothing in the goal moves.
- Canonical pilot vocabulary: `grammatik/Grammatik/X86/Typen.lean`
  (`Gabbro.Grammatik.X86`): 16 registers in architectural encoding order,
  `Byte`/`Wort`/`Adresse` as `BitVec 8/64/64`, `Breite`, `Flags`
  (`af : Option Bool`, undefined not false), per-byte `Speicher` with
  R/W/X bits, `Zustand`, exactly 14 `Befehl` constructors, `Decodiert`.
- Merged helpers (20 modules): `Wort` (`cfAdd/cfSub/ofAdd/ofSub`,
  `parityEven`, `sext`), `Speicher` (`addrOff`, `read64`/`write64`,
  `Fuss` byte footprints), `Ausfuehrung` (`schritt`, `effAddr`, `ripNach`),
  `Codec` (`regCode/codeReg`, `leBytes32/64`, `rexByte`, `modrmReg`),
  `Byteschritt` (`geholt`, `fetchDekodiert`, `byteschritt`),
  `Bild` (`Abschnitt`, `Relok`, `Modus`, `kanonischBereich`, `geladen`),
  `TSO` (`TSOZustand`, `issueByte`/`loadByte`/`flushKern`, `zaunBereit`,
  `TSOSchritt`, `fifo_reihenfolge`), `Zugriffe` (`Zugriff`, `zugriff`),
  `Stapel` (`Rahmen`, `ausgerichtet16`, `sichereWort`, `Belegung`),
  `Regionen` (`Region`/`Vorrat`, `reserviere`, `initialisiere`),
  `Gleitprofil` (`mxcsrGueltig`, `FPKontext`, `muster64`/`bites64`),
  `InvariantenOpt`, `AufrufOpt` (`InlinePflicht`, ghost call events),
  `SpeicherKommutation`, `Relokation`, `Ganzzahl`, `FlagBeweis`, `Vektor`.
- Accepted design docs: `dokumente/x86/WELLE-A.md`,
  `LEAN-ZUERST.md`, `BYTE-PILOT.md`, `EMITTER-INVENTAR.md` (every emitter
  path with widths/orders), `IR-VALIDIERUNG.md` (one shared SCFG, layers
  A/B/C, generic `valX86_sound` shape), `TSO-GX-BRUECKE.md` (per-access
  forward simulation into W, granularity counterexamples, OBS-5),
  `QUELLBRUECKE.md` (source-computed `P`/`E`/duties reuse, no assumed
  refinement), `IMAGE-ABI.md` (file/virtual mapping, two bias modes,
  external-body obligations a/b/c), `FLOAT-ZEIT.md` (f64-first, f32 bridge
  refused until proved, three cost levels), plus the three independent
  audits `REVIEW-GRUNDLAGEN.md`, `REVIEW-TSO.md`, `REVIEW-OPT-BINAER.md`,
  `REVIEW-QUELLE-INVARIANTEN.md` and counter-review 308.
- In flight (not foundations): 287 (single typed IR, working; reviewer 303
  scheduled), 327 (safety-first performance revision, candidate pending;
  reviewer 328; merge owner 330; merge review 333), 331 (complete optimiser
  spec in `grammatik/OPTIMIZER.md`; reviewer 334). Lane 280 (Rust codec)
  stays stopped; the Rust mirror stays unwired.
- Friend-reserved paths are OFF LIMITS to Muse authors:
  `grammatik/Grammatik/X86/OptimizationRules.lean`,
  `grammatik/Grammatik/X86/OptimizationWitnesses.lean`.
  The optimiser spec is owner 331; friend stack/source-TSO/final-image
  pipelines already owned are not assigned below.

## 1. Outstanding dependency graph (what blocks the chain)

```
ISA forms (pilot=14 only) --> decode/encode --> fetch+step --> image/ABI --> closing validator
  narrow b8/b16/b32 MISSING      done (pilot)      done (pilot)    Bild merged    valX86_sound OPEN
  mul/div/shift/logic MISSING    LOCK/fence MISSING (no target form for rmw/drain)
  scalar SSE2 f64 PROPOSED       f32 bridge REFUSED until proved
  indirect control PARTIAL (call32/ret only; jump tables need certificates)

Source units --> duties --> lowering --> SCFG --> optimisation certs --> layout/refinement
  tables/globals OPEN   zuBody fragment only   287 WORKING    SCFG WAITS on 287
  atomics duty VACUOUS  payload hand-off OPEN  accessList OWNERLESS (review finding)
  arenas/gates/linking OPEN per construct      spill/SIMD need TSO table first

Concurrency --> TSO bridge --> legs
  per-access simulation OPEN (D-tso, L-read/write/view/step/run)
  O-align decidable half STARTABLE, tearing proof OPEN
  OBS-5 (i)-(iv) OPEN: local drain != foreign-buffer drain; binding contracts missing
  O-cas-cost: unbounded retry voids constant bounds; O-time transfer OPEN

Budget/time --> cost summary schema PROPOSED, budget_simulation OPEN, cycle bounds UNPROVED
Templates: C-target instances exist; every x86-byte instance OPEN (no C lemma discharges it)
```

**Can start now** (no SCFG needed): ISA extensions A1-A6, source-side
`accessList` B1, decidable overlap checker B2, TSO-side spill/drain lemmas
B3-B4, table layout C1, gate-stub caller checks C2, entry predicates C4,
validator syntactic skeleton C5, atomic-duty audit C6, cost-summary schema C3.
**Cannot start** (wait for the accepted 287 IR interface; do NOT invent a
second IR): SCFG syntax/semantics, rule register, `check_C`/`lowerOk`/
`layoutOk` soundness, inlining/LICM/CSE motion lemmas, SCFG-side spill/SIMD
applications, the `valX86_sound` proof itself. SCFG-consuming rows below
define only their non-SCFG half and mark the consumer side WAITING.

## 2. Proposed wave: 16 authors + 16 paired reviewers

Each author owns ONLY the named new module plus `MUSE-REPORT-<N>.md`.
No existing central file, no friend path, no second IR. Every target theorem
quantifies over arbitrary values/programs; every source-syntax theorem gets a
joint non-degenerate `_zeuge` (a table some function writes; a reached run
with a memory-changing step). Every row carries a planted refusal/negative
case. HARD RULES 1-14 bind every lane; reviewers check the exact committed
candidate hash and record ACCEPT or concrete REPAIR (a changed commit needs a
fresh review). Umbrella `Grammatik.lean` additions are additive-only at
integration; authors never edit the same central file concurrently.

### A. Selected ISA (practical safe profile; costly extensions deferred)

**A1 — author 335: `grammatik/Grammatik/X86/NarrowOps.lean`.**
Dep: `Typen` (`Breite`, `Speicher`), `Wort` (masks/extension), `Speicher`
(`lesbar8`), `Codec` (REX/modrm patterns).
Target direction: 8/16/32-bit load/store/move definitions with
zero/sign-extension and a proved mask discipline; narrow flag snapshots stay
absent (booked, not silently inherited from 64-bit flags).
Witness: aligned mixed-width spill/fill round-trip changing memory.
Refusal: unaligned or cross-footprint narrow access refused by the Bool.
Policy: widths explicit at every op; unknown signedness keeps the loud
`narrow` guard. Profile: ESSENTIAL (most real flags/atomics are narrow;
review finding: 64-bit covering access IS cross-carrier overlap).
Closes: narrow-carrier gap (review §3.1). Reviewer: 373.

**A2 — author 336: `grammatik/Grammatik/X86/MulDiv.lean`.**
Dep: `Wort` (modular ops), `Ausfuehrung` (`schritt` shape), `FlagBeweis`.
Target direction: 64-bit MUL/IMUL/DIV/IDIV with defined-when checks;
division by zero and overflow trap to the `hardware` stop class the source
`FortschrittG` already names (no new stop kind).
Witness: non-trivial quotient/remainder with a memory store.
Refusal: divisor-zero image refused by the decided guard, never folded away.
Policy: trapping ops are never "pure" for DCE/motion. Profile: ESSENTIAL
(emitter `Binaer` mul/div). Closes: integer-family gap. Reviewer: 374.

**A3 — author 337: `grammatik/Grammatik/X86/ShiftLogic.lean`.**
Dep: `Wort`, `FlagBeweis` (carry/overflow characterisation).
Target direction: SHL/SHR/SAR/AND/OR/NOT/NEG with count-masking
(count mod 64) and per-op flag facts; signed-division-vs-shift mismatch
named as a refusal, not a peephole.
Witness: shift with masked count plus flag read changing memory.
Refusal: oversized-count behaviour pinned; `x-x -> 0` on floats refused.
Policy: no strength reduction without range evidence (consumer: existing
`StaerkeReduktion`). Profile: ESSENTIAL. Closes: shift/logic gap. Reviewer: 375.

**A4 — author 338: `grammatik/Grammatik/X86/ControlFlow.lean`.**
Dep: `Codec`, `Byteschritt` (`fetchDekodiert`), `Bild` (`kanonischBereich`).
Target direction: SETcc/CMOVcc/LEA definitions; direct-target theorem
`target = virtual_next_RIP + sign_extend(disp)` with the target proved a
decoded instruction start or a listed entry; faulting `CMOV`-memory form
keeps its fault on the untaken path (no speculation).
Witness: conditional move selecting different stored words per flag.
Refusal: branch into mid-instruction/data/off-image refused.
Policy: length from decoding only, never an emitter annotation.
Profile: ESSENTIAL (branches, address modes). Closes: IMAGE-ABI §6 direct
half; jump-table certificates stay with image work. Reviewer: 376.

**A5 — author 339: `grammatik/Grammatik/X86/LockedOps.lean`.**
Dep: `TSO` (`TSOZustand`, `TSOSchritt`), `Ausfuehrung`, `Zugriffe`.
Target direction: LOCK-prefixed single-op RMW (XADD shape) and MFENCE as
machine definitions with per-event access records and full-barrier order
facts; single-`LOCK`-op = constant-cost shape; CAS-loop = unbounded shape
with NO constant bound claimed. No W/GX refinement claimed (bridge owns it).
Witness: locked add with two-core interleaving recorded, memory changed.
Refusal: split load-then-store without LOCK never satisfies the `rmw` shape.
Policy: failure-as-stutter is safety-only; cost needs shape-(i) bound.
Profile: ESSENTIAL (every `exchange` lowering needs it). Reviewer: 377.

**A6 — author 340: `grammatik/Grammatik/X86/ScalarFloat.lean`.**
Dep: `Gleitprofil` (`mxcsrGueltig`, `muster64`/`bites64`), `Ausfuehrung`.
Target direction: scalar SSE2 DOUBLE forms only
(ADDSD/SUBSD/MULSD/DIVSD/UCOMISD/CVTSI2SD/CVTTSD2SI+wrapper/MOVSD) under a
checked `mxcsrGueltig` premise; NaN relation class-level with the
non-observability lemma OPEN; SNaN/flag reservation joint.
Witness: double op with signed-zero/divide special case stored to memory.
Refusal: every `float` (f32) node refused at the bridge (no double-rounding
paragraph); x87/FMA/packed encodings refused syntactically.
Policy: one source op = one machine op; no reassociation, no FMA-as-peephole.
Profile: ESSENTIAL kesk (f64); packed/AVX/FMA DEFERRED optional profiles.
Closes: FLOAT-ZEIT §4 f64 halves. Reviewer: 378.

### B. Memory and concurrency (per-access, no block atomicity)

**B1 — author 341: `grammatik/Grammatik/X86/AccessList.lean`.**
Dep: `RennfreiVoll` (`zugriffe`/`ereignisse`), `RMW`
(`exchange_liest_schreibt` pattern), all ~70 `RufSchrittG` rules.
Target direction: SINGLE-owner `accessList(rule)` function
(reads+values, writes+values, RMW flag) with per-rule completeness against
`LiestG`/`SchreibG`; both bridge and IR cite it (fixes the ownerless
overlap, review §5.2).
Witness: multi-access leaf (exchange reading two carriers) with a
memory-changing run.
Refusal: a rule with an uncovered access shape is an explicit constructor,
never a silent drop. Policy: incompleteness = unsoundness, recorded OPEN.
Closes: O-access/D-access. Reviewer: 379.

**B2 — author 342: `grammatik/Grammatik/X86/OverlapRefusal.lean`.**
Dep: `Zugriffe` (`Zugriff`), `Regionen` (`Region`/`Vorrat`),
`Bild` (`Abschnitt`), `Speicher` (little-endian coefficients).
Target direction: decided alignment/containment/non-overlap checker over
footprints plus the aligned-single-carrier bytes-value agreement lemma;
tearing correspondence stays OPEN.
Witness: adjacent-carrier layout with a proved disjoint accepted access and
a refused spanning access on the same image.
Refusal: unaligned/cross-carrier shared access refused (counterexample-C
shape as negative probe). Policy: conservative `unknown-overlap => refuse`.
Closes: O-align decidable half. Reviewer: 380.

**B3 — author 343: `grammatik/Grammatik/X86/SpillPrivate.lean`.**
Dep: `TSO` (per-access relation), `Stapel` (`Rahmen`/`Belegung`),
`SpeicherKommutation`.
Target direction: TSO-side freshness => disjointness => commutation lemma
for private spill slots (`GetrenntK` shape); the SCFG-side application
WAITS for the accepted 287 interface (marked, not invented).
Witness: spill fill/reload commuting with a concurrent disjoint access,
memory changed on both sides.
Refusal: address-taken or named-by-extent slot never fresh.
Policy: spills are ordinary validated accesses, never invisible.
Closes: O-spill producer half. Reviewer: 381.

**B4 — author 344: `grammatik/Grammatik/X86/FenceDrain.lean`.**
Dep: `TSO` (`zaunBereit`, `flushKern`, `fifo_reihenfolge`).
Target direction: local-drain definitions and per-core FIFO facts with the
explicit NON-theorem: a local fence does not drain other cores' buffers
(OBS-5 boundary stated as a proved limitation, not a gap hidden in prose).
Witness: two-core store-buffer trace where a local fence changes only the
acting core's observability.
Refusal: any claim that local MFENCE discharges a foreign/device read.
Policy: spawn/join/handler visibility needs the publication lemma (OPEN).
Closes: O-irq/O-spawn local half only. Reviewer: 382.

### C. Source, image and cost (validator-facing, SCFG-gated where marked)

**C1 — author 345: `grammatik/Grammatik/X86/TableLayout.lean`.**
Dep: `declOf`/`fieldRangeO`/`typAt` (Parser front end), `Bild`
(`Abschnitt`), `Regionen`.
Target direction: computed table/global layout (extents, widths,
alignments) and carrier enumeration with content from the source; any Rust
layout hint re-decided, never a premise.
Witness: non-empty unit (table with a written slot) with a memory-changing run.
Refusal: overlapping extents or unaligned `aligned N` placement refused.
Policy: layout facts are Lean theorems or refusals (no C `sizeof` facts).
Closes: QUELLBRUECKE §3.1 tables. Reviewer: 383.

**C2 — author 346: `grammatik/Grammatik/X86/GateStub.lean`.**
Dep: `Bild`, `Codec`, gate declaration shape (N063-N066).
Target direction: decided gate-declaration checks (distinct in-registers,
out-register unclobbered, arity, clobbers incl. rcx/r11, total `errors`
map) plus caller-stub byte-shape obligations; C186/C187 malformed shapes
as refusal predicates. Callee-side contract (obligation (c)) stays OPEN.
Witness: gate stub with distinct registers and decoded errno channel.
Refusal: region answer without `or R`; stack gate without trampoline
registers; forged int->ptr at any site (M140). Policy: declaration alone
admits nothing. Closes: IMAGE-ABI §7 caller half. Reviewer: 384.

**C3 — author 347: `grammatik/Grammatik/X86/CostSummary.lean`.**
Dep: `Budget.lean` (`Op.cost`, `totalCost`), `KostenG` (`kostenTiefF`).
Target direction: cost-summary SCHEMA (`kostenSummeOk` Bool,
`expandBound`, `targetWork` skeleton, per-site attempt bounds, waiting
exclusions needing exact source correspondence); `budget_simulation`
stated OPEN, never derived by re-summing.
Witness: counted expansion of one source step class with honest spill/fence
counts on a memory-changing run.
Refusal: unbounded-retry site behind a constant bound refused; exclusion
without source correspondence refused. Policy: source steps, machine work
and cycles never conflated. Profile: ESSENTIAL schema; cycle bounds
DEFERRED. Closes: FLOAT-ZEIT §8.1 framework. Reviewer: 385.

**C4 — author 348: `grammatik/Grammatik/X86/EntryState.lean`.**
Dep: `Bild` (`Bild`/`Modus`/entries), `Stapel` (`ausgerichtet16`).
Target direction: checked entry predicates (hosted main, nolibc
`anfang`/`ende` handoff, module init/exit, bare-metal `_start`, thread
roots, clone-child trampoline state) with stack/alignment/permission/IF
discipline; trap return and kernel behaviour named only.
Witness: entry predicate established on a concrete loaded image prefix.
Refusal: entry with unsaved MXCSR/XMM it touches; guard page missing where
promised; non-entry external transfer. Policy: manifest row without
validated save/restore bytes admits nothing. Closes: IMAGE-ABI §5
predicates. Reviewer: 386.

**C5 — author 349: `grammatik/Grammatik/X86/ValidatorSkeleton.lean`.**
Dep: `Bild` (`groesseOk`/`dateiOk`/`virtuellOk`), `Codec`,
`Byteschritt` (`byteschritt`), C1/C2 outputs.
Target direction: decided `valX86` SKELETON (section mapping, decode
coverage, permissions, relocation site-class checks) with proved syntactic
refusals (altered byte, invalid site, permission violation);
`valX86_sound` stated as OPEN obligation in CUTS, never as an assumed
premise of a delivered closing theorem.
Witness: accepted minimal image prefix plus its one-byte-mutation refusal.
Refusal: the §15 rejection shapes (altered byte, bad site, wrong ABI,
unchecked foreign body, forged pointer, BSS mismatch, unlisted mapping).
Policy: untrusted backend output re-read as bytes and re-validated.
Closes: validator framework; the soundness proof WAITS on IR+TSO+decoder
coupling. Reviewer: 387.

**C6 — author 350: `grammatik/Grammatik/X86/AtomicPayload.lean`.**
Dep: `Spec` (`AkzeptiertSpecX`/`FussSX`/`GeteiltV`/`GeteiltA`),
`AtomarSem` (`HavocA`), bridge `nutzerA_aus_quelle`.
Target direction: decided footprint-membership checks for admitted shared
atomics and the duty-side audit of the atomic fragment; plain-payload
hand-off stays OPEN (no TSO atomicity claimed here).
Witness: unit with one admitted shared atomic and a memory-changing run
through its guard discipline.
Refusal: contract-mentioning atomic in `GeteiltV`; unguarded payload
hand-off without the residue proof. Policy: rely quantifies over every
havoc value; observations preserved as a SET, never narrowed.
Closes: QUELLBRUECKE §3.3 checker half. Reviewer: 388.

## 3. Slot arithmetic (fits 40 today, fits 20 afterwards)

| Role | Lanes | Count |
|---|---|---|
| New authors (A1-A6, B1-B4, C1-C6) | 335-350 | 16 |
| Paired exact-candidate reviewers | 373-388 | 16 |
| Fixed: org 329 + org review 332 | 329, 332 | 2 |
| Fixed: merge owner 330 + merge review 333 | 330, 333 | 2 |
| Fixed: optimiser spec 331 + its review 334 | 331, 334 | 2 |
| **Total with all running** | | **38 <= 40** |
| Spare for repair/re-run sessions | | 2 |

Draining work (287 IR owner + 303 its reviewer + 328 design reviewer) frees
its slots as it completes; the coordinator starts new authors only against
actually free slots and never exceeds 40 concurrent processes. On later days
(cap 20) the same queue runs in halves: ISA batch first (A1-A6 + reviews =
12), then memory/source batch (10 + reviews = 20 across two halves), since
no row depends on another new row except B3/C5 consuming B1/C1 outputs
(seed order inside the batch: B1 before B3's consumer half, C1 before C5's
layout half; the WAITING halves simply stay marked).

## 4. Lane policy (no force, no push, no remote branches)

1. One isolated local clone per lane, branch `muse/<N>`, no remote; private
   `$TMPDIR` scratch; warm `.lake` copied from a built tree.
2. Author commits owned files only via `arbeitsprotokoll/.commitmsg` +
   `./commit.sh`, ending with its `Co-Authored-By` line; never red builds
   (`./lean-bau` green for the whole tree, standard goal axioms kept).
3. Reviewer receives the author's exact commit hash + task + check output in
   its own clone; records ACCEPT or concrete REPAIR; a changed commit
   invalidates the review and needs a fresh exact-commit verdict.
4. Merge rehearsal: merge owner integrates only ACCEPTED exact candidates in
   its isolated clone (`--no-commit` inspection, no semantic auto-repairs),
   moves the report to `messung/muse/`, rebuilds, then commits.
5. Merge peer re-checks the merged result (parents, blob identity, no
   unrelated changes, `diff --check`, English filenames, valid links).
6. Root publishes serially only after: full changed-source Lean build, Rust
   suite, emission check, `gabbro_ziel` axiom probe, outgoing secret-pattern
   grep, and origin-ancestry check (`git pull` merge if origin moved, then
   re-run). Never force-push; lane branches never leave the machine;
   worktrees/clones deleted only after checked integration.

## 5. What is NOT in this wave (deferred, not denied)

- Optional costly profiles AFTER essentials with measured benefit AND
  affordable complete Lean rules: BMI/popcount, shuffles, AVX2 packed
  integer tier (goal retained, gates: lane separation + alignment/tearing +
  flag treatment proved), AVX-512/AMX/APX, crypto accelerators, FMA-as-form
  (never as peephole), gather/scatter/compress, NT stores, string
  specialisations. "Last 10%" is qualitative priority, never reduced proof
  coverage or a measured performance promise.
- Second-link-unit optimisation (needs `GabbroZielVerbund` premises),
  MMIO/DMA/device semantics (own profiles, never RAM inheritance),
  unbounded-region opt-in mechanics, kernel-side gate behaviour (supplied
  proved binding contracts per IMAGE-ABI §11(c) or refusal).
- Any Rust backend work beyond the stopped 280 draft: waits for the
  reviewed Lean interfaces row by row.

## 6. Checkable acceptance

- Every author report names exact definitions/theorems, the last
  `./lean-bau` line, `_zeuge` names with their non-degenerate shapes,
  refusal probes, CUTS, and `#print axioms` for each main theorem.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no `Prop`-typed
  premise; every premise used; contracts at their place with actual values;
  no semantics that cannot change memory; generic theorems only, no
  per-program rules.
- Reviewer reports name the exact candidate hash and VERDICT; integration
  needs ACCEPT + green gates + unchanged standard axioms.
- This document claims no implementation, no measurement, no closed chain.

---
*CUTS: plan only. No Lean module, no validator, no refinement, no cost
transfer and no image acceptance is proved here. IR-dependent halves wait for
the accepted 287 interface. File links verified against the tree at write
time; line numbers cited are as-read and may drift.*
