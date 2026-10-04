# Source-to-final-byte closure plan after the overnight source wave (lane 644)

*Owner: lane 644. Scope: this document plus `MUSE-REPORT-644.md` only.
Status: work plan, not a proof and not progress. Full source-to-final-bytes
validation remains OPEN. No Lean, checker, goal, emitter, ledger or control
file is changed by this lane. Reviewer: lane 645.*

*Base: master `24e625c0` in clone `/home/simon/Dokumente/gabbro-muse/a644`
(branch `muse/644`, verified). All definition names below were resolved by
reading the cited files in this clone; line references are to this base.*

*Central record: [DIRECT-COMPILER.md](../../DIRECT-COMPILER.md). Binding closure
plan since 2026-10-04: [COMPILER-SCHLUSSPLAN.md](COMPILER-SCHLUSSPLAN.md). Design:
[DIRECT-COMPILER-DESIGN.md](../../DIRECT-COMPILER-DESIGN.md). Optimiser spec:
[OPTIMIZER.md](../../grammatik/OPTIMIZER.md). Closing schema:
[QUELLBRUECKE.md](QUELLBRUECKE.md) §4. Concurrency bridge:
[TSO-GX-BRUECKE.md](TSO-GX-BRUECKE.md). Portability:
[TARGET-PORTABILITY.md](TARGET-PORTABILITY.md). Lowering decision:
[DIRECT-LOWERING-DECISION.md](DIRECT-LOWERING-DECISION.md). Prior plans:
[CONNECTION-PLAN.md](CONNECTION-PLAN.md) (lane 558),
[CONCURRENCY-CLOSURE-PLAN.md](CONCURRENCY-CLOSURE-PLAN.md) (lane 605),
[NEXT-PROOF-WAVE.md](NEXT-PROOF-WAVE.md) (lane 401).*

## 0. What this plan is and is not

This plan organises the NEXT wave only: the generic source-to-final-byte
closure after the overnight direct-source lanes (624/626/628/630/632/634)
and the currently assigned owners 646/648/650/652/654/656/658 plus
ExtendedExecution575. It assigns exact NEW file ownership, producer
dependencies, target statement sketches, witness obligations and semantic
rejection criteria for at most eight follow-up tasks (§7). It proves
nothing, closes nothing, and changes no verdict: every ACCEPT/REPAIR stays
with the paired independent reviewer on the exact committed candidate.

Out of scope for this plan: re-owning anything 646/648/650/652/654/656/658
or 575 already own; a second IR or source interpreter; Rust backend work
(lane 280 stays stopped: Lean first); per-program rules; any numeric
performance promise.

## 1. The fixed witness and what must replace it on the trust path

`SourceValidatorConnection.lean` (lane 632) is exactly what its CUTS say:
one genuinely checked finite certificate over ONE fragment — `witD` (one
table, one `.int 0 100` field), `srcStmt` (write 42 into row 0),
`bildStore` (fetched bytes decode to `store64 rbx rax 0`), profile scope
pinned to `.p48`. Its `srcCert_sound` derives the joint representation,
read-back, footprint and validator legs for that witness from the recomputed
Bool `srcCertOk`, with four planted refusals (mutated bytes/profile/map/
base). This is a valuable honesty pattern (checked Bool, recomputed sides,
no proof-valued field, no assumed simulation), but it is a WITNESS, off the
generic trust path: it quantifies over no source text, no declaration, no
unit, no duty.

What must replace it on the trust path is the generic closing schema of
[QUELLBRUECKE §4](QUELLBRUECKE.md) (schema only, unproved), in three parts
that no single lane may collapse into one another:

1. **Full-unit computation from source** (`einheitAllg` shape): the validated
   unit `E` is computed in Lean from the source text (`uebersetzeAllg`,
   T3 parse fidelity; `Pflichten`), never trusted from a Rust print.
   632 fixes `witD`; the replacement quantifies over every `E`.
2. **Generic validator soundness** (`valX86_sound` shape): `valX86 E bild =
   true → X86Verfeinerung E bild`, proved once, generically, per access.
   632's `srcCertOk` checks one layout extent; the replacement checks the
   full unit (code, starts, invariants, `Q`, memory, layouts, relocations).
3. **Delivered closing theorem** (`schluss_x86` shape): refinement DERIVED
   via `valX86_sound`, never an independent refinement premise
   (`schluss_x86_aus_verfeinerung` stays internal plumbing, labelled).

Lane 648 (generic finite-data certificate for the admitted `assignSlot`
fragment) is the correct NEXT stepping stone toward part 2, not part 2
itself: its scope is the admitted fragment (`regelOk`/`fragmentProfilOk`/
`fragmentZielOk`), and its report must keep the fragment boundary explicit.
Task T3 (§7) owns the adapter specification that turns fragment certificates
(648, 646, T1, T2) into the full-unit `valX86 E bild` shape — specified, not
claimed.

## 2. Accepted producers this wave consumes (verified names)

Only the checked definitions below are stable producer interfaces.
Consumers reuse them; redefinition is a rejection (§8).

- **599 `ExpressionLowering.lean`**: `senkFrag` (lit/var/one bounded
  ADD/SUB over atoms, else `none`), `EnvRepr`, `Frisch`, `senkung_korrekt`
  (lowered list through `lauf` puts `intWort` of the exact source value
  into `dst`; memory untouched; foreign registers and `rsp` kept),
  `senkung_ohne_ueberlauf_add/sub`, planted refusals
  (`senkFrag_verweigert_mul/tief`). Fragment ends at depth-one
  arithmetic; everything else refuses by construction.
- **628 `SourceAssignmentLowering.lean`**: `senkAssign` (`senkFrag` output
  plus one `store64`), `intWort_zahlWort`, and the MAIN statement
  `senkAssign_korrekt` with premises `hExec` (real `execStmt` step),
  `hTgt` (matching target `write64`), `hRd` (target readability),
  `hOk` (representation admission), `hsenk`/`hrenv`/`hFr`/`hrsp`/
  `hBasis`/`hBaseR`/`hdisp`/`ha`, concluding generated-`lauf` run,
  register value, `RepSlot` and read-back. Joint witness
  `senkAssign_korrekt_zeuge` (source slot `12 → 42`, mapped target bytes
  change, forged-opcode fetched refusal). CUTS: arbitrary-sequence
  `laufBytes` induction OPEN; pilot integer fragment only.
- **634 `SourceCodeFrame.lean`**: `CodeFremdN` (width-generic foreignness)
  with the Nat-interval bridge `codeFremdN_von_intervallen` (explicit
  no-wrap bounds on both sides), narrow-store fetch/decode preservation
  (`geholt_nach_write8/16/32_fremd`, decode twins), MAIN
  `quellDaten_schritt_laesst_code` (one represented source data store
  preserves fetch, decode and every fetched code byte under the checked
  mapping, permission shapes and bounds, with `RepSlot` + read-back),
  named refusals SM-WX/SM-SPAN/SM-SCHUTZ/SM-UMBRUCH/SM-UEBERLAPP.
- **630 `SourceAccessCompleteness.lean`**: `fragmentListe` (write of `t`
  plus one read per carrier of `i.orte ++ e.orte`, computed from actual
  source data), `fragmentDelta_voll` (actual `execStmt` delta IS the
  enumeration), `blattFragment_voll` (G completeness: access list,
  recorded write, read/write containment, slot ownership via the
  disjoint-slot frame), `fragmentStore_passt`/`fragmentLoad_passt`
  (realised footprint match), `regelOk` (only `assignSlot` admitted),
  `fragmentProfilOk`/`fragmentZielOk` (carrier/width/alignment admission),
  `fragmentOhneUmbruch` (derived no-wrap).
- **598 `ValidatorExecution.lean`**: `valEintrittStark` (strengthened entry
  admission: mapping + whole-section decode coverage + containment +
  executable byte + successful fetch-and-decode from loaded bytes),
  consequence legs `valStark_wohlgeformt/eintrag/ausfuehrbar/fetch_exist/
  fundstelle/gibt_deckung/schritt`, interior/truncated/BSS/permission
  counterexamples, positive witness `valStark_store_zeuge`.
- **596 `TSOTrace.lean`**: `SpurKnoten` (TSO state + grown history,
  views, clock), `SpurSchritt` (issue keeps history, flush appends one
  message), `SpurErreichbar`, clock invariant `SpurInv` with preservation
  `spurSchritt_inv`, append-only shape `spur_schritt_hist/erhaelt`,
  freshness `spur_flush_frisch_vor`, release views, forwarding-is-youngest,
  finite-trace extension `spur_verlauf_waechst`, joint two-core witness
  `spur_zeuge_gelenk` (two timestamps, foreign activity). The resetting
  `histVon` 0/1 snapshot is legacy; consumers take the append-only
  `traceHist/traceSicht/traceFrisch` (lane 605 §2 gate).
- **603 `WordAccessGrouping.lean`**: `wortEintraege` (eight canonical
  byte-store entries), `FremdFrei`, `WortGruppe`, `DrainSchritt`/
  `DrainSpur`, grouped read-back `wort_gruppe_liest_zurueck`, grouped
  frame `wort_gruppe_rahmen`, realised-store fidelity
  `realisiert_store_gruppe_treu`, tearing refusals
  (`ausrichtung_reicht_nicht`, `riss_unter_verweigerter_gruppe`), and the
  explicit void bridge `GruppeNachW`/`keine_gruppe_nach_w` (no
  source-bridge claim inside the module). Pure own-drain witness only;
  interleaved foreign activity is lane 652's task.
- **565 `ScalarFloatCodec.lean`**: `fpEncodeMovsdRR/AddsdRR/Lade/
  Speichere`, independent `fpDecode`/`fpDecodeRest` over actual bytes,
  round-trips, refusals (wrong prefix, 66-prefix, REX, truncation,
  mod=1, register-store, memory-ADDSD), `fpGeholt`/`fpFetchDekodiert`/
  `fpByteschritt` over the extended `FpZustand`, fetched-step
  consequences (`fpByteschritt_schritt/addsdRR_rechnet/klasse/hoch/
  movsdRR_flags`), MXCSR-gated refusals. Scalar SSE2 only; UCOMISD,
  memory ADDSD and packed forms refuse.

Supporting stable APIs (reuse, do not fork): 570 `SourceMemory`
(`repOk`, `zahlWort`/`wortZahl` + round-trip, `slotAddr`, `RepSlot`,
`rep_schritt_bleibt`); `Codec.decode/encode` + `roundtrip`;
`Byteschritt` (`fetchDekodiert`, `geholt`, `byteschritt`,
`kanonisch_schritt_ueberein`, `kette*` layouts); `Bild`/`Relokation`/
`geladen`; 560 `LoadedExecution` (`bildZustand`, `bildStore*`);
568 `AccessExecution` (`realisiert_store64_fuss/gefunden`,
`realisiert_load64_gefunden`); 569 fetched stack execution; 571
entry admission; 572 budget/work connection; `TSO` (`issueByte`,
`loadByte`, `flushKern`, `zaunBereit`); 573/574 `BridgeWrite`/
`BridgeRead` (`bruecke_schritt_rep`, `wLesbar_aus_gruppe/weiterleitung`,
`BrueckenProfil`, `WortGuard` handoff vocabulary); 624/626 float
source/entry observations; 349 `ValidatorSkeleton` (`valX86` mapping/
decode check — checks mapping and coverage, not refinement).

## 3. Missing derived facts (the OPEN register for §7)

Nothing below is claimed; each is a proof obligation with its consumer:

- **M1. Generic validator admission.** No `valX86 E bild` over a full
  computed unit exists (349 checks image mapping + decode coverage only;
  598 strengthens the entry leg only; 632/648 are fragment certificates).
  Needed by the closing schema part 2 (§1). Owner: T3 (specification +
  fragment-leg decomposition, not the soundness proof itself).
- **M2. Arbitrary-sequence fetched-byte induction.** 628 proves the
  statement correspondence through abstract `lauf` over `Decodiert`;
  agreement between that run and `laufBytes` from actual memory for an
  ARBITRARY generated sequence is OPEN (concrete sequences agree by
  `decide`). Needed by every lowering consumer. Owner: T1/T2 carry the
  per-shape fetched legs; the generic induction is a named CUT until a
  dedicated lane derives it from `kanonisch_schritt_ueberein` +
  634-style frames.
- **M3. Control-flow lowering.** No branch/loop lowering exists (656
  proves flag-dependency stability for the byte step, not a source `wenn`
  correspondence). Needed for any whole-`Block` claim beyond straight
  lines (646 covers ≥2 assignments). Owner: T1.
- **M4. Call lowering with ghosts and stack.** `AufrufOpt` gives the ghost
  obligation shape (`geistPaar`, actual `rho`/`v`/`s0`/`s1`); no fetched
  call/return correspondence exists. Needed for inter-procedural closure
  and inlining certificates. Owner: T2.
- **M5. Typed-carrier W transition.** 573 derives store-side preservation,
  574 load-side readability, both short of a `SchrittW` transition; 596
  gives the append-only trace to build on. In flight: 650. The full
  `SchrittW`/GX per-access simulation stays OPEN after it. Owner: T4
  (ordinary accesses only; LOCK/RMW stays refused).
- **M6. Interleaved foreign drain.** 603 groups pure own-drains; foreign
  issues/flushes between own flushes are unproved. In flight: 652.
- **M7. Derived work accounting.** 572 connects budget-stop to target work
  for the covered fragment; `Deckung` has no producer for generated
  lowering code yet, and optimiser passes do not recompute work. In
  flight: 654. Validation-cost accounting (fuel, cache rules) is
  additional. Owner: T6.
- **M8. FP source correspondence.** 565 executes fetched scalar bytes;
  no source `GleitOp` → byte correspondence exists, and the `f32` bridge
  is undecided (model computes binary64; genuine `f32` single-rounding
  differs). 658 (waiting on accepted dependencies) adds validator
  admission + MXCSR entry, not the source leg. Owner: T8 (narrow
  memory-form leg first); the `f32` path decision stays a CUT.
- **M9. Decoder coverage vs silicon fidelity.** `DecodingCoverage` (435)
  proves entry-byte coverage from the actual decoder; per-form execution
  correspondence against silicon is OPEN by design (see §4). No lane may
  present coverage as hardware correspondence. No new task needed; T1–T8
  must cite the distinction in their CUTS.
- **M10. Profile/entry/binding closure.** Entries, runtime bodies,
  binding code and every reachable support byte must be covered or
  refused per [TARGET-PORTABILITY](TARGET-PORTABILITY.md); 571 admits
  entry + first instruction, 346 stubs gates, 560 loads images. The
  whole-image reachability argument is OPEN. Owner: T7.

## 4. Instruction semantics and decoders are not silicon fidelity

The accepted target definitions are checked contracts the validator
decides — `Ausfuehrung.schritt` (per-form step equations over the
canonical `Befehl` vocabulary), `Codec.decode/encode` (byte↔instruction
 over the canonical subset), `Speicher` (permission-checked byte
function), `TSO` (per-core FIFO buffers over canonical memory),
`Gleitprofil` (MXCSR RNE, FTZ/DAZ off, masks set, per-context state).
They prove facts about the MODEL, and every byte outside the canonical
subset is refused, including architecturally valid non-canonical forms.

What they are NOT, and what no lane may claim: correspondence with
physical silicon behaviour (retired-instruction effects, fault delivery,
TLB/cache/store-buffer interaction, interrupt timing, MXCSR sticky-flag
wiring, per-form cycle counts). Per
[DIRECT-COMPILER-DESIGN §2](../../DIRECT-COMPILER-DESIGN.md), that
correspondence is OPEN for every form including the 14-form pilot, and
silicon behaviour beyond the named hardware assumptions is never proved.
The accepted shape for hardware is narrow: named assumptions
(`HardwareAnnahmen`, `HardwareProfil`, per-form step costs) feed the
time/work transfer; everything else about the chip stays a CUT. Reviewers
reject any "decoder round-trip, therefore hardware-correct" or "coverage,
therefore fidelity" step by name.

## 5. O3/invariant optimisation proof integration and validation cost

Optimisation integrates through [OPTIMIZER.md](../../grammatik/OPTIMIZER.md) §§2–7
as aligned by lane 638: source-anchored block pairs plus validator-
recomputed claims through the L1–L4 lowering contracts — no persistent
SSA language, no trusted `irWF`, no second interpreter. Each rule binds
ONLY facts actually available at its site (source invariant at its
guaranteed place with actual values, site effect/duty binding, the W/GX
ordering that actually holds there). The first certificate pilot (T5)
proves the pattern on one local rule before any pass pipeline is
specified: certificate ADT with finite data only (no proof-valued
fields), executable `Bool` checker, ONE generic soundness lemma
(`pruefeOpt c = true →` refinement per §2.2 of OPTIMIZER.md), derived —
never assumed — correspondence, and a conservative route (keep the
check, keep the call, scalarise) for exhausted optional fuel. Required
validation failure refuses; optional failure falls back to the certified
cheaper route, never a warning.

Compilation INCLUDING validation cost is a first-class proof obligation,
not a build-system afterthought:

- **Validator work bounds.** Every `Bool` the validator decides needs a
  stated fuel/work bound in the same module (bounded `decide`, bounded
  layout-relaxation rounds, bounded dataflow worklists per OPTIMIZER.md
  §8). Unbounded fixpoints, hash-iteration orders and fuel-free
  relaxation are refusals. T6 derives the accounting interface from 654's
  work bound and `CostSummary`/`ValidationBudget`.
- **Generic cache rule.** Cached certificates are UNTRUSTED: a cache hit
  re-runs the validator `Bool` before acceptance (lane 401 verdict on
  430: input-equality congruence only, no verdict caching). Cache key
  covers source-contract hash + effect summaries + callee summaries +
  hardware/ABI profile + proof-schema version + optimiser version; any
  validator change bumps the schema. No cache hit skips final
  fetched-bytes revalidation. Hashing alone is no theorem.
- **OS/freestanding profiles.** Per
  [TARGET-PORTABILITY](TARGET-PORTABILITY.md): one source model, IR and
  validation chain serve every profile; ABI/image/entry/loaded-mapping
  are explicit checked profile inputs; environment services are Gabbro
  bindings with user-logic contracts and implementation proof
  obligations, never hardware assumptions. T7 closes the per-profile
  reachability argument (every executed byte covered, including
  handwritten entry paths, each with its booked reason).
- **Named assumptions only.** OS, runtime, loader and binding bodies stay
  user logic with checked contracts; only named silicon/device/timing
  behaviour is a hardware assumption (goal-statement header). No lane
  invents a hardware premise to discharge a software obligation, and no
  timing bound proves a source body, a simulation, fairness or a bounded
  CAS retry (DESIGN §5: CAS loops carry divergence or a contention
  bound, never a constant).

## 6. In-flight lanes and ExtendedExecution575 (do not duplicate)

- **646** (Block of ≥2 assignments → fetched machine execution;
  composition API for a future validator). T1/T2 consume its composition
  API; they do not re-prove two-assignment composition.
- **648** (generic finite-data certificate for the admitted
  `assignSlot` fragment). T3 consumes its certificate shape; T5 consumes
  its admission predicates as the unoptimised baseline.
- **650** (growing TSO history → typed-carrier W transition). T4 is gated
  on accepted 650 + accepted 652; it does not rebuild the history
  relation or the grouping.
- **652** (whole-word drain with interleaved foreign accesses). See T4.
- **654** (derived work bound for direct lowering; `Deckung` producer).
  T6 is gated on accepted 654; it does not re-derive the lowering work
  formula.
- **656** (fetched conditional byte-step flag-dependency simulation). T1
  is gated on accepted 656; it does not re-prove flag read-set stability.
- **658** (scalar FP final-byte validator admission + MXCSR entry;
  waiting for accepted dependencies). T8 stays on the integer/narrow
  side and does not touch FP admission.
- **575** (unified extended decoder + executable byte-step; candidate
  committed, review 593 pending). T1/T2/T8 build on `Byteschritt` +
  per-form codec APIs directly, so they stand whether or not 575 lands;
  where the unified step applies they cite it as an optional consumer,
never as a premise. No lane duplicates the 575-reserved path
`grammatik/Grammatik/X86/ExtendedExecution.lean` (path string, not a
link: the candidate is committed but pending review and not in this
tree).

Filenames in §7 were checked absent from `grammatik/Grammatik/X86/` at
this base; the coordinator re-checks against 646–658 committed paths at
launch (their lane files name no Lean file, so collision is by content,
not by number).

## 7. Eight follow-up tasks (each: owner file, dependencies, sketch, witness, rejection)

Reviewer for each: an independent lane with the exact committed candidate
hash, ACCEPT or concrete REPAIR; repairs invalidate the review.
Every task: joint non-degenerate `_zeuge` (inhabited source table with a
real reached memory-changing run + planted negative mutations), all
premises used, standard goal axioms, explicit CUTS, no `sorry`/`admit`/
new axiom/`native_decide`/`unsafe`, small increments through the queued
wrappers, `git diff --check` clean.

### T-A. Branch lowering to fetched conditional execution

- **NEW path**: `grammatik/Grammatik/X86/BranchLowering.lean`.
- **Producer dependencies** (accepted only): 646 block composition API,
  accepted 656 flag-dependency rule, 599 `senkFrag`/`senkung_korrekt` for
  the condition value, `ControlCodec`/`ControlFlow` byte rows,
  `Byteschritt.fetchDekodiert/byteschritt`, 634 code/data frame for the
  fall-through and target legs.
- **Target sketch**: `wennSenkt_korrekt`: for a source `wenn` statement
  whose condition expression is in the 599 fragment and whose both
  branches are 646-admitted blocks, the generated bytes (condition code
  + fetched `jcc` + both legs at checked displacements) execute from
  fetched memory to the post-state of exactly the taken branch; the
  untaken leg is covered by the mapping but not executed; flag values
  outside 656's consumed set are proved irrelevant to the outcome.
- **Witness**: one table written on the taken leg only (source slot
  change on one side of the branch), reached run taking that edge and
  changing memory, planted mutations: flipped consumed flag changes the
  edge, changed unconsumed flag leaves it stable, forged branch
  displacement refused, truncated `jcc` refused.
- **Rejection**: assuming both executions identical instead of deriving
  outcome agreement from the consumed-flag set; hoisting a faulting
  operation above the branch (fault-order change); covering only one
  leg in the mapping.

### T-B. Direct-call lowering with ghosts and stack discipline

- **NEW path**: `grammatik/Grammatik/X86/CallLowering.lean`.
- **Producer dependencies**: 646 composition, `AufrufOpt.geistPaar` +
  `FolgeLog` lemmas (ghost shape with ACTUAL `rho`/`v`/`s0`/`s1`), 569
  fetched stack execution, `Stapel` frame discipline, 309/313 ABI
  obligations, `Codec` call/ret rows, 634 frame for return-address bytes.
- **Target sketch**: `aufrufSenkt_korrekt`: a direct call to a known
  body lowers to fetched `call32`/body bytes/`ret` that execute to the
  callee post-state with the ghost entry/return pair spliced at the
  site in source order; callee-saved restores hold on all paths; the
  call cost is carried, not forgotten (budget leg cites 654's shape).
- **Witness**: caller + callee sharing one table the callee writes
  (non-degenerate on both sides), reached nested run changing memory in
  the callee, planted mutations: indirect target without legal-entry
  proof refused, clobbered callee-saved register refused, dropped
  return ghost refused (`FolgeG` order loss).
- **Rejection**: quantified-away ghost parameters (`forall rho`/`forall
  v`); devirtualisation without a proved singleton callee set; inlining
  that drops contracts, budget or the reason channel (OPTIMIZER.md I3).

### T-C. Full-unit validator adapter specification

- **NEW path**: `grammatik/Grammatik/X86/ValidatorAdapter.lean`.
- **Producer dependencies**: 648 certificate shape (when accepted), 646
  composition, T-A/T-B leg shapes (specified interfaces, not proofs),
  598 `valStark_*` legs, 349 `valX86`, QUELLBRUECKE §4 schema (cited as
  obligation, not premise), 630 admission predicates as the
  fragment-scope boundary.
- **Target sketch**: `adapterSpez`: the `valX86 E bild` Bool shape
  over the FULL computed unit (code, starts, invariants, `Q`, memory,
  layouts, relocations) with each conjunct bound to exactly one
  fragment-leg producer or an explicit OPEN marker; `adapterZerlegung`:
  acceptance decomposes into per-leg checks, each re-decided in Lean;
  NO soundness claim (`valX86_sound` stays OPEN with its per-leg proof
  debt itemised).
- **Witness**: the 632 witness re-expressed as ONE leg instance of the
  adapter (same `witD`/`srcStmt`/`bildStore`), plus a two-leg instance
  (two admitted slots) showing leg conjunction — both witness-only, so
  labelled; planted mutations: leg dropped from the conjunction
  refused, unit field (`starts`, `Q`) changed without revalidation
  refused.
- **Rejection**: any refinement premise in the adapter theorem (that is
  `schluss_x86_aus_verfeinerung`, not the adapter); a proof-valued
  certificate field; trusting a Rust print for any unit field; claiming
  `valX86_sound`.

### T-D. Ordinary-access per-access simulation into W

- **NEW path**: `grammatik/Grammatik/X86/AccessSimulation.lean`.
- **Producer dependencies**: accepted 650 (typed-carrier `SchrittW`
  leg), accepted 652 (interleaved foreign drain), 603 grouping/frame,
  573/574 bridge legs, 596 trace API, 630 access enumeration
  (`fragmentListe`, `blattFragment_voll`).
- **Target sketch**: `zugriffSimuliert`: one ordinary (non-LOCK,
  aligned, single-carrier, non-overlapping, LE-agreeing) target access
  sequence derived from a 650/652 trace refines to one W step under the
  inherited representation/history relation, with foreign disjoint
  writes preserved and own FIFO drained; the statement carries the
  O-align side conditions as DECIDED checks, never as assumed facts.
- **Witness**: two-core reached trace with foreign activity and two
  timestamps (extends 596's `spur_zeuge_gelenk` shape), grouped drain
  installing one word, planted mutations: overlapping foreign
  issue/flush refused, misaligned access refused, LOCK-prefixed access
  refused (no RMW claim), tearing example from 603 reproduced.
- **Rejection**: serialising one aligned word into eight observable
  byte writes; claiming LOCK/RMW/fence correspondence; fairness or
  termination premises; a whole-`SchrittW`/GX simulation premise.

### T-E. First optimiser certificate pilot (one local rule)

- **NEW path**: `grammatik/Grammatik/X86/FoldCertificate.lean`.
- **Producer dependencies**: 599 fragment semantics (unoptimised
  baseline), 628 `senkAssign` shape, 630 admission predicates,
  OPTIMIZER.md §7 certificate/checker/soundness pattern (cited, not
  assumed), accepted 654 work shape for the cost side (recompute, never
  inherit).
- **Target sketch**: `faltungZertifikat_sound`: for ONE local rewrite
  (copy folding C2 over `senkFrag` atoms, or literal folding C1 where
  the overflow channel is preserved), an untrusted finite-data
  certificate plus a recomputing `Bool` checker, with the generic
  soundness `pruefeOpt c = true →` same value/fault/observation on the
  599/628 executions; optimiser fuel exhaustion yields the certified
  unoptimised route.
- **Witness**: one admitted assignment optimised and one kept (both
  executed from fetched bytes with identical observations), planted
  mutations: stale avail fact (redefined value between) refused by
  recomputation, overflow-hiding fold refused, FP-width-changing fold
  refused.
- **Rejection**: proof-valued certificate fields; trusted Rust verdict;
  `ensures` derived from heuristics; refusal turned into a warning;
  any per-program rule.

### T-F. Validation-cost accounting and cache rule

- **NEW path**: `grammatik/Grammatik/X86/ValidationCost.lean`.
- **Producer dependencies**: accepted 654 (derived work bound),
  `CostSummary`, `ValidationBudget`, `HardwareAssumptions`, 598/349
  validator legs whose work is bounded, lane-401 430 verdict (congruence
  only).
- **Target sketch**: `validierungsKosten`: each validator `Bool` in the
  chain carries an explicit fuel/work bound proved sufficient for its
  decision on admitted inputs, with exhaustion → refusal (required) or
  certified cheaper route (optional); `cacheKongruenz`: cache hits
  re-run the `Bool`, keyed by source-contract + effect + callee-summary
  + hardware/ABI profile + schema + optimiser version, with schema bump
  on any validator change; no hit skips fetched-bytes revalidation.
- **Witness**: one bounded validator run measured against its bound on
  the 632 witness image, one stale-schema cache hit refused, one
  exhausted-fuel optional pass falling back to the certified route.
- **Rejection**: verdict caching (storing `true` instead of
  re-deciding); unbounded fixpoint or hash-order traversal; timing
  premises proving software facts; any maximum-performance claim.

### T-G. Per-profile entry/binding/support-byte closure

- **NEW path**: `grammatik/Grammatik/X86/ProfileClosure.lean`.
- **Producer dependencies**: 571 entry/user-duty connection, 346
  `GateStub`, 560 loaded execution, 348 `EntryState`, 540/541
  portability architecture, 634 frame (support bytes stable under data
  stores), `Bild` relocation checking.
- **Target sketch**: `profilAbdeckung`: for one EXPLICIT checked profile
  (ABI + image format + entry convention + mapping, all decided inputs),
  every reachable final byte — emitted unit, generated driver,
  compiled-in binding code, runtime, handwritten entry path — is either
  covered by a validated leg or the image refuses; OS/binding contracts
  appear as user-logic proof obligations, never as assumptions.
- **Witness**: one freestanding-profile image with a program-supplied
  entry (reached from the entry byte, memory changed through a binding
  gate), planted mutations: unmodelled reachable byte refused,
  unresolved relocation refused, missing binding contract refused,
  wrong-profile image (Linux bytes under the freestanding profile)
  refused.
- **Rejection**: implicit Linux/POSIX/libc/ELF dependence; unchecked
  entry stubs; loader promises as hardware assumptions; int→ptr or
  int→fn-ptr conversion anywhere in the chain.

### T-H. Narrow memory-form lowering leg

- **NEW path**: `grammatik/Grammatik/X86/NarrowLowering.lean`.
- **Producer dependencies**: 335 `NarrowOps` + 562 `NarrowCodec` byte
  rows, 570 `repOk` admission extended by decided width rows (no fork of
  the interface), 634 narrow-store preservation legs, 342
  `OverlapRefusal.zugriffOk` (alignment/contract/profile gate), 599
  fragment shape for values.
- **Target sketch**: `schmalSenkt_korrekt`: one admitted narrow slot
  access (8/16/32-bit form with its explicit width, alignment contract
  and extent proof at the site) lowers to fetched narrow bytes that
  execute to the represented value with zero/sign extension exactly per
  the source type; unaligned shapes are admitted ONLY where the
  selected contract/profile permits (else refused by decision, citing
  the exact gate).
- **Witness**: one narrow slot written and read back through fetched
  bytes (memory-changing run), one unaligned positive probe where the
  profile permits (634 §2 pattern), planted mutations: width-mismatched
  extension refused, out-of-extent narrow access refused, profile-gated
  unaligned access on the wrong profile refused.
- **Rejection**: silent width truncation; upper-half-zeroing treated as
  truncation instead of semantics; entry-range fact reused across a
  writing call; any claim beyond the admitted widths/forms.

## 8. Semantic rejection criteria (all tasks, all reviews)

A candidate is REPAIRED (never accepted, however green the build) if it:

1. Carries the desired correspondence as a premise, a proof-valued
   certificate field, or a renamed checked conclusion.
2. Quantifies a contract's parameters or result away, derives `ensures`,
   or turns a refusal into a warning.
3. Introduces a second IR, a miniature source interpreter, an
   alternative x86 executor, or a parallel checker over the same claim.
4. States a per-program rule (a name, an example, a function) where a
   generic theorem over every source text is owed.
5. Reuses W/GX lemmas for target steps without the per-access bridge,
   or presents byte-level projection/grouping as atomicity.
6. Weakens any guarantee (memory safety, race freedom, contracts,
   costs, lock discipline, FP/concurrency semantics) to make a wall go
   green, or advertises enabledness as fairness/completion.
7. Trusts a Rust print for source syntax, values, units or duties, or
   invents hardware/silicon premises for software obligations.
8. Ships a degenerate witness (no written table, no reached
   memory-changing run) or a missing planted refusal.

## 9. Launch order and capacity note

Dependency order: T-A and T-H first (consumers: accepted 646/656/562
rows, no in-flight gate); T-B after T-A (control + call compose); T-C
after accepted 648 (fragment shape fixed); T-D after accepted
650 + accepted 652; T-E after accepted 648 + accepted 654 (baseline +
work shape); T-F after accepted 654; T-G any time (profile work is
orthogonal, needs 571/346/560 only). T-D and T-F both gate on 654
acceptance — stagger them, do not run both against the same unreviewed
candidate. No task starts filler to look busy: if the queue empties,
organisation supplies the next disjoint closure item from §§3–5, capped
at the standing 15-model policy including reviewers and repairs.
