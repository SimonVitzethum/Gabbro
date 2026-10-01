# End-to-end trust audit: source text to final executable bytes (lane 415)

*Owner: lane 415. Owns only this file plus `MUSE-REPORT-415.md`.
Status: AUDIT, not an implementation and not a proof.
Snapshot: `0b3132b7` (`muse/415` clone), read 2026-10-01.
Nothing here closes the source-to-final-bytes chain, claims measured speed,
physical-hardware correspondence, or full final-byte validation.
Central record: `DIRECT-COMPILER.md`. Design: `DIRECT-COMPILER-DESIGN.md`.
Optimiser spec: `grammatik/OPTIMIZER.md`. Allocation: `dokumente/x86/WORK-ALLOCATION.md`.*

*Claim boundary: each helper below is judged against its own stated claim
(file header + `CUTS`), not against the whole compiler. An explicitly OPEN
bridge is recorded as OPEN, not as a bug. A false theorem or false model
semantics would be a defect; a legitimately incomplete deliverable is a
numbered closure gap in §7. No per-program rules, no desired-correctness
assumption, no safety weakening is used or proposed.*

*Build note (honest): a fresh `./lean-probe` of `Bild.lean` was attempted
from this clone and timed out after 120 s on the queued Lean slot (shared
with other lanes), so no fresh build number is claimed here. All positive /
negative evidence below is the committed `by decide` / `by simp` / `by rfl`
closed theorems as read in the tree, cross-checked by grep for
`sorry|admit|axiom|native_decide|unsafe` (zero real hits; all `admit*`
matches are English "admitted/admits" in comments). This commit is
docs-only and touches no Lean file, so no Lean rebuild is owed by it.*

## 0. The exact generic theorem that has to exist

The end condition (`DIRECT-COMPILER.md` §§27-33, design §1 chain) is one
generic closing theorem over EVERY admitted source text and EVERY final
image, with refinement DERIVED, never assumed:

```
schluss_x86 (E : Einheit-computed full unit) (bild : Bild) (bytes mapping …) :
  Lean-parse-fidelity (uebersetzeAllg text = P over declOf u) →   -- T3, OPEN as coupling
  checker Bool (Akzeptiert / PrueferX vs AkzeptiertSpecX) = true → -- premise (a), EXISTS
  NutzerPflichtA (every body vs every havoc atomic value) →        -- premise (b), EXISTS
  HardwareAnnahmen O E.Q (named silicon/device/timing only) →      -- premise (c), EXISTS
  Laufzeit E sp init (declared starts, idle root) →                -- premise (d), EXISTS
  valX86 E bild = true →                                           -- decided, PROPOSED, DOES NOT EXIST
  every reachable executed body of the LOADED image refines GX     -- via valX86_sound
    (values, faults+channels+order, observations, IEEE, control,
     contracts at actual sites/values, call logs + FolgeG, race/lock/
     visibility/sync, progress classes, budget refusal/channel/order)
  → ZielFX/ZielX over GX (hence gabbro_ziel legs, unchanged premises)
```

Non-negotiable shape properties (from `QUELLBRUECKE.md` §4,
`IR-VALIDIERUNG.md` §2.4, `REVIEW-OPT-BINAER.md` §§4.1-4.4):

1. `valX86` binds the FULL unit (`valX86 E bild`, never `valX86 P fragment`
   or duty-only binding). A per-function validated result with an unchecked
   link is a refusal.
2. Refinement is DERIVED via generic `valX86_sound`
   (`valX86 E bild = true → refinement holds`); no independent simulation
   premise `hR` appears in `schluss_x86`. An internal composition lemma
   taking `hR` is plumbing only.
3. Lowering is CHECKED: `lowerOk(E, G0) = true` admits the single shared
   SCFG; per-step `check_C` and `layoutOk(Gn, B, Img)` admit each
   optimisation and the final layout. Rust output (optimiser, allocator,
   encoder, layout, linker, certificates, tuning tables, cache hits) is
   evidence re-decided by these Bools, never a trusted verdict.
4. Default is refusal: unproved form, failed check, missing proof, or
   exhausted OPTIONAL fuel refuses (or takes a certified cheaper route,
   itself validated). MANDATORY validation failure refuses outright, never
   a warning. No `ensures` is derived; no refusal becomes a warning.
5. Source budget, target machine work, and hardware time are three separate
   quantities with separate transfer lemmas (all OPEN). Re-summing declared
   costs is bookkeeping, not `budget_simulation`.
6. Only named silicon/device/timing is a hardware assumption (`Spec.lean`
   header). OS, runtime, loader, binding bodies are user logic with checked
   contracts. File offsets, virtual addresses, load bias, relocation
   operands are checked against the final image AND the executed mapping,
   including every reachable support byte.

Today NONE of `SCFG`, `lowerOk`, `check_C`, `layoutOk`, `valX86`,
`valX86_sound`, `schluss_x86`, `DutyExport/EffectExport/AtomicExport/
FpExport/CostExport/LowerMap` exists as a Lean definition (confirmed by
grep over `grammatik/Grammatik/X86/` and the §8 ledger of
`REVIEW-QUELLE-INVARIANTEN.md`). The IR itself (lane 287) is still WORKING,
not accepted. That is the single largest closure fact; everything below is
measured against it.

## 1. Focus module 1: `Bild.lean` (lane 283) — CORRECT within claim

Read: `grammatik/Grammatik/X86/Bild.lean` (578 lines).

What it proves (generic over every image, all premises used):

- Canonical 48/57 boundary facts: `kanonisch_tief_48`,
  `kanonisch_hoch_48`, `kanonisch_loch_48`, `kanonisch_57_weiter_als_48`
  (lines 98-117), all `by decide`.
- One checked file→virtual mapping: `fileReich` / `virtReich`
  (125-132), disjointness `paarweise` (139-144), `abteilFinden`
  (151-156), total `dateiByte` with zero default (159-160), `ladenByte`
  with file-backed / BSS-tail / outside cases (164-170), permission
  projections (173-188), loaded memory `geladen` over the shared
  `Speicher` vocabulary (192-196).
- Decided well-formedness `wohlgeformt` (260-272): `groesseOk`,
  `dateiOk`, `virtuellOk`, canonical range, `ausrOk`, `wxOk` (W^X),
  pairwise file AND virtual disjointness, entry containment
  `eintragEnthalten`, class-checked `relokOk` (240-251), `modusOk`
  (fixed / parametric-4K-aligned, 255-257).
- Loaded-memory facts: `geladenByte_datei` (283-288),
  `geladenByte_bss` (292-297), three permission agreements (299-314),
  outside-domain frame `ausserhalb_rahmen` (318-324).
- Positive witness: `zeugenBild_wohlgeformt` (356-358, `by decide`),
  `zeugenFund_daten/loch`, `zeugenByte_geladen` (nonzero byte through
  the generic equality), `zeugenLesbar8/zeugenSchreibbar8`,
  memory-changing joint witness `schreibLese_zeuge` (454-477: `write64`
  reads back through `read64` and observably changes the byte),
  BSS image `bildBss_wohlgeformt/null`, parametric-bias image
  `bildParam_wohlgeformt/byte` (bias ≠ file offset, 519-527).
- Negative witnesses, each closed: `bildUeberlapp_verweigert`
  (395-397), `bildUmbruch_verweigert` (411-413),
  `bildEintrittAussen_verweigert` (420-422), `bildRelokOffen_verweigert`
  (431-433).

Why this is NOT vacuous: the positive case carries a nonzero mapped byte
(`zeugenByte_geladen`: byte 9 at `0x2000`), readability+writability
through `geladen`, and an actual `write64/read64` memory change. The four
refusals each flip exactly one conjunct of `wohlgeformt`. `#print axioms`
for all 26 theorems present (551-576).

What it explicitly does NOT claim (CUTS 529-549, honest and load-bearing):

- No decoder/boundary proof: `abteilFinden` matches section ranges, never
  decoded bytes. Decoded-instruction starts, control-flow targets, and
  re-decode of patched relocation sites are OPEN (next dependency).
- No relocation correspondence: `relokOk` checks resolution STATE, site
  containment, class-vs-section-kind, and the value target rule only.
  Patched-byte re-decoding and correspondence are OPEN — this is the
  concrete consumer gap for `Relokation.lean` (see §4) and the future
  `layoutOk`.
- No source correspondence, no concurrency, no loader-software claim:
  `geladen` is a pure function of the image; BSS-zero and permission
  agreement are proved of that function, not of any loader. Loader
  contract is unwitnessed (IMAGE-ABI §11).
- `Profil` has only `p48/p57`; `ausr` is the section's DECLARED alignment,
  not a proved 4K hardware demand.

Consumer in the single architecture: `wohlgeformt` + `geladen` are the
declared inputs of the future `valX86` skeleton (C5) and of
`direktZielOk`-style target checks (`ControlFlow.lean`). No consumer may
read `relokOk = true` as "the patched bytes decode correctly" — that
reading is refused by CUTS and would be a trust escalation.

No defect found. No invented bug: the OPEN items are OPEN by statement.

## 2. Focus module 2: `Byteschritt.lean` (lane 319) — CORRECT within claim

Read: `grammatik/Grammatik/X86/Byteschritt.lean` (510 lines).

What it proves:

- Executable-prefix fetch from ACTUAL memory: `holeFetchAux` /
  `geholt` capped at `fetchCap = 15` (17-41), with length cap
  `holeFetchAux_laenge_le` / `geholt_laenge_le` (81-97) and per-byte
  execute facts `holeFetchAux_ausfuehrbar` / `geholt_nur_ausfuehrbar`
  (121-149). Fetch checks execute permission ONLY, never data-read
  permission — pinned by the witness `kette_mov_store_load`
  (code not data-readable, 339-346) and `ohne_exec_verweigert`
  (readable-but-not-executable refuses, 396-399).
- Fetch-to-decoder correspondence with RUNTIME checks:
  `fetchDekodiert` (49-56) decodes actual fetched bytes with the
  independent `Codec.decode`, then checks consumed-length + suffix
  consistency, `laengeOk`, and execute permission of the consumed
  prefix. `fetchDekodiert_entspricht` (157-182) carries all four facts.
  A forged `Decodiert` can never become a trusted fetch: `byteschritt`
  (70-76) takes ONLY the state.
- Byte-step-to-`schritt` correspondence both directions:
  `byteschritt_weiter` (185-191), `byteschritt_verweigert_ohne_fetch`
  (195-199), `byteschritt_verweigert_ohne_schritt` (203-208),
  prefix-only execute use `fetch_nutzt_nur_praefix` (214-219).
- Canonical agreement for an ARBITRARY admitted instruction
  `kanonisch_schritt_ueberein` (227-252), proved from the round-trip
  instances — so the OPEN arbitrary-input decoder length soundness is
  NOT needed here (CUTS 478-484 states this explicitly; the runtime
  equation check + refusal carries the case).
- Witnesses: memory-changing MOV/STORE/LOAD chain through real bytes
  (`kette_mov_store_load`: `rcx = 42`, data cell 0 → 42); altered-opcode
  refusal (`opcode_geaendert_verweigert`: REX.X forgery refuses, intact
  steps to 4106); changed-displacement-changes-target
  (`sprungziel_folgt_byte`: 4117 vs 4118); truncated-prefix refusal;
  execute-denied refusal; RET-at-boundary without over-read
  (`ret_an_grenze_ohne_ueberlesen`).

Deliberate non-claims, correctly stated (CUTS 452-490):

- `verweigert` is absence of a transition, NEVER normal termination;
  `ret`-with-empty-caller and thread end are OPEN; `laufBytes`
  fuel-exhaustion answers `weiter`, not halt. Any consumer reading
  `laufBytes n s = .weiter` as "terminates" is unsound — the definition
  (274-279) says otherwise.
- No physical-hardware claim (model `Speicher` function, not silicon;
  caches/TLBs/store-buffers/self-modifying-code coherence OPEN to the
  TSO bridge).
- No whole-source/whole-binary/entry/ABI/relocation/cost claim.
- Only gate is checked execute permission of the consumed prefix.

Consumer in the single architecture: `fetchDekodiert` /
`byteschritt` are the declared fetch+step of the future closing
validator's fetched-bytes revalidation (`OPTIMIZER.md` §8.7) and of the
per-access TSO refinement (each target step's accesses come from
`Zugriffe.zugriff`, see §4). The module does NOT supply multi-step
control-flow validation, decode coverage of a whole image, or entry
predicates — those belong to C5/C4 and remain OPEN.

No defect found.

## 3. Focus module 3: `InvariantenOpt.lean` (lane 288) — CORRECT within claim

Read: `grammatik/Grammatik/X86/InvariantenOpt.lean` (550 lines).

What it proves — over ACTUAL source syntax and ACTUAL
`eval/execBlock/execStmt` (header lines 5-10), no toy model:

- Computable check `isWahrAll` (46-52: `wahr`, literal `le`/`eq`,
  `und`/`oder`; deliberately NO `nicht` arm) with soundness
  `isWahrAll_sound` (140-180) over `eval`, via extractor inversion
  `alsLitOpt_lit` (68-76), `eval_alsLit` (79-93), literal bridges
  `litLeBool_sound` / `litEqBool_sound` (95-131). The missing `nicht`
  arm is SOUNDNESS load-bearing (a `false` from a non-literal shape
  implies nothing) and is stated, not hidden.
- Constant folding `foldAddLit` + `eval_foldAddLit` (188-195, `rfl`),
  widening value lemma `eval_weiter_n` (199-203, `rfl`).
- Check/branch elimination with EXACT trace transfer:
  `exec_pruefung_wahr` (215-223) and `exec_ite_wahr` (228-235) run the
  rest in the POST-READ world `σ.lese Λ'' c.orte`; read observations
  transfer exactly; the refused `else` needs no fault transfer
  (unreachable, proved).
- Scope-tagged invariant elimination `exec_pruefung_inv` (261-268):
  same transfer, but truth evidence is a program invariant through a
  NAMED `InvScope` (`ruhe|sich|wechsel`, 250-253) instead of the
  computable checker. Cost, call-log, fault and interleaving transfers
  are the same separate obligations as for the computed check; the
  scope discharge itself (which leg, at which program point) belongs to
  the later certificate layer and is NOT discharged here — correctly
  stated as OPEN in CUTS, not smuggled in through the tag.
- Stability-gated load rule `slot_read_stabil` (277-285): a repeated
  read of the same slot returns the same value when the index evaluates
  the same AND the carrier is unchanged between the reads. The
  stability premise is the EXPLICIT separate obligation, discharged per
  instance by exclusive ownership, held-lock stability or immutability
  — never by thread-local token reasoning alone, never across
  publication, fences or acquire/release edges, and never for atomics,
  MMIO or foreign-observable memory (stated lines 270-276).

Witnesses (all joint, non-degenerate): the witness declaration `wD`
(300-351) has one private table with one slot over `0 .. 10` that the
witness contract `wV` writes (`wit_schreibt`, 402-403); `wit_elim`
(410-413) inhabits the generic elimination on the witness program;
`wit_step` (417-423) is the reached run with a memory-changing step
(slot reads `5` afterwards). Every `_zeuge` companion (428-515) is
present: `alsLitOpt_lit_zeuge`, `eval_alsLit_zeuge`,
`litLeBool_sound_zeuge`, `litEqBool_sound_zeuge`,
`isWahrAll_sound_zeuge`, `eval_foldAddLit_zeuge`,
`eval_weiter_n_zeuge`, `exec_pruefung_wahr_zeuge`,
`exec_ite_wahr_zeuge`, `exec_pruefung_inv_zeuge` (at `ruhe` scope),
`slot_read_stabil_zeuge`. `#print axioms` for all 8 main theorems
(541-548).

OPEN, explicitly not claimed (CUTS 517-539): multiplication folding
(`imin`/`imax` range type needs range evidence, not definitional);
discharge of `InvScope` tags (needs the `invRuhe`/`invSicht`/
`sperrWechsel`/`sperrSicht` legs at the use site — never inside a
running writer or held section); discharge of `slot_read_stabil`'s
stability premise; cost/ghost-budget transfer; `Folge` preservation
across call-adding transformations (ours touch no calls); fault
transfer beyond the refused unreachable `else`; interleaving transfer
(single-thread `exec` only); atomics, MMIO, foreign-observable memory
(all refused here); any source-to-bytes or concurrent/hardware claim.

Consumer in the single architecture: `isWahrAll` is the recomputation
the future per-pass validator re-runs (nothing trusted from Rust);
`exec_pruefung_wahr` / `exec_ite_wahr` are the accepted shapes for the
fold/simplify certificates (C1-C4/S1-S3 rows of `OPTIMIZER.md` §3);
`exec_pruefung_inv` + `InvScope` are the accepted shapes for the
check-removal certificates (B1-B3 rows) once the certificate layer
discharges scope + entailment at cited SSA versions;
`slot_read_stabil` is the accepted shape for load-reuse certificates
(A1-A2 rows) once stability is discharged per instance. No consumer may
treat an `InvScope` tag as a discharged leg, or a `slot_read_stabil`
instance with `rfl`-stability on identical worlds as a concurrent
stability proof — both readings are refused by the stated premises.

No defect found in §3.

## 4. Neighbouring accepted modules: consumer-gap check

All files below are read at snapshot `0b3132b7`. Verdict pattern is the
same throughout: correct within the stated claim; the gaps are the named
OPEN consumers, not defects.

- `Zugriffe.lean` (lanes 317/318): single-owner per-instruction access
  extraction `zugriff` with per-constructor lemmas, no-memory-access
  successes, read/write-in-footprint facts, and failure-refusals.
  Consumer: the per-access TSO refinement reads every target step's
  accesses from here.
  FINDING F3 (review finding, not a defect): the extraction covers the
  14-constructor pilot vocabulary only. Narrow (8/16/32-bit), LOCK/RMW,
  fence, FP/SIMD, and indirect-control forms have no `zugriff` arm yet;
  any consumer that treats pilot-only footprint completeness as
  whole-programme access completeness would be unsound. The module does
  not make that claim (tearing stays OPEN per its CUTS); the gap closes
  with waves A1-A6. No repair inside this module; guard its consumers
  until the arms land.
- `TSO.lean` (lane 274): per-core FIFO byte store buffers
  (`TSOZustand`, `issueByte`/`loadByte`/`flushKern`/`zaunBereit`,
  `TSOSchritt`, `fifo_reihenfolge`), byte-level `Sicht` link, and the
  store-buffering witness (`sb_*`, `tso_store_buffering`). Proves byte
  facts only: aligned multi-byte single-copy atomicity, LOCK RMW, and
  the cross-granularity W/GX simulation are OPEN by its CUTS. The
  local-fence limitation is a proved limitation
  (`zaun_kein_fremd_drain`), not a hidden gap.
- `Relokation.lean` (lane 291): `rel32` round-trip, address equation,
  next-RIP formation, `abs64` round-trip, byte patching with overlap
  refusal. The flag `relAnnahmeEndgueltig = false`
  (`relAnnahme_offen`) means no helper fact admits a site on its own.
  Consumer gap: patched-byte RE-DECODE against `Codec` (the
  `Bild.relokOk` OPEN item in §1) still waits for the `layoutOk`
  consumer; the arithmetic here is the reusable half.
- `AccessList.lean` (lane 341): single-owner `accessList(rule)` with
  per-rule completeness against `LiestG`/`SchreibG`, the exchange RMW
  lemmas, and the `luecke_faellt` refusal. Fixes the previously
  ownerless overlap. Its CUTS names the two OPEN consumers: the bridge
  D-access/L-access-complete and the IR lowering map. Byte values,
  alignment, tearing and TSO visibility stay OPEN to lanes B2/B4.
- `OverlapRefusal.lean` (lane 342): decided
  alignment/containment/non-overlap checker with `Unknown => refuse`
  policy enforced by the Bool, plus the aligned-single-carrier
  bytes-value agreement and the adjacent-carrier accept/refuse pair
  (counterexample-C shape as negative probe). Closes the O-align
  decidable half; tearing correspondence stays OPEN.
- `SpillPrivate.lean` (lane 343): TSO-side freshness => disjointness
  => commutation with the decided admission gate `spillPrivatOk`
  (address-taken, extent-named, out-of-frame slots refused; in-frame
  private slot admitted) and a two-core TSO witness. SCFG-side
  application WAITS for the accepted 287 interface (marked, not
  invented).
- `AufrufOpt.lean` (lane 310): inlining ghost obligation with ACTUAL
  `rho`/`v`/`s0`/`s1` (`geistPaar`, `geistPaar_laenge`, `FolgeLog`
  order lemmas). Its CUTS is honest about the halves it does NOT
  cover: return-side derivation from a successful `rufAt` outcome
  (only the entry half `vorOk` is proved), duty discharge
  (`InlinePflicht.hp`/`hr` are CARRIED, not discharged), indirect
  calls (no ghost form), bounds/depth/budget timing, and the
  SCFG/target bridge. A ghost with quantified-away parameters would
  break `FolgeG` and is refused by construction.
- `StaerkeReduktion.lean` (lane 311): `mul`/`div`/`rem` by `2^k` to
  shifts/masks with nonneg/never-zero/width side conditions, plus the
  self-contained refusal `sdiv_kein_shift` (truncation is not shift for
  negative numerators). Value correspondence only; `FolgeG`/budget/
  concurrency stay out. Hardware count masking is NOT bridged:
  `shrW_breite` pins counts below the width instead.
- `ControlFlow.lean` / `LockedOps.lean` / `MulDiv.lean` /
  `ShiftLogic.lean` (waves A2-A5, this snapshot): per-form execution
  definitions with flag/fault facts, direct-target theorem
  (target = virtual next-RIP + sign-extended disp, decoded-start or
  listed entry), faulting `CMOV`-memory keeping its untaken-path fault,
  LOCK single-op RMW with per-event access records, and the CAS-loop
  unbounded shape with NO constant bound claimed. No W/GX refinement
  is claimed by any of them (the bridge owns it).

## 5. Vacuity-risk audit (checked, not trusted)

For each helper: does a non-degenerate joint witness exist, are all
premises used, and could the theorem hold vacuously?

1. `Bild.wohlgeformt` family: NON-VACUOUS. Positive image accepted AND
   four independent single-conjunct refusals; the memory witness moves
   a real nonzero byte through `write64`/`read64`. A checker that
   accepted nothing (or refused nothing) would fail here.
2. `Byteschritt` chain: NON-VACUOUS. The MOV/STORE/LOAD chain changes
   memory through real fetched bytes; the altered-opcode and
   changed-displacement probes show the executed instruction follows
   the bytes (positive and negative directions both pinned).
   `laufBytes` fuel-exhaustion answering `weiter` is documented, so a
   bounded run cannot be mistaken for a termination proof.
3. `InvariantenOpt` eliminations: NON-VACUOUS with one noted weakness.
   `wD` writes its table, `wit_step` changes memory, `isWahr` fires by
   computation, and the `nicht`-free checker shape plus the
   `InvScope`/stability premises keep the rules from firing on hope.
   Weak point: `slot_read_stabil_zeuge` uses identical worlds
   (stability by `rfl`) — it inhabits the lemma jointly but does not
   exercise a discharged stability obligation. Bounded weakness, not a
   defect: per-instance discharge is the certificate layer's job (P0.3).
4. Premise-use check: every cited theorem's premises are consumed by
   its proof (verified by reading: `hfind`/`hhi`/`hlo` in Bild,
   `hf`/`hs` in Byteschritt, `h`/`hidx`/`hinhalt`/`s` in
   InvariantenOpt). No discarded premise, no `Prop`-typed premise, no
   conclusion restating a premise, no `forall rho` / `forall v`
   quantification of contracts — ghost pairs carry actuals.
5. `Sicht`-family legs on bridged units: REVIEW-QUELLE-INVARIANTEN §2
   notes these legs are vacuous on every currently certified program
   (no shared carriers there). That vacuity lives in the SOURCE-side
   programme sample, not in the X86 helpers — but any future optimiser
   certificate citing holder/quiescent facts for a concurrent programme
   must re-establish non-vacuity there. Flagged for the certificate
   layer, not repaired here.

## 6. Validator inputs that must never be trusted from Rust

No `valX86` exists yet, so this is a forward constraint on its
consumers (C5 owner, then the Rust backend). Every item below must be
re-decided by a Lean Bool; a Rust print of any of them is evidence
only (`OPTIMIZER.md` §§7-8, `IR-VALIDIERUNG.md` §§2/4):

- Decoded instructions and lengths: from `Codec.decode` on final
  bytes only, never an emitter annotation (cf. `direktZielOk`,
  `fetchDekodiert` checks).
- Avail/liveness/dominators and block/node maps: validator
  recomputes; stale facts across an invalidation boundary refuse.
- Range/alias/footprint facts: recomputed entailment at cited SSA
  versions; entry facts do not travel into writers or across
  may-write calls; `Unknown` overlap blocks motion.
- Layout, displacements, relocation operands, load bias, file/virtual
  mapping: revalidated on FINAL bytes (`layoutOk` + fetched-bytes
  revalidation); relaxation-round changes without revalidation refuse.
- Cost sums and attempt bounds: re-summed as a mismatch check only;
  `budget_simulation` and cycle bounds need their own proofs.
- Tuning tables, search order, cache hits, profile data: untrusted
  hints; a wrong table may only slow valid code, and a stale cache
  entry re-runs the validator Bool before acceptance.
- Ordering strength: `seqcst`-instead-of-weaker is NOT a conservative
  route (stronger can deadlock where weaker progressed, `KernHaltE`).
- Loader behaviour, binding bodies, foreign footprints (OBS-5),
  device protocol order: user-logic contracts or refusals, never
  hardware assumptions.

## 7. Runtime / link / loader coverage (all reachable bytes)

`IMAGE-ABI.md` obligations against what `Bild` + neighbours cover:

- Covered now: section mapping, permissions incl. W^X, entry
  containment in executable sections, two bias modes, BSS-zero and
  permission agreement as pure-function facts, relocation STATE +
  site containment + class/target rules, `rel32`/`abs64` arithmetic
  and patching with overlap refusal.
- OPEN (each a numbered bridge task in §9, each a refusal until
  closed): (a) decoded coverage of every executed byte + re-decode of
  patched sites; (b) direct/indirect control-target closure
  (jump-table certificates, `entry fn` provenance under N575-N577, no
  forged pointers per M140); (c) the loader contract as checked
  software (mapping actually installed, BSS actually zeroed,
  bias/relocations actually applied — `geladen` proves the function,
  not the installation); (d) ABI/stack/region/binding bodies for every
  reachable support byte (generated driver, compiled-in binding code,
  runtime, handwritten entry paths) with callee-summary checks at
  every call edge; (e) thread/interrupt entries, guard pages,
  MXCSR/XMM save-restore, trap-return behaviour; (f) second-link-unit
  optimisation premises (`GabbroZielVerbund`).
- Naming hygiene for the closers: `TableLayout.layoutOk` (when it
  lands) is a table-layout predicate, not `layoutOk(Gn, B, Img)`; the
  `valX86_sound` / `schluss_x86` sketches in `QUELLBRUECKE.md` §4 are
  commented target shapes in a design doc, not accepted Lean
  definitions. Conflating either would be a trust escalation.

## 8. Proof-vs-CUTS ledger (what may be said)

| Helper | May be said | Must NOT be said |
|---|---|---|
| Bild | decided image well-formedness + loaded-memory facts, with accept + 4 refusals + memory-changing witness | decoded coverage, patched-byte correspondence, source/concurrency/loader claims |
| Byteschritt | executable-prefix fetch + fetch-to-decoder + byte-step-to-`schritt` correspondence, with memory-changing chain + 5 refusal shapes | physical hardware, whole-binary/entry/ABI/cost claims, termination |
| InvariantenOpt | computable-check soundness + exact-trace eliminations + scope-tagged/stability-gated rules, jointly witnessed | discharged scopes, discharged stability, budget/`Folge`/interleaving transfer |
| Zugriffe | per-instruction access extraction over the pilot 14 | whole-programme access completeness (F3: narrow/LOCK/fence/FP/SIMD arms missing) |
| TSO | byte-level buffers/forwarding/flush/fence-readiness + proved local-fence limit | word atomicity, LOCK RMW, W/GX simulation |
| Relokation | `rel32`/`abs64` arithmetic + patching with refusals | patched-byte re-decode, site admission |
| AccessList | single-owner per-rule completeness + `luecke` refusal | byte/alignment/tearing/TSO-visibility closure |
| OverlapRefusal | decided O-align half + `Unknown`-refusal + carrier agreement | tearing correspondence |
| SpillPrivate | TSO-side spill freshness/commutation + admission gate | SCFG-side application (waits for 287) |
| AufrufOpt | ghost-pair shape with actuals + order lemmas | return-side derivation, duty discharge, indirect ghosts, budget |
| StaerkeReduktion | range-gated shift/mask rules + `sdiv` refusal | reassociation/FMA/float/vector reduction |
| ControlFlow/LockedOps/MulDiv/ShiftLogic | per-form execution + target/fault/atomicity-unit facts | source lowering, ISA expansion, final-byte validation, speed |

Every row's right column is the module's own CUTS or the named OPEN
consumer — legitimately incomplete, not a defect — except F3, which is
phrased as a review finding because a reader could mistake pilot-only
footprints for complete ones.

## 9. Prioritized necessary repair / missing-bridge tasks

P0 (blocks every end-to-end claim):
- P0.1 Shared SCFG frozen + accepted (lane 287) — no second IR in
  the meantime; all SCFG-consuming rows define only their non-SCFG half.
- P0.2 Decided `valX86` skeleton + `lowerOk`/`check_C`/`layoutOk`
  (C5 owner) with `valX86_sound` stated OPEN in CUTS, never assumed.
- P0.3 Source-duty exports computed in Lean from the source
  (`DutyExport`, `EffectExport`, `AtomicExport`, `FpExport`,
  `CostExport`, `LowerMap`); Rust prints of any of them are hints.
P1 (blocks concurrent/shared-byte programmes):
- P1.1 Per-access x86-TSO → W refinement + `schwach_ist_gX` reuse
  (D-tso, L-read/write/view/step/run); O-access cites `accessList`,
  O-align cites the decided checker; tearing proof or refusal.
- P1.2 F3 closure: `zugriff` arms for every newly admitted form
  (narrow first — 64-bit covering access IS cross-carrier overlap),
  each with footprint + refusal probes.
- P1.3 Patched-byte re-decode + `layoutOk` coupling (`relokOk` +
  `Relokation` arithmetic + `Codec` round-trips, decided per site).
P2 (blocks whole-image acceptance):
- P2.1 Entry/ABI/stack/region/binding coverage for ALL reachable
  bytes (C1/C2/C4 owners): table layout, gate-stub caller checks,
  entry predicates, callee summaries at every edge; OBS-5
  foreign-footprint obligations per binding.
- P2.2 Cost schema (`CostSummary`): `kostenSummeOk` + `expandBound` +
  per-site attempt bounds as a framework with `budget_simulation`
  OPEN; CAS-retry sites never behind constant bounds.
P3 (gates for profile/width/float/SIMD work):
- P3.1 Width/profile/flag gates: narrow flag snapshots, AF-`none`
  discipline, `CMOV`-memory fault preservation, divide-error as
  `hardware`-stop, shift-count masking pinned below widths.
- P3.2 FP admission (narrow, literal-only, RNE-preconditioned) and
  SIMD admission (lane separation + atomicity table + privateness +
  tail) — both default-REFUSE until proved; cache/profile/tuning
  discipline per §6.

## Appendix A. Files read (exact)

`DIRECT-COMPILER.md` (ledger + end condition), relevant parts of
`DIRECT-COMPILER-DESIGN.md` (§§1-7A), `grammatik/OPTIMIZER.md`
(§§1-10), `dokumente/x86/WORK-ALLOCATION.md`,
`dokumente/x86/{BYTE-PILOT,EMITTER-INVENTAR,FLOAT-ZEIT,IMAGE-ABI,
IR-VALIDIERUNG,LEAN-ZUERST,QUELLBRUECKE,REVIEW-GRUNDLAGEN,
REVIEW-OPT-BINAER,REVIEW-QUELLE-INVARIANTEN,REVIEW-TSO,
TSO-GX-BRUECKE,WELLE-A}.md`, and
`grammatik/Grammatik/X86/{Typen,Wort,Ganzzahl,Speicher,
SpeicherKommutation,Zugriffe,Ausfuehrung,Byteschritt,Codec,Bild,
Relokation,Regionen,Stapel,TSO,FlagBeweis,Gleitprofil,Vektor,
InvariantenOpt,AufrufOpt,StaerkeReduktion,AccessList,
OverlapRefusal,SpillPrivate,ControlFlow,LockedOps,MulDiv,
ShiftLogic}.lean` (definitions, theorem statements, CUTS tails,
`#print axioms` blocks).

## Appendix B. Mechanical checks performed

- Grep over all eleven neighbouring + three focus X86 modules for
  `sorry|admit|axiom |native_decide|unsafe`: zero real hits (every
  `admit*` match is English "admitted/admits" in comments).
- `#print axioms` blocks present in every module read.
- Attempted fresh `./lean-probe` of `Bild.lean`: timed out after 120 s
  on the queued Lean slot; no fresh build number claimed (docs-only
  commit owes no Lean rebuild). Positive/negative evidence is the
  committed `by decide`/`by simp`/`by rfl`-closed theorems as read.
- No experimental Lean files created; nothing private to keep.

## Appendix C. Review-response note (lane 495)

Independent review 495 (REPAIR) found the first-committed revision of
this file truncated mid-sentence in §3 (tool-write cutoff artifact as
the final file bytes), so promised §§4-9 and appendices were absent
and forward references dangled. This revision is the repair: §§0-3
unchanged (every citation in them verified correct by the reviewer),
§§4-9 and appendices A-C restored, all forward references (§4, §7,
§8 ledger) resolve inside the file, and the DIRECT-COMPILER citation
above uses the document's named parts (the reviewer noted its headers
are unnumbered, so no `§§27-33` number is cited). No safety weakening,
no assumed correctness, no overstated proof in the repair.
