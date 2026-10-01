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
  NAMED `InvScope` (`ruhe|sich
...[truncated 9113 chars]