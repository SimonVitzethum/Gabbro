# Adversarial implementation audit: DYNAMIC-REGIONS (lane 411)

*Owner: lane 411. Owns only this file plus `MUSE-REPORT-411.md`.
Method: read the accepted modules and the source definitions they claim to
serve; checked every claim against the file's own CUTS and the named consumer.
No Lean file added or changed, no Rust change, no central-file edit.
This document proves nothing and closes no chain; it records what the
dynamic-region path can justify today and what is still missing.*

*Scope boundary: source heap ceiling, fresh disjoint external regions,
generic layout, the missing per-program proof-free bridge, and the refused
int-to-pointer paths. TSO granularity, optimisation rules, cost transfer and
whole-image acceptance belong to other lanes and are cited only where this
path touches them.*

## 0. Files actually read (anchors with line numbers as-read)

- Target regions: `grammatik/Grammatik/X86/Regionen.lean` (full, 631 lines;
  header 1-14, `Region`/`Vorrat` 20-33, `reserviere` 92-104, freshness/
  disjointness 186-206/281-299, `initialisiere` 231-239, ceiling-free
  `FreiStand`/`freiReserviere` 426-442, no-static-bound 477-488, witnesses
  490-570, CUTS 572-595).
- Target byte memory: `grammatik/Grammatik/X86/Speicher.lean`
  (`Speicher` fields from `Typen.lean` 41-45, `read64`/`write64` 47-136,
  no-wrap/footprints 156-193, read-back/frames 324-373, width-indexed
  377-661, joint witness 663-710, CUTS 712-727).
- Target overlap admission: `grammatik/Grammatik/X86/OverlapRefusal.lean`
  (`zugriffOk` 44-47, policy 95-98, agreement lemma 143-179, adjacent-carrier
  witnesses 183-274, counterexample-C 281-291, joint witnesses 299-355,
  CUTS 357-380).
- Single access owner: `grammatik/Grammatik/X86/AccessList.lean`
  (`ZugriffBefund.luecke`, generic completeness lemmas, CUTS 238-250).
- Source heap ceiling: `grammatik/Grammatik/ArenaDyn.lean`
  (`DynArena` 24-31, `dynGrow` 36-39, `dynGrow_isSome` 64-71,
  `dynGrow1_gdw_alloc` 83-98, `dynGrowListe` 141-146, `Form` section
  `DynForm` from line 271).
- Goal statement: `grammatik/Grammatik/Zielsatz/Spec.lean` (arena-runtime
  comment block 676-686, premise (d) `Laufzeit.reserve` 899-915, (d)
  `Laufzeit.commit` 916-928, budget (M10) 1045-1047, `DynForm` coverage
  note 1443-1444).
- Region gate template: `grammatik/Grammatik/SchablonenOhneLibc.lean`
  §4 `tor.region` (~359-412: `regionStumpf`, `tor_region`,
  `tor_region_adresse`, `region_zugriff`, and the explicit NOT-proved list).
- Checker sentences: `crates/gabbro-check/src/saetze.rs`
  (`syscall.stub` ~4319-4360, `zeiger.index_in_der_ausdehnung` ~4409-4457,
  `fremd.ohne_code` ~4511, `klon.uebergabe` ~4651, `M140` nominal rule).
- Canonical vocabulary: `grammatik/Grammatik/X86/Typen.lean`
  (`Speicher` 41-45, `Befehl` pilot 14 constructors 53-68, CUTS 81-86).
- Source layout front end: `grammatik/Grammatik/Parser/UebersetzeAllg.lean`
  (`fieldRangeO` 72, `typAt` 84, `declOf` 147).
- Wave plan: `dokumente/x86/WORK-ALLOCATION.md` (B1 `AccessList` 178-190,
  B2 overlap 191-201, C1 `TableLayout` 228-237, C2 `GateStub` 239-248,
  C5 validator skeleton 275-288).

## 1. Source heap ceiling: what exists and where it stops

**Exists and checked (within stated claims).**

- `ArenaDyn.dynGrow` refuses past the ceiling `M` by construction
  (`dynGrow_ueber_M`, `dynGrow_isSome` 56-71); the planted probes
  (`planted_ueber_M`, `planted_defekt_sichtbar`) pin the guard against the
  unchecked variant. The `Form` section (`DynForm`, `Block.dynGrowB`,
  `Block.dynAlloc`) connects the dynamic form to the existing `Block`
  machine rules, and `Spec.lean` 1443-1444 records that the goal statement
  needs no new case for it.
- `Spec.lean` premises (d) `Laufzeit.reserve` (899-915) and (d)
  `Laufzeit.commit` (916-928) name the reservation/commit services with
  their proved template obligations (`arena_spanne_passt`,
  `arena_commit_bereich` in `SchablonenArena.lean`) and state explicitly
  what stays assumed: the gate's contract (a below-ceiling failing commit
  reaches the program's `else`). Comment-only, no premise moved.
- The target side mirrors the ceiling discipline: `Regionen.reserviere`
  refuses empty/unaligned/over-ceiling/wrapping requests (92-104) with
  proved extent/rights (`reserviere_ausmass`), containment
  (`reserviere_innerhalb`), cursor monotonicity (`reserviere_decke`),
  freshness (`reserviere_frisch`), full refusal (`reserviere_voll_verweigert`),
  and disjointness against every tracked region under the cursor invariant
  (`reserviere_disjunkt_unten` + `alleUnten` preservation 301-350).
  Positive and negative probes are real (`zeugenReserviere_erfolg`,
  `zeugenReserviere_voll`, both `decide`).

**What is correctly OPEN, not a bug.**

- `Regionen.lean` CUTS states it plainly: "No source correspondence:
  nothing here claims the regions are the lowering of any Gabbro
  `Arena`/allocator construct, duty, cost or template." The target
  `Reservierer`/`Vorrat` and the source `DynArena`/`DynForm` are two
  vocabularies about ceilings with no proved map between them. The file
  does not pretend otherwise; flagging this as a defect would be inventing
  a bug where the file declares an open bridge.
- The ceiling-free opt-in (`freiReserviere`) is honest about what it loses:
  `freiReserviere_ohne_statik_gebunden` proves every bound below `2^64` is
  exceeded, while every single extent still satisfies no-wrap. No physical
  unbounded-address claim is made (CUTS 590-592). Correct within claim.
- Budget side (M10, `grow` against a fixed budget) is a Spec comment; no
  target cost lemma cites it. That is validator/cost-lane business, not a
  region-file defect.

## 2. Fresh disjoint external regions: the gate path

**Exists and checked (within stated claims).**

- `tor.region` (`SchablonenOhneLibc.lean` §4) proves the emitted region stub
  decides exactly as the generic `dekodiere` over `1 .. 2^63-1`
  (`tor_region`), the handed address is the kernel word itself and never
  zero, and no error word becomes an address. The section lists what is NOT
  proved: the kernel keeping the contract (gate assumption, premise (c)),
  and machine G having no byte pointers (LG002 refusal, OFFEN O37).
- The ONE generic form `region_zugriff` connects the gate contract (user
  logic: `ensures n <= lenof(result)` plus the fresh/disjoint sentence) to
  what `N571` makes of it (index inside the region and inside no other live
  region). The checker side is real code with sentences and probes:
  `N571` (`zeiger.index_in_der_ausdehnung`), `N463` widened, emitter
  `C186` (`syscall.stub`: region answer without its `or R` channel),
  gifts 1383-1387, example 183.
- On the target side, `initialisiere` gives the canonical shape of "a fresh
  region becomes usable storage": zeroed bytes plus declared rights inside
  the extent, frame lemmas outside it (241-267), and the bridge to the
  permission-checked accessors (`initialisiere_schreibbar8`,
  `initialisiere_lesbar8`) feeding the joint memory-changing witness
  `region_schreibLese_zeuge` (534-570).

**Gaps (consumer-facing, prioritised in §6).**

1. `region_zugriff` is a source/C-template generic form; nothing in
   `Regionen.lean` or `OverlapRefusal.lean` cites it. The target
   `reserviere` freshness/disjointness and the gate-contract
   fresh/disjoint sentence are proved in isolation with no shared
   statement. A consumer that wants "the target allocator discharges the
   gate assumption" has no lemma to cite. (Task R1.)
2. `initialisiere` installs rights over the whole extent but is not wired
   to any loader/image mapping: `Regionen.lean` CUTS names it ("No
   loader/image integration: `Bild.lean` mapping, entries, relocations and
   the loader contract are untouched"). `Bild.lean` has `Abschnitt` layout
   and `OverlapRefusal` already builds an adjacent-carrier image on it
   (183-208), but no theorem says a `reserviere`d region lands in a loaded
   section with matching rights. (Task R2, owned by image work; recorded
   here as the consumer gap.)
3. OFFEN O37 stands: byte pointers have no G form, so example 183 stays
   `UNCERTIFIED` (first refusal LG003, behind it LG002). The region path
   is proved at the stub/contract level but no certified end-to-end
   program exercises it. Not a defect in any helper; a missing bridge
   endpoint.

## 3. Generic layout: the thinnest part of the path

- `Typen.lean` is data only: widths (`Breite`), registers, flags with
  `af : Option Bool`, `Speicher` as four functions. It states no layout
  fact and claims none (CUTS 81-86). Correct within claim.
- Source layout facts exist per-table in the front end (`fieldRangeO`,
  `typAt`, `declOf` in `UebersetzeAllg.lean`), but there is no generic
  target layout function: WORK-ALLOCATION C1 (`TableLayout.lean`: computed
  extents/widths/alignments, carrier enumeration, `aligned N` refusal) has
  no file in `grammatik/Grammatik/X86/` (directory listing §0: 27 modules,
  no `TableLayout.lean`). `OverlapRefusal.wortTraeger` (133-135) hard-codes
  one 8-byte carrier; the adjacent-carrier image hard-codes two sections.
  These are witnesses, not a layout rule, and the file says so
  (CUTS: "No source correspondence").
- Consequence: `zugriffOk` admits an access against ONE caller-supplied
  `Region`, and `fussEnthalten` checks containment in that region. Nothing
  decides WHICH region a source carrier lives in, or that two source
  carriers land in disjoint target regions. The per-access admission is
  sound; the layout question it presupposes is unanswered. (Task R3: the
  C1 module; explicitly do not duplicate `fieldRangeO`/`typAt`, consume
  them.)

## 4. The missing per-program proof-free bridge (what "no second IR" means here)

The task asks for the missing per-program proof-free bridge. Concretely,
for an arbitrary admitted program, the chain

```
source carrier (declOf/typAt/fieldRangeO)
  -> target region (Region/Vorrat/reserviere)
  -> initialised storage (initialisiere + lesbar8/schreibbar8)
  -> admitted access (zugriffOk / klassifiziere / aliasZulassen)
  -> source access completeness (AccessList eintraege_* / schreibG_voll)
```

has proved endpoints and unproved joints:

- Joint A (carrier -> region): OPEN. No function maps a source carrier to
  a target `Region`; C1 is the owned task for it. `AccessList` works over
  source carriers (`D.Tab ⊕ D.Glob`), `zugriffOk` over target footprints;
  nothing translates between them.
- Joint B (region -> storage): HALF-OPEN. `initialisiere` + the
  `schreibbar8`/`lesbar8` lemmas prove the shape once a region is given,
  but no loader theorem connects `reserviere` output to `Bild` sections.
- Joint C (target access -> source access): OPEN by design placement.
  `AccessList` gives generic completeness over EVERY `RufSchrittG` step
  without per-rule inversion (CUTS 238-250); the per-rule syntactic
  classification for the non-exchange rules stays OPEN. The TSO bridge and
  the IR lowering map are the named consumers; neither cites the other
  side yet. This audit confirms the ownerless-overlap finding
  (REVIEW-TSO §5.2) is fixed on the source side (single owner exists) but
  the target side (`Zugriffe.zugriff` per-event records) still has no
  completeness statement against `accessList`. (Task R4.)
- What must NOT be built to fill these joints: a second IR, a toy machine
  with its own evaluator, or a per-program rule. The waiting consumer is
  the accepted 287 IR interface; rows that need it are marked WAITING in
  the wave plan. This audit endorses that marking for joints A/C.

## 5. Refused int-to-pointer paths: verified closed where claimed

- Source language: `M140` is the nominal shape rule; a number at a pointer
  slot is refused, and the sentence file pins the handoffs (`N260` for the
  null-pointer literal, `M135` for bool/number crossings). The region-gate
  stub is the ONE place a word becomes an address, proved in `tor.region`,
  and it is a kernel-answer decoding, not a language expression. No
  expression-level int-to-ptr exists. Closed as claimed.
- Exporter: `lean_g.rs` refuses the byte-pointer target by name (LG002);
  a region program is outside the certified register exactly like every
  `ptr<..> u8` program (OFFEN O37, stated in `tor.region` CUTS-equivalent).
  Loud refusal, not silent admission. Closed as claimed.
- Target model: `natAdresse` (`Regionen.lean` 223) turns a `Nat` into an
  `Adresse`, and `inRegion_natAdresse`/`natAdresse_addrs` reason about it.
  This is waterproof WITHIN the target model (offsets are numbers there by
  construction) and is not an int-to-pointer cast across the language
  boundary: no source number flows into it without passing the gate stub
  and the checker. The day a lowering map feeds source indices into
  `natAdresse`, that map must cite `N571`/`N463` extents; today no such map
  exists, so there is nothing to audit yet. Recorded as a precondition on
  R1/R3, not a finding against `natAdresse`.
- `OverlapRefusal` policy `unknown-overlap => refuse` (95-98, 111-116)
  with the counterexample-C negative probe (281-291) is the target-side
  analogue: unplaceable overlap is refused, never widened into admission.
  The tearing correspondence stays OPEN explicitly (CUTS 364-368); per-byte
  TSO is not claimed as multi-byte atomicity. No correction needed.

## 6. Prioritised repair / missing-bridge tasks

| # | Task | Consumer | Notes |
|---|---|---|---|
| R1 | Cite `region_zugriff` from the target allocator: prove `reserviere` output satisfies the gate-contract fresh/disjoint sentence shape, or state the exact mismatch as a lemma-shaped OPEN item | direct-compiler bridge (x86-byte instances of allocator correspondence) | Needs no IR; must not invent a second allocator. Precondition: R3's extent language or a minimal shared extent statement. |
| R2 | Wire `reserviere`/`initialisiere` to `Bild` sections: a handed region lands in a loaded section with matching rights | image/loader work (C5 `valX86` soundness needs it) | `OverlapRefusal` adjacent-carrier image is the natural seed witness. Owned by image work; listed here as the consumer gap. |
| R3 | C1 `TableLayout.lean`: computed carrier layout from `declOf`/`fieldRangeO`/`typAt`, disjoint extents, `aligned N` refusal | `zugriffOk` callers, validator skeleton | Consume the front end, do not re-derive layout facts in Rust or by annotation. |
| R4 | Target-side completeness of `Zugriffe.zugriff` against `AccessList`: per-event records cover the same accesses the source completeness lemmas cover, or an explicit `luecke`-style refusal where they do not | TSO bridge D-access/L-access | Do not redo the 70-case inversion; cite the generic lemmas. |
| R5 | Certified region end-to-end program once O37 lifts (byte-pointer G form): example 183 shape through `tor.region` + `N571` + target access | whole-chain validation | Blocked on O37, not on any file audited here. |

Explicit non-tasks (checked, no action): `Regionen` ceiling/`alleUnten`
proofs, `Speicher` read-back/frames, `OverlapRefusal` policy and
counterexample-C, `M140`/LG002 refusals, `tor.region` stub soundness, the
ceiling-free model's bounded-loss statement. Each is correct within its
stated claim and carries real positive and negative probes.

## 7. Probes reproduced

Read-only verification (no file written):

- `zeugenReserviere_erfolg` / `zeugenReserviere_voll` (`Regionen.lean`
  511-522): positive allocation at the range base and refusal past the
  ceiling, both by `decide`. Stated as theorems; re-check via
  `./lean-probe grammatik/Grammatik/X86/Regionen.lean` (full-file green
  expected; run recorded in `MUSE-REPORT-411.md`).
- `region_schreibLese_zeuge` (534-570): nonzero write through the
  initialised witness region reads back with an observed byte change.
- `spanne_verweigert_unversetzt` / `spanne_verweigert_aussen` /
  `gegenbeispielC_verweigert` (`OverlapRefusal.lean` 244-291): unaligned
  spanning access and partial-overlap pair refused by decision.
- `push_in_traeger_angenommen` / `store_in_traeger_angenommen` with
  `nachbarTraeger_disjunkt` (227-274): real `push`/`store` footprints
  accepted on disjoint adjacent carriers on one image.

No new probe file is committed: the accepted modules already carry the
positive, negative and joint witnesses this audit cites.

## 8. Verdict

The dynamic-region path is sound in its parts and open in its joints. Every
helper audited is correct within its stated claim; every CUTS block
accurately names what it does not prove; the refusals (`M140`, LG002,
`len = 0` / `ausr = 0` / over-ceiling / unknown-overlap) are loud and
probed. What is missing is the per-program bridge R1-R4, which needs the
C1 layout module and the accepted IR interface, not a rewrite of anything
audited here. No safety weakening and no desired-correctness assumption was
found in the audited files; none is proposed by this audit.

/- CUTS: audit only. No Lean module, no validator, no refinement, no cost
   transfer and no image acceptance is proved here. Line numbers are as-read
   and may drift. Full source-to-final-bytes validation remains OPEN. -/
