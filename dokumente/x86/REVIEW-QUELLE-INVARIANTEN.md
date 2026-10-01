# Source and invariant trust-boundary review (lane 292)

*Owner: lane 292. Scope: `dokumente/x86/REVIEW-QUELLE-INVARIANTEN.md` + report only.
Method: read the actual Lean definitions listed in §0 against
`dokumente/x86/QUELLBRUECKE.md` (lane 277) and `dokumente/x86/IR-VALIDIERUNG.md`
(lane 275). No Lean file added or changed, no Rust read beyond file names,
no build run (task: no gratuitous builds). Grep negative for every
phase-B schema name in §7 was verified (`DutyExport`, `EffectExport`,
`AtomicExport`, `FpExport`, `CostExport`, `LowerMap`, `valX86`,
`schluss_x86`, `X86Verfeinerung`, `SCFG`, `check_C`, `layoutOk`, `lowerOk`:
no `.lean` file under `grammatik/` or `bruecke/` defines them).
This document proves nothing and closes no chain; it audits what the
source side can justify today.*

## 0. Files actually read (anchors)

Front end: `grammatik/Grammatik/Schlusssatz.lean` (`uebersetzeAllg` 58-71,
`uebersetzeAllg_von_zeichen` 93-108, `Kette` 264-284, `schlusssatz` 365ff),
`grammatik/Grammatik/Parser/Uebersetze.lean` (`USide` 52-71, `UEns` 75-86,
`UStmt` 101-114, `URet` 118-123, `UTab` 127-135, `UFn` 182-194,
`UProg` 201-208), `grammatik/Grammatik/Parser/UebersetzeAllg.lean`
(`declOf` 147-196, `mkSig` 108-118),
`grammatik/Grammatik/Parser/UebersetzeAllg2.lean` (`lowerAllg` 938-949,
`progOfFn` requires 930-934, `pre108` 1190-1191).
Bridge: `bruecke/Bruecke/Quelle.lean` (full, 238 lines),
`bruecke/Bruecke/Pflichten.lean` (full, 300 lines),
`bruecke/Bruecke/Pruefung.lean` (full, 175 lines),
`bruecke/Bruecke/Simulation.lean` (notably `bruecke_koerperGutR` 222-233,
`bruecke_nutzer` 266-276), `bruecke/Bruecke/Start.lean`
(`startPflicht_wahr` 22-27, `lowerAllg_requires` 38-47),
`bruecke/Bruecke/Atomar.lean` (`declOf_kein_atomar` 27-28),
`bruecke/Bruecke/Nachbedingung.lean` (`wfU` 160, `post_iff` 164-204),
`bruecke/Bruecke/Realisierung.lean` (`postP` 249-251, `Rang` 244-246,
`stmt_statisch` 34-114).
Goal: `grammatik/Grammatik/Zielsatz/Spec.lean` (`Einheit` 1509-1515,
`Einheit.ws` 1522, `AkzeptiertSpec` 1606-1617, `LogikPflicht` 1653-1656,
`StartPflicht` 1665-1667, `NutzerPflicht` 1671-1673,
NOT CLAIMED 1360-1462), `grammatik/Grammatik/SperreSem.lean`
(`SperrInv.leer` 58), `grammatik/Grammatik/ZielOrtRahmenBeweis.lean`
(`axWahr` 70), `grammatik/Grammatik/ZielOrtInv.lean` (`invGutS_leer` 273),
`grammatik/Grammatik/KorrespondenzAllg.lean` (`korrOk` 558,
`korrOk_fnCorr` 1910), `grammatik/Grammatik/Budget.lean` (`totalCost` 109).

## 1. QUELLBRUECKE §1 audit: accurate with the exceptions below

§1.1-§1.2 names match the sources quoted. Three precisions:

1. `einheitAllg` (`Quelle.lean` 93-98) sets five fields explicitly
   (`P`, `S := SperrInv.leer`, `Q := axWahr`, `starts := startsAllg`,
   `sp0 := nullSp`) and leaves the sixth, `gestartet`, at its
   structure default `[]` (`Spec.lean` 1515). The document's
   "FRAGMENT DEFAULTS" list names `gestartet := []` correctly, but a
   reader of `einheitAllg` alone does not see it; the default is load-bearing
   for `Einheit.ws` (`starts ++ gestartet ++ gestartet`, `Spec.lean` 1522)
   and for every `FaedenVor.lean` pool lemma. Any full-unit identity claim
   must cite the default explicitly.
2. `declOf` defaults beyond "no globals": `Glob := Empty` (157),
   `marke/Inv := Empty` (178), `Ax := Empty` (181), `Reg := Empty` (186),
   `maskiert := fun _ => false` (166), `erlaubt := fun _ _ _ _ => false`
   (155), `gruende := 0` (`mkSig` 112), `konsumiert/produziert := []`
   (116-117). `QUELLBRUECKE.md` §1.1 lists the index carriers but not the
   all-false/all-empty rows; they matter for §3 below because an
   optimisation reading e.g. `maskiert` or `erlaubt` from a bridged unit
   reads a constant, not a source fact.
3. `startsAllg` (`Quelle.lean` 84-89) is filtering, not copying: unknown
   `entry` names (`fnIdx` error) are dropped to `none`, and known names
   whose `params != []` are dropped by the `if h` guard. A unit whose only
   entry is misspelled or parameterised therefore has `starts = []` and
   runs only the idle root. This matches the text ("unknown names filtered
   out", "parameterless entry roots only") and is sound (fewer roots is a
   smaller (d)), but a validator must bind `startsAllg u`, never a
   Rust-supplied root list; otherwise an empty-start unit and its bytes
   diverge silently.

`uebersetzeAllg_von_zeichen`, `uOf`, `nullB`/`nullSp`/`stimmigB`/`rangB`,
`zuBody`/`preExpr`/`postU`/`meetsU`, `nutzer_aus_quelle` /
`nutzerA_aus_quelle`, `emitLayLeer` / `ketteAllg`, and the `AkzeptiertSpec[X]` /
`Pruefer[X]` / `GabbroZiel[SC/Verbund]` shape statements were all found
where cited. No invented name was found in QUELLBRUECKE §1.

## 2. What source range / ownership / invariant evidence justifies at each reached site

The bridged fragment's evidence is thin by construction. Per reached site:

* **Function entry (the only range site).** `preExpr` (`Pflichten.lean`
  157-158) is `shapeConjuncts` (integer `.int lo hi` params only,
  `shapeOfTy` 142-144) plus one `true` per held lock. `wfU`
  (`Nachbedingung.lean` 160) is `Body.WF (shapeOfU u)` over table slots.
  So at entry the validator may assume: integer params in range, every
  slot field in its declared range. Nothing else: pointer params contribute
  no conjunct (dropped by `filterMap`), index params contribute none unless
  their `Ty` is `.int`, held locks contribute `true`. This justifies
  entry-anchored facts only.
* **Interior points (loop heads, load sites, hoist targets): none.**
  There is no flow-sensitive range invariant in the bridge. `meetsU`
  quantifies over all `ρ`/`s` satisfying the entry pre; the duty proof may
  establish locals, but no Lean-computed fact exports them. An
  optimisation that deletes a bound/trap check at an interior point on
  "source range" grounds therefore cites nothing the bridge computes.
  The only honest source-range inputs to SCFG layer C are the entry
  `preExpr` conjuncts and the slot typing `shapeOfU`; everything else must
  be validator-recomputed analysis, not source evidence.
* **Ownership / alias separation.** The bridge computes whole-function
  write sets only: `fn.schreibt : List String` (table names),
  `schreibtB` (checked against `u.tabellen`), `writesAt`/`mkSig.schreibt`,
  and `stmt_statisch` (each lowered stmt writes a declared carrier or
  calls a function whose writes are contained). There is no per-site
  footprint object, no extent, no alignment, no freshness mark, no
  immutability bit, no per-access lock covering. `declOf.geteilt` is
  `!needs.isEmpty` but `Glob` is `Empty`, so on a bridged unit it is dead
  code. Consequence for IR-VALIDIERUNG §3 item 3: the three global
  interleaving conditions (exclusive ownership, held-lock stability,
  immutability) have NO source-computed witness on the bridged fragment
  today. `heldAt` + `haelt_eq` give per-function held locks and
  `preExpr` erases them to `true`; that tells the validator a lock was
  held at entry, not that it is held continuously between two interior
  accesses, and not that every writer in the unit respects it (the latter
  needs whole-unit effect exports that do not exist yet — see §8).
* **Invariants.** `einheitAllg` fixes `S := SperrInv.leer`
  (`⟨fun _ => [], fun _ _ => true⟩`, `SperreSem.lean` 58) and the bridge
  discharges `LogikPflicht` via `invGutS_leer` (`Simulation.lean` 254).
  Every invariant leg (`invRueck`, `invGrund`, `invRuhe`, `invSicht`,
  `sperrWechsel`, `sperrSicht`, `spawnSicht`) is vacuous on a bridged unit.
  No invariant-derived rewrite (stable protected loads, invariant-hoisted
  checks, lock-protected CSE) is justified by source evidence on this
  fragment. See §5 for the exact NOT CLAIMED boundary.

## 3. Metadata fields still free or defaulted (full-unit table)

For `E = einheitAllg u P hn`:

| Field | Value | Source-computed? |
|---|---|---|
| `E.P` | `P` from `uebersetzeAllg` | yes (T3) |
| `E.S` | `SperrInv.leer` (no places, `true`) | no — default |
| `E.Q` | `axWahr` (`fun _ _ _ => true`) | no — default |
| `E.starts` | `startsAllg u` (filtered entries) | yes, filtered (§1.3) |
| `E.sp0` | `nullSp u h` (zero slots, `globs := nomatch`) | yes iff `nullB`; globals vacuous |
| `E.gestartet` | `[]` by structure default | no — default |

For `D = declOf u`: `Tab/Field/Lock/Fn` index carriers yes; `Glob`,
`Inv`, `Ax`, `Reg`, `Marke` empty; `typ` from field ranges yes;
`erlaubt` false; `maskiert` false; `braucht/needsAt` from tables (present
but unexercised without globals); `gruende` 0; `requires` wahr;
`haelt/schreibt` from `held`/`schreibt` yes; `konsumiert/produziert` empty.
QUELLBRUECKE §§1.2/4 correctly book "compute every field or prove identity
field by field" as open; the table above is the precise delta. In
particular `E.P = P` alone never identifies `E` (§4 schema's `hE` must stay
full-unit identity).

## 4. False user-contract synthesis: what is refused vs erased

* **Refusals (safe, never synthesis).** `postU … .getD False` (`postP`,
  `Realisierung.lean` 249-251; `meetsU`, `Pflichten.lean` 294-298):
  a `none` promise (any `ensures` clause outside the fragment, arithmetic
  inside `ensures` per `ensSide` 101, `slotB`/`tabB` per `ensExpr`,
  `assignB`/`assignTabB`/lock stmts per `stmtBody`, `bool` return per
  `zuBody`) makes the duty `False`-flavoured, i.e. unprovable — a refusal,
  not a weaker duty. `hyps … | none => False` (`Pflichten.lean` 291):
  a call to an unknown name makes every duty calling it unprovable.
  `keinBoolB`/`postB`/`oldsB`/`schreibtB`/`artB`/`namenB`/`freiB`
  (`Pruefung.lean` 18-58) refuse bool places, out-of-fragment posts,
  >9 `old`s, undeclared writes, mismatched pointer/index kinds, duplicate
  or `result`/`old#i`-colliding params. `post_iff` is `↔` under exactly
  those hypotheses (`Nachbedingung.lean` 164-171), so no refused shape
  leaks into `EnsAmRueck`.
* **Erasures (sound only in the stated direction).**
  `preExpr` maps each held lock to `true` and drops non-`.int` params.
  Dropping a conjunct weakens the pre (duty harder) — safe for soundness,
  unsafe as an optimisation licence: the validator may NOT read back a
  pointer extent or a lock fact from `preExpr`. `conv _ _ a` reads as its
  operand (`sideExpr` 83); the range-fit check lives in the lowering
  (`lowWertAt`), not in the duty — reusing the value without the fit
  check would be synthesis. `resultClause` is absent when `ergebnis = none`
  (`Pflichten.lean` 237-238); a `wert` return with no declared range then
  promises nothing about the answer — the duty is weaker there, and
  `post_iff`'s `resultClause_wahr` closes it only because G's own answer
  range is equally unconstrained. An optimiser may not invent a range for
  such a value.
* **Name capture closed.** `oldName` 0-8 (`Pflichten.lean` 53-55),
  `oldNamen`/`freiB`/`oldsB` (`Pruefung.lean` 35-44): at most 9 `old`s,
  params named `result`/`old#i` refused. A rule that substitutes `old#i`
  or `result` as ordinary names would capture; the bridge refuses the
  program instead. Any SCFG binder discipline must preserve this.

Net: the bridge never synthesises a user contract — outside-fragment
duties are unprovable by construction. The hazard for optimisation is the
reverse: reading an erasure (`true` for a lock, absent conjunct for a
pointer, absent answer clause) as a positive fact.

## 5. Unavailable writer and held-section invariants

`Spec.lean` NOT CLAIMED 1383-1391 (read verbatim): no table/group
invariant "at a point where an unfinished thread is inside a function that
writes one of its carriers", and no lock invariant "INSIDE its holder's
section (the holder may break it; claimed is that no other thread observes
the protected carriers there, and that every acquire and release sees
it)". On top of that, bridged units have `S = leer`, so even the
return-side invariant legs are vacuous there.

Consequences for `X86/InvariantenOpt.lean` (lane 288):

* No proposed rule may assume an invariant holds inside a running writer
  or inside an arbitrary held section. The only invariant facts the goal
  provides are at returns (`invRueck`/`invGrund`), at quiescence/observers
  (`invRuhe`/`invSicht`), and at lock moves (`sperrWechsel`/`sperrSicht`) —
  and none of them is populated by `Pflichten src` today.
* Counterexample shape (writer break): table `T` with invariant
  `I := (a = b)`; writer body `store a 1; <hoisted load of b here>; store b 1`.
  Between the two stores `I` is broken by design. A rule "hoist the
  invariant-protected load of `b` above the store to `a` because `I` holds"
  changes the observed value when a concurrent thread (or the writer's own
  pre-state) is considered, and is unsound. Same shape for a lock section:
  holder writes protected carrier twice with a temporary break; moving a
  reader (even the holder's own second read, if the rule claims "protected
  ⇒ stable") across the first write is unsound inside the section.
* Any invariant-derived optimisation on the bridged fragment must therefore
  be refused until (i) the unit carries a non-`leer` `S` computed from
  source with per-field `traeger` evidence (`InvTraeger`), and (ii) the
  rule cites the exact leg (`invRuhe`/`invSicht`/`sperrWechsel`/
  `sperrSicht`) at its exact site. `IR-VALIDIERUNG.md` §3's motion rules
  are compatible with this only if their "validator-decided" side is
  understood as "refuse on `S = leer`".

## 6. Program-name special cases

Must stay off the trust path (QUELLBRUECKE §5 is accurate and complete
for the files read): `corrlean.rs Cert104` rows for `einzahlen`/`lies`,
`Cert104`/`certOkG`/`refD`/`GRow`/`printEnd104`/`ZeugnisStmt104b`,
`schlusssatz_104`/`Kette104*`/`kette_104`/`kette_108`/`gPB`/`lowerProg`/
`gEL104`/`refCProg`, `GenOblig*`/`Export*`/`Instanz*`/`Korpus*`/
`KetteMehrfadenC`/`CText*`, `REGISTER.txt`/`Zertifikate.lean`,
`*_zeuge` beyond inhabitation, C-form census/`MARKE_EMIT*`.
Not name-specific (generic, may be used): `fnSuch`/`ptrTab`/`ptrParam`
lookups by string (they resolve names, they do not branch on them);
`fnNr := Fin.val` (positional, printer agrees by construction);
`calleesOf` sorted/deduped (printer order, proved against `mem_calleesOf`);
`oldName`/`result` binders with `freiB` capture guard; `pre108`
(`stripTopNeben` drops `concurrent` items — roots move to `wurzeln`/`starts`
— and `normTopU32` widens bare `u32`; both are generic preprocessing, not
per-program); `uExp104`/`src108` pins (witnesses exercising generic
theorems, e.g. `lowerAllg104fragment` by `decide`).

## 7. Correspondence directions; proved theorem vs schema

Proved (may be cited; each with its file):
`uebersetzeAllg_von_zeichen` (parse fidelity, `Schlusssatz.lean` 93),
`lower_of_uebersetze` + `uOf_eq` (`Quelle.lean` 109/137),
`stimmig_of`/`rang_of`/`null_bereich` (decided-shape soundness),
`post_iff` (`Nachbedingung.lean` 164), `bruecke_koerperGutR` /
`bruecke_keineLogik` / `bruecke_logik` / `bruecke_nutzer`
(`Simulation.lean`), `nutzer_aus_quelle` / `nutzerA_aus_quelle`
(`Quelle.lean` 144/156) via `nutzerPflichtA_ohne_atomar` over
`declOf_kein_atomar`, `ketteAllg` (table-free closed C chain),
`korrOk_fnCorr` (C rows only), `gabbro_ziel[_sc]` (model goal).
Schema (proposed, NOT proved, must not be cited as theorems):
`valX86_sound`, `schluss_x86_aus_verfeinerung` (labelled internal),
`schluss_x86`, `lowerOk`, `check_C`, `layoutOk`, `X86Verfeinerung`,
`DutyExport`/`EffectExport`/`AtomicExport`/`FpExport`/`CostExport`/
`LowerMap`, SCFG syntax/semantics/checkers/rule register. The grep in §0
is the evidence of absence.
Direction discipline (QUELLBRUECKE §4 review-repair, endorsed):
the delivered closing theorem takes NO refinement premise; per-access
refinement is DERIVED from `valX86 E bild = true` via generic
`valX86_sound`. The composition lemma taking `hR` is internal plumbing
only. The check binds the FULL unit (`valX86 E bild`, with
`hE : E = einheitAllg u P hn`), never `P` alone and never duties alone.
Counterexample shape (free metadata): checker Bool proved about unit
`E₁` (e.g. `S = leer`) + duties proved about `E₁` + bytes validated
against `P` of a different unit `E₂` (e.g. with lock invariants or
non-empty `gestartet`) — concluding `ZielFX` for either unit is unsound.
The schema's full-unit identity premise exists exactly to refuse this.

## 8. IR-VALIDIERUNG §5.1 audit: none of the six exports exists yet

| Claimed interface | Lean status | What exists instead |
|---|---|---|
| `DutyExport` | absent | `preExpr`/`postU`/`meetsU`/`hyps`/`calleesOf` per function (`Pflichten.lean`); no per-site check/assume marker export |
| `EffectExport` (`writes`/`gwrites`, `haelt`/`boden`) | absent as an export | `Signatur.schreibt/gschreibt`, `writesAt`, `heldAt`, `stmt_statisch` (whole-function sets); `Glob` empty so `gwrites` vacuous; no `boden`/floor export found on this path |
| `AtomicExport` | absent | `NutzerPflichtA`, `GeteiltV/GeteiltA`, `VertragsFrei`, `N484` (model side); bridge side vacuous via `declOf_kein_atomar` — no atomic-bearing duty exists |
| `FpExport` | absent | IEEE kernel model (`Gleitkomma*.lean`, cited in Spec NOT CLAIMED 1380-1382); no per-site rounding-scope export on this path |
| `CostExport` | absent as an export | `Budget.lean Op.cost/totalCost` (level (a) source); levels (b)/(c) and any transfer absent |
| `LowerMap` (source-node → SCFG anchors) | absent | no SCFG lowering; `zuBody` is Body-anchored, not SCFG-anchored |

The §2.4 soundness statement is therefore a requirements statement, not a
description of available data. Each phase-B owner must build its export as
a Lean computation from `UProg`/`P` with a `decide`-checked consumer,
exactly as `korrOk` consumes `KCert` — not as a Rust-attached hint the
validator trusts.

## 9. Per-family verdicts against IR-VALIDIERUNG §3

1. Constant/copy prop: entry shapes only (§2). Rule needs validator-
   recomputed `avail` + dominators; source contributes entry conjuncts.
   Sound direction preserved; no interior source fact may seed `avail`.
2. DCE incl. faults: `zuBody` preserves order; purity must be decided from
   token threading + stop classes. Budget-stop timing (§3 item 11 ghost
   accounting) is open — re-summing `totalCost` is bookkeeping, not a
   preservation proof. Agree with the document's OPEN marking.
3. CSE/redundant loads: REFUSE all shared-load reuse on the bridged
   fragment. Token-order check is necessary but not sufficient; none of
   the three interleaving evidences is source-computed (§2). Local-object
   disjointness alone is explicitly insufficient across publication/
   fence/acquire-release — endorsed. Counterexample: two loads of `x`
   with no intervening token op in one thread, first load before a
   release that publishes `x`, reuse after an acquire in another thread —
   token threading identical, GX executions differ.
4. Inlining: no ghost call/return events exist; `FolgeG` order has no
   bridge witness. `requires` is `wahr` so entry checks are vacuous, but
   `ensures`/footprint/floor containment and fresh renames still need the
   map. Refuse cross-call propagation/CSE/DCE without layer-C exports.
5. Regalloc/spills: no spill objects, no freshness lemma on this path
   (lane 289 owns it); `declOf` has no address-taken notion. Refuse until
   the freshness⇒disjointness⇒commutation lemma against the lane-274
   relation is proved. Private-spill reasoning against abstract memory
   would be unsound.
6. Peephole: no rule register exists; each rule needs a generic lemma over
   arbitrary operands with flags/fault/cost side conditions re-decided.
7. LICM: refuse hoisting of possibly-faulting ops and of all token ops on
   shared accesses. Entry ranges do not travel to loop heads; the
   non-faulting premise has no source witness interior to the loop.
8. Unrolling: needs explicit `k` + trip evidence + remainder map; all absent.
   Bounded-only; no new back edge.
9. SIMD: endorse total refusal until a generic vector rule for fault order,
   visibility, tearing, FP control status is proved. The "easy candidate"
   stays refused before its proof — prioritised queue position is not
   admission. Additionally, width/alignment/extent source facts for vector
   widths do not exist on the bridged fragment.
10. Cross-cutting FP: no reassociation/fusion/precision/mode-scope motion;
    reference is lane 278's mapping; uncovered = refused. Endorsed.
11. Cross-cutting stops/atomics/locks/costs/progress: stops never
    deleted/introduced/reclassed; orderings never weakened; lock regions
    never crossed except pure SSA under token with lock held at both ends;
    three cost levels separated with (c) OPEN with lane 278 and ghost
    budget correspondence OPEN; declining never weakens a bound. Endorsed
    without exception. Note: (a) re-sum mismatch is a refusal, not a
    soundness argument.

§7 non-goals (speculative fault motion, cross-thread/cross-publication
reordering, atomic/fence/lock motion, FP reassociation, interprocedural
facts without a map, address-dependent rewrites, profitability as
legality, whole-program/link-time, premature vectorisation) are all
correctly marked non-goals; each has at least one concrete unsound
instance in §10 or §9 above.

## 10. Counterexample shapes (one per unsound rule)

* C1 (metadata substitution): as §7 — `E.P = P` proved, bytes checked
  against `P`, conclusion drawn for `E` with different `S`/`Q`/`starts`/
  `sp0`/`gestartet`. Refused by full-unit `hE`.
* C2 (assumed refinement): closing theorem with `hR : X86Verfeinerung`
  as a public premise instantiated by "the backend is correct". This is
  the defect QUELLBRUECKE §4's repair already removes; any reintroduction
  under a new name (e.g. `simOK`, `relates`, `models`) is the same defect.
* C3 (shared CSE): §9 item 3 shape.
* C4 (writer invariant): §5 shape.
* C5 (interior range): function with entry `x in 0..255`, call to `f`
  that may write `x`'s carrier (whole-function `schreibt` contains it),
  then `narrow`-guarded use of `x` after the call deleted on "entry range"
  grounds. Entry range does not survive the call; deletion is unsound.
* C6 (lock-erasure): `preExpr`'s `true`-per-held-lock read back as "lock
  L held at this interior point", used to justify protected-load CSE
  between two points where L is in fact released and reacquired. Entry
  holding does not imply continuous holding.
* C7 (capture): callee param named `result` or `old#3` unified with the
  binder of `clauseAux`; refused by `freiB` at the bridge, must be refused
  by any SCFG binder layer too.
* C8 (atomic payload): unguarded plain hand-off (`publish` payload,
  Spec NOT CLAIMED 1378-1379, OFFEN O25 residue) treated as message-passing
  ownership transfer for CSE/ownership purposes. The checker refuses it
  (`N484` footprint rule admits no shared atomic in a contract); an
  optimiser may not admit through the back door what the checker refuses
  at the front.

## 11. Claim ledger

May be said: the §0 definitions were read; QUELLBRUECKE §1 is accurate
subject to §1 precisions; source evidence on the bridged fragment is
exactly §2 (entry ranges, whole-function writes, vacuous invariants);
§3 tables every defaulted field; §4 separates refusals from erasures; §5
marks writer/held-section invariants unavailable with NOT CLAIMED anchors
and a concrete unsound shape; §6 keeps per-program artefacts off the trust
path; §7 separates six proved bridge/checker/model theorems from seven
unproved schema names (verified absent); §8 records all six SCFG exports
absent with their existing substitutes; §9/§10 give per-family verdicts
and counterexample shapes.
May NOT be said: that any source-to-SCFG lowering, SCFG checker, rule
lemma, TSO-bridge table entry, decoder, validator, cost transfer, or
source-to-byte closing theorem exists or was verified here; that any
existing certificate validates bytes; that any per-program rule is
generic; that `IR-VALIDIERUNG.md`'s §2.4 statement is proved; that the goal
covers a program the validator has not accepted. No source-to-IR or binary
closure claim is made.

*CUTS: docs-only review. No Lean theorem proved or checked by build; no
decoder, execution, TSO, layout, validator, template, or cost fact
established. File-existence grep is the only mechanical check (schema
names absent). All definition claims are by reading the cited lines; any
line drift after this commit invalidates the anchor. Follow-up belongs to
phase-B owners per QUELLBRUECKE §7 and IR-VALIDIERUNG §5.2; this review
does not pre-empt their proofs.*
