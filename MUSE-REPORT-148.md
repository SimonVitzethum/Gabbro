# MUSE-REPORT-148 (lane 148, T2 groundwork: rule the open C forms)

## What was done

New file `grammatik/Grammatik/ErhaltungT4.lean` (registered as
`import Grammatik.ErhaltungT4` in `grammatik/Grammatik.lean`), containing:

- A header comment with the full measurement: all 31 `OffeneForm`
  constructors of `Erhaltung.lean` against the T4 correspondence lemmas
  (`CFormen.lean`, `CFormenI.lean`, `CFormenM.lean`, `CFormenH.lean`),
  every lemma name grep-verified on 2026-09-13.
- 16 `..._steht` theorems (one per covered slot, some shared): the
  slot's decided table row, closed by `decide` (data, `[propext]` only).
- 19 `bridge_...` theorems, one per covered slot/direction. Each bridge
  conjoins the covering T4 lemma applied to its full premise list
  (every premise used) with the slot's decided row. Where the emitted
  shape differs from the lemma shape, the adapter is named in the doc
  string (`bedingt` via generator `?:`-to-`if`, `schrittStmt` via
  `++`-to-`+= 1`, `syscallStub` via stub-is-`.ext` with assumption
  shape `AxCorr`, `cEnum` via enum-to-literal elaboration, `boolTyp`
  via `_Bool`-as-`0`/`1` value convention, `adressVon` via `PtrTo` as
  the provenance statement, `pfeilZugriff` via `slotA`-plus-load).

Exact new theorem names: `logUndOder_steht`,
`bridge_logUndOder_und`, `bridge_logUndOder_oder`, `boolLit_steht`,
`bridge_boolLit_wahr`, `bridge_boolLit_falsch`, `boolTyp_steht`,
`bridge_boolTyp`, `cEnum_steht`, `bridge_cEnum`, `deref_steht`,
`bridge_deref`, `bitNicht_steht`, `bridge_bitNicht`, `cSizeof_steht`,
`bridge_cSizeof`, `cConst_steht`, `bridge_cConst_lese`,
`bridge_cConst_schreib`, `adressVon_steht`, `bridge_adressVon`,
`voidTyp_steht`, `bridge_voidTyp`, `bedingt_steht`, `bridge_bedingt`,
`zeigerIndex_steht`, `bridge_zeigerIndex`, `pfeilZugriff_steht`,
`bridge_pfeilZugriff`, `zusammZuweisung_steht`,
`bridge_zusammZuweisung`, `schrittStmt_steht`, `bridge_schrittStmt`,
`syscallStub_steht`, `bridge_syscallStub` (35 total).

## Measurement table (every open form)

COVERED (16 slots, bridge in the file):
`logUndOder` (`ecorr_und` CFormenM:175, `ecorr_oder` CFormenM:196),
`bitNicht` (`ecorr_bnot` CFormenI:738),
`boolLit` (`ecorr_wahr`/`ecorr_falsch` CFormenI:383/387),
`boolTyp` (`truth_b2i` CFormenI:374),
`deref` (`ev_ld` CFormenM:36),
`cSizeof` (`ev_sizeofQuot` CFormenM:258),
`cConst` (`constTab_read` CFormenM:319, `ro_store_stuck` CFormenM:310),
`adressVon` (`ptrTo_named` CFormenM:54),
`voidTyp` (`retCorr_none` CFormenM:411),
`bedingt` (`scorr_ite` CFormenI:1133),
`zeigerIndex` (`ecorr_byteGuard` CFormenH:521),
`pfeilZugriff` (`ecorr_slotNamed` CFormenI:883),
`zusammZuweisung` (`scorr_plusGleich` CFormenI:986),
`schrittStmt` (`scorr_plusGleich`, plus `cas_success`/`cas_failure`
CFormenH:128/162 for the untouched-CAS leg, referenced not bridged),
`syscallStub` (`scorr_axiomCall` CFormenH:205),
`cEnum` (`ecorr_lit` CFormenI:378).

UNCOVERED (15 slots, reason in the file header):
`zeigerArithmetik` (price is a refusal; lemmas cover only in-bounds
evaluation), `cInclude`, `cTypedef`, `cDefine`, `cAttribut`, `cInline`,
`typOfErw`, `wennGnuC`, `statikAssert` (preamble/alias/macro/
attribute/compile-time-only: no evaluation), `doubleTyp`, `floatTyp`
(no floats in the C semantics; `CIT`/`CVal` are integer-only),
`schleifeStmt` (`retry` explicitly uncovered, CFormenI:2170),
`abbruchStmt`, `fortStmt` (no `StmtCorr` produces bare `.brk`/`.cont`;
`scorr_leave` lowers to `.goto`; break/continue live only inside
generated skeletons), `unerreichbarBuiltin` (no `Exec` rule, no lemma).

## Verification

- `./lean-probe grammatik/Grammatik/ErhaltungT4.lean`: 0 errors.
  `#print axioms`: `..._steht` on `[propext]`; bridges on
  `[propext, Classical.choice, Quot.sound]`, except `bridge_boolTyp`
  (`[propext]`), `bridge_deref` (`[propext]`),
  `bridge_cConst_schreib` (`[propext, Quot.sound]`). No `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`.
- `./lean-bau` (full project): `Build completed successfully (113 jobs).`
- Rule 13: no bridge has a premise universally quantifying over
  `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`. Correspondence
  hypotheses (`ExprCorr`, `BlockSem`, `ArgsTo`, `AxCorr`) are for fixed
  terms; the `∀ t`/`∀ g` frame premises of `bridge_syscallStub` range
  over table/global indices and come verbatim from `scorr_axiomCall`.
  Hence no `_zeuge` companion is owed. No rule-13 TARGET (`ZEUGE:`)
  was named in this task.
- Rule 4: each bridge concludes a conjunction present in no premise
  (derived correspondence + decided row); all premises are used.

## corrcert.rs: what the certificate prints vs what lemma recheck needs

Today (`crates/gabbro-check/src/corrcert.rs`): per-run JSON
`{"sites":[{"gabbroSite":N,"cSite":N,"form":"word"}]}` beside the C
output (`<stem>.corrcert`), words from `CForm::as_str` (mirrors Lean
`cformWort`), plus the four recomputed legs
(`vollstaendig`/`geordnet`/`geschlossen`/`ohne_extra`, mirroring
`vollB`/`geordnetCertB`/`geschlossenB`/`ohneExtraB`). Hook landed only
for top-level items (`emittiere_mit_corr`/`korr_form`, one row per
lowered item of named form, in lowering order, byte-identical C);
statement/expression-level rows are booked but not threaded.

To be rechecked by the T4 lemmas (design only, no Rust touched), each
row would additionally have to carry, in checkable form: (a) the LEMMA
name, not just the form (19 forms vs ~60 lemmas: a `zuweisung` row
could be `scorr_assignVar`, `scorr_plusGleich`,
`scorr_assignSlotNamed`, ...; the rechecker cannot pick the lemma from
the form word); (b) the lemma's instantiation: the concrete Gabbro
term with type indices, the concrete `CX`/`CS` term, and the side
conditions the lemma consumes (`K.loc` mapping, `CIT` computation
type, `declOk`/`tyFits`, `darf`, layout facts `tnr`/`fnr`/`off`/
`count`/`ssize`, `SameML` links); (c) world/memory snapshots (or
hashes) chaining consecutive rows, because `StmtCorr`/`ExprCorr`
conclude from `corrW`/`EnvRel` pre-states and the simulation composes
only if the snapshots chain — per-row isolated recheck proves nothing
about the run. Concretely: keep `<stem>.corrcert` as the site skeleton
and add a keyed `<stem>.corrbeleg` sidecar `(gabbroSite, cSite) ->
{lemma, gabbro-term, c-term, seitenbedingungen, vor/nach-welt-hash}`.
The hard part is (c), not (a)/(b).

## What remains open

- The 15 uncovered slots need C-semantics-side work outside this lane:
  float types, `retry`/`while` correspondence, skeleton-internal
  break/continue correspondence, `unreachable`, and (by decision, not
  proof) the erased/trust items.
- Per-run certificate-to-lemma linkage (the `(c)` gap above) is design
  only, as tasked.
- The `schrittStmt` CAS leg (`cas_success`/`cas_failure`) is referenced
  in a doc string, not bridged; a second bridge conjoining the CAS
  correspondence is a one-theorem follow-up.

## Where the task statement is wrong

The task says `Erhaltung.lean` lists "about 30 C forms whose
correspondence is undecided" and asks for "the bridge lemma that closes
the Erhaltung.lean obligation". The formal obligation per slot
(`entschieden` of its row) is already closed without any T4 lemma:
`tafel_geschlossen` proves `satz_tafel` by `decide` (0 slots `offen`;
the file's own §5 prose saying otherwise is stale). What is undecided
is price ADEQUACY (cut C5, stated in the file). The bridges built here
close the adequacy gap per slot (admitted shape corresponds + row
stands); no lemma can or needs to prove the decidable row from a
simulation, and the file's CUTS say so plainly. Count is 31 slots
(30 census + `syscallStub`), 16 covered / 15 uncovered.
