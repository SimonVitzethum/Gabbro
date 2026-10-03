# MUSE-REPORT-1020: Exact review of author 870 (alias commutation rule)

CANDIDATE: 870 7e51b5f8ae59c2dc02351d8ee44c8487b24704a5
VERDICT: ACCEPT

## Review basis

Pinned snapshot inspected at `.tmp/review/SNAPSHOT.json` (head
`7e51b5f8ae59c2dc02351d8ee44c8487b24704a5`, base `b040b155`, clean tree):
`OWNER-TASK.md`, `MUSE-REPORT-870.md`, `PATCH.diff` (3 files only:
`MUSE-REPORT-870.md`, one import line `Grammatik.X86.OptAliasCommute` in
`grammatik/Grammatik.lean`, new module
`grammatik/Grammatik/X86/OptAliasCommute.lean`), and `BUILD-EVIDENCE.json`
with the complete stepwise probe history. I read the new module in full
(405 lines). Base `b040b155` equals this clone's parent commit, so the
snapshot sits directly on current master. I did not re-execute the build
(this lane owns the report only and may add no source to the clone); the
build facts below come from the author's recorded evidence, cross-checked
against the file content for consistency.

## Build and axiom evidence (recorded, consistent)

- Final `./lean-bau`: `Built Grammatik (511 jobs)`, success, after one
  genuine red iteration (name collision `aliasZulassen` with
  `X86/OverlapRefusal`, repaired by renaming to `aliasCommuteZulassen`;
  probe names renamed the same way). The red-then-green history is credible
  development evidence, not a pasted result: intermediate probes show real
  errors (`rewrite` miss at line 122, unsolved `spur.length` goal at 170,
  `Decidable` synthesis failures, `List.mem_cons_self` arity) each followed
  by a green re-probe.
- `#print axioms` for every main theorem: refusals and probes at
  `[propext]` or no axioms; value core at `[propext, Quot.sound]`;
  `OptAliasCommute_verbindung` at `[propext, Quot.sound]` and its
  `_zeuge` companion at `[propext, Classical.choice, Quot.sound]`.
  No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in the file.
- `gabbro_ziel` family still prints exactly
  `[propext, Classical.choice, Quot.sound]` after the change.
- Scope discipline held: no new diagnostic/gift/example/CLI numbers, no
  MARKE changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files touched.

## Substantive findings

1. Real vocabulary, no invented semantics. The rule is stated over the
   actual `Syntax`/`Semantik` `World.storeSlot` / `World.schreibSlot`
   fragment and the real declared cost `CostSummary.expandBound`, per the
   owner task's fallback while no accepted shared IR exists. Value lemmas
   (`storeSlot_hit`, `storeSlot_miss`, the four commute read-backs) are
   over arbitrary `Wert` of arbitrary slot type, floats included, with no
   rounding or width change anywhere in the commute path.
2. Refusals are loud and cover the DESIGN failure case. Fence/lock/
   acquire-release between the sites refuses even with full token evidence
   (`aliasVerweigert_schranke`); shared motion without interleaving
   evidence refuses (`aliasVerweigert_anteil`); name inequality alone is
   not disjointness (`aliasVerweigert_fuss`); reordered token order
   refuses (`aliasVerweigert_token`). A refused site keeps its certified
   unoptimised translation; nothing becomes a warning. No `ensures`
   derived; no faulting form speculated above its guard (two plain
   stores only, both total).
3. Every premise of the connection theorem is used by its proof
   (`hDisj`/`hz` feed `hNe`, `hStab`/`hz` feed `hS`, `hFloat`/`hz` feed
   the IEEE conjunct, `s`/`src`/`op`/float indices/`Λ` each land in
   their conjunct). The side conditions are validator-decided
   (`admission = true -> fact`), exactly the shape the owner task
   demands; the disjointness is assumed-from-admission, not computed,
   and the certificate shape (local record plus recomputed layer-B/C
   citations) is named in the section-6 comment.
4. Witness is joint and non-degenerate.
   `OptAliasCommute_verbindung_zeuge` instantiates all premises together
   on `refD` (whose `einzahlen` writes its table), stores `7`/`5` at
   disjoint indices `0`/`1` under a held lock, beside reached F-machine
   run `MB` with a memory-changing step. No degenerate empty-run or
   table-free witness.
5. Bounded weaknesses, all disclosed in CUTS and none verdict-changing:
   (a) the cost conjunct is definitional order-independence
   (`expandBound s src = expandBound s src` by `rfl`); the formal
   level-(c) work bound stays OPEN on lane 278 — appropriate for pure
   motion of identical block shape, and honestly cut;
   (b) no full-frame equality beyond the two touched slots (noted as
   following the same `storeSlot_miss` shape);
   (c) single slot family only, no cross-table/field citation;
   (d) correspondence stops at source worlds and `gleitRechne` values:
   no byte forms, no TSO/GX bridge, no silicon/ABI/loader claim.
   The claim stays inside the proved boundary throughout.

## Bounded acceptance

ACCEPT for the source-world rule lemma `OptAliasCommute_verbindung`
with its witness, refusals and probes: value/fault/observation/IEEE/
lock/cost preservation for commuting two proved-disjoint slot stores
under validator-recomputed admission, with the DESIGN failure case
refused. The acceptance explicitly does NOT cover byte-level lowering,
TSO/concurrency-bridge behaviour, cross-table motion, or machine-work
bounds — all cut in the file. No repairs required; no guarantee
weakened; no desired-correctness premise smuggled in.

## CUTS (of this review, not the candidate)

- No independent Lean re-execution (report-only lane; build facts are
  recorded evidence plus full-content cross-read).
- Integration merge itself (`muse/870` into master) not performed here;
  base matches master tip parent, single import-line delta is in the
  auto-resolvable class.
- Downstream consumers (lowering lane, validator citation layer-B/C)
  remain open by design.
