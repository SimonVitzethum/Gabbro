# MUSE-REPORT-1030: Exact re-review of author 880 (copy coalescing rule, repair resubmission)

CANDIDATE: 880 1bd04eb13b4c28cd1eaa5e6d97b1615c0137a9d5
VERDICT: ACCEPT

Acceptance is bounded; the bounds are stated in "Accepted as" below.

This supersedes the previous verdict (REPAIR on 880 `5bce2fe6…`). The new
pinned snapshot was inspected in full; every previous finding was re-checked
against the changed proofs. Do not use the stale snapshot: only the HEAD above
is reviewed here.

## Scope verified (new snapshot)

- `.tmp/review/SNAPSHOT.json` pins author 880, head
  `1bd04eb13b4c28cd1eaa5e6d97b1615c0137a9d5`, base `b040b155` (matches this
  clone's master), same three files, clean tree.
- PATCH touches exactly those three files (one import line in
  `grammatik/Grammatik.lean`, the now 533-line new file, the author report).
  No MARKE_EMIT, numbers, source/checker/Spec/goal/emitter, or friend-reserved
  optimiser files touched.
- DESIGN citation unchanged and correct (§7 example 1 + "Layout / allocation"
  row failure case).
- Hygiene re-verified by inspection of the exact new file: no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `intro _`, or `have _ :=`
  (grep hits are prose "admitted" only); every premise is consumed by its
  proof; CUTS block and `#print axioms` for all 15 items present.
- Build evidence: staged `BUILD-EVIDENCE.json` ends with `./lean-bau`
  `== exit 0`, `Build completed successfully (511 jobs)`, and axiom prints
  within `[propext, Classical.choice, Quot.sound]` for every theorem
  (`kopieRein*` at `[propext]`; `kopieBind_liest*`, connection and witness at
  the full standard set, same as accepted sibling 860). The evidence also
  shows the genuine red-then-green repair path (implicit-`Λ`, unsolved-goal,
  and one transient `sorryAx` leak in an unfinished intermediate step, all
  disclosed by the author and absent from the final green probes). No source
  is owned by this lane, so no rebuild was run here; verification is exact
  file inspection plus this staged evidence.

## Previous findings: all addressed

- F1 (conclusion restated premises) — RESOLVED via R1. The connection is
  restated over a CONCRETE copy shape: the copy is `Expr.var x`, not an
  arbitrary expression. C1 is derived from the COMPUTED local var-read fact
  (`eval _ (.var x) _ ρ = ρ.get x`, by `rfl`, not a premise) plus the avail
  equation — it is no longer an instance of an assumed expression equation.
  The orte equality is DERIVED (`kopieRein_klingt` + `var`-orte `rfl`), not
  assumed. Only C3 still feeds a premise (`hW`) to a helper, as before.
- F2 (certificate unlinked) — RESOLVED via R2. Two proved
  admission-to-semantics instances exist: `kopieRein_klingt` (decided purity
  implies empty `orte`, by induction with a conservative `false` catch-all
  over memory/globe/device/binder/`fall` forms) and `kopieBind_liest` (var
  read of the just-bound slot IS the bound value, `rfl`). The remaining
  assumed premise `hVerfuegbar` is exactly the semantic content of
  avail+dominance (the environment holds the dominating value), and the
  other, `hRein`, is a decidable syntactic check. CUTS books the per-site
  discharge of both from recomputed avail/dominance as an explicit OPEN
  obligation owned by the validator/lowering lane, and the witness NOTE
  states its `rfl` discharges do NOT count as that discharge.
- F3 (overstated wording) — RESOLVED via R3. The section-4 doc comment
  carries an explicit ASSUMED-vs-PROVED split; the author report withdraws
  the unqualified "proves value preservation" sentence.

Kept from before (re-verified): five Bool refusal lemmas with probes,
`coalWort` round-trip, joint non-degenerate witness
(`refEin_schreibt`, `refB_erreicht`, `refB_schreibt`), new negative probe
`probe_kopieRein_slot` (slot read refused) and purity probe
`probe_kopieRein_add`, plus bridge companions `kopieRein_klingt_zeuge` and
`kopieBind_liest_zeuge` with the table-writing conjunct.

## Accepted as (bounded acceptance)

The proved core (concrete `var`-shape connection, derived orte equality,
refusals, word image, joint witness) with the explicit open residue:
per-site `hRein`/`hVerfuegbar` discharge from recomputed avail/dominance
(validator/lowering lane). No float `Endblock` window, no multi-copy
chains/2-cycles, conservative purity, no level-(c) machine-work bound, no
silicon/TSO-GX/ABI claim, spill-slot copies with `SpillPrivate` — all
recorded in CUTS. No byte-level or hardware-state claim is made, correctly.

## Last build result

No build owned by this lane (report-only review). Upstream evidence cited
above: `./lean-bau` exit 0, 0 error lines, 511 jobs, standard `gabbro_ziel`
axiom set; `Spec.lean` untouched.

## What remains open

- Validator/lowering lane: per-site discharge of `hRein`/`hVerfuegbar` from
  recomputed avail/dominance (named open obligation, not this candidate).
- Program-level source-to-final-bytes validation and the per-access
  target-to-W/GX bridge remain OPEN (unchanged by this review).

## Task feedback

Nothing in the review task is believed wrong. One non-blocking nit: the
section-4 doc comment says "DESIGN C2/copy folding" while the file header
says "section 7 example 1" — inconsistent label for the same example;
suggested cleanup on a future touch, not a repair driver.
