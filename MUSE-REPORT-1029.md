# MUSE-REPORT-1029: Exact review of author 879 (optimiser rule: spill freshness)

CANDIDATE: 879 e3eb6772 (`Lane 879: optimiser rule spill freshness (DESIGN section 7 row)`).
Full 40-hex HEAD was not included in the review bundle (`.tmp/review/author-879/`
holds `OWNER-TASK.md`, `MUSE-REPORT-879.md`, `BUILD-EVIDENCE.json`, `PATCH.diff`
and a snapshot copy of the new file). Content pin from `PATCH.diff`: new file
blob `2bcd4e73`, report blob `3e30cf92`, `grammatik/Grammatik.lean`
`c9337c3e..4552242a` (one appended import line). The reviewed snapshot
(`.tmp/review/author-879/grammatik/Grammatik/X86/OptSpillFresh.lean`, 398 lines)
starts byte-identical to the PATCH hunk.

VERDICT: ACCEPT (bounded: the rule lemma as stated, within its CUTS; serial
merge-time gates -- source build, axiom, emission, key scan -- still apply at
integration and are not waived by this review).

## What was reviewed

New file `grammatik/Grammatik/X86/OptSpillFresh.lean` (+1 import line in
`grammatik/Grammatik.lean`): the DIRECT-COMPILER-DESIGN section 7 row
"Layout / allocation" as a generic rule lemma over arbitrary values with
validator-decided side conditions. Certificate `SpillCert` (six `Bool`s) with
admission `spillZulassen` (conjunction); six refusal theorems (one per flag,
proved of the decided `Bool` by `simp`) plus positive probe
`probe_spillZulassen_ok`; four preservation lemmas delegating to canonical
vocabulary; connection `OptSpillFresh_verbindung` (seven conjuncts) with joint
witness `OptSpillFresh_verbindung_zeuge`.

## Independent checks performed

- Forbidden patterns: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the
  snapshot (grep; remaining hits are the words "Probe"/`#print axioms` and two
  `intro _` inside witness-helper `have`s, see note below). No premise typed
  `Prop` itself. English throughout. CUTS block and `#print axioms` for every
  main theorem present.
- Name/signature resolution against this clone: every consumed canonical lemma
  exists with a matching signature -- `sichere_lade_rundreise`,
  `ergebnis_bleibt_vor_rahmen`, `sichereWort_erhaelt_berechtigungen`,
  `writeBytesN_hit`, `sichereWort_rahmen`, `schlitz_disjunkt` (all
  `X86/Stapel.lean`), `spillSlot`/`spill_fill_kommutiert` (`X86/SpillPrivate.lean`),
  `expandBound_gilt`/`blattSummary`/`blattSummary_beschraenkt`
  (`X86/CostSummary.lean`), `rahmenZeuge`/`speicherZeuge`/`zeuge_lesbar8`
  (`X86/Stapel.lean`), `refD`/`refP`/`refO`/`refSp0`/`initB`/`refEin_schreibt`/
  `refB_erreicht`/`refB_schreibt`/`vertragVon`/`RufStartF`/`RufErreichbarF`
  (`ReferenzB.lean`/`Syntax.lean`/`RufMaschineF.lean`).
- Premise use in `OptSpillFresh_verbindung`: `hAdm` via `hBoundOf hAdm` /
  `hSepOf hAdm`; `hBoundOf`/`hSepOf` supply bound and disjointness;
  `hWr` in all four preservation lemmas; `hLes` in the round-trip;
  `haussen` in the outside-bytes lemma; `hwrAB`/`hwr2`/`hwrBA` plus
  disjointness in `spill_fill_kommutiert`; `hAlle` in `expandBound_gilt`.
  No conclusion restates a premise; no contract parameters are quantified away
  (no `Vertrag` premises at all); no new semantics or evaluator; no `ensures`
  derived anywhere.
- Witness: joint instantiation on the checked frame (slot 1 spills `42`, slot 3
  holds foreign word `22`, `schlitz_disjunkt` with `by decide` bounds),
  beside non-degenerate `refD` (`refEin_schreibt`), reached run `MB`
  (`refB_erreicht`) with memory change (`refB_schreibt`, slot value differs),
  plus an observably changing spill-slot byte (`hWechselt`: zero becomes the
  low byte of `42`, via `writeBytesN_hit`). Satisfies the ZEUGE requirement.
- Refusals: all three DESIGN-row failure cases refuse by name
  (`spillVerweigert_fusion` = fused 16-byte over two carriers,
  `spillVerweigert_nachbar` = neighbour-frame overlap,
  `spillVerweigert_adresse` = address-taken via call arg), plus token-threading,
  all-paths save/restore and slot freshness; the positive probe passes by
  `decide`. Refusal is validator admission (`Bool`), never a hardware fault;
  out-of-frame/permission cases stay loud `none` through `sichereWort`.
- Design fidelity: flags and citations match DESIGN §7 row
  (`DIRECT-COMPILER-DESIGN.md:524`) and `dokumente/x86/IR-VALIDIERUNG.md:377-390`
  (fresh private objects, token-threaded ordinary frame accesses, save/restore
  on every path, freshness-to-commutation). No new ISA, no second IR, no
  source/checker/Spec/goal/emitter change.
- Scope prohibitions: PATCH touches exactly three files (report, one import
  line, new file). No friend-reserved optimiser files, no diagnostic/gift/
  example/CLI numbers, no MARKE changes (grep over PATCH for
  `MARKE|N[0-9]{3}|beispiele/|instrumente/` finds only the task-text mention
  in `OWNER-TASK.md`).
- Architecture review (byte forms, REX/registers/width/flags, operands,
  pre-fault effects, access order, TSO/atomicity, feature/MXCSR/interrupt
  gates): not applicable beyond what is claimed -- the file decodes nothing,
  touches no register/flag/MXCSR/interrupt state, and models spills only as
  canonical permission-checked 64-bit frame accesses. IEEE is carried as whole
  little-endian byte equality (bit patterns incl. NaN payloads, no rounding or
  width change), which is exactly as strong as the statement and no stronger.
  TSO is reused, not re-proved (`spill_fill_kommutiert`: both-orders byte
  agreement with a disjoint foreign store). No aligned multi-byte atomicity,
  no LOCK RMW, no source-to-target simulation is claimed; CUTS states each
  boundary precisely and matches the report's open list.
- Live reproduction: `./lean-probe grammatik/Grammatik/X86/SpillPrivate.lean`
  in this clone: `== 0 error(s) in the COMPLETE output; exit 0`, with
  `spill_fill_kommutiert` on `[propext, Quot.sound]` -- the exact lemma and
  footprint the candidate's concurrency conjunct consumes. The candidate file
  itself is not in this tree (review-only lane, no source ownership), so its
  build evidence is the author's queued-wrapper log: `lean-probe` 0 errors,
  `lean-bau` green (511 jobs), axiom prints standard subsets of
  `propext, Classical.choice, Quot.sound`, consistent with the content.
- One linter-history note in BUILD-EVIDENCE (an intermediate probe warned
  about unreferenced `hAdm`-family binders) is resolved in the pinned content:
  the witness existential binders are underscore-prefixed (`_hAdm`, ...),
  which is correct -- they are existentially supplied (via `probe_spillZulassen_ok`,
  `hBoundOfZ`, `hSepOfZ`, ... into `OptSpillFresh_verbindung`), not premises.

## Observations (below REPAIR grade, recorded for the record)

- The two `intro _` steps prove witness-helper implications
  (`spillZulassen ... = true -> 1 < zahl`, `... -> Disjunkt ...`) whose
  consequents hold unconditionally on the witness frame. Discarding an
  antecedent there is honest mathematics (the witness admission is separately
  supplied as `probe_spillZulassen_ok`), not a vacuous theorem premise.
- `SpillCert` has no dedicated source-extent flag (cf. IR-VALIDIERUNG "never
  named by any source extent"); the substance is covered by
  `nichtAdressGenommen` together with the cited B+C disjointness (`hSepOf`).
  The DESIGN §7 row (the task's contract) asks for exactly the six flags given.
- The "call logs" conjunct is carried as absence of new calls/shared accesses
  (one private `write64`/`read64` pair) rather than a source `Folge` equality;
  the author discloses this scoping in report and CUTS. Correct for a
  below-source spill rule; a `Folge`-level claim would belong to a future
  source-to-target simulation, which CUTS leaves open.

## Last build result

`./lean-probe grammatik/Grammatik/X86/SpillPrivate.lean` (this clone):
`== 0 error(s) in the COMPLETE output; exit 0`. No source changes in this lane,
so no `./lean-bau` was consumed here; `git status` clean except this report.
Author's pinned evidence: `./lean-bau` `== exit 0`, `Build completed
successfully (511 jobs)`; `./lean-probe OptSpillFresh.lean` 0 errors; axioms
standard.

## What remains open

Per CUTS (accepted as precise): SCFG-side application waits for the accepted
287 interface; no multi-byte atomicity beyond byte-extensional agreement; no
LOCK RMW; no source-to-target simulation; no cost/fairness/timing claim beyond
counted `expandBound`; no new ISA form. Integration-time serial gates
(source build, `gabbro_ziel` axioms, emission, key scan) remain with the merger.

## Remarks on the task

Nothing in the task appears wrong. The full 40-hex HEAD for 879 was not in the
review bundle; the candidate is pinned above by short HEAD plus exact PATCH blob
hashes and the reviewed 398-line snapshot. No unsupported desired-correctness
premises, no weakened guarantees, no fake closure found.
