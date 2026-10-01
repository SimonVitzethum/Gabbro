# MUSE-REPORT-588: Independent exact-candidate connection review of 570

Lane 588, branch `muse/588`, clone `/home/simon/Dokumente/gabbro-muse/a588`.
Owns only this report. No Lean/Rust changes committed; verification scaffolding
(candidate file + umbrella import) was removed after checking, tree verified clean.

CANDIDATE: 570 fd2af5c8cf4f918eed995c1692a8f6ec14f97361
VERDICT: ACCEPT

## What was reviewed

Lane 570 (`grammatik/Grammatik/X86/SourceMemory.lean`, 594 lines, +1 umbrella
import line): a representation interface between real source `Deklaration`/`World`
table carriers and target `Speicher` bytes for the bounded integer fragment
(one `.int lo hi` slot as one little-endian 8-byte word), reusing real `execStmt`
(`World.schreibSlot`), real `write64`/`read64`/`read64_rahmen`/`read64_nach_write64`
(`X86.Speicher`), real `regionDisjunkt`/`alsRegion` (`X86.Regionen`), real
`typWeite`/`zeilenWeite`/`TabLayout` (`X86.TableLayout`), and the existing
`disjunkt_von_intervallen` interval lemma. Base `8596f83e`, diff is exactly the
3 files in `SNAPSHOT.json` (report + import + new module).

## Independent reproduction (queued wrappers, this clone)

- Fetched exact pinned HEAD from the author clone into `refs/review/m570`;
  extracted `SourceMemory.lean`, installed it with the one import line, probed/built.
- `./lean-probe grammatik/Grammatik/X86/SourceMemory.lean`: **0 errors**; all
  `#print axioms` lines match the author's report (`rep_schritt_bleibt` and the
  witness on `[propext, Classical.choice, Quot.sound]`, everything else on a subset).
- `./lean-bau`: **439 jobs, build completed successfully** with the candidate file.
- Goal axioms unchanged: `gabbro_ziel`, `gabbro_ziel_sc_aus`, `gabbro_ziel_gx`,
  `gabbro_ziel_verbund` all on exactly `[propext, Classical.choice, Quot.sound]`.
- Hygiene greps on the exact candidate file, all clean: no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`, no `intro _` / `have _ :=`, no `forall rho`/`forall v`
  contract quantification, no `Prop`-typed premise. `CUTS:` block present (line 542).

## Semantic checks (not just a build)

- New real facts, not copied premises: `zahlWort_wortZahl` (roundtrip under checked
  bounds); `schreibSlot_hit` + three `schreibSlot_fremd_*` frame lemmas over the
  actual `schreibSlot` operation; `rep_fremd_*` combined source+target frame
  preservation via `read64_rahmen`; `rep_schritt_bleibt` (one real
  `Stmt.assignSlot` step unfolded through `execStmt` + matching `write64`
  preserves `RepSlot` AND parses back via `wortZahl`); `disjunkt_von_layout`
  (accepted disjoint layout entries give disjoint 8-byte footprints);
  4 planted refusals, all `by decide` (oversize range, `bool` width, out-of-extent
  slot, overlapping regions).
- Joint nondegenerate witness `rep_schritt_bleibt_zeuge`: one table with one
  `.int 0 100` field that the witness contract writes; a reached one-step
  `execStmt` run changing the source slot `0 -> 42`; the mapped target bytes
  provably changed (`witM.bytes witA != m'.bytes witA` by `decide` on byte 0);
  all main-theorem premises instantiated jointly with the conclusion.
- Every premise of the main theorem is consumed (checked by reading the proof:
  `hOk`->bounds, `hU`+`hExec` cases, `← hLese`, `hk`/`hv` rewrites,
  `hTgt`+`hRd` into `read64_nach_write64`+roundtrip). No toy models, no forged
  decoded input, no guessed ISA/FP faults, no hardware claims, no int->ptr
  conversion (addresses are target-side `natAdresse` computations).

## Accepted bounded claim (exactly this, no more)

Value bridge + framing for the single bounded-integer slot fragment: a source
`assignSlot` step evaluating to `v` together with the matching `write64` of
`zahlWort v` establishes `RepSlot` and parse-back; all disjoint carriers keep
their `RepSlot`; disjoint accepted layout entries supply the needed `Disjunkt`.
`RepSlot` + decided `repOk`/`regionDisjunkt` Bools is the stable
producer/consumer interface for the validator/TSO bridge.

## Known gaps (follow-ups, NOT acceptance blockers)

1. The written-slot address `a` in `rep_schritt_bleibt` is a free parameter, not
   pinned by `a = slotAddr base off`; the region conjuncts of `repOk_klingt` are
   discarded (`obtain <hLo, hHi, -, ->`). Address pinning is the explicit next
   integration (one premise + rewrite; the witness already instantiates
   `witA = slotAddr 4096 0` consistently with `repOk ... 4096 16 0`).
2. `feldOff`/`slotOff` are defined but used in no theorem; wire them into the
   pinned address equation or drop them.
3. Prose names `layoutOk` (header comment, `RepSlot` doc, `disjunkt_von_layout`
   doc, CUTS) but no definition references it; only `regionDisjunkt`/`alsRegion`
   are used. Stop naming it until it is consumed.
4. Fragment bounds honestly cut: single-slot writes only, no sums/FP/bools/
   globals/function pointers, no validator soundness, no concurrency claim.

Last `./lean-bau` result line (with candidate installed): build completed
successfully (439 jobs). After scaffolding removal the tree is clean and the
candidate file is absent from this branch by design (review is report-only).
