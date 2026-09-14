# MUSE-REPORT-165 (lane 165): T2 general -- correspondence certificates as form families

## What was done

Generalised lane 164's one-program certificate (`Korrespondenz104.lean`,
untouched and still building) to form families over the existing T4
judgements, in a NEW file `grammatik/Grammatik/Korrespondenz.lean`
(imported at the end of `grammatik/Grammatik.lean`):

- Rows (`GRow`): `void`, `storeSlot` (slot store of ANY carried `CX`
  expression, any index `CX`), `storeNamed`, `storeGlob`, `setVar`,
  `setOp` (`+=`/`-=`/`&=`/`|=`), `bindLet`, `ite` (arm row lists),
  `call` (any callee number, parameter-argument `CX` list, optional
  bound local), `ret`, `forTrav` (the `scorr_traverse` form).
  Elaboration `growRow`/`growsCS` to `CS`.
- Decidable check `gbodyOk` (per `GBody = rows + vm/pp/ks`): supported
  expression families (`exprOk`: literals, locals, `+`/`-`/`*`,
  `==`/`<`/`<=`/`>` comparisons, slot loads, globals), slot-layout
  sanity (`rowLaysOk`), bound-local freshness (`rowsFresh`, threaded),
  traverse hygiene (`rowsTravOk`, the `hw` premise decided on the
  elaborated rows).
- Derivations `RBlock` (15 ctors) / `REnd` (14 ctors, no `bindCall` --
  `Endblock` has none) over the T4 judgements; freshness/`hw` come
  from the decided checks, not from premises.
- Theorems: `rblock_sound` (-> `BlockCorr`), `rend_corr`
  (-> `EndCorr`), flagship `gcert_sound` (-> `EndSem` through
  `cCorr_end`); helpers `freshRaw_ok`, `gbodyOk_hygiene`.
- 104 re-derived: `einRowsG`/`liesRowsG` (+ `einRowsG_elab`,
  `liesRow_elab` pinning rows to the emitted bodies), `ein_rend`/
  `lies_rend`, `einBodyG_ok`/`liesBodyG_ok` by `decide`,
  `ein_end_general`/`lies_end_general` (`EndSem`), `ein_fn_general`/
  `lies_fn_general` (`FnCorr` via `cCorr_ruf`), `einzahlen_zeuge_general`
  (IDENTICAL proposition to `einzahlen_zeuge`/`einzahlen_zeuge_cert`).
- Corpus pins, printed by the extended printer and accepted by
  `decide`: `printed16_stand_ok`, `printed16_belegen_ok`,
  `printed118_gib_ok`, `printed118_nimm_ok`, `printed15_ok`,
  `printed25_ok`.
- Rust (`crates/gabbro-check/src/corrlean.rs`, 104 path byte-identical):
  general section printing `GRow` rows + pasteable `GBody` literals,
  expression renderer over exactly the `exprOk` families, CIT by usual
  conversions, calls by source order, `GREFUSAL` by name for the rest
  (globals/named bases: no block numbers; `let`-calls: no callee
  signature; `traverse`/loops/match/etc.). 6 new tests.
- Two printer-side bugs found and fixed while measuring: shared
  `layout` computed `ss = off + sum` instead of `sum` (wrong record
  size for every non-first field; 104 passed by accident at offset 0),
  and `bool` fields had no byte size (refused all of 15/16).

## Last results

- `./lean-bau`: `Build completed successfully (151 jobs).` (lake exit 0)
- `./cargo-pruef`: exit 0, 0 failing tests (all suites; 7 old + 6 new
  corrlean tests pass).
- `pruefe-kennungen.py`: ALL PASS. `pruefe-englisch.py`: no finding in
  this lane's lines (2 pre-existing elsewhere, as in lane 164).
- No emitter/example change: `MARKE_EMIT`/`MARKE_EMIT_G` untouched,
  `./emission-pruef` not rerun (nothing it measures changed).
- `#print axioms`: pins `[propext]` or none; everything else
  `[propext, Classical.choice, Quot.sound]` (the T4 base classes).

## Corpus count (measured, `gabbro corr-lean` over all 101 `beispiele/*.gab`)

- 5 units with bodies fully certified (zero `GREFUSAL`): 104, 15, 16,
  118, 25.
- 3 more units with zero refusals are VACUOUS (no `impl fn` at all):
  20, 24, 51.
- Everything else is refused by name; the dominant refusal causes are
  globals/named-table access (no block numbers from source),
  `traverse`/loops, `match`/`switch`, atomics/device forms, and calls
  with non-parameter arguments. `52-baugatter` fails on exactly one
  function (`hoechstmarke_melden`: global store).

## What remains open (also in the file's CUTS)

1. Row-to-statement link is proof-level (rows pin the C side; the
   Gabbro side rides in the derivation's T4 premises). The
   printer-to-emitter agreement is printer-side, tested in Rust.
2. `exprOk`/`rowLaysOk` are pins, not consumed premises (consumed:
   freshness + traverse hygiene). Family enforcement beyond the pins
   is by provability.
3. `ks` values stay model data (as in 164).
4. Trailing call-with-result has no row (`Endblock.bindCall` does not
   exist); the `traverse` Lean family exists but the printer still
   refuses it (no bound rendering).
5. `storeNamed`/compound/global rows have derivations but no corpus
   instantiation yet.

## Task feedback (judgment calls, nothing believed wrong)

- Added `.gt` to `exprOk` beyond the task's parenthetical list because
  `ecorr_gt` is in the cited E17 T4 family; `!=`/`>=`/`!`/`&&`/`||`
  stay refused (no T4 lemma in the cited set / not listed).
- Generalised the store index to any `CX` (task: "slot store of any
  expression" is about the value; 118's literal indices forced the
  index too).
- Rule-13 note: no theorem added here takes a universal-over-syntax
  premise, so no `_zeuge` companion is owed; `einzahlen_zeuge_general`
  is the joint non-degenerate instantiation anyway (written table,
  reached run with a memory-changing step).
- Structural lesson, measured twice: multi-self-call-per-branch `def`s
  (`rowsTravOk`, `rowsFresh`, `rowCXs`) compile to `@[irreducible]`
  well-founded recursion and `decide` cannot touch them; the mutual
  row/list split (as in working `growRow`/`growsCS`) fixes it.
  A lane that adds a recursive check should `#print` it and try one
  `decide` before building proofs on it.
