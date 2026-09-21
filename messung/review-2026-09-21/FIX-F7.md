# Fix lane F7 — smaller Rust findings (review G02, G03, G05, G07, G09)

*2026-09-22, branch `review-0921-integration`, built and measured LOCALLY (fisch unreachable).
`free -g` before every heavy run: 31 GB total, 20 GB available, swap 8 GB.*

Code commit: `17af4282` (all code, examples, gifts, docs); this report is the commit after it.

## 1. G02 F3 — the O12 `RELEASE HOLDS (syntactic)` row (MED-LOW): FIXED, shared

- **One analysis, in one place:** `crates/gabbro-check/src/freigabe.rs`. `obligations_g.rs` and
  `gegenbeispiel.rs` call it; each lost its ~470-line copy. The counterexample output keeps
  its own header note (passed as `zusatz`).
- **Order-aware.** The section is walked in execution order with one set: the cells promised at
  this point. The rules:
  - An unconditional direct call first KILLS the cells of every table its declared `effects`
    write. That covers `writes`, `consumes` and `publishes`; with no written `effects`, or a
    write through a non-carrier, it kills all cells. The call then ADDS the cells its `ensures`
    reads.
  - A direct write kills the cells of the table it writes. That covers `=`, `publishes`,
    `exchange`, `alloc`, `reset` and `grow`. A write through something that is not a declared
    carrier kills every cell.
  - Only a statement's last call promises. A call nested in an argument only kills.
- **Nothing is skipped any more.** Every block is walked (`unterbloecke`, exhaustive).
  - `locks` and `observes` bodies are brackets, walked in line.
  - Every other sub-block is conditional: its calls never promise, and its writes still kill.
  - A `locks` inside `observes` now gets a row.
  - An early `return`/`leave`/`next` is checked as a release.
- **Binder-aware cells.** A quantifier or `count` binder, or a callee parameter, used as an index
  renders `[…]`. A `[…]` cell is never countable.
- **Measured against the old binary.** Each of these rows read HOLDS before and reads UNPROVED
  now, with the reason named:
  - `setze(30); konto.slots[1].stand = 5;` (G02's example);
  - `setze(30); stoere();`;
  - `setze(30); if … { konto.slots[1].stand = 4; }`.

  The positive side stays HOLDS: `konto.slots[1].stand = 5; setze(30);` and
  `stoere(); setze(30);`. The binder case and the early exit cannot be exported: the lock
  invariant with a name index gives `LG003`, and `return` under `locks` gives `LG004`. Both are
  pinned on the analysis directly.
- **Tests:**
  - `tests/obligations_g.rs`: 7 `f7_*` tests, 4 through the export and 3 on `freigabe_abschnitt`
    directly;
  - `tests/gegenbeispiel.rs`: 1 test, the G02 example through the counterexample output.
- **Corpus:** the rows are unchanged. 124 has 2 × HOLDS and 119 has 1 × UNPROVED, as before.
- **Side effect:** `grammatik/Grammatik/GenOblig104.lean` and `GenOblig108.lean` were
  regenerated.
  - They were stale BEFORE this lane. `pruefe-genlean.py` reported 2 findings at baseline, since
    lane 204 added the RELEASE section and never regenerated them.
  - Now: `GENLEAN: GRUEN`, 2 of 2 byte-identical.
  - The change is comments only. `lake build` is green.

## 2. G09 F2 — `E011` never held calls against `touches` (MED): FIXED

- **The callee half.** `aufrufgraph::Graph::rufwirkungen_im_block` builds the call sites of the
  `traverse` body and object, using the same `sammle_kanten`/`nimm_ruf` edges and the same
  pointer-contract reader as the graph.
  - Each named callee contributes its transitive `huelle`; each indirect call contributes its
    type contract. Both go through `ersetze`.
  - `wirkungen::pruefe_touches` holds every `reads`/`writes`/`consumes`/`publishes`/`allocs`
    place against `touches`, with the same known-world filter and the same `deckt` as a direct
    deed.
  - A lower-bound hull still refutes. Its incompleteness stays with `E009`.
- **Found on the way:** `E011` never ran for a function with a DERIVED `effects` clause, because
  it hung off the written-clause arm. It runs there now.
- **Gifts:**
  - `1169-traverse-call-not-in-touches`: `E011` now; before, 0 errors on the touches rule;
  - `1170-traverse-derived-effects-touches`: `E011` now; before, 0 errors in total.
- **Positive and bite rows:** 5 `f7_*` tests in `tests/traverse_object.rs`. They cover a call
  named in `touches` (silent), a writing call, a reading call with and without `reads`, a call
  in the object, and the derived clause.
- **Sentence:** in `wirkungen.rahmen`, the aussage now says callees are included. The G09 gap is
  struck through and marked closed, and the `gemessen_an` field names 1169 and 1170.
- **Corpus hit: 1 file, `beispiele/09-ohne-zeiger.gab`.**
  - `blatt_loeschen` reads `Kappenraum.slots`, and the `touches` of `einsammeln` named only
    `consumes Kappenraum.slots` (the function's `effects` line names both).
  - Repaired by adding `reads Kappenraum.slots` to the `touches` line, with a comment.
  - The emitted C is byte-identical (`cmp`).
  - Not repaired by letting `consumes` cover `reads` in `touches`: that would have loosened the
    existing direct-deed rule.
  - This is a tightening of a corpus file's promise and should be checked at merge (cf. lane 184).

## 3. G03 F4 — `tr_traverse`: a table name wins over a same-named binding (LOW): MEASURED, FIXED in the exporter

- **Measured: the checker ALLOWS a parameter or `let` to cover a table name.** Both probes are in
  `kratz/review-0921/F7/`:
  - `shadow1.gab`, `fn f(T : ptr<normal, rw> U)` with `traverse i over slots of T`: 0 errors;
  - `shadow2.gab`, `let T = 3;`: 0 errors.
- **The exporter got it wrong, and not only in `tr_traverse`.** `lean-g shadow1.gab` exported
  `.traverse GTab.T` and `.assignSlot GTab.T`, over the 4-slot `T`, while the source walks the
  8-slot `U`. The same flat resolution sits in `write_table`, `slot_access` and `foot_carrier`.
- **Fix:** `lean_g::carrier_not_covered` refuses (`LG005`, by name) any parameter or binding
  spelled like a table, global or arena. It is fail-closed and adds no code.
  - The binder walk is exhaustive over `StmtArt`, with no `_` arm.
  - I did not add a checker refusal: the language permits covering (`namen.rs`
    `rumpf_geltung`, and `domaene.rs`/`kosten.rs` resolve the local first). Refusing it would be
    a language change, and the gap is the exporter's.
- **Tests** (`tests/lean_g.rs`):
  - `refuses_parameter_covering_a_table`;
  - `refuses_let_covering_a_table_and_exports_the_renamed_twin`, where the twin exports
    `.traverse GTab.U`.
- **Corpus:** no `lean-g` verdict changed over 913 files.

## 4. G05 F1 — the 147/148 hash (MED): FIXED

- **The fold.** `fnv` now returns `xor_worte(h4, h4 >> 22)`. I used `>> 22`, not the suggested
  `>> 16`: bit k of an input word reaches only bits k..31 of `h4`, so the top ten bits (22..31)
  are the ones every input bit reaches.
- **Measured on a Python model of the exact code** (the number of input bits that do NOT reach
  `% 1024`):
  - unfolded: sip bits 10–31 and sp bits 10–15;
  - `>>16`: sip bits 26–31 still missing;
  - `>>22`: none.
- **Top-byte-only variation of sip** gives 1, 4 and 256 distinct buckets respectively.
- **Emitted C:** the diff is one line per file, `return h4;` → `return xor_worte(h4, h4 >> 22);`.
  - `cc -std=c11 -Wall -Wextra -Werror -c` is clean on both files.
  - A driver on the 147 C returns the same values as the Python model. The G05 pairs split:
    10.0.0.5 → 501, 11.0.0.5 → 641, sp 41024 → 413, 74.0.0.5 → 757.
  - UBSan at `-O0` is silent, and `-O2` output is identical to `-O0`.
- **Costs:** `fnv` rose from 95 to 101 ops (read off `K001`). Every caller still checks clean,
  0 errors on both files.
- **Headers and comments** in both files now describe the fold and say what the fold changed.
- **Counters:** `MARKE_EMIT` is not affected, because both files still emit. The emission check
  gives ALL PASS.

## 5. Small items

- **G03 F7:** the stale globals comment printed by `obligations_g.rs` was fixed ("lane 198
  exports `static mut` globals; a unit without one has `Glob := Empty`"). The same stale note in
  the `tr_sinv_pred` doc comment of `lean_g.rs` was fixed too.
- **G07 F6** (the label cap applies per arm, not per match): NOT changed. It bounds code size
  only, linear in the source, and is not a safety issue.
- **G07 F7** (the headroom test edits examples): NOT changed. It is a process note, and the
  guard is `TIEFE_MAX`/`P038`.
- **G04 F6** (`costs` on `-> never`): already settled by fix lane F5 (`namen.never_forever_
  angenommen`).

## 6. G02 — O12 rule half

**It is NOT the RELEASE HOLDS item.**

- The RELEASE row is an informational comment in two outputs. F7 made it sound as a syntactic
  reading.
- O12 half (2) asks for a checker REFUSAL at every locked-section exit whose invariant does not
  follow from the callee promises. It stays open.
- Lane 204 measured that such a refusal would fall on `119`, a false positive. With the F7
  analysis the corpus rows are the same (119 UNPROVED), so that measurement stands.
- Recorded in `OFFEN.md` O12 and `TODO.md`.

## Measured results

| Check | Result |
|---|---|
| `cargo test --no-fail-fast` | **72 collections, 1325 passed, 0 failed, 1 ignored** (baseline 1310/0/1; +15 new tests), 45 s |
| `instrumente/pruefe-emission.sh` | **ALL PASS** (37 run through, 288/288 translate; ASan not run here), 1 min 16 s |
| `cd grammatik && lake build` | 281 jobs, 0 errors (`GenOblig104/108`, `Pflicht104/108` rebuilt) |
| `pruefe-genlean.py` | **GRUEN** (was 2 findings at baseline) |
| `pruefe-saetze.py` | pass (443 codes, 184 sentences, 0 invented) |
| `pruefe-kennungen.py` | ALL PASS |
| `pruefe-todo.py` | 16 findings (= baseline) |
| `pruefe-zahlen.py` | 37 findings (= baseline, measured with the change stashed) |
| `pruefe-englisch.py` | red as on master; German comment lines 7965 before and after (no new German) |

`#print axioms`: no Lean statement was touched. Only generated comments changed in two
generated files.

## Corpus diff

The diff covers 913 files (`beispiele/*.gab` plus `beispiele/gift/*.gab`). For each file it
compares the `check` codes, the `lean-g` verdict and the `obligations --g` release rows between
the old and the new binary. The script is `kratz/review-0921/F7/korpus.sh`.

- **Checker verdicts:**
  - `09-ohne-zeiger` gets `E011` and is repaired in the source, as described in item 2;
  - 147/148 still have 0 errors after the fold and the cost bump;
  - the new gifts 1169 and 1170 are `E011`;
  - nothing else changed.
- **`lean-g` verdicts:** unchanged. No corpus program covers a carrier name.
- **Release rows:** unchanged.

## Open

- **O12 half (2):** the checker release rule, unchanged.
- **E011 holds world state only,** as `E010` does. A `traverse` over a PARAMETER, or a callee
  effect on a caller parameter, is still not held (booked in `wirkungen.rahmen`).
- **The exporter refuses a covering binding rather than resolving scope.** A scoped exporter
  would be the more permissive repair, if a program ever needs one.
- **The 147/148 hash is still word-wise,** not byte-wise FNV-1a. The comments say so.
