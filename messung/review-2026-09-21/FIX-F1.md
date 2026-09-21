# Fix lane F1 — integer `match` coverage (2026-09-21)

Findings fixed here: review G07 F1 (severe) and F3, the matching G09 F3, G07 F5, and the
cosmetic note in `INTEGRATION.md`. This lane builds on `review-0921-integration` at `0f55da77`.
Everything was built and run locally (fisch unreachable). `free -g` before the heavy runs showed
31 GB total and 19–20 GB available.

## What was built

**1. The checker refusal** (`crates/gabbro-check/src/intmatch.rs`, called from the `Match`
arm of `m1.rs`). An integer `match` is accepted only when its arms name every value that M1
knows the scrutinee can hold, each value in exactly one arm. "Can hold" means M1's range of the
scrutinee expression at the `match`: the declared type range, narrowed by the flow facts M1
already trusts for every unchecked table index (`narrow`, a guarding `if`, `x & 3`). So the
rule adds no new assumption, and no independence either. Coverage is decided by an interval
sweep, so no `2^64` values are enumerated. Four codes come from the reserved block:

| Code | Refuses | Gift |
|---|---|---|
| `N411` | a value of the scrutinee's range that no arm names (the first gap is named) | `1128` (`-- erwartet: N411 allein`: `0 .. 254` over `u8`; `cc -Werror` accepts the emitted C, so N411 is the only line) |
| `N412` | an arm that names a value an earlier arm already names, or that names no value (`5 .. 3`) | `1129` |
| `N413` | an arm value outside the scrutinee's storage type (`-1` over `u8`/`u32`, a bound past `i128`) | `1130` |
| `N414` | integer arms over a non-integer (`tagged`, pointer, opaque new type, `bool`), or a variant arm among integer arms | `1131` (`bool`) |

A sentence was added to `saetze.rs` (`m1.ganzzahl_match`). The positive and counter probes
are in `tests/intmatch.rs` (13 → 22 tests). The positive probes cover:

- a declared range (`u32 in 0 .. 7`);
- the full `u8` range in two arms;
- a narrowed scrutinee;
- `INT64_MIN` and `u64::MAX` labels.

All positive probes are compiled with `cc -std=c11 -Wall -Wextra -Werror`.

The existing C001 tests now assert both lines, the checker code and the emitter's `C001`. The
positive tests were rewritten to cover their scrutinee. `range_past_256_values_is_refused` now
uses a covered `u32 in 0 .. 1000`, so its `C001` is the emitter's alone (a lowering limit, not
a coverage fault).

Overlapping and empty arms (`N412`) and labels outside the type (`N413`) are refused at the
checker. This is cheap and clearly right: the emitter refused both already with `C001`, so no
accepted program changes. The checker now says so first. An arm that lies inside the storage
type but outside M1's range is accepted, because its label never fires and the C stays exact.

**2. The conservative reading is kept** (safety first). `int_match_may_miss` still makes
every flow pass count the path past all arms: `endet_immer` in `lib.rs` and `m1.rs`, and the
joins in `m2.rs`, `phasen.rs` and `arena.rs`. `N411` makes that path dead in accepted programs,
but no proof over every reader of `endet_immer` was attempted. The cost is precision only: a
covered integer `match` whose arms all return does not count as ending. The test
`a_covered_match_still_does_not_end_a_narrow_arm` pins this.

**Also fixed:** the empty `match x { }`. `all()` over no arms was vacuously "ends" in both
`endet_immer` copies. Measured before the fix: `narrow i to 0 ..< 4 else { match y { } }`
followed by `T.slots[i]` was checker-clean, and only the emitter's `C001` stopped it. The
empty match now counts as "may miss" (M105 fires), and over an integer it is `N411`. The
`lean.rs` exporter refuses it as well.

**3. Audit of the passes that branch over `match` arms** (every `StmtArt::Match` site in
`crates/`):

| Pass | Verdict |
|---|---|
| `lib.rs`/`m1.rs` `endet_immer`, `m2`, `phasen`, `arena` | Second line kept (G07 `49a8996d`), now also for the empty match. |
| `kosten.rs` `Match` | Max over the arms plus the scrutinee. The miss path costs only the scrutinee, which is no more, so this is sound. `block`/`rest` go through `endet_immer`, which covers G09 F3. |
| `zeugnis.rs` | **Fixed.** An integer match was booked as `match (tagged)`, whose reason cites `D005` and `-Wswitch`. Neither reads an integer switch. It is now its own row, `match (integer)`, with the reason `N411`. |
| `paarung.rs` (V009) | **Finding, not fixed:** see below. |
| `pflichten`, `namen`, `wirkungen`, `clone`, `domaene`, `schleifen`, `zeremonie`, `blindstellen`, `certstmt`, `corrlean`, `fusswache2` | Walkers or binder collection with no join over paths. They are independent of totality. `schleifen` S002 goes through `endet_immer`. |
| `gegenbeispiel`, `obligations_g` | These count calls in arms as conditional, which is correct with or without a miss. `sperr_abschnitte` is a walker. |
| `kbedingung` (D005) | Tagged scrutinees only. Over a tagged value with integer arms, D005 fires beside N414. |
| `lean.rs`, `lean_g.rs` | They refuse the integer match (G07 `f3addbd2`; LG004). `lean.rs` now refuses the empty match too. |

**4. Emitter.** The CLI writes no C for a unit with any refusal (`main.rs`), so the `switch`
without `default` now meets only covered matches. `C001` for a label outside the C type stays.
G07 F5 is fixed: `-2^63` is spelled `(-9223372036854775807 - 1)`. Before, it was written as
`-9223372036854775808`, which gcc 16.2.1 turns into an unsigned constant, and `-Werror`
refuses it (measured). The `pruefe-cformen.py` regex follows. Also measured with gcc 16.2.1:
`case -1:` over `unsigned` compiles silently under `-Wall -Wextra -Werror`, which confirms that
G07 F2 was silent. `switch` over a `bool` variable draws no `-Wswitch-bool`, so the `bool`
refusal is a choice, not a `cc` backstop.

**5. Lean `CFormMatch.lean`.**

- The header and doc comments no longer claim that the checker runs `erschoepfendB` or that the
  emitted `switch` is proved. They say what is tied to what.
- New §4b:
  - `swFaelle`, the `CS.sw` cases built from `fallListe`;
  - `swFaelle_lookup`, which shows that it dispatches as `wahl`;
  - `sw_erschoepfend_trifft`: under `erschoepfend` and a value in range, every run of that
    `switch` runs the chosen arm, and `swMiss` is impossible;
  - `sw_luecke_ueberspringt`: the planted gap skips.
- The witness `match_exhaustive_zeuge` dropped the decorative `refB_erreicht`/`refB_schreibt`
  conjuncts. It now shows that the `switch` on the fixture-read value `100` has a run, and that
  every run executes arm 1's body.
- Still NOT proved:
  - that `emit.rs` writes exactly `swFaelle`;
  - that the Rust sweep computes `erschoepfendB`;
  - the witness scrutinee is a literal, not the emitted load.
- New SATZKARTE §40. The `pruefe-cformen.py` rows `stmt:switch-int`/`stmt:case-int` no longer
  name lane 228 as owner; the lemma is OPEN.

**6. Tidy.** `int_match_may_miss` and its doc moved above the `endet_immer` doc comment, so
each function carries its own doc again. The `ast.rs` and `emit.rs` comments that said "no
checker pass decides coverage" were updated.

## Measured

| Check | Result |
|---|---|
| `cargo test --no-fail-fast` | 68 collections, **1244 passed, 0 failed, 1 ignored** (baseline 1235/0/1; +9 = `tests/intmatch.rs` 13 → 22) |
| `lake build` (grammatik) | 281 jobs, 0 errors; `gabbro_ziel` axioms `[propext, Classical.choice, Quot.sound]`; new theorems standard (`sw_erschoepfend_trifft`: `propext, Quot.sound`; witness: the three); no `sorry`/`native_decide`/`axiom` |
| `pruefe-emission.sh` | exit 0, **ALL PASS**: 37 run through, 288 of 288 compile, 2 reverse probes. ASan was not run on this machine (= baseline). The MARKE_EMIT counters were not touched and none moved. |
| `pruefe-saetze.py` | exit 0: 433 codes, 0 invented |
| `pruefe-kennungen.py` | ALL PASS |
| `pruefe-todo.py` | 16 findings (= baseline) |
| `pruefe-englisch.py` | red with the same 2 pre-existing `saetze.rs` seams (= baseline) |
| `pruefe-cformen.py` | red with 1 unclassified statement in `140-atomic-array-counter`, identical before and after (measured with the old binary and old script) |

**Corpus diff** (`gabbro pruefe` and `gabbro emit` codes for every file, before and after):

- all 127 `beispiele/*.gab`: **unchanged**;
- 745 → 749 gifts;
- the only changes are the five lane-227 gifts 1072–1076. They now also fall at the checker:
  - 1072: N411 + N414;
  - 1073: N411 + N412;
  - 1074: N411;
  - 1075: N411 + N412;
  - 1076: N411 + N413.
  Their `C001` expectation still holds;
- the four new gifts 1128–1131.

No corpus program contains an integer match, so no example verdict could move. That is now
measured as well.

## Open

- **V009 misses a gate through a `match` whose arm ends** (all match kinds, not only integer).
  `paarung.rs` checks inside the arms and never what follows. `if` has that rule
  (`endet_immer(zweig)` → the rest is gated). The probe was measured:
  `let s = STUFE; match s { 0 => { return X; } 1 .. 255 => { } } return granulat;` is clean
  before; with the one-branch fix it falls with V009. **Not committed**, because the V009
  sentence in `saetze.rs` says the rule "is not to be extended" until the ordering sample has
  run. That is Simon's decision. The draft gift is in
  `.claude/muse-arbeit/kratz/review-0921/F1/1132-match-arm-ends-gate.gab`.
- The Lean correspondence lemma for the emitted integer `switch` (the chain from `emit.rs` to
  `swFaelle`), and a proof that the Rust sweep equals `erschoepfendB`.
- Lifting the second line (`int_match_may_miss`) would need an argument over every reader of
  `endet_immer`. It was deliberately not attempted.
- A dense dispatch over a full `u32` cannot be written: range arms cap at 256 values, so the
  scrutinee must be narrowed first. `u16` full needs 256 arms.
- G07 F6 (label count per match) and F7 (depth headroom test) are untouched.
