# M150: unary minus leaves the width (lane-134)

Status: measured 2026-09-11 on lane-134 (base 6f26e76). New checker rule in
`crates/gabbro-check/src/m1.rs` only, pinned by gift probes 749/750/751 and
three unit tests inside `m1.rs`. Targeted suite
`cargo test -p gabbro-check --test beispiele` (25/25) and
`cargo test -p gabbro-check --lib` (36/36) green.

## The hole class

Every binary integer operator refuses an out-of-width result at the
operation (`M104`, via `typen::…` plus `laeuft_ueber`). Unary minus built the
same out-of-width range -- `IntBereich::genau(breite, true, -max, -min)` --
and never asked the question. That is the M102/M104 family pattern with one
member missing: the check lives at the operation, not at the assignment.

`M101` does not cover for it. It compares intervals, never widths, so into a
wider result even the assignment stays silent:

```gabbro
impl fn negiere(x : i32) -> i64 effects { pure } {
    return -x;   // pre-fix: 0 errors, 0 hints
}
```

The computed type claims values up to `2147483648` for an `i32` operand;
`-x` at `x == INT_MIN` is undefined behaviour in the C it lowers to. The
neighbouring division got this right long ago: `INT_MIN / -1` leaves the
width through `teile` and falls at `M104`.

## Pre-fix measurement (unchanged checker, hole evidence)

All three probes passed with **zero** diagnostics before the fix
(`sollte mit M150 fallen, gefallen ist []`, one run each):

- 749 (must-fall core): full-range `i32` negated into `i64`.
- 750 (must-pass twin + falling site): V1-narrowed `0 .. 100` beside an open
  parameter -- both silent pre-fix.
- 751 (boundary): `i32 in -2147483647 .. 2147483647` beside full `i32` --
  both silent pre-fix.

Everything before them in the sorted gift run stayed green, so the silence
is the rule's, not the harness's.

## The rule

At the `UnOp::Negativ` node, the mathematical range `-max .. -min` has to
fit the operand's own width (`passt_in_die_breite`), else `M150`. Mirrors
`M104` in three points:

- fired at the operation, with the `SYNTAX.md §4` note (compile error, not
  wrap-around) and the V1 remedy note (`narrow x to … else { … }`);
- a `wrapping` operand stays exempt (`!t.laeuft_um()`), as at `M104` -- its
  overflow is declared, not found;
- the range is read WITH its V1/V2 facts, not off the declaration, so a
  narrowed operand stays silent.

The `checked_neg` failure arm (only reachable at `i128::MIN`, i.e. a
literal, not a width) refuses and answers `Unbekannt` rather than inventing
a type -- the `M139` lesson in the other direction.

## What stays silent, and why (must-pass, pinned exactly)

Unit tests `m1::m150_proben` assert exact code lists through the full
`crate::pruefe`, which the file-level gift run cannot (it asserts
containment only):

- open negation falls with exactly `["M150"]` -- no second code beside it;
- V1-narrowed (`narrow x to 0 .. 100`), declared boundary
  (`-2147483647 .. 2147483647`), and `wrapping`-slot operands fire nothing;
- the boundary pair (one value apart) falls with exactly `["M150"]`.

## Known limits, not findings

- The emitter refuses ALL unary minus (`C001`, pinned by gift 219), so no
  shippable program changes behaviour. `M150` closes the checker half: the
  range claim that flows into the certificate no longer leaves the width.
  Probe 219 (`i32 in -100 .. 100`, expects `C001`) is unaffected and green.
- The signed-same-width model of `-` over unsigned operands (gift 219
  documents the C mismatch) is untouched; `M150` judges fit against that
  model instead of replacing it.
- Clean corpus `beispiele/` is unaffected (25/25 incl.
  `jedes_beispiel_geht_sauber_durch`): no clean file negates an
  out-of-width range. The mutation catalog (`mutiere-pruefer.py`) does not
  cover the new lines yet -- that catalog grows in its own lane, not here.
