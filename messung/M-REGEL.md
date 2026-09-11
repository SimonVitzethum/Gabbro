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

---

# M152: the remainder at `INT_MIN % -1` traps (lane p09)

Status: measured 2026-09-11 on lane p09 (base 2dc02ad). New checker rule in
`crates/gabbro-check/src/m1.rs` only, pinned by gift probes 780/781/782 and
three unit tests inside `m1.rs`. Targeted suites
`cargo test -p gabbro-check --test beispiele` (25/25) and
`cargo test -p gabbro-check --lib` (126/126) green.

## The hole class

Division over `INT_MIN / -1` leaves the width through `teile` and falls at
`M104`. The remainder over the same inputs claims a range that FITS
(`|a % b| <= |b| - 1`, so `0 .. 0` for a `-1` denominator) -- and `M104` has
nothing to say about a fitting range. Yet the C the emitter writes (`a % b`,
signed, `emit.rs`) traps exactly where the division does: C defines `%`
through `/` (C11 6.5.5), and `INT_MIN % -1` raises SIGFPE on x86-64
(measured 2026-09-11: Schultz-style probe compiled `-O0`, exit 136 with core
dump; at `-O1` the same probe prints `0` -- the optimizer assuming what the
checker never refused). That is the M150 pattern with the sign flipped: the
check lives at the operation, not at the assignment -- and no assignment
could catch it anyway, since the claimed range fits every result type.

## Pre-fix measurement (unchanged checker, hole evidence)

The core probe passed with **zero** diagnostics before the fix:

```gabbro
impl fn rest(x : i32, y : i32 in -1 .. -1) -> i32 effects { pure } {
    return x % y;   // pre-fix: 0 errors, 0 hints; emitter writes `return x % y;`
}
```

- 764 (must-fall core): full-range `i32` dividend against a `-1`
  denominator -- silent pre-fix.
- 765 (must-pass twins + falling site): denominator `1 .. 100` and dividend
  `-100 .. 100` beside the open pair -- all silent pre-fix, the open pair
  falling post-fix.
- 766 (boundary): `i32 in -2 .. -2` beside `i32 in -2 .. -1` -- both silent
  pre-fix, the second falling post-fix.

## The rule

At the `BinOp::Rest` node, with the zero-denominator refusal (`M102`)
already discharged: if `rest` computed a range at all (same signed form, so
the operation really lowers to signed C `%`), both sides signed, the
dividend range holds the smallest value of its width and the denominator
range holds `-1`, refuse `M152`. Mirrors `M150` in three points:

- fired at the operation, with the `SPRACHE.md §3` note (compile error, not
  a trap) and the V1 remedy note (narrow the divisor away from `-1`, or the
  dividend away from the smallest value);
- the ranges are read WITH their V1/V2 facts, not off the declaration, so a
  narrowed divisor or dividend stays silent;
- unsigned operands stay silent: `%` over unsigned C is defined for every
  nonzero denominator.

Deliberately NO `wrapping` exemption, unlike `M104`/`M150`: the unsigned
lowering that exempts them covers only `+ - * <<` (`emit.rs::rechnet`), so
a `wrapping` remainder still lowers to signed C `%` and still traps --
measured with an `i32 wrapping` slot operand, which falls post-fix.

## What stays silent, and why (must-pass, pinned exactly)

Unit tests `m1::m152_proben` assert exact code lists through the full
`crate::pruefe`, which the file-level gift run cannot (it asserts
containment only):

- open remainder over `-1` falls with exactly `["M152"]` -- no second code
  beside it;
- denominator `1 .. 100`, the unsigned pair, and dividend `-100 .. 100`
  fire nothing;
- the boundary pair (one value apart in the denominator) falls with exactly
  `["M152"]`.

## Known limits, not findings

- Mixed-width `%` (neither side a literal) answers `Unbekannt` with no
  refusal, as before -- `M152` gates on `rest` having computed a range, so
  it claims nothing there. That silence predates this lane.
- An empty dividend range answers `None` out of `rest` (unreachable code)
  and stays silent -- the only honest answer where no value flows.

---

# V2-subtraction: `M104` at the operation (lane p09)

Status: measured 2026-09-11 on lane p09 (base 2dc02ad). No new number: this
IS `M104`'s case, asked one door too late. Fix in
`crates/gabbro-check/src/m1.rs` only, pinned by gift probe 783 and two unit
tests (`m1::vsub_proben`). Same targeted suites green (25/25, 126/126).

## The hole class

Under a V2 fact (`a >= b`, `a > b` between two places), `a - b` took an
early return with the narrowed range
`untergrenze .. (ba.max - bb.min).max(untergrenze)` -- and never asked the
overflow question. With two open `i32` under `a >= b` that range is
`0 .. 4294967295`: out of the width the C computes in (`INT_MAX - INT_MIN`
overflows 32-bit `int`), yet into an `i64` result even `M101` stays silent,
because it only compares intervals. Measured over the unchanged checker:
`if a >= b { return a - b; }` into `i64` passed with **0 errors**. Into an
`i32` result `M101` spoke at the assignment -- the wrong level, which is the
M150 lesson verbatim: the check lives at the operation, not at the
assignment.

## The fix

The early return now asks the same question as the tail below it: a
narrowed range that leaves the width refuses through the existing
`ueberlauf_ausdruck` (`M104`), with the `wrapping` exemption unchanged (its
overflow is declared, and the emitter computes `Minus` unsigned). A narrowed
range that keeps the width returns exactly as before -- the V2 precision is
kept, only the silence is gone.

## What stays silent, and why (must-pass, pinned exactly)

- `a : i32 in 0 .. 100`, `b : i32 in 0 .. 50` under `a >= b` into `i64`:
  the V2 range is `0 .. 100`, keeps the width, fires nothing (unit test
  `enge_v2_differenz_schweigt`, gift 783 second arm).
- Gift 783 first arm and unit test `offene_v2_differenz_faellt_an_der_operation`
  fall with exactly `["M104"]` -- the operation's own code, no second code
  beside it.

## Known limits, not findings

- The fix trusts the V2 fact the same way the narrowed range always did; a
  stale fact would mislead both equally. Fact lifetime is V1-V3 territory,
  not this lane's.
