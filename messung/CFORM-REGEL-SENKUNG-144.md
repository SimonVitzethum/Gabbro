# Ruling record: lowering batch of lane-144 (2026-09-11)

Status: ruled. Five forms lowered in `emit.rs`, one new refusal.
Evidence: corpus units in `messung/proben/emission-144/` (lowering pins
plus one refusal pin), `cc -Werror` green at `-O0`/`-O2`, all 71
`beispiele` units byte-identical before/after.

## Lowered

- `doubleTyp`: `f64` to `double` via `ctyp_primitiv`; unknown widths fall
  to `None` into `C001`, so no width silently becomes `double`.
- `floatTyp`: `f32` to `float` with `f`-suffixing where the node computes
  in `float`; same fail-closed shape.
- `schleifeStmt`: `while` is the `retry` skeleton only (`emit.rs::retry`,
  counter-guarded); `leave`/`next` lower to `goto`, so no user path
  writes it.
- `typOfErw`: `bezugnahme` writes the checked reference once
  (single-source per W7); undeclared targets stay a comment under `N006`.
- `wennGnuC`: guard fires exactly when every match arm returns, handing
  `D005`'s closed distinction down.
- `statikAssert`: declared spaces keep the assert; `cc` green at both levels.

## Refused

- `anvertrauen` over a range type (`entrust` space): checker-clean yet
  emitted comment-only with no check -- now named `C001`. Tree-wide sweep:
  only `beispiele/25` uses declared-space `entrust`; all entrust gifts
  fall at checker codes `N004/5/6`, never reaching emit.
