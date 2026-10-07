# Report 11 — Sequential Sail Arm: integer data-processing

Clone: `/home/simon/Dokumente/gabbro-arm/work/11`, branch `arm/11`.

## Done

- Baseline `./arm-bau` green (6 jobs, exit 0, 0 errors).
- Skeleton `arm/Arm/Isa/IntCore.lean` (Nat-level `pow2`/`mask`/`trunc`,
  `rdXn`/`wrXn` over `Eff`), wired into `arm/Arm.lean`; `./arm-probe` 0 errors.

## New definitions/theorems

- `Arm.Int.pow2`, `Arm.Int.mask`, `Arm.Int.trunc`, `Arm.Int.rdXn`, `Arm.Int.wrXn`.

## Last build

- `./arm-probe arm/Arm/Isa/IntCore.lean`: 0 errors, exit 0.

## Open

- Everything else: `AddWithCarry`, `DecodeBitMasks`, shift/extend helpers,
  all execute families, `Integer.lean`, per-family examples + planted-wrong cases.

## CUTS

- Skeleton only; no semantics, no theorem yet.
