# MUSE-REPORT-238 — Efficiency census: emitted layouts vs Rust

## What was done

Measured, not estimated: exact emission spellings read off
`crates/gabbro-check/src/emit.rs` (read-only, untouched), compiled with
gcc 13 `-std=c11 -O0` on x86_64 Linux, against handwritten `#[repr(C)]`
Rust equivalents compiled with rustc 1.97.1. Ran both, byte-compared
size/align/offset per shape.

- New file: `messung/SPEICHER-CENSUS.md` — per-shape table (16 rows:
  u32 slots, records ×2 field orders, atomic scalar, atomic array [u32;256]
  from `beispiele/140`, arenas ×2, linear token, erased ghost, tagged
  union from `beispiele/120`, const table, mmio + port device handles,
  accumulates cells, nested array field, format handle, option index),
  fixed-cost total for `laufzeit/start.c`, top-3 overhead causes, budget
  statement for lanes 244/239, and the Rust reference source inline.
- This report: `MUSE-REPORT-238.md`.

## Results (exact)

- 15 of 16 shapes delta **0 bytes** vs `repr(C)` Rust, including all
  padding and field offsets. Per-table runtime overhead in the emitted
  unit is 0 bytes (no counters, no lock words; only arenas carry `used`).
- Top-3 overheads: lock mutex 40 B/lock (start.c, not in unit);
  arena `used` 4 B + up to 3 B pad (measured +4/+0 and +4/+2);
  linear token 1 B vs ZST (deliberate; ghost is fully erased, 0 B).
- Fixed cost: **40·L + 8·R bytes data** + R thread stacks (8 MiB virtual
  default); `beispiele/124` (L=1, R=2) = 56 B data.

## Verification

- `git status --porcelain` after scratch cleanup shows only the two new
  files (nothing modified):
  `?? messung/SPEICHER-CENSUS.md` (+ this report at commit time).
- `./cargo-pruef` untouched: no repo code changed, so no build was needed
  and none was run. MARKE_EMIT untouched. No Lean changes (`./lean-bau`
  not affected).
- Scratch probes (`.tmp/census_size.{c,rs}` + binaries) were removed after
  the run to keep the tree clean; the Rust source is reproduced verbatim
  in census §5 for re-runs.

## Open / cuts

- x86_64 Linux only; the tagged-union al-8 row (S8) is the one to
  re-measure on aarch64. Stack figure is the `ulimit -s` default, not a
  unit constant. No `gabbro emit` run was used — the census pins the
  emit.rs spellings themselves.
- Nothing in the task looks wrong. One note for lane 244: the only
  emitted-vs-Rust delta that is a choice rather than layout-inherent is
  the 1-byte linear token (S6); everything else is forced by C/`repr(C)`
  agreement.
