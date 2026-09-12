# MUSE-REPORT-68: bit intrinsics, Lean definitions (PLAN-BITS.md section 3, model half)

Lane 68. New file `grammatik/Grammatik/Bits.lean` (wired into `grammatik/Grammatik.lean`
via `import Grammatik.Bits`), parametric in the width from the start: the width is
carried as `w + 1`, never `w - 1`.

## What was built

Nat-level models (all fuel- or div/mod-based, no `decide` over large tables):
- `natBits`, `log2n`, `clzn`, `ctzAux`/`ctzn`, `popAux`/`popcountn`,
  `rotln`/`rotrn`, `byteOf`, `bswap16n`/`bswap32n`/`bswap64n`, plus helpers
  (`pkt_div/mod/lt`, div `ladder0-7`, `split2/4/8`, `byteOf_pair/nest/nest8`,
  `horner_step`, `*_nest` folds, `popAux_add_fuel/add_mul_pow`,
  `rotln_lt`, `rotrn_lt`, `rotrn_rotln`, `popcountn_rotln`, `ctzAux_spez`,
  `ctzn_spez/le`, `clzn_log2n`, `log2n_spez`, `bswap*_lt/invol`).

`Zahl` wrappers with the exact PLAN-BITS.md section 3 signatures:
- `Zahl.clz (w) (x : Zahl 1 (2^(w+1) - 1)) : Zahl 0 w`
- `Zahl.ctz`, `Zahl.log2_floor`: same signature
- `Zahl.popcount (w) (x : Zahl 0 (2^(w+1) - 1)) : Zahl 0 (w+1)`
- `Zahl.rotl`/`Zahl.rotr (w) (x : Zahl 0 (2^(w+1)-1)) (s : Zahl 0 w)`
- `Zahl.bswap16/32/64` as three functions (task-allowed form), since the
  widths are concrete types (`2^16-1`, `2^32-1`, `2^64-1`).

Six target theorems (values compared via `.n`; `r` tied to the wrapper by `rfl`):
- `log2_floor_spez`: `2^r <= x < 2^(r+1)` for `r = log2`
- `clz_log2`: `clz x + log2_floor x = w`
- `ctz_spez`: `2^r ∣ x` and `¬ 2^(r+1) ∣ x`
- `popcount_rotl`: popcount invariant under rotation
- `rotl_rotr`: `rotr ∘ rotl = id`
- `bswap_bswap16/32/64`: involution at all three widths

ZEUGE (`clz_log2`): `clz_log2_zeuge` -- width 32 (`w = 31`), `x = 1`
(clz 31, log2 0) and `x = 2^31` (clz 0, log2 31), all four numerals by `decide`.
Note: `clz_log2` has no universal premise over program syntax, so rule 13's
inhabitation clause does not fire on vacuity grounds; the witness is supplied
because the lane names the theorem as TARGET.

## Verification

- `./lean-probe grammatik/Grammatik/Bits.lean`: `== 0 error(s)`.
- `./lean-bau` last line set: `== 0 error line(s) in the COMPLETE output`
  (`Grammatik.Bits` replayed, whole project green).
- `#print axioms`: `log2_floor_spez`, `clz_log2`, `clz_log2_zeuge` depend on
  `[propext, Quot.sound]`; the rest additionally on `Classical.choice`
  (from `Decidable.em` case splits and `div_add_mod`/`Nat` library lemmas).
  No `sorry`/`axiom`/`native_decide`/`unsafe` in the file.
- Every premise of every added theorem is used (specs need positivity from
  `zahlNat_bounds.1` and the upper bound from `.2`; range lemmas need `hs`/`hx`
  via the halves; packet lemmas need the byte bounds).

## What remains open (also in the file's CUTS block)

- Syntax integration: no `Expr`/`Stmt` constructor exposes these yet (model half only).
- `rotl_rotr` is one direction (`rotr ∘ rotl = id`); the mirror is the same shape.
- `bswap` is three functions rather than one parametric theorem.
- C lowering note (in CUTS): `clz`/`ctz`/`log2_floor` to `__builtin_clz/ctz`
  (`log2` as `31 - __builtin_clz`), `popcount` to `__builtin_popcount`,
  `rotl/rotr` to the shift-or idiom, `bswap*` to `__builtin_bswap*`.
  The zero case is unreachable because `Zahl 1 (2^(w+1)-1)` excludes `0`.

## Notes on the task statement (nothing believed wrong)

- The prescribed `Zahl` signatures elaborate as stated; `s : Zahl 0 w`
  unwraps via `zahlAmt_le` (`Int.toNat_le`), results rewrap via
  `Int.ofNat_le/ofNat_lt` plus the Nat-level range lemmas.
- Two Lean-core facts worth recording: `omega` abstracts `2^k` atoms and
  fails on goals mixing them with strict/≤ arithmetic (use
  `Nat.add_lt_add_of_lt_of_le`, `Nat.lt_of_lt_of_le`, `Nat.le_trans`
  instead); `rw [h]` rewrites all occurrences including under binders/divisor
  positions, so recursive values under `rw`-sensitive goals must be frozen
  with `generalize ... = c` first. `set` is unavailable in this core setup.
