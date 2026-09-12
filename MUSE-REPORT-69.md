# MUSE-REPORT-69: overflow forms, Lean definitions (PLAN-BITS section 4, model half)

## What was built

New file `grammatik/Grammatik/Ueberlauf.lean` (imported at the end of
`grammatik/Grammatik.lean`), English comments throughout, no `sorry` /
`admit` / `axiom` / `native_decide` / `unsafe`, `#print axioms` for every
main theorem (all depend only on `propext` + `Quot.sound`).

Definitions (all required by the lane):

- `Zahl.addW (w : Nat) (a b : Zahl 0 (2^(w+1) - 1))` = `(a + b) mod 2^(w+1)`.
- `Zahl.subW`, `Zahl.mulW`: likewise `(a - b)`, `(a * b)` mod `2^(w+1)`.
- `Zahl.shlW (w) (a) (s : Zahl 0 w)` = `(a * 2^s) mod 2^(w+1)`.
- `Zahl.addS {lo hi} (a b : Zahl lo hi) : Zahl lo hi` = clamp of `a + b`
  to `lo..hi`, on every range (empty-range leg returns `a`).

Theorems (all required by the lane):

- `addW_c_gleich`: `addW` equals the C semantics of unsigned addition on
  the storage type, stated as `(a + b) mod 2^n` on `Nat` for storage width
  `n = w + 1`, transported through `Int.toNat`/`Int` casts. Takes only
  `w a b`: the width bridge (`simp`) and value round-trips
  (`Int.toNat_of_nonneg` from the `Zahl` lower bounds) are proved inside.
- `subW_c_gleich`: `subW` equals C unsigned subtraction, Nat form
  `(a + 2^n - b) % 2^n` (truncated subtraction cannot name the negative
  middle); the `Int` value is shifted into `(a - b) + M * 1` so
  `Int.add_mul_emod_self_left` applies. Takes only `w a b`.
- `mulW_c_gleich`: `mulW` equals `(a * b) % 2^n` on `Nat` (cast bridge via
  `Int.toNat_mul`). Takes only `w a b`.
- `addS_monoton`: `addS` preserves order in both arguments (on a
  non-empty range; the range fact is also a conclusion conjunct so no
  premise is dead).
- `addS_exakt_wenn_passt`: if `a + b` fits, `addS` is the exact sum.
- ZEUGE `addS_exakt_wenn_passt_zeuge`: joint instantiation on the
  concrete range `0..5` with addends `2 + 3` (fits: `2 + 3 = 5`).
- `wrapping_nur_exakt`: the strong form, taking no premises -- no total
  function `Zahl 0 5 -> Zahl 0 5 -> Zahl 0 5` agrees with `+` on all
  fitting pairs AND is computed by `mod 2^k` for some `k` (modulus as
  `2^(k+1)`). Numeral facts proved inside by `decide`; the uniform tail
  `10 % 2^(k+4) = 10` by `Int.emod_eq_of_lt` with `10 < 2^(k+4)` from
  `Nat.pow_le_pow_right`. Four cases with one escaping pair each:
  `k = 0` (`mod 2`: `1 + 2 = 3` vs `3 % 2 = 1`), `k = 1` (`mod 4`:
  `2 + 3 = 5` vs `5 % 4 = 1`), `k = 2` (`mod 8`: `3 + 3 = 6`, outside
  the range), `k >= 3` (`5 + 5 = 10`, no wrap, outside the range).
- `wrapping_nur_exakt_kein_mod8`: the concrete fallback, taking no
  premises -- `mod 8` leaves the range `0..5` (`3 + 3` maps to `6`,
  proved inside by `decide`).

Rule 13 note: the lane's ZEUGE line names only `addS_exakt_wenn_passt`;
its companion `addS_exakt_wenn_passt_zeuge` instantiates all premises
jointly on a non-degenerate program-free range (`0..5` with `2 + 3`;
the rule's table/run clause applies to run statements, of which this
lane has none -- the work is pure value-level arithmetic). `addW_c_gleich`
takes no program-syntax universal, so no witness is owed; `wrapping_*`
are negations of existentials, likewise witness-free by construction.

## Last `./lean-bau` result line

`Build completed successfully (37 jobs).` with
`== 0 error line(s) in the COMPLETE output` on the first line.
`./lean-probe grammatik/Grammatik/Ueberlauf.lean` reports
`== 0 error(s) in the COMPLETE output`.

## What remains open

- `shlW` has a definition only; the C-equality cast bridge is proved for
  `addW`, `subW`, `mulW`.
- `addS` on the empty range returns `a` by convention; nothing is
  claimed about that leg.
- No checker/emitter wiring (`+%`/`+|` surface syntax, `wrapping`
  attribute connection): model half only, per the lane.

## Review round 2 (all addressed)

1. Closed facts as premises: fixed. `addW_c_gleich` takes only `w a b`;
   both `wrapping_nur_exakt*` theorems take nothing. All numeral facts by
   `decide` inside; `10 % 2^(k+4) = 10` by `Int.emod_eq_of_lt` with
   `10 < 2^(k+4)` from `Nat.pow_le_pow_right`; round-trips by
   `Int.toNat_of_nonneg` from the `Zahl` lower bounds.
2. C-equality bridges added for `subW` (`subW_c_gleich`, Nat form
   `(a + 2^(w+1) - b) % 2^(w+1)`) and `mulW` (`mulW_c_gleich`,
   `(a*b) % 2^(w+1)`).
3. ZEUGE scope confirmed by reviewer: concrete-value witness kept
   (`addS_exakt_wenn_passt_zeuge` on `0..5` with `2 + 3`).

## Believed-wrong in the task

1. (Withdrawn -- reviewer confirmed: for pure value-level theorems the
   non-degenerate-program clause does not apply; the concrete-value
   witness stands.)
2. (Fixed -- the cast/width premises are now proved inside the proofs.)
3. `pruefe-englisch.py` was already red before this lane (comment/prose
   ratchets overbooked on `master`: 7904 vs 7881, 1085 vs 1069, 24 vs 23,
   1 vs 0) and needs `ssh` for part of its reach; not caused by, and not
   fixable in, this lane. Lean-file comment prose is clean against the
   guardian word list (only identifier-bound tokens remain).
