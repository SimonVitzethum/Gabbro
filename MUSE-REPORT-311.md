# MUSE-REPORT-311: Range-justified integer strength reduction

## Task

Model range-proved integer strength reduction in Lean first, complementary to
lane 288 (invariant/check-branch elimination): `mul`/`div`/`rem` by powers of
two become shifts/masks only where source signedness/nonnegativity/divisor/range
proofs justify them; machine widths carry checked nonoverflow/shift counts;
undefined/fault behaviour is preserved. Generic correspondence against actual
source `eval`/`execStmt` plus real canonical word ops, one actual syntax
rewrite, one jointly inhabited source table-write witness. Owned files only:
`grammatik/Grammatik/X86/StaerkeReduktion.lean`, one umbrella import in
`grammatik/Grammatik.lean`, this report.

## What was done

New file `grammatik/Grammatik/X86/StaerkeReduktion.lean` (296 lines), in
`namespace Gabbro.Grammatik.X86`, opening `Gabbro.Grammatik` for the real
source types (`Zahl`, `Expr`, `eval`) and `ReferenzB` for the witness program.

New definitions (3 target helpers over the REAL canonical `Wort = BitVec 64`,
real `<<<`/`>>>`/`&&&`/`ofNat`, no model of their own):
- `shlW (x : Wort) (k : Nat) : Wort`
- `shrW (x : Wort) (k : Nat) : Wort`
- `maskW (k : Nat) : Wort` (`ofNat 64 (2 ^ k - 1)`, low `k` bits set)
- `staerkeMul` (actual source-syntax rewrite `a * 2 ^ k` -> `a << k`,
  typed `Expr` to typed `Expr`, shift amount as `Expr.lit`)

New theorems (all proved, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`):
- `mod_pow2_and_mask`: `n % 2 ^ k = n &&& (2 ^ k - 1)`, bit-for-bit via
  `Nat.testBit_mod_two_pow` / `Nat.testBit_two_pow_sub_one`.
- `mul_pow2_shl`: `Zahl.shl`-value = `Zahl.mul`-value for multiplier `2 ^ k`.
  Every premise (`hw1`, `hw2`, `h0`) is a source side condition forwarded
  to `Zahl.shl`; nothing weakened.
- `div_pow2_shr`: `Zahl.shr`-value = `Zahl.div`-value (`tdiv` vs `ediv`
  agree on nonneg numerators via `Int.tdiv_eq_ediv_nonneg`); `1 <= 2 ^ k`
  proved inline from `Nat.one_le_two_pow`, never assumed.
- `rem_pow2_band`: `Zahl.band`-value with mask `2 ^ k - 1` =
  `Zahl.rem`-value with divisor `2 ^ k`, through `mod_pow2_and_mask`.
- `sdiv_kein_shift`: `(-3).tdiv 2 = -1 /\ (-3) / 2 = -2` by `decide` --
  the documented REFUSAL of any signed reduction (no signed-division
  folklore, no arithmetic-shift lowering of `sdiv`/`srem`).
- `shlW_toNat`, `shlW_keinUeberlauf` (checked nonoverflow: product fits
  64 bits => shift IS the product), `shrW_toNat`, `shrW_breite`
  (count below operand `Breite` and below 64, result stays in width),
  `maskW_toNat` (`k <= 64`), `maskW_and`.
- `staerkeMul_behält`: the rewrite preserves the evaluated value against
  the REAL `eval` (proof: `mul_pow2_shl` on the evaluated operand; proof
  irrelevance covers the literal proof fields).
- `staerkeMul_behält_zeuge`: joint witness -- ALL premises (width 8,
  count 2, all range proofs by `decide`, `a := .lit 3`, worlds
  `refSp0.welt []`, `Env.nil`) instantiated together on the
  non-degenerate `refD` (`einzahlen` writes its table,
  `refEin_schreibt ()`); `3 * 2 ^ 2` becomes `3 << 2`.
- Probes on real operands: `probe_shlW` (`3 << 2 = 12`), `probe_shrW`
  (`12 >>> 2 = 3`), `probe_maskW` (`0xFF &&& mask 4 = 15`), all nonzero
  and value-changing.
- `speicher_shlW_rueck`: the shifted word goes through REAL `write64`/
  `read64` (reuses `zeugenSpeicher`, `read64_nach_write64`,
  `writeBytesN_hit`): stored, read back as `12`, byte observably changed.

`#print axioms` for every main theorem: all within
`propext, Classical.choice, Quot.sound` (word probes use subsets, two use
none); details in the build log.

Umbrella import `import Grammatik.X86.StaerkeReduktion` appended to
`grammatik/Grammatik.lean` (only existing-file change).

## Last `./lean-bau` result line

`Build completed successfully (372 jobs).` (was 371 before this file)

## What remains open (see also CUTS in the file)

- Actual bytes: correspondence stops at canonical `Wort` ops and
  `write64`/`read64`; encoding/decoding/RIP/ELF/execution transfer stays
  with the validation lanes (PLAN-UEBERSETZUNGSVALIDIERUNG §§0-5).
- No `div`/`rem` syntax rewrite yet (values proved, rewrite deferred to a
  lowering lane with its own witness); no `execStmt`-level statement
  (single-expression `eval` correspondence only; no log/budget/concurrency).
- Result RANGE text differs (`shl` range vs `mul` four-corner range):
  only VALUES proved equal; range transfer is the checker's `M104`.
- Hardware count masking (`k >= 64` masked on silicon, zero in the model)
  is not bridged; `shrW_breite` pins counts below the width instead.

## Task points believed wrong

None. One scoping note: the task asks for correspondence "against actual
source eval/execStmt" -- this lane delivers `eval` (expression level);
`execStmt` (statement runs) needs a statement-level lowering with
world-threading that does not exist yet for any optimisation lane, so it
is booked above as remaining work rather than half-delivered here.
Deliberately NOT done: any `sdiv`/`srem` rewrite (refused with reason),
reassociation, floats, inferred contracts.
