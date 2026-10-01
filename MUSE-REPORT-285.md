# MUSE-REPORT-285: Mathematical carry and signed-overflow characterisation

## Task
Model-free mathematical characterisation of the EXISTING `add64`/`sub64`
flags (`grammatik/Grammatik/X86/Wort.lean`): signed interpretation of `Wort`,
OF iff the exact signed sum/difference leaves [-2^63, 2^63-1], sign-bit
correctness, unsigned carry/borrow and low-byte parity facts. Reuse existing
operations; no second adder; concrete boundary witnesses incl. CF-true/OF-false,
OF-true/CF-false, signed-min negation/subtract overflow; reusable lemmas for
the instruction-semantics/optimiser consumer. No source/ISA hardware theorem.

## Deliverable (owned files only)
- `grammatik/Grammatik/X86/FlagBeweis.lean` (NEW, ~550 lines)
- `grammatik/Grammatik.lean` (+1 line: `import Grammatik.X86.FlagBeweis`)
- this report

## What was proved (all over the REAL `Wort`/`add64`/`sub64`, no new adder)
- §1 signed interpretation: `sint` (`BitVec.toInt`), `sint_mem` (range).
- §2 sign-bit readings: `sfTest_msb`, `sfTest_toNat` (2^63 threshold),
  `sint_neg_of_msb`, `sint_nonneg_of_nmsb`, `sfTest_sint` (SF = negative).
- §3 wrap cases: `bmod_in_range`, `bmod_high`, `bmod_low` (exact value of
  `s.bmod 2^64` per range, via `Int.bmod_eq_of_le`/`Int.bmod_def` + `omega`).
- §4/§5 main results, nothing assumed:
  `add64_of_iff`, `sub64_of_iff` (OF = true iff exact signed sum/difference
  is outside [-2^63, 2^63-1]), via `add64_of`/`sub64_of` + sign-bit case
  analysis; wrappers `add64_sint`, `sub64_sint` (`BitVec.toInt_add/sub`).
- §6 optimiser facts: `add64_sint_eq_of_no_overflow`,
  `sub64_sint_eq_of_no_overflow` (cleared OF: result IS the exact value),
  `add64_of_false_bounds`, `sub64_of_false_bounds` (cleared OF = range
  conjunction), `add64_cf_false_nat`/`add64_cf_true_nat` (cleared/set carry
  = exact Nat sum / sum - 2^64), `sub64_no_borrow_nat`/`sub64_borrow_nat`,
  `add64_sf_sint`, `sub64_sf_sint`.
- §7 parity: `parityEven_low8` (PF reads only the low byte),
  `parityEven_zero`, `parityEven_xor_self`, `xor64_pf_self`.
- §8 boundary witnesses (`decide` conjunctions, value + flags jointly):
  `sint_werte`, `wit_add_carry_no_overflow` (CF true OF false),
  `wit_add_overflow_no_carry` (OF true CF false), `wit_sub_min_negation`
  (`0 - min`), `wit_sub_min_minus_one` (`min - 1`, CF false OF true),
  `wit_add_both_flags` (`min + -1`, CF true OF true), `wit_sub_min_self`.
- §9 memory probes: `flagMem` store + `flagMemNachAdd`/`flagMemNachSub`
  with `wit_mem_add_carry`, `wit_mem_sub_overflow` (store/load roundtrip
  of boundary results through `write64`/`read64` jointly with flag facts).

## Checks
- `./lean-probe grammatik/Grammatik/X86/FlagBeweis.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (369 jobs).`
- `#print axioms`: every theorem depends only on `propext`,
  `Classical.choice`, `Quot.sound` (or a subset); `sint_werte` on none.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no MarKE/diagnostic/
  gift/example numbers; no Rust; no `Prop`-typed premises; every premise used.
- Rule 13: no theorem quantifies over program syntax (`Vertrag`/`Stmt`/
  `Endblock`/`ErgExpr`/`Expr`/`Args`) and the task names no `ZEUGE:` target,
  so no `_zeuge` companion is required; §§8-9 are the concrete jointly
  instantiated boundary + memory probes.

## Refusals / cuts (see `CUTS:` in the file)
- No instruction execution, decoder, encoding, TSO bridge, source
  correspondence, ABI/loader, cost transfer or final-image acceptance.
- Only 64-bit `add64`/`sub64` (+ XOR parity) characterised; narrow widths
  have no flag snapshots here. PF even-parity and AF nibble-carry meanings
  are inherited from `Wort.lean`, stated, not verified against hardware.
- No source/ISA hardware theorem claimed; physical instruction semantics
  remain named silicon behaviour plus a later bridge.

## Notes on the task text (possible defects, not blockers)
- `WELLE-A.md` and `LEAN-ZUERST.md` do not exist in this clone
  (`muse/285` branched from an older master); AGENTS.md was followed from
  the lane prompt. Missing files were not read outside the clone.
- Two toolchain facts future lanes should know: (1) there is no mathlib,
  so `rcases`/`obtain`/`by_contra`/`norm_num` are unavailable — `cases`,
  `by_cases`, `omega`, `simp`, `decide` cover everything used here;
  (2) `simp` evaluates `2^64 : Int` to a literal, which breaks hypothesis
  matching — §4/`mpr` keeps the `bmod` form symbolic and proves the sign
  fact via `rw [hw]; omega` instead; (3) a `{ x with f := <expr> }`
  update whose value breaks after `:=` fails to parse — keep the value on
  one line or lift it to a top-level `def` (as in §9).
