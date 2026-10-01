# MUSE-REPORT-600: Invariant-derived instruction selection with byte execution

## What was done

New file `grammatik/Grammatik/X86/InstructionSelection.lean`
(namespace `Gabbro.Grammatik.X86.Anweisungswahl`, umbrella import added to
`grammatik/Grammatik.lean`), connecting accepted source facts to actual
encoded pilot-instruction choice with three register-only rules. No new
interpreter, no new IR: every correspondence reuses source `eval`/`execBlock`
and the canonical decoded `schritt`/`decode`/`roundtrip`.

Definitions: `waehleNull` (zeroing choice keyed on flag liveness),
`waehleAddNull` (add-zero elimination), `waehleSelbstMov` (self-move
elimination on checked register equality), `wahlOk` (flag/branch checker),
`waehleInv` (invariant-gated elimination tagged by `InvScope`),
`invBeispiel` (witness invariant "slot reads zero").

Theorems: `xor_selbst_null`, `add_null_ident`, `null_laengen` (10 vs 3
bytes), `pin_xor_rax`, `pin_mov0_rax`, `runde_null_rax` (accepted round
trips), `schritt_null_mov`, `schritt_null_xor`, `schritt_null_gleich`,
`xor_selbst_zf`, `zweig_weicht_ab` (following `je` diverges, so missing flag
liveness is rejected), `waehleNull_le/tot`, `wahlOk_verweigert_xor_le`,
`wahlOk_erlaubt_mov/tot`, `schritt_addNull_wert`, `waehleAddNull_tot/le`,
`waehleSelbstMov_gleich`, `waehleSelbstMov_fremd` (alias check, premise
`dst ≠ src` used), `schritt_selbstMov_ident`, `quelle_add_lit_null`
(source `add a b` with COMPUTED `alsLitOpt b = some 0` preserves `eval`;
no Rust metadata trusted), `quelle_add_lit_null_zeuge` (joint witness:
source fact + `wV.schreibt` + memory-changing run `wit_step`),
`inv_am_eintritt`, `inv_standort_falsch`, `inv_nach_lauf_falsch` (entry fact
killed by the actual witness writer run; `waehleInv` without held stability
refuses), `waehleInv_verweigert`, `waehleInv_erlaubt`.

## Last build result

`./lean-bau`: `Build completed successfully (440 jobs).`
`./lean-probe` on the file: `0 error(s)`. Axioms are standard subsets of
`propext, Classical.choice, Quot.sound` (several theorems axiom-free).
No `sorry`/`admit`/`axiom`/`native_decide`; every premise is used.

## What remains open

See the `CUTS` block in the file. Main items: byte-level mul/shift strength
(the pilot has no `shl`/`imul` forms, so that stays a source-level value fact
in `StaerkeReduktion`); discharge of `InvScope` tags (goal legs at the use
site); load/store rules with real memory aliasing; cost/budget, call-log and
concurrency transfer; hardware correspondence.

## Task remarks

Nothing in the task was wrong, but one expectation needed scoping: a
"constant-strength" byte rule in the `StaerkeReduktion` sense (mul-by-`2^k`
to shift) is unstatable against the current 14 pilot forms, which have no
shift instruction. The lane delivers the statable fragment (add-zero identity
elimination) and records the shift half as an explicit CUT rather than
weakening the claim. Performance is stated as selected-instruction/length
facts only, as instructed.

## Producer/consumer interfaces and next tasks

- Produces: `waehleNull`/`waehleAddNull`/`waehleSelbstMov` choice functions
  with value/flag/byte lemmas, for the validator lane (`valX86`) to call as
  a checked peephole table; `wahlOk` as the flag-liveness gate shape.
- Consumers: validation/closing-theorem lanes can compose `runde_null_rax`
  with `schritt_null_gleich` for decode-then-execute byte observations.
- Next independent tasks: (a) a load/store selection rule with
  permission/footprint alias facts (needs `Zugriffe`/`AccessList`
  interfaces); (b) wiring `wahlOk`-style gates into the branch-layout leg;
  (c) a shift-instruction pilot extension if the ISA pilot grows, unlocking
  the `staerkeMul` byte half.
