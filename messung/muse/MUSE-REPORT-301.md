# MUSE-REPORT-301: Independent review of candidate 285

## Scope and method

Reviewed ONLY the pinned snapshot in `.tmp/review/author-285/` per `SNAPSHOT.json`
(author 285, head `6e10c1deffe07a31bc19b7eda33be2626d4876b3`, base
`dd02d9120be5540dc3773affcc4c647c4bae940b`, clean, files: `MUSE-REPORT-285.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/FlagBeweis.lean`)
and its tool-result evidence `BUILD-EVIDENCE.json`. No other clone read, no code
edited, no central files touched. Existing source (`grammatik/Grammatik/X86/Wort.lean`,
`Speicher.lean`, `Typen.lean`) in this clone used only for cross-checking.

Checks performed in this clone:
- `./lean-probe .tmp/review/author-285/grammatik/Grammatik/X86/FlagBeweis.lean`
  => `== 0 error(s) in the COMPLETE output` (full axiom list printed, see below).
- `grep` for `sorry` / `admit` / `native_decide` / `^axiom` => all absent (rc=1 each).
- `grep` for second adder `def (add64|sub64|addB|subB)` => absent; file defines only
  `sint`, `flagMem`, `flagMemNachAdd`, `flagMemNachSub`.
- `grep` for `MARKE|N[0-9]{3}|gift|beispiel` => absent; no diagnostic/gift/example/CLI numbers.
- `grep` for `intro _|have _ :=` and contract-quantifier patterns => absent.
- `PATCH.diff` new-file section byte-compared against snapshot `FlagBeweis.lean`
  => identical (`PATCH-MATCHES-SNAPSHOT`).
- `PATCH.diff` file list is exactly the 3 owned files (report, one umbrella import
  line `import Grammatik.X86.FlagBeweis` appended to `Grammatik.lean`, new
  `FlagBeweis.lean`); no other files touched.

## What the candidate claims (bounded)

Mathematical characterisation of the EXISTING Lean `add64`/`sub64` flag snapshots
from `Wort.lean`: signed interpretation `sint` (`BitVec.toInt`), OF iff the exact
signed sum/difference leaves `[-2^63, 2^63-1]`, sign-bit readings, unsigned
carry/borrow Nat facts, low-byte parity facts, concrete boundary witnesses, two
memory roundtrips. Explicitly NO source/ISA hardware theorem; physical instruction
semantics remain named silicon behaviour plus a later bridge. CUTS block lists
exactly this.

## Findings

1. Main theorems `add64_of_iff` / `sub64_of_iff` are genuine derivations, not
   assumed equivalences. Proof path verified in source: `add64_of`/`sub64_of`
   (sign-bit OF definition in `Wort.lean` lines 186-205) + `sfTest_sint` rewriting
   + `BitVec.toInt_add`/`toInt_sub` wrap + the three `bmod` case lemmas
   (`bmod_in_range` via `Int.bmod_eq_of_le`, `bmod_high`/`bmod_low` via
   `Int.bmod_def` + `Int.emod_eq_of_lt`/`omega`). Case analysis covers
   in-range (reduces to sign-bit truth-table contradiction) and both out-of-range
   directions with the correct sign consequences. Nothing is a premise restated as
   conclusion; every premise is used (`omega` consumes range facts, `h` consumed
   via `simp [hc] at h` in the no-overflow corollaries).
2. Reuse, no second adder: confirmed. `add64_sint`/`sub64_sint` prove
   `(add64 x y).1 = x + y := rfl` then apply the toolchain `BitVec.toInt_add/sub`.
   Carry/borrow lemmas consume `add64_cf`/`sub64_cf`/`add64_wert`/`sub64_wert` and
   `Nat.mod_eq_of_lt`/`omega`. Sign lemmas consume `sfTest`/`msb` definitions.
3. Required boundary combinations all present and jointly instantiated (value +
   flags in one `decide` conjunction), verified green by the 0-error probe:
   `wit_add_carry_no_overflow` (CF true, OF false), `wit_add_overflow_no_carry`
   (OF true, CF false), `wit_sub_min_negation` (`0 - min`, CF true OF true),
   `wit_sub_min_minus_one` (`min - 1`, CF false OF true), `wit_add_both_flags`
   (CF true OF true), `wit_sub_min_self`, plus `sint_werte`. Correct values
   (e.g. `0xFF..FF+1=0`, `0x7F..FF+1=0x80..00`, `min-1=max`) match the
   pre-existing `Wort.lean` probes and standard two's complement.
4. Memory probes are real state-changing roundtrips, not empty runs:
   `flagMem` is fully permissive with zeroed bytes; `flagMemNachAdd/Sub` are the
   stores after `writeBytes`; `wit_mem_add_carry`/`wit_mem_sub_overflow` prove
   `write64 ... = some ...` jointly with `read64 ... = some ...` via the existing
   `read64_nach_write64` (which exists with that exact signature in this clone's
   `Speicher.lean`), plus joint flag facts by `decide`. The `writeBytes` arity
   in this clone (`Speicher -> Adresse -> Wort -> Adresse -> Byte`) matches the
   candidate's `{ flagMem with bytes := writeBytes flagMem 0 ... }` usage, and the
   probe passes here. (BUILD-EVIDENCE shows the author hit and repaired the
   `{ x with f := }` line-break parse and the `writeBytes` arity during
   development; final snapshot is the repaired form.)
5. Axioms: independently reproduced `#print axioms` output lists only `propext`,
   `Classical.choice`, `Quot.sound` or subsets, `sint_werte` on none. Matches the
   report's claim exactly.
6. Rule 13: no theorem quantifies over program syntax (`Vertrag`/`Stmt`/`Endblock`/
   `ErgExpr`/`Expr`/`Args`) and the owner task names no `ZEUGE:` target, so no
   `_zeuge` companion is required. The §§8-9 concrete boundary + memory probes
   jointly instantiate values, flags and stores anyway.
7. Claim boundaries honest: no TSO, decoder, encoding, source correspondence,
   ABI/loader, cost or final-image claim in code or report; narrow widths, PF
   even-parity meaning and AF nibble meaning explicitly inherited/stated, not
   verified against hardware. No genericity violation, no name-specific rule, no
   inferred `ensures`, no weakening. Report's `./lean-bau` 369-job line was not
   independently re-run (per review instructions, no gratuitous full builds);
   the delivered bounded claim rests on the reproduced 0-error `lean-probe` plus
   axiom output, which is the needed gate for this file.
8. Report discrepancies: none material. `BUILD-EVIDENCE.json` shows the expected
   failed intermediate probes (unknown `BitVec`/`Int` lemma names, the
   `writeBytes` arity error, an 8-error intermediate `FlagBeweis.lean` state);
   these are development traces, and the final snapshot probes green. The note
   about missing `WELLE-A.md`/`LEAN-ZUERST.md` is consistent with this clone
   (absent here too) and correctly handled by staying inside the clone.

No defect found. No counterexample reproduced because every checked claim held;
there was nothing to refute.

## Verdict rationale

The bounded delivered claim is true, the needed checks (`lean-probe` 0 errors,
axiom standardness, no forbidden tactics, no second adder, joint boundary and
memory witnesses, honest CUTS) are green, and no material defect remains. This
does not mean compiler or binary validation is complete; it means this one
mathematical component is sound for its stated consumer use.

CANDIDATE: 285 6e10c1deffe07a31bc19b7eda33be2626d4876b3
VERDICT: ACCEPT
