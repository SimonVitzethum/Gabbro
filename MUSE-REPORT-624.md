# MUSE-REPORT-624: Direct-source closure — float source observations

Lane 624, clone `/home/simon/Dokumente/gabbro-muse/a624`, branch `muse/624`.
Owned files only: `grammatik/Grammatik/X86/FloatSourceObservations.lean`
(new), one additive import in `grammatik/Grammatik.lean`, this report.
Task source: `dokumente/x86/FLOAT-OBSERVATION-CLOSURE.md` (owner lane 604),
closure item P1 with the F-EQ exclusion of P0.

## What was done

Proved the finite-value float observation-equivalence fragment over the ACTUAL
language operations (one existing typed source semantics, no new IR, no new
interpreter, no checker/emitter/s Rhaggypec/friend edits): `fllt`/`flle`
(`gleitLt`/`gleitLe`), `gleitNarrow` and `gleit` range-holding (`gleitPasst`),
register-write truncation (`gleitRoh`). The premise is comparison agreement
only — never a blanket all-observations assumption. Payload equality is never
claimed (class-level only). NaN non-inhabitation is an honestly labelled
corollary. Float `==`/`!=` is explicitly excluded (F-EQ stays a tracked
separate prerequisite; no checker change, as instructed).

Definitions: `vergleichsGleich` (comparison agreement in all four directions
against every third value); witness declaration `fltWitD` (one table, one
`.fl (0,1) (1,1)` field) with `fltWitSig`, contract `fltWitV`, oracle
`fltWitO`, callee table `fltWitR`, values `minusGleit`/`plusGleit` (`-0`/`+0`
in `0 .. 1`, decided), world `fltWitSigma` (slot holds `-0`), environment
`fltWitRho` (variable holds `+0`), expressions `fltWitI`/`fltWitE`.

Theorems (all in `Gabbro.Grammatik.X86`, file
`grammatik/Grammatik/X86/FloatSourceObservations.lean`):

- Comparison core: `null_flt_still`, `nullN_klasse`, `nullP_klasse`,
  `nullN_exakt`, `nullP_exakt`, `null_flt_links`, `null_flt_rechts`,
  `null_fle_links`, `null_fle_rechts`, `null_vergleichsGleich`
  (`vergleichsGleich (-0) (+0)`, the inhabited model-equivalent finite pair).
- Consequences: `null_roh_gleich` (`gleitRoh` agrees, both `0`),
  `vergleichsgleich_passt` (GENERIC: comparison agreement + finiteness gives
  `gleitPasst` success agreement for every range), `null_passt_gleich`
  (its signed-zero instance).
- NaN corollary: `kein_gleit_nan` (no `Gleit` value is NaN).
- F-EQ exclusion pins: `eval_fllt_ist_gleitLt`, `eval_flle_ist_gleitLe`
  (covered operators, `rfl` on actual `eval` arms),
  `eval_eq_beobachtet_int` (`eq` observes integer `.n` only; `Expr.eq`
  takes `.int` arguments, so no model term equates two floats).
- Target reuse hooks for the ScalarFloat decoder consumer: `null_wf`,
  `null_muster_rundweg` (exact word round-trip of both zeros via
  `bites64_muster64`, stronger than class-level),
  `null_ucomi_gleich` (UCOMISD equal row on `(-0,+0)`, matching
  `fle`-both-true), `cvttPaket_entfaltet` (let-free unfold equation),
  `cvttPaket_gleitRoh` (GENERIC: `cvttPaket = gleitRoh` on finite
  well-formed values — the consumer reuses source truncation).
- Joint witness: `null_beobachtung_zeuge` — writing contract AND function,
  reached one-step `assignSlot` run changing the slot `-0 -> +0`
  (memory-changing step through real `execStmt`/`World.schreibSlot`),
  observations agreeing (`vergleichsGleich`, `gleitRoh`, `gleitPasst`),
  bit patterns disagreeing (`zuBits` inequality — the concrete
  distinguishing bit-level operation no source form can observe).
- Refusals: `nan_passt_verweigert` (NaN answer never fits),
  `bereich_passt_verweigert` (`5.0` against `0 .. 1` never fits).
- Inhabitation companions for the three syntax-quantified `eval` pins:
  `eval_fllt_ist_gleitLt_zeuge`, `eval_flle_ist_gleitLe_zeuge`,
  `eval_eq_beobachtet_int_zeuge` (all premises jointly instantiated on the
  non-degenerate witness declaration; the run half is covered by
  `null_beobachtung_zeuge` on the same declaration).
- Small facts: `fltWitHT`, `fltWitHw`, `fltWitSchreibt`, `fltWitHL`.

## Check results

- `./lean-probe grammatik/Grammatik/X86/FloatSourceObservations.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (whole `grammatik/`): `Build completed successfully (446 jobs).`
- `#print axioms`: core float lemmas depend on `[propext]` only (or nothing);
  the `eval` pins, the joint witness and its companions inherit
  `[propext, Classical.choice, Quot.sound]` from `Semantik.eval` — within
  the standard goal axioms, nothing new introduced. No `sorry`/`admit`/
  `axiom`/`native_decide`/`unsafe` anywhere.
- `cargo-pruef` NOT run: no Rust file touched (Lean-only lane); nothing in
  this change can affect `cargo test` (no shared sources with the Rust
  crates beyond the checked-in tree, which builds green).

## What remains open (exact CUTS, also at the file end)

- Generic comparison-agreement-implies-truncation-agreement is NOT proved:
  from `vergleichsGleich` alone, `gleitRoh` agreement needs exact-value
  uniqueness, which is open. Proved for the inhabited `-0`/`+0` pair.
  Explicit obstruction, not a hardware axiom.
- F-EQ (refusing checker-accepted float `==`/`!=`, closure P0) is a separate
  checker prerequisite; untouched here by instruction.
- The `ucomiFlags`/`cvttPaket` hooks are word-level reuse pins, not
  decoded-byte steps: `Codec` still has no FP forms, so no byte sequence
  decodes to a float form (unchanged audit finding).
- sNaN-quieting divergence stays conditional on the unreachable sNaN
  operand; MXCSR/sticky flags have no source channel.
- Full source-to-final-loaded-bytes validation remains OPEN.

## Apparatus findings (for follow-up lanes)

- Unfolding `cvttPaket` directly poisons downstream `rw`/`cases` (its body
  `let` shadows the argument, so occurrences are missed) and tripped kernel
  `(kernel) excessive memory consumption` on the joint case analysis.
  Workaround that held: prove a let-free unfold equation by `rfl`
  (`cvttPaket_entfaltet`) and rewrite with it instead of `unfold`.
- `cases h : e` fails with `generalize ... not type correct` on `dite`
  goals whose branches carry proof fields mentioning `e`
  (`gleitPasst_isSome` attempt); a `by_cases` + `dif_pos`/`dif_neg`
  transport of the conjunction proved `vergleichsgleich_passt` instead.
- `Option.noConfusion` mis-elaborated in one match context; plain `cases`
  on the equation (none vs some) is the robust closer there.

## Task assessment

Nothing in the task turned out to be wrong. Two scoping notes: (1) the task
asks for "the exact finite-value observation-equivalence fragment" while P1
of the audit also lists a generic lemma — the generic part is proved for
range-holding but recorded open for truncation (above), which matches the
audit's own "proved obstruction must be labelled blocked" rule. (2) The
inhabitation rule's "reached memory-changing run" is satisfied by a
one-step `assignSlot` run with a changed slot value (`-0` to `+0` are
numerically equal but different memory states — bit patterns differ, which
is exactly the point of the lemma); no multi-step trace was needed.

Commits on `muse/624`: `fb4d032c` (skeleton), `8a065594` (comparison +
range fragment), `e8acdad9` (F-EQ pins + target hooks), `16262b91`
(witness + refusals + zeuges). This report is the final commit.
