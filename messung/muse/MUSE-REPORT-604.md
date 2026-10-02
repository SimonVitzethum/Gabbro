# MUSE-REPORT-604: Float payload and exception observability in real source

*Lane 604, branch `muse/604`, clone `/home/simon/Dokumente/gabbro-muse/a604`.
Read-only audit; owns only `dokumente/x86/FLOAT-OBSERVATION-CLOSURE.md` + this report.*

## What was done

Audited the real source pipeline for channels that can distinguish
model-equivalent FP results (NaN payload, signed zero, sNaN quieting,
MXCSR/sticky observation): typed source syntax (`Syntax.lean`,
`Typen.lean`, `Semantik.lean`), checker (`m1.rs`, `namen.rs`,
`umgebung.rs`), exporter (`lean_g.rs`), GabbroV bridge (`Body.lean`,
`Coverage.lean`, `V1/V2`), target models (`X86/ScalarFloat`,
`X86/Gleitprofil`, `X86/FloatExceptions`), emitted C forms
(`emit.rs`, `CFormenF.lean`), lexer/AST float forms, probes, metal
entry, corpus. Full findings + ownership plan P0–P5 live in the owned
doc; headline results below.

## Findings

1. **NaN payload: no value to observe.** `Val (.fl..) = Gleit lo hi`
   requires finiteness; literals are finite decimals only (no NaN/sNaN/
   inf spelling in `lex.rs`); computed NaN/inf is `Logik.bereich` proof
   duty; gate answers fitted finite via `gleitWortPasst`. Non-observability
   holds by construction.
2. **Bit reinterpretation refused three times**: F005 (bitwise/shift/
   remainder on floats, gift 90 pins it), F005 mixed (no float/int op, no
   cast form exists), typed memory (no int-alias read; `memcpy` only in
   string helpers). `gleitRoh` reaches the machine only via oracle
   register writes; `-0`/`+0` both give `0`.
3. **F-EQ (new finding, code-read)**: float `==`/`!=` is CHECKED
   (`m1.rs:3698-3700`, no float distinction) and EMITTED as C `==`/`!=`
   (`emit.rs:op_text`, no float guard — only mixed-width arithmetic is
   refused) but has NO model term (`Expr.eq` is int-only; only
   `fllt`/`flle` exist) and NO correspondence row (`CFormenF` F4 covers
   `<,<=,>,>=` only). IEEE equality agrees with model-equivalence on
   finite values, so nothing observable breaks today — but it is a
   checked+emitted form with meaning in neither model. Recommend refusal
   (widen F005); zero corpus impact (no `beispiele/` file uses float
   `==`, verified by grep). Owning lane must do the 5-minute empirical
   confirmation (exact probe in closure doc §6 P0).
4. **MXCSR/sticky: no channel either direction.** No source form names
   it; emitted C has no fenv/MXCSR touch (only prelude comment +
   `FLT_EVAL_METHOD` assert + manifest `-ffp-contract=off`); probes read
   it test-only; `metall_schalte` (`start.S:146-150`) only
   saves/restores across context switch, establishes nothing. Gates
   cannot smuggle it (contracts over model values + template register).
   `GLEITKOMMA.md` §5 gaps stand: FTZ/DAZ unpinned, mode stability
   uncovered, fast-math unprobed.
5. **Target residue verified**: ScalarFloat source link is class-level
   with payload explicitly OPEN; sNaN-quieting divergence is conditional
   on an unreachable operand; `Codec`/`DecodingCoverage` have zero FP
   references (decoder path fully open, owner 575); GabbroV refuses all
   float duties (no Body bridge — middle layer missing); `gleitkommatext`
   would emit invalid C for NaN/inf bits (unreachable today; recommend
   defensive refusal).

## Deliverables

- `dokumente/x86/FLOAT-OBSERVATION-CLOSURE.md` (new): full audit with
  exact file:line evidence + ordered ownership plan P0–P5 with acceptance
  criteria + verification log + CUTS.
- This report.

## Build / test status

None — docs-only lane by task ("for tools/docs work do not add Lean
imports or claim a new Lean build"). No Lean/Rust file touched;
`git status` shows only the two owned files. No `./lean-bau` /
`./cargo-pruef` run (nothing to rebuild); the doc records this openly.

## What remains open / what I believe is wrong

- F-EQ confirmation is code-read, not executed — P0 owner runs the
  two-line probe before/after the refusal. If the probe shows the checker
  DOES refuse float `==` somewhere I did not read, §3 downgrades to a
  documentation gap (name the refusing rule).
- Initial MXCSR establishment on metal entry is unowned (only
  save/restore exists) — P2 owner question.
- The `nan_payload_unbeobachtbar` lemma (P1) must exclude `==`/`!=` by
  premise until P0 lands; I did not prove the lemma, only reduced it to
  a finite-valued statement with a `-0`/`+0` witness shape.

## Names of new definitions/theorems

None — no Lean work in this lane. Proposed (not proved): F005 widening
for float equality (checker lane), `gleit_beobachtbar_nur_klasse` +
`nan_payload_unbeobachtbar` corollary (model lane).
