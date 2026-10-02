# MUSE-REPORT-616: Independent overnight closure review of 604

*Lane 616, branch `muse/616`, clone `/home/simon/Dokumente/gabbro-muse/a616`.
Review of exact candidate 604 (`6b289d14`, base `0044c258`) from
`.tmp/review/SNAPSHOT.json` + `author-604/` (PATCH.diff, OWNER-TASK.md,
MUSE-REPORT-604.md, BUILD-EVIDENCE.json, closure doc). Owns only this report.*

## Isolation

`pwd` = `/home/simon/Dokumente/gabbro-muse/a616`, branch `muse/616` — match,
proceeding. Candidate commit `6b289d14` is not present in this clone and no
fetch is permitted; review performed against the pinned PATCH.diff (only two
new files, no other paths) plus independent code-read of every load-bearing
claim in this clone (HEAD `377b290e`, descendant of the candidate base).

## What 604 claims

Docs-only audit (`dokumente/x86/FLOAT-OBSERVATION-CLOSURE.md` + report, no
Lean/Rust/checker/Spec/emitter/friend file touched): which real source-pipeline
channels can distinguish model-equivalent FP results. Headline: NaN
uninhabited by construction; bit reinterpretation refused (F005 x3); NEW
finding F-EQ (float `==`/`!=` checked+emitted, no model term, no
correspondence row — recommend F005 widening); no MXCSR/sticky channel either
direction; target residue (ScalarFloat class-level link, decoder FP gap open);
ordered ownership plan P0–P5. Explicitly NOT a proof; full validation OPEN.

## Independent verification (all by direct read/grep in this clone)

- **F-EQ checker leg**: `m1.rs:3698-3700` confirmed — the float F005 arm is
  inside `if !op.ist_vergleich()`, so all six comparisons skip it and return
  `Typ::Wahrheit`. Float `==` typechecks. As claimed.
- **F-EQ model leg**: `Syntax.lean:402-408` confirmed — `eq` takes
  `.int` args only; floats have only `fllt`/`flle`. No float equality term.
  `UebersetzeAllg.lean:798-799` maps `"=="` to `Expr.eq` unconditionally,
  so float `==` in `ensures` is likewise untranslatable (strengthens the
  finding beyond what §3 states). As claimed.
- **F-EQ emitter leg**: `emit.rs:op_text:18382-18383` writes `==`/`!=`
  unconditionally; the Binaer path (`18108-18114`) has no float guard; the
  only float refusal nearby (`18028-18046`) is arithmetic-only
  (`Plus|Minus|Mal|Geteilt` + mixed float/double). So `x == y` on two `f64`s
  emits `(x == y)`. As claimed.
- **F-EQ correspondence leg**: `CFormenF.lean:41` F4 covers `<,<=,>,>=`
  only (`ecorr_fllt/_flle/_flgt/_flge`, lines 294-319); no `eq` row. As
  claimed.
- **NaN uninhabited**: `Typen.lean:110-114` `Gleit` requires
  `gleitEndlich`; `lex.rs:532-593` float lexing is decimal-point-only
  (no NaN/sNaN/inf spelling; out-of-range → `L007`). As claimed.
- **Trichotomy comment**: `m1.rs:5600-5614` verbatim including
  "Gleitkomma waere ihr erster Verletzer". As claimed.
- **No MXCSR/fenv in emitted C**: `emit.rs` grep finds only the prelude
  comment, `FLT_EVAL_METHOD` assert and `-ffp-contract=off`. As claimed.
- **Decoder FP gap**: `DecodingCoverage.lean` has zero `FpBefehl`/
  `fpSchritt`/XMM/SSE references. As claimed.
- **GabbroV total float refusal**: stronger than the cited lines —
  `lean_g.rs:295-341` `VTy` has no float variant at all (`Int/Bool/Ptr/
  Index/Grund/Sum/Nie`), so `g_ty` on any float type necessarily fails.
  As claimed, independently grounded.
- **`gleitkommatext` latent note**: `emit.rs:17393-17402` confirmed —
  `NaN`/`inf` substrings pass through unreplaced (invalid C), unreachable
  today. Accurate and correctly labelled non-soundness.
- **Corpus**: `beispiele/26-gleitkomma.gab` uses `>=`/`<=`, no `==`;
  float mentions elsewhere are gifts/declarations, not float equality.
  The "zero of 146" count was not exhaustively re-proved here, but P0
  acceptance re-verifies it and §3 is honestly labelled code-read with the
  exact 5-minute probe specified — residual risk is bounded and owned.

## Rejection-criteria check

No hardware claim (CUTS: "MXCSR bit positions and silicon behaviour are
profile inputs, never verified here"); no self-consistency-as-proof; no
guessed ISA (decoder gap open); no hidden simulation (P1 lemma proposed, not
proved; sNaN divergence flagged conditional on unreachable operand); no
weakening (PATCH touches only the two owned docs files); no Spec/checker/
goal/friend edits; no new Lean theorems hence no witness/axiom obligation
(none added); CUTS precise (F-EQ code-read status, as-read line numbers,
named re-openers). The one over-broad sentence ("only `03-format` and
`26-gleitkomma` mention floats" — gifts do too) is immaterial to every
conclusion and needs no repair lane.

## Minimal repair locations

None required. Optional one-word touch-ups (the corpus sentence above) may
ride with any P0–P5 owner; not a condition.

## Bounded accepted scope

Docs-only audit + P0–P5 ownership plan with per-item acceptance criteria.
No closure of source→decoded-byte validation is claimed or granted; that
work remains OPEN per the doc's own header. Consumer owners: P0 (checker
lane, F005 widening + empirical probe), P1 (model lemma, needs P0 or the
exclusion premise), P2 (entry MXCSR establishment), P3 (emitter hardening,
may ride P0), P4 (owner 575 decoder path), P5 (per-op correspondence).

## Build / test status

None — docs-only review of a docs-only candidate; no Lean/Rust file touched
in either lane, nothing to rebuild. No `./lean-bau` / `./cargo-pruef` run;
per task, docs work adds no Lean imports and claims no Lean build.

## Names of new definitions/theorems

None — no Lean work in this review lane.

## Verdict

CANDIDATE: 604 6b289d14db15c76e3b6c28326adbbbbaad9fc2c0
VERDICT: ACCEPT
