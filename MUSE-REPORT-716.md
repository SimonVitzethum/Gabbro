# MUSE-REPORT-716: Rust compiler validation and ELF integration review

Lane 716, branch `muse/716`, clone `/home/simon/Dokumente/gabbro-muse/a716`
(verified: `git branch --show-current` = `muse/716`). Owned deliverable:
`dokumente/x86/UPSTREAM-PR-2-RUST-REVIEW.md` (written, in this commit).
No source, import, witness, test or semantics file was changed in this
clone; all testing happened on the disposable fixture `.tmp/fix716`
(git-ignored) plus the fixture-only probe/ log files under `.tmp/`.

## What was done

Read the pinned PR2 (`987b286df9d8465714a00bab8226f7b9c7f4afc1`, base
`5d5a72e5889a3063b417b955fa7824e72c52ef7c`) and PR1 bodies in full from
`.tmp/UPSTREAM-PRS/pr-{1,2}/METADATA.json`; measured the diff (27 files,
+31296, Rust only under `crates/gabbro-check/src/x86/`, Lean only new
`X86/` modules + `Grammatik.lean` imports); read all 8 changed Rust
modules end to end (`codec`, `lower`, `opt`, `pipeline`, `elf`, `mod`,
both goldens) and spot-checked every lowering/validator/image/entry
function against its named Lean counterpart (`ExpressionLoweringDeep`,
`Pipeline`, `PipelineImage`, `PipelineEntry`, `OptimizationRules`).

Built the fixture `.tmp/fix716` = tracked base + the exact 27 PR files
overlaid (verified byte-identical with `diff -q`), plus a fixture-only
repro test and a fixture-only filtered wrapper `cargo-pruef-x86` (same
`cargo-slot`/`lean-slot` queues, `cargo test --no-fail-fast x86`). Ran it
to completion.

## Results

- PR claim reproduced: 137 x86 tests pass on the PR tree, golden 42 FALL
  cases and 4059-vector codec sweep included. Fixture line:
  `== total: 137 passed, 2 failed, 0 ignored`, where the 2 failures are
  my own B1 probes and nothing else.
- B1 confirmed executable: `opt.rs:304:22`
  (`attempt to divide with overflow`) and `opt.rs:312:22`
  (`attempt to calculate the remainder with overflow`) for
  `const_int(Div(MIN,-1))` / `const_int(Rem(MIN,-1))`. Fix:
  `checked_div`/`checked_rem`.
- Further findings B2–B5 + two minor blemishes with locations, fixes and
  a merge verdict are in the review document. Headline integration
  answer: the Rust side is a handwritten mirror with no live Lean step,
  no AST/checker/CLI connection and no user path from `.gab` source to
  image; golden agreement is frozen point-in-time evidence. Verdict:
  accept as untrusted producer after B1, no CLI activation, no
  loadability claim (the ELF images are pinned non-page-faithful by
  test, which is correct and must stay).

## Build record

- This clone: no build run (nothing to build — review lane, no source
  touched). `./lean-bau` result line: not applicable; Lean gate belongs
  to a Lean review lane (only `Grammatik.lean` imports are affected).
- Fixture: `./cargo-pruef-x86` → `== exit 101; failing tests: 2`
  (`x86_716_div_min_durch_minus_eins`,
  `x86_716_rem_min_durch_minus_eins`; all 137 PR tests green). Full log
  at `.tmp/fix716/.tmp/cargo-test-full.log` (disposable).
- Bottleneck recorded: the `cargo-slot` lease was held by other lanes;
  the fixture build waited ~15 min before starting. No gate was skipped.

## Open / believed-wrong

- Nothing in the task looks wrong; the PR body's modesty ("tested on
  golden cases, not proved", "would not load correctly under a real OS
  loader") matches the code. One correction to keep attached: "Lean
  stays the authority" is true of the theorems, not of any runnable
  path — the toolchain never consults Lean.
- B3 (`Shr` on negatives: Lean floor vs Rust trunc) and B5 (div-by-zero
  fold direction) are divergences proven by reading both sides, not by
  execution; golden coverage decides whether they bite, and the suite
  passes, so they bite only outside the covered fragment.
- B2 (shift-count masking for `Shr/Shl` reports with `k >= 64`) and B4
  (unbounded recursion) are latent: no consumer / no reachable depth
  today. Reported so the consumer lane does not inherit them silently.
