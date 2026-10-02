# MUSE-REPORT-717: exact review of author candidate 716

Lane 717, branch `muse/717`, clone `/home/simon/Dokumente/gabbro-muse/a717`
(verified: `pwd` + `git rev-parse --abbrev-ref HEAD` = `muse/717`; mismatch
protocol satisfied). Owned deliverable: this file only. No source, import,
witness, test, semantics or PR file was changed in this clone.

CANDIDATE: 716, head `378fe47c99f959d050e0e3635d0041331089d7c4`
(base `011ff474004a8a617338584d68b13a64c87b1051`), files
`MUSE-REPORT-716.md` + `dokumente/x86/UPSTREAM-PR-2-RUST-REVIEW.md`
(per `.tmp/review/SNAPSHOT.json`). The author head object is not in this
clone, so the candidate was reviewed as the exact supplied `PATCH.diff`
(2 diffs) plus the file copies under `.tmp/review/author-716/`: patch adds
73 lines (report, file has 73 + trailing newline) and 257 lines (review
document, file has 257 lines) — patch and copies agree. Author base
`011ff474` exists locally. Pinned upstream PR2 reviewed against:
`987b286df9d8465714a00bab8226f7b9c7f4afc1` (base
`5d5a72e5889a3063b417b955fa7824e72c52ef7c`), both commit objects present
locally; all source checks below are against the exact pinned bytes in
`.tmp/UPSTREAM-PRS/pr-2/`, never against a live tree.

## VERDICT: ACCEPT

The audit is accurate: its measurements reproduce, its code quotes match the
pinned bytes, every finding B1–B5 verifies, its integration verdict
(accept-as-untrusted-producer after B1; no CLI activation; no loadability
claim) follows from the evidence, and I found no missed MUST-FIX, no
invented proof completion, no weakened refusal and no stale candidate.
ACCEPT means the audit is accurate; it does NOT approve or merge upstream
PR2 itself. The retained open MUST-FIX is B1 (`checked_div`/`checked_rem`
+ regression tests); B2–B5 stay as stated advisories/pins.

## What was checked (all against pinned bytes)

- Diff scope: `git diff base head --stat` = 27 files, 31296 insertions(+),
  zero deletions. Name list: 8 files, all `crates/gabbro-check/src/x86/`
  (`codec.rs 772`, `codec_golden.rs 4372`, `elf.rs 257`, `lower.rs 390`,
  `mod.rs 48`, `opt.rs 2019`, `pipeline.rs 2119`, `pipeline_golden.rs 2037`
  lines — all counts match §0); 18 new `grammatik/Grammatik/X86/` modules;
  `Grammatik.lean` +18 lines, all `import Grammatik.X86.*`. Nothing else
  moves: no checker pass, no `emit.rs`, no CLI, no `Spec.lean`, no
  `gabbro_syntax`. `typen.rs` predates the PR (present at base = wave A).
- Integration answer (handwritten Rust mirror, no live Lean step, no user
  path): confirmed. `mod.rs` "Unwired…" quote verbatim; `opt.rs` CUTS
  ("No conversion…", "No CLI wiring…") verbatim; `pipeline.rs` CUTS
  ("input model is NOT the typed Lean syntax…", "TESTED on the golden
  cases, not proved") verbatim. Zero `std::process`/`Command`/`std::env`/
  `std::fs`/`std::net`, zero `unsafe`, zero `todo!`/`unimplemented!` across
  all 8 files; no `.unwrap()`/`panic!`/panicking `.expect(` in library
  code (only `unwrap_or`/`unwrap_or_else` and the custom `Cursor::expect`
  returning `Result` — see nits). Golden headers state point-in-time
  evidence (scratch harnesses NOT committed, branch
  `feat/x86-compiler-pipeline` at `af57ba71`) — the audit quotes them
  fairly.
- Counts: 42 `FALL` case headers in `pipeline_golden.rs` (44 `grep FALL`
  hits = 42 cases + 2 code refs); `#[test]` attributes across the 9 x86
  files sum to exactly 33+13+49+17+4+1+2+8+10 = 137, matching the "137
  passed" claim. Codec header states 4059 vectors kept as data.
  `every_lean_case_has_a_rust_twin_and_back` asserts the 42-name list;
  `compile_to_image_agrees_with_the_lean_verdicts` asserts per-case
  two-sided agreement — the audit's methodology note is correct.
- Fidelity samples re-checked: `ohne_doppel` keeps LAST occurrence
  (filter `!gs[i+1..].contains(g)`); `sprung_ok` = `k < 2^31`;
  `prolog_ok` pairwise `q.0 != r.1 && q.0 != r.0` over later pairs,
  matching Lean `List.Pairwise ZugOk`; `int_wort`/`sprung_disp` wrap via
  `rem_euclid`; `bau_ok` contains `pl <= c.code_base` (blemish premise
  holds); `lies_elf` takes `d.get(start..)` (trailing bytes accepted —
  blemish holds); `seitentreu` + `pilot_images_are_not_page_faithful`
  (`assert!(!seitentreu(&bild(), 4096))`) present.
- B2: `strength_div`/`strength_mul(_comm)` unbounded in `k`
  (`pow2_log2` yields up to 126), only `strength_rem` bounds `k <= 64`;
  Lean `strengthDiv` likewise unbounded, `strengthRem` has `k ≤ 64` —
  the cross-PR note is correct. `TargetOp` is consumed nowhere in
  `lower.rs`/`pipeline.rs` (zero hits): advisory status correct.
- B3: Lean `constInt?` shr = `x / 2 ^ y.toNat` with Lean `Int` `/` =
  floor; Rust `Shr` fold = truncating `x / pow2(k)` (`opt.rs` ~323).
  `Shr(-3,1)` = `-2` vs `-1`: divergence real, uncovered-inputs-only
  status correct (suite passes).
- B4: `sink_tief`/`apply_block`/`to_opt_*`/`typ_ok_*`/`slot_adressen`/
  `grund_liste` recurse without depth budget; only the cert producer has
  `STEP_CAP`: latent robustness note correct, severity (no unsound
  accept) correctly stated.
- B5: Lean `lift2 f (some x) (some y) = some (f x y)`, so div-by-zero
  folds to `some 0` while Rust returns `None`: safe-direction claim
  correct.

## Executable reproduction (disposable fixture only, this clone untouched)

Fixture `.tmp/fix717` = detached worktree at the exact pinned PR2 head
`987b286d` (git-ignored `.tmp/`, removed after the run) + fixture-only
probe `crates/gabbro-check/tests/x86_717_sonde.rs` calling the real
`opt::const_int` on hand-built `IExpr::div/rem(lit(i128::MIN),
lit(-1))` + fixture-only filtered wrapper `cargo-pruef-717`
(`cargo test --no-fail-fast --test x86_717_sonde` through the same
`cargo-slot`/`lean-slot` queues). Full log: `.tmp/fix717-run.log`
(20 lines, retained clone-locally, ignored).

Result: `== exit 101; failing tests: 2` —
`x86_717_div_min_durch_minus_eins` panicked at
`crates/gabbro-check/src/x86/opt.rs:304:22`,
`x86_717_rem_min_durch_minus_eins` panicked at
`crates/gabbro-check/src/x86/opt.rs:312:22`
(`attempt to calculate the remainder with overflow`). B1 confirmed
executable at the audit's exact lines and messages. I did not rerun the
full 137 (author's fixture log + the exact 137 `#[test]` count above
cover it); the two failures here are my own probes, nothing else ran
in this filtered target.

Missed-panic scan (extra, beyond the audit): all raw `/ % << >>` in
library code of the 8 files reviewed — every remaining site is guarded
(`checked_*`/`saturating_*`/`rem_euclid`/`k>=64` branches/`slot_byte`
`i ≤ 7`/`breite ≤ 64`): no second B1 found. `pipeline.rs` `IntExpr`
has no Div/Rem nodes, so via `compile_to_image` the panic needs a
hand-built `opt::IExpr` — the audit's reachability sentence is precise.

## Nits (do not affect findings, verdict or repairs)

1. "debug panic / release wrap" (report §Results, review §4 B1): for
   Rust `/` and `%`, `MIN/-1` overflow panics in release too — the fix
   (`checked_div`/`checked_rem`) is identical either way.
2. "remaining `unwrap`/`expect`/`panic!` are inside `#[cfg(test)]`
   modules only, verified by line" (§1 item 4): the token `expect(`
   occurs in library code as the custom `Cursor::expect(&mut self)
   -> Result<(), String>` (opt.rs:729 + 9 call sites, all `?`-handled).
   Substantively true (no panicking expect/unwrap in lib code), literally
   imprecise. A future revision may say "no panicking `.expect()`/
   `.unwrap()`/`panic!`".

## Open / retained

- MUST-FIX (upstream PR2, retained): B1 — `x.checked_div(y)` /
  `x.checked_rem(y)` in `const_int` + the two regression tests.
- SHOULD before any consumer (retained as stated): B2 bound
  `Shr`/`Shl` reports to `k <= 63`; B3/B5 golden pins (negative-`Shr`
  fold, div-by-zero fold); B4 depth budget for lowering recursion.
- MUST NOT (retained): no CLI flag, no loadability claim, no
  "translation validation" label for golden agreement on this code.
- `./lean-bau`: not run — review lane, no Lean/Rust/comment file
  touched (owned file is this report only), so no build gate applies;
  same standing as author lane 716. No network/provider/credentials/
  outside-clone actions taken.
