# MUSE-REPORT-158 (lane 158: term identity, the Rust half, differential)

## What was built

1. `grammatik/Grammatik/TermIdent104.lean` (143 lines), imported at the end
   of `grammatik/Grammatik.lean`. Twelve `rfl`-checked differential
   witnesses: for every `CertExpr` shape the Rust printer
   (`crates/gabbro-check/src/certemit.rs`, `CertExpr::print`) can emit, a
   checked Lean term `e` with `printInt e = some c`, where `c` is spelled
   EXACTLY as Rust prints it (verified against the `print` arms and unit
   tests of `certemit.rs`). Witness 1 is the first program that works:
   `beispiele/104-referenz.gab` (`const NKONTO : u32 = 2` -> `(.lit 2)`).
   No new definitions, no new theorems (anonymous `example`s only), no
   `sorry`/`axiom`/`admit`, English throughout, `CUTS` block at the end.
   There is no `#print axioms` because there is no named theorem; the
   witnesses are `rfl` equalities over `printInt` (whose axioms are those
   of `ZeugnisIdent.lean`: `propext, Classical.choice, Quot.sound`).
2. `instrumente/pruefe-termidentitaet.py` (executable measurement):
   verifies the Rust print arms against their unit-test vectors textually,
   executes the standalone `certemit` test suite (`rustc --test`, no cargo,
   no network), compares every Rust template against the Lean `CertExpr`
   spelling, runs a corpus census over `beispiele/*.gab`, generates one
   Lean file per corpus program under `$TMPDIR/termident/programs`, checks
   the goals through the repo's `./lean-probe` (queued; content-deduped
   with one combined run to spare the shared queue), and prints
   match / mismatch / not-comparable counts with reasons.

## Last builds

- `./lean-probe grammatik/Grammatik/TermIdent104.lean` -> `== 0 error(s)`.
- `./lean-bau` -> `== 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (143 jobs)`
  (`[141/143] Built Grammatik.TermIdent104`).
- `python3 instrumente/pruefe-termidentitaet.py` ->
  `RUST OK: test result: ok. 28 passed; 0 failed`,
  `LEAN combined 28 values -> 0 error(s)`,
  `LEAN TermIdent104 shape battery -> 0 error(s)`,
  `LEAN mismatch demo shl/shr -> 3 error(s)` each (nonzero = confirmed),
  `== counts: 51 match, 2 mismatch, 60 not-comparable (0 BAD rust-src lines)`.
- `python3 instrumente/pruefe-kennungen.py` -> `ALL PASS`.
- `python3 instrumente/pruefe-englisch.py` -> 2 German hits, both in
  pre-existing files (`lean_g.rs`, `main.rs`, `saetze.rs`); none in
  lane-158 files.
- `python3 instrumente/pruefe-zahlen.py` -> BEFUNDs only in pre-existing
  files (`RUECKLAUFWERTE.md`, `TODO.md`, `PASSREGISTER.md`, `README.md`,
  `ZEREMONIE.md`: stale counts/patterns, red before this lane); none
  names a lane-158 file. Not fixed here: count registers drift under
  parallel lanes, and touching them collides on merge.

## Counts, exactly

- MATCH (10 shapes): `lit`, `add`, `div`, `band`, `bor`, `bxor`, `wide`,
  `var`, `glob`, `slot` -- Rust string and Lean `CertExpr` spelling
  identical, Lean side `rfl`.
- MATCH (41 corpus programs): every bare-numeral `const` value checks as
  `printInt (.lit n) = some (.lit n)` (28 distinct values, one combined
  Lean run, 0 errors; per-program files ride on it by content identity).
- MISMATCH (2, findings): Rust `Shl`/`Shr` print with NO width --
  `(.shl (.lit 3) (.lit 2))`, `(.shr (.lit 12) (.lit 2))` -- while
  `CertExpr.shl/shr` and `printInt` carry one (`(.shl 3 …)`). The Rust
  strings are not `CertExpr` terms at all: a generated file pasting one as
  the expected term fails with `Application type mismatch` (3 errors).
  Same gap as MUSE-REPORT-149 measured; reported exactly, not weakened.
- NOT COMPARABLE (60): 6 shapes Lean prints but Rust has no variant for
  (`sub`, `neg`, `mul`, `rem`, `sdiv`, `srem` -- no `CertExpr::` use in
  `certemit.rs`); 54 corpus programs with no bare-numeral `const`
  (`konst_zahl` folds only `Zahl` literals: `6 * 7`, names, table
  literals like `const SQUARES` yield no certificate by construction).

## What remains open (also in-file CUTS)

- The Rust residue lane 149 booked is still trust base: nothing proves
  `certemit.rs` prints `printInt e` for the CHECKED `e`. This lane shows
  the two printers agree shape by shape where both exist; the implication
  "the printed term is the checked term" is not in Lean.
- `konst_zertifikate` (`emit.rs:2909`) is dead code: its only caller is its
  own unit test. Wiring it to the emitter (over CHECKED const values)
  is the Rust-side step that would make the corpus differential live.
- Per-program declarations: the generated checks run on `refD` (the task's
  "generated Lean term" fallback). Typing each program's own `lean-g`
  export and re-running the comparison per declaration is future work
  (needs a built binary; `target/` is absent in this lane).
- Table/field carriers travel as constructors in Lean and as names in Rust
  (witness 11): same shape, spelling differs by construction.

## Task feedback (rules 4/12/13)

- "For every expression the corpus certifies (run `gabbro certificate`
  over `beispiele/*.gab`)": `gabbro certificate` dispatches to
  `zeugnis::zeige` (`main.rs:516`), the TRANSLATION certificate, which
  carries no `CertExpr` terms -- the corpus certifies ZERO expressions
  through that command (verified by reading `zeugnis.rs`; no binary was
  built in this lane to re-measure what the source already says). The
  `CertExpr` printer has no CLI path at all. I measured what the Rust side
  actually prints (its unit-test vectors, executed: 28 passed) instead of
  what the command name suggests.
- "Obtain the same typed expression via `gabbro lean-g` where it can
  export": `lean-g` exports G program terms (declarations/programs), not
  per-expression typed terms for certificate comparison, so even where it
  exports there is no `e` to compare against. Used generated Lean terms
  throughout (the task's stated fallback).
- "Runs `lake env lean` on each": hard rule 2 forbids bare `lake`/`lean`;
  the script calls the repo's `./lean-probe` (queued) instead, and checks
  byte-identical goals once plus one combined run -- re-running an
  identical goal measures the shared queue, not the claim.
- No rule-13 witnesses: the file adds no theorems (anonymous `example`s
  only) and the task names no `ZEUGE:` target. The generic `glob` witness
  (example 12) quantifies over a declaration and one of its globals, not
  over program syntax, so no inhabitation burden attaches.
- No codes, gifts, or examples used (none reserved).
