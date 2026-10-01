# MUSE-REPORT-331: full Lean-folder optimiser specification + friend handoff

Branch: `muse/331`. Clone/toplevel verified `/home/simon/Dokumente/gabbro-muse/a331`.
Task: lane 331 (documentation only; no Lean/Rust/source/Spec/goal changes).

## Deliverable

- NEW `grammatik/OPTIMIZER.md` (1041 total lines, 842 non-empty useful lines:
  within the requested ~500–900 useful lines). Complete optimiser
  design/specification in the actual Lean model folder, in English, with
  root-relative links adjusted for `grammatik/` (`../DIRECT-COMPILER.md`,
  `../DIRECT-COMPILER-DESIGN.md`, `../dokumente/...` via `../lanes/...`,
  `Grammatik/X86/*.lean`).
- Covers all 12 requested sections: scope/trust path; IR/effects/control
  interface; exhaustive rule table (fold, SCCP, GVN/CSE, DCE, checks,
  strength, alias, LICM, inline/devirt, unroll/tails, SIMD planned, FP,
  peephole/address/branch/alloc); invariant-fact lifetime (entry/return/
  ruhe/holder, writer blackout, SSA versions, callee invalidation,
  whole-unit footprint, no guessed ensures, call ghosts); concurrency/
  per-width atomics (TSO bridge OPEN, RMW/order/reread rules, local-fence
  limits, MMIO profile); budget/stop vs machine-work vs hardware-time;
  certificate/checker architecture (proposed `OptCert`/`pruefeOpt` Bool,
  soundness derived not assumed, negative default + conservative route);
  fast pipeline (compact IR, revisioned analyses, fuel, deterministic
  parallelism, untrusted cache, timeouts, warm batching, final fetched-
  bytes revalidation); pass ordering with MEASURE-THEN-CHOOSE caps and
  the safety-above-final-10% rule; verification register/test matrix
  (generic statements + joint `_zeuge`, poison certs + positive probes,
  10 test rows, gates, dependency graph, UNKNOWN measurements);
  friend handoff (reserved `Grammatik/X86/OptimizationRules.lean` +
  `OptimizationWitnesses.lean`, start order, acceptance contract, no
  second IR, submission mechanics); open obligations O1–O10 + Lean-first
  phase order. Ends with an honest CUTS block.

## Actual inspected state (not repeated from docs)

- `grammatik/Grammatik/X86/` holds 20 accepted modules, 11,223 lines
  (per-file `wc -l` taken). Headers + key definitions read for
  `InvariantenOpt` (`alsLitOpt`, `litLeBool`, `isWahrAll`, `holdsBool`),
  `AufrufOpt` (`GeistAntwort`, `geistPaar`, `geistPaar_laenge`),
  `StaerkeReduktion` (`shlW`, `shrW`, `maskW`, `mod_pow2_and_mask`),
  `Typen` (`Register`, `Breite`, `Flags`, `Bedingung`), `TSO`
  (`TSOEintrag`, `TSOZustand`), `Wort`/`Ganzzahl`, `Speicher`
  (`lesbar8`, `read64`), `Zugriffe` (`Zugriff`), `Gleitprofil`
  (`MXCSR`, `mxcsrRundungRNE`), `Vektor`.
- Absence verified 2026-10-01: NO `X86/IR.lean`, NO
  `X86/OptimizationRules.lean`, NO `X86/OptimizationWitnesses.lean`.
  The file states lane 287's IR ([287.md](../lanes/287.md), read in
  full) is PENDING and distinguishes that task from an accepted file;
  the two friend-reserved paths are given as path strings, never as
  hyperlinks (no dead future-file links).
- Reviewer lane 334's task ([334.md](../lanes/334.md)) read; the file
  is written to be reviewable against its checklist (single shared IR
  honesty, rule premises/certs, witness obligations, link resolution,
  planned-vs-proved precision).
- Link check: all 77 markdown links in `OPTIMIZER.md` resolve against
  the tree (script-checked, 0 bad). `HEAD` excerpts of
  `DIRECT-COMPILER.md`, `DIRECT-COMPILER-DESIGN.md`, and `emit.rs`
  (19,250 lines, construct scope referenced, not enumerated) read.

## Preserved guarantees / no overclaim

- No Lean, Rust, Spec, goal, diagnostic/gift/example number, or counter
  touched. `git status` shows only the two new files. No per-program
  rules; no `ensures` derivation; no refusal-to-warning; no speed/LOC/
  benchmark promise; full source-to-binary closure stated OPEN
  throughout; friend not claimed started.
- Priority recorded as specified: broad practical performance, last
  marginal ~10% qualitatively not needed, safety first, fast validated
  (not unvalidated) compilation.

## Build / verification

- Documentation task per lane instruction ("no gratuitous build");
  no `.lean`/`.rs` file added or modified, so `./lean-bau` is
  unaffected. Markdown link resolution verified by script (77/77 good).
  No `./lean-bau` run (nothing to build); reviewer can confirm green
  trivially since the tree's Lean inputs are untouched.

## Open / cuts

- Everything in CUTS of `grammatik/OPTIMIZER.md` applies: plan only,
  IR/certificates/validators/lowering/bridge/transfers unimplemented,
  measurements unknown. Nothing further open on this lane's side.

## Commit

Both owned files committed via `arbeitsprotokoll/.commitmsg` +
`./commit.sh` on `muse/331`.
