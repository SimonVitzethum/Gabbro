# MUSE-REPORT-315: Independent review of lane 311 (strength reduction)

Scope: review ONLY the pinned snapshot in `.tmp/review/` per SNAPSHOT.json
(author 311, head `7c72ae49d764f9c055bf7185cc29357384a2fb7a`,
base `345627a46732923a03a5f792ff4050b7e3b7c837`, files
`MUSE-REPORT-311.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/StaerkeReduktion.lean`, clean true).
No code or central-file edits; this report is the only owned file.

## Checks performed

- Read the full candidate file (296 lines), PATCH.diff, MUSE-REPORT-311.md,
  BUILD-EVIDENCE.json, OWNER-TASK.md, and the real source definitions the
  candidate builds on in this clone: `Typen.lean` (`Zahl`, `Zahl.mul/div/
  rem/band/shl/shr`, `Int.tdiv_eq_ediv_nonneg`), `Syntax.lean` (`Expr.shl/
  shr/mul/div/rem/band/lit` signatures and result ranges), `Semantik.lean`
  (`eval` delegates to the same `Zahl` ops; `.lit n` is `⟨n, le_refl,
  le_refl⟩`), `ReferenzB.lean` (`refD`/`refEin`/`refEin_schreibt`),
  `X86/Typen.lean` (`Wort = BitVec 64`, `Breite`), `X86/Speicher.lean`
  (`write64`/`read64`/`zeugenSpeicher`/`read64_nach_write64`/
  `writeBytesN_hit`/`addrOff_null`).
- Ran `./lean-probe .tmp/review/author-311/grammatik/Grammatik/X86/StaerkeReduktion.lean`:
  `== 0 error(s) in the COMPLETE output`. `#print axioms` output matches
  the author's build evidence theorem-for-theorem: value/bridge/rewrite
  theorems within `[propext, Classical.choice, Quot.sound]` or subsets;
  `sdiv_kein_shift` and `probe_shlW` axiom-free.
- Grepped the candidate for `sorry|admit|native_decide|unsafe|^axiom`:
  no hits (the only `axiom` substring in the file is inside `#print axioms`
  lines). No `intro _` / `have _ :=` discards; every theorem premise is
  used (side conditions are forwarded into the `Zahl.shl/shr/band/div/rem`
  applications they came from).

## Findings (all report claims verified)

- Value correspondence is genuine, not assumed: `mul_pow2_shl`,
  `div_pow2_shr` (via the real `Int.tdiv_eq_ediv_nonneg` on nonneg
  numerators), `rem_pow2_band` (via `tmod=emod` round-trip plus the proved
  `mod_pow2_and_mask`) compute against the actual `Zahl` definitions;
  the `show` steps match `Zahl.shl/shr` (`a.n * 2 ^ b.n.toNat`,
  `a.n / 2 ^ b.n.toNat`) and `Zahl.mul/div` (`a.n * b.n`, `a.n.tdiv b.n`).
- The rewrite `staerkeMul` is well-typed real syntax (`Expr` to `Expr`,
  shift amount `.lit k`, result range `.int 0 (h1 * 2 ^ k.toNat)` exactly
  the `Expr.shl` range), and `staerkeMul_behält` proves value preservation
  against the real `eval`. Only VALUES are claimed equal; the range-text
  difference vs `.mul`'s four-corner range is honestly booked as the
  checker's `M104` business.
- Witness gate holds: `staerkeMul_behält_zeuge` instantiates ALL premises
  jointly (`w=8, k=2`, proofs by `decide`, `a=.lit 3`,
  `refSp0.welt []`, `Env.nil`) on non-degenerate `refD` with
  `refEin_schreibt ()` (the table `einzahlen` writes). A second,
  memory-moving witness `speicher_shlW_rueck` stores `shlW 3 2` through
  real `write64`/`read64` and proves the byte observably changed.
  Probes are nonzero and value-changing (`3<<2=12`, `12>>>2=3`,
  `0xFF &&& mask 4 = 15`).
- No weakening: all source side conditions (`hw1/hw2/h0`, divisor `>= 1`
  proved inline from `Nat.one_le_two_pow`) are kept; `sdiv`/`srem` are
  refused with a `decide`d counterexample, not lowered. Target helpers
  are the canonical `BitVec` ops, no private model. Nonoverflow
  (`shlW_keinUeberlauf`) and count-below-width (`shrW_breite`, hence
  `< 64`) are checked, not masked; the hardware-masking gap is labelled
  OPEN in CUTS, not bridged silently.
- Genericity holds: every theorem is ∀-quantified; the only program name
  (`refD`) appears in the witness, never in a definition or rule. No
  contract parameters quantified away, no inferred ensures, no cost/TSO/
  byte-encoding claim beyond the stated Wort/memory boundary. Report
  numbers verified (296 lines, 372-job green build, one-line umbrella
  import, CUTS present).
- Scoping note (reported, not a defect): the owner task's "eval/execStmt"
  is delivered at `eval` (expression) level; there is no `div`/`rem`
  syntax rewrite and no `execStmt`/log/budget/concurrency transfer. All
  three are explicitly listed as OPEN in CUTS and the report. Under the
  lane-315 rule, honestly labelled coverage cuts are not bugs.

No material defect found. No counterexample to reproduce.

CANDIDATE: 311 7c72ae49d764f9c055bf7185cc29357384a2fb7a
VERDICT: ACCEPT
