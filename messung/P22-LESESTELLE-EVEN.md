# P22 — LESESTELLE parser gaps, even-numbered (12 closed, 1 withdrawn)

Lane p22, 2026-09-11. Base `2dc02ad` (verified: worktree `.claude/worktrees/p22`,
branch `p22-ziel` sits on `2dc02ad`, clean tree). Mission: close half the
LESESTELLE parser gaps; p21 takes the odd-numbered ones.

## Registry deviation (reported, not stopped on)

The mission names `grammatik/Grammatik/Syntax.lean` + `Zucker.lean` as the
grep scope. Both files contain **zero** `LESESTELLE` hits (checked
case-insensitively over `grammatik/`). The actual registry of the gaps is
`messung/SYNTAX-PARSER-ENTWURF.md` (26 LESESTELLE rows, file order lines
35-247), referenced by `dokumente/SYNTAX.md:1472`. Numbering below follows
that file in file order. No odd-numbered gap was touched.

## Count deviation (finding)

The draft claims 25 LESESTELLE rows (coverage section) and `SYNTAX.md:1472`
repeats 25. The file actually lists **26** LESESTELLE-kind rows: 14 G-LEX +
4 G-NAME + G-FILTER + G-LAYOUT + G-SPACE + G-HELD + 2 G-SCHEME + G-COST +
G-CONC = 26. The `relabel` arm of `opname` (line 208) is an annotation on a
core row, not a LESESTELLE row, and stays unnumbered and out of scope for
both lanes.

## Numbering (file order in SYNTAX-PARSER-ENTWURF.md)

Odd = p21 (names only, untouched): #01 ident, #03 digit, #05 int, #07 hex,
#09 float, #11 char, #13 newline, #15 path, #17 identlist, #19 buildgate,
#21 space, #23 inductlist, #25 costexpr.

Even = p22 (this file): #02 letter, #04 hexdigit, #06 dec, #08 bin,
#10 string, #12 quote, #14 comment, #16 pathseg, #18 regbind, #20 bitpos,
#22 heldpred, #24 induct, #26 concurrentdecl.

## Closed gaps (rule + witness)

| # | production | tree-vs-token mapping rule | witness probe |
|---|---|---|---|
| 02 | `letter` | Lexer character class (a-z, A-Z, German letters); letters build idents, no constructor takes one. | `messung/p22-lesestelle/p22-gap02-letter.lean`: class predicate, 6 checked examples |
| 04 | `hexdigit` | `digit \| a-f \| A-F`; feeds the `hex` spelling only. | `p22-gap04-hexdigit.lean`: class predicate, 5 checked examples |
| 06 | `dec` | Decimal spelling, one spelling only; the VALUE feeds `Expr.lit` and becomes both bounds n..n. | `p22-gap06-dec.lean`: token `42` is `Expr.lit` at `.int 42 42` |
| 08 | `bin` | Binary spelling (`0b` prefix, one spelling); same carrier as every integer spelling. | `p22-gap08-bin.lean`: token `0b101` is `Expr.lit` at `.int 5 5` |
| 10 | `string` | Quote-delimited runs; adjacent quoted parts concatenate (embedded quote by doubling). Content of claim/reason/assume/section/asm strings only. | `p22-gap10-string.lean`: part concatenation, 3 checked examples |
| 12 | `quote` | Delimiter U+0022; opens/closes strings, never content. | `p22-gap12-quote.lean`: `'"'.toNat = 34`, checked |
| 14 | `comment` | Starts at `--`, runs to newline, discarded before parsing. | `p22-gap14-comment.lean`: `--` head match, 4 checked examples |
| 16 | `pathseg` | Resolves before the tree to a declared Fn, Tab, or generated op; the tree carries the entity, never segment strings. | `p22-gap16-pathseg.lean`: `#check @Expr.fnref` takes `(f : D.Fn) (n : Nat)`, `#check @Stmt.call` takes `(f : D.Fn) (args : Args …)` — no `String` argument in either |
| 18 | `regbind` | The `name : value` pair never stands alone; it arrives as a positional argument of the foreign-body call. | `p22-gap18-regbind.lean`: `#check @Block.bindAxiom` takes `Args D Γ Λ (D.aparams a)`, `#check @Args.cons` builds them positionally |
| 20 | `bitpos` | Erased. `@[hi:lo]`, `offset_into`, `@bitpos` become `Expr.bitfeld` over `leseBytes` with computed `Nat` offset and width; a plain `int` position is the emitter's alone. | `p22-gap20-bitpos.lean`: `#check @Expr.bitfeld` ends in `… → Nat → (breite : Nat) → Expr …`, `#check @Expr.leseBytes` carries the offset bound `hi + ↑n ≤ D.count t` — no position syntax |
| 22 | `heldpred` | `Held(L)` (optional `shared`) is a derivation fact, carried as the context index `Res.held L ∈ Λ`; `shared` selects the second lock kind. | `p22-gap22-heldpred.lean`: `Res.held L ∈ [Res.held L]`, checked |
| 26 | `concurrentdecl` | No `Syntax.lean` constructor. Member paths resolve to dispatch roots; the set becomes the explicit `Nb : Nebeneinander` premise (Wettlauf §6), wired by Extraktion. | `p22-gap26-concurrentdecl.lean`: `Extraktion.miniNb 0 1`, checked — one declared pair set holding its pair |

## Withdrawn with reason (in place)

- #24 `induct` (G-SCHEME) — **withdrawn, unmappable.** `induct = "induction"
  "over" domain` names a compiler-generated scheme; per the draft row itself
  ("names the scheme, no term") and `Syntax.lean` ("by induction = kein
  Term") there is no constructor, no constructor argument, and no check
  anywhere in the tree that the name could attach to. A tree-vs-token rule
  would restate the absence, and no Lean witness can exhibit one: there is
  nothing to check, not even an erasure with a named carrier (contrast #20,
  whose erasure lands in `Expr.bitfeld`). The mapping, if any exists, lives
  in the compiler that generates the schemes — outside the grammar. No probe
  file was created for #24, deliberately.

## Verification

- Scoped builds only, local, `free -g` gate passed (11 GB available):
  `lake build Grammatik.Syntax Grammatik.Zucker` (5 jobs) and `lake build
  Grammatik.Extraktion` (11 jobs) in this worktree. No default/full target,
  no `cargo test`, no `abnahme`, no programmlogik build.
- All 12 probes checked green with
  `LEAN_PATH=grammatik/.lake/build/lib/lean lean <probe>`
  (12 of 12 `OK`, sequential, 2026-09-11). Build outputs under
  `grammatik/.lake/` are git-ignored and uncommitted.
- One repair during verification: `String.isPrefixOf` evaluates but does not
  kernel-reduce, so the #14 `rfl` examples failed; the probe now matches on
  the character list directly. Evidence that `#eval`-green is not
  `rfl`-green.
- No guardian surface touched: probes live under `messung/p22-lesestelle/`
  with `p22-` names (never `sonden/`, never `messung/fragmente/F*.gab`);
  English only; no German doc cell rephrased; no odd gap edited.

## Risks

- The 25-vs-26 count split: if p21 numbers over the claimed 25 instead of
  the listed 26, our parities diverge from #25 on. The table above pins the
  numbering to file order; reconcile against it, not the draft's total.
- `G-RELABEL` (relabel arm of `opname`) is unnumbered by design here; if a
  lane claims it, numbering shifts. It is named in this file so the claim is
  visible.
