# MUSE-REPORT-135 — T3 part 1: Lean lexer and expression parser

Lane 135, branch `muse/135`. Task: a Gabbro parser in Lean
(`Parser/Lexer.lean`, `Parser/Ausdruck.lean`), covering SYNTAX.md
section 4 `expr` with precedence and the new PLAN-BITS operators.

## What was built

Three new files (the third split off on reviewer instruction, see §4):

- **`grammatik/Grammatik/Parser/Lexer.lean`** — `Token`
  (`ident/wort/zahl/gleit/text/zeichen/ende`), `LexFehler`,
  `wortschatz` (242 words), first-character bucket table
  `schluesselTafelC`, total `lex : String → Except LexFehler
  (List Token)`. Theorems: `lex_total`, `lex_keywords`
  (`∀ w ∈ wortschatz, lex w = ok [wort w, ende]`, by `decide`
  over all 242 words), `lex_keywords_zeuge` (rule-13 companion on
  five concrete words), ten small lexer probes (`lex_bereich`
  maximal munch, `lex_operatoren` for `+% -% *% <<% +|`,
  `lex_at_hash`, `lex_kommentar`, `lex_text_beispiel`,
  `lex_text_offen`, hex/binary/float/ident examples), plus the 22
  `sondeNN_lex` token pins (see below).
- **`grammatik/Grammatik/Parser/Ausdruck.lean`** — surface AST
  `SExpr` (16 constructors; `Some(x)`/`None` stay calls as in
  `parse.rs`, `Klammer` dropped, `Zaehle`/`ArrayLit`/`LibraryCall`
  refused), structural `beqSExpr`, precedence parser
  (`parseOr`…`parsePrimary`, fuel-indexed, structural — no
  `termination_by`), printer `druck`, `parseTop`,
  `parseTopAusText`, micro round trip `print_parse` (5 legs
  `pp_lit/pp_var/pp_wahr/pp_falsch/pp_not` + conjunction).
- **`grammatik/Grammatik/Parser/AusdruckProben.lean`** — 22
  parse-shape probes `sonde01`–`sonde22` on `beispiele/` lines
  (18 corpus-cited + 2 plan-cited for `+%`/`+|`, which have zero
  corpus occurrences, measured).

Every probe is split in two: `sondeNN_lex` (in Lexer.lean) pins
the token list of the source line, `sondeNN` (in Proben) pins the
tree on those tokens. A mistranscribed list fails its lex pin
loudly. Tree shapes were compared against `ast.rs`/`parse.rs` by
reading (no cargo in this lane); all differences are booked in
the CUTS blocks (13 items: spans, `Klammer`, call labels,
float text vs bits, `result`/`old` context-sensitivity, `count`,
`sizeof`-over-type, `&T`, `beqSExpr` soundness, fuel
completeness, general round trip, micro scope, `None` printing).

## Verification

Last `./lean-bau` result lines:

```
== lake exit code: 0
== 0 error line(s) in the COMPLETE output
Build completed successfully (92 jobs).
```

`./lean-probe` on each of the three files: exit code 0 with the
`#print axioms` output visible (only `[propext,
Classical.choice, Quot.sound]`; `druck` is `[propext]`). No
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere. Every
theorem premise is used; no theorem quantifies over program
syntax, so rule 13 bites only on the ZEUGE target
`lex_keywords`, whose companion `lex_keywords_zeuge` instantiates
five concrete words jointly.

## Findings (measure, don't guess)

1. **Vacuous greens.** The old `./lean-probe` ignored Lean's exit
   code: an OOM-killed run printed "0 errors" on empty output. I
   lost several cycles to phantom greens before the reviewer
   fixed both wrappers (exit code + `LEAN ABORTED` + `NOT green`
   lines). Lesson I will keep: never rely on output you did not
   see end with your canary — I verified every claim below with
   a canary error visible in the output.
2. **Kernel heartbeat cliff for composed lex+parse.** Measured
   2026-09-13 with exit-code-checked probes: `parseTopAusText
   "1"`, `"(1)"`, `"1 + 2"` decide instantly; `"(1 + 2)"` and
   `"1 + 2 + 3"` exhaust the `whnf` heartbeat budget (200000);
   `parseTop` on literal token lists and `lex` alone stay fast at
   any tested size. Consequence: neither the general
   `parse_expr_roundtrip` nor an operator-sized `print_parse` is
   provable by kernel `decide` in Lean 4.33 — `print_parse` covers
   five micro trees (atoms + `!y`), operator shapes live at token
   level in the sondes. The general round trip needs induction
   over the parser (fuel sufficiency, printer injectivity,
   `beqSExpr` soundness), not evaluation.
3. **Well-founded recursion does not reduce in this kernel.**
   A `List.map`-based printer and `termination_by` parser got
   stuck (`decide` never fires); mutual *structural* recursion
   reduces fine. All three files use structural recursion only.
4. **Vocabulary count.** The task says 239 words; `kw.rs` and the
   SYNTAX.md table both hold **242** unique words (five stand in
   two rows each: `fields`, `protects`, `rank`, `chain`, `via`).
   `lex_keywords` covers all 242, a superset of the task.
5. **Printer bug found and fixed:** `ruf "None" []` printed as
   `None()`, which does not parse (`None` takes no parens);
   `druck` now prints bare `None`.
6. **`String ==` is kernel-slow** (byte-array unfolding);
   keyword/name/tree comparisons run on character lists
   (`schluesselTafelC`, `strEq`, char-list side tables).
   `lex_keywords` re-validates the bucketing word by word.

## What I believe is wrong in the task

- "239 words" should read 242 (see finding 4).
- "parseExpr (print e) = e for every SExpr produced by the
  parser" as a `decide` goal is not merely hard but
  kernel-intractable (finding 2); the task's fallback
  (`print_parse` on examples) is the right target but must
  itself stay micro-sized — my six-to-eleven-leg versions were
  all killed, five micro legs survive.
- The task names exactly two new files; the reviewer-approved
  third (`AusdruckProben.lean`) is load-bearing: one file with
  all probes is killed before it finishes (exit 137, no error
  line), while the three files build in 20 s + 2.3 s + 1.0 s.

## Open for T3 part 2 (statements, items, declarations)

- A statement/item/declaration reader on top of this expression
  parser (SYNTAX.md sections 6–12), reusing `lex`, `SExpr`,
  fuel discipline and the lex-pin/parse-pin split.
- General `parse_expr_roundtrip` by induction (needs fuel
  sufficiency per input size, printer injectivity, `beqSExpr`
  soundness/completeness as theorems, not `Bool` checks).
- `beqSExpr`/`beqTop` soundness (`= true ↔ =`), after which the
  sondes can state propositional equalities.
- Type-word arguments to `sizeof`/`lenof` (needs a `typeexpr`
  reader), `count k in D : p` (needs `domain`/`pred`), string
  positions/spans for diagnostics, refusal codes `L001`–`L007`.
- Environment note for the next lane: this box is under chronic
  memory pressure (swap full, five competing lanes); keep every
  kernel `decide` under ~15 s per file and always check the exit
  code line, not the error count.
