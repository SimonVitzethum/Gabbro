/-
  File:      Grammatik/Parser/Anweisung.lean
  Subject:   T3 PART 2 (PLAN-TRANSLATION-VALIDATION.md section 1): Gabbro
              statements and blocks (SYNTAX.md section 7) over the Lean
              lexer and expression parser.

  The surface tree `SAnw`/`SEnde` with fuel-indexed readers
  (`parseStmt`, `parseBlock`, `parseTopStmt`, `parseTopBlock`).
  Probes live in `Parser/AnweisungProben.lean`.
-/
module
public import Grammatik.Parser.Expr.Typ
public import Grammatik.Parser.Stmt.Anweisung.Defs2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here, and every shape difference against
  `crates/gabbro-syntax` found by the probes.

  *Every difference below was found by reading `ast.rs`/`parse.rs`
  (`cargo` cannot run in this lane); each is a documented gap, not a
  silent one.*

  1. Predicates ride raw: loop headers (`traverse` domains,
     `retry … until`, invariants), `narrow` ranges, `xform` bodies,
     `awaits`/`publishes` payloads and `exchange` tails are raw
     words, never `pred`/`domain` trees. There is no `pred`
     reader (SYNTAX.md section 5) in this lane.
  2. Type ascriptions ride raw: `let x : T = …` skips `T`
     unchecked (`nimmBisZeichen "="`), so a malformed type reads
     as long as it holds no top-level `=`.
  3. `let … else` accepts any expression source; `parse.rs`
     refuses non-call non-place sources (`P016`).
  4. `fnStart` (like `schleifenKopf`) steps over an `effects {…}`
     group and stops at any other `word {` adjacency: a header
     brace inside parens (an anonymous `structty` in a signature)
     would stop it early. No corpus signature carries one.
  5. `nimmBisWort`/`nimmBisZeichen` track only braces: a `;` or
     `else` inside a string cannot occur (strings lex as one
     token), and parens/brackets need no tracking for the
     stoppers used.
  6. `schliesseBlock` splits a trailing `return`/`leave`/`next`
     off EVERY block: a mid-body `return` at the end of a loop
     body reads as an ender, where `parse.rs` keeps it a plain
     statement (`endblock` only at function/`else` level).
  7. `P033` (lone `;`), `P035` (abolished forms), error recovery
     (`synchronisiere_anweisung`) and spans: refused or dropped;
     this reader stops at the first error with no code.
  8. `beqSAnw`/`beqTopStmt`/`beqTopBlock` are not proved sound or
     complete: the probes compare by kernel `Bool` evaluation
     (see also the equality-shape finding below).
  9. `parseTopStmt`/`parseTopBlock` are total but not complete:
     fuel `length * 8 + 32` suffices for every probe (each
     `decide` checks its own fuel); a huge input may report
     out-of-fuel instead of parsing.
  10. No printer, no round trip: statements/blocks have no
      `druck`, so there is no `print_parse` for this level.
  11. EQUALITY SHAPE (measured 2026-09-13): kernel `decide` does
      not reduce recursive `Bool` equality over a MUTUAL
      inductive family -- even comparing two empty blocks gets
      stuck (not slow: 2M heartbeats still stuck). Larger mutual
      `def` blocks compile to the irreducible `PSum` fixed point
      (`#print` shows it), which `decide` cannot unfold; the
      two-function shape compiles to `brecOn`, which reduces.
      Consequence: statements AND blocks live in the ONE type
      `SAnw` (a block is a node), `else if` branches ride as
      `elsif` nodes and `match` arms as `arm` nodes, and the
      equality block stays three functions. Any new tuple-list
      field on `SAnw` re-opens this trap.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopStmt
#print axioms Gabbro.Grammatik.Parser.parseTopBlock
