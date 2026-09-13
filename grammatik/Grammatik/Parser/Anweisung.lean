/-
  File:      Grammatik/Parser/Anweisung.lean
  Subject:   T3 PART 2 (PLAN-UEBERSETZUNGSVALIDIERUNG.md section 1): Gabbro
              statements and blocks (SYNTAX.md section 7) over the Lean
              lexer and expression parser, step 1.

  Skeleton: the surface AST `SStmt`/`SBlock` and a stub reader. Forms,
  printer and probes land in the next steps.
-/
import Grammatik.Parser.Ausdruck

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- A surface statement: SYNTAX.md section 7 `stmt` without types,
    spans or attribute checks. Expressions ride as `SExpr`, blocks as
    `SBlock`; heads that the reader does not yet split store their
    raw words (`sonst String`, e.g. `traverse` headers). Against
    `ast.rs` `StmtArt`: every constructor below names its Rust
    counterpart in its doc comment. -/
inductive SStmt
  | lass : String → SExpr → SStmt
  deriving Repr

/-- A surface block: a statement list (`block`; `endblock` lands next). -/
inductive SBlock
  | mk : List SStmt → SBlock
  deriving Repr

/-- Stub reader: always reports missing fuel. -/
def parseStmtStub : Except String SStmt :=
  .error "no fuel"

end Gabbro.Grammatik.Parser

/-
  CUTS: everything of section 7 except `let x = e;` is open (see file
  header: this is the skeleton step).
-/

#print axioms Gabbro.Grammatik.Parser.parseStmtStub
