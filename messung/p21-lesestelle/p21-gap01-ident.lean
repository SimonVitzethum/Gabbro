/-
  GAP-01 `ident` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, first LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): ident = ( letter | "_" ) { letter | digit | "_" }.

  MAPPING RULE (tree vs token). `ident` has no constructor: it never stands
  alone as a term. The lexer classifies the spelling; the parser discharges it
  in exactly two ways, and the spelling itself is erased in both:
    (a) a binder or declaration name is recorded at its declaration site
        (fn name, param, let-bound name, table, lock, mark, ...);
    (b) every USE resolves to the POSITION of its binder -- a de Bruijn index
        into the context -- not to the spelling.
  So `let x = 3; x` maps the use `x` to index 0, i.e. `Expr.var .hier`;
  under one more binder the same spelling maps to `Expr.var (.dort .hier)`.
  Two different spellings bound at the same position are the same term.

  MINIMAL PARSE WITNESS. Surface `x` with binders ["x"] resolves to 0;
  with binders ["y", "x"] to 1. The model below is the resolution step;
  the carrier link is the `Var`/`Expr.var` constructor it feeds.
-/
import Grammatik.Syntax

namespace P21.Gap01Ident

/-- Binder-position resolution: the use `m` against the binder stack (head = innermost). -/
def resolve : List String → String → Option Nat
  | [], _ => none
  | n :: ns, m => if n == m then some 0 else (resolve ns m).map (· + 1)

-- Surface `let x = 3; x`: the use resolves to index 0, the tree is `Expr.var .hier`.
example : resolve ["x"] "x" = some 0 := rfl
-- Surface `let y = 1; let x = 2; x`: one binder in between, index 1.
example : resolve ["y", "x"] "x" = some 1 := rfl
-- An unbound spelling resolves to nothing: there is no position, hence no term.
example : resolve ["y"] "x" = none := rfl

-- Carrier link: the position feeds `Var`, the use feeds `Expr.var`. No spelling remains.
open Gabbro.Grammatik in
#check @Expr.var
open Gabbro.Grammatik in
#check @Var.hier

end P21.Gap01Ident
