/-
  GAP-25 `costexpr` (G-COST) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, twenty-fifth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, section 9): costexpr = "O" "(" expr ")".
  invariant = "invariant" ident "cost" costexpr "runs" ( "online" | "offline" ).

  MAPPING RULE (tree vs token). `costexpr` has no constructor: the asymptotic
  class annotates the INVARIANT declaration, and checking it against the
  declaration is not a term. The parser keeps the bound expression `e` for the
  checker (the `D.Inv` predicate and `Programm.invariante` see the invariant,
  not the class) and records the `O(…)` wrapper as measurement-side metadata:
  which growth class the invariant's cost was declared under. `O` is a G6
  identifier in fixed position, not vocabulary; the `expr` inside is an
  ordinary expression with an ordinary tree.

  MINIMAL PARSE WITNESS. Surface `invariant I cost O(n) runs online` with
  `n = 200`: the checker sees bound 200, the class tag `O`. The model below
  is the split: bound expression for the checker, wrapper for the record.
-/
import Grammatik.Syntax

namespace P21.Gap25CostExpr

/-- Elaboration split: the bound goes to the checker, the class to the record. -/
def costOf (bound : Nat) : Nat × String := (bound, "O")

-- Surface `cost O(n)` with n = 200: checker sees 200, record keeps the class.
example : costOf 200 = (200, "O") := rfl
-- The class tag never depends on the bound value.
example : (costOf 200).2 = (costOf 5).2 := rfl

-- Carrier link: the invariant predicate the class annotates (the class is not in it).
open Gabbro.Grammatik in
#check @Programm.invariante

end P21.Gap25CostExpr
