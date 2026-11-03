module

import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Legacy

namespace Gabbro.Grammatik.Parser.Uebersetze.ExistsWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private def unit : UProg :=
  {tabs := [{name := "T", count := 2, cols := []}], locks := [], fns := []}

private def function : UFn :=
  {name := "sample", params := [], kinds := [], res := none,
   held := [], puts := [], gives := [], body := [], ret := .empty}

private def context : UCtx :=
  {names := [], kinds := [], types := [], tabs := unit.tabs, locks := [], held := [],
   res := none, fname := "sample", alias := [], lits := []}

/-- An ordinary expression parsed through `parseOr`, not the predicate-only reader:
    `true && exists k in slots of T : false`. -/
private def tokens : List Token :=
  [.wort "true", .zeichen "&&", .wort "exists", .ident "k", .wort "in",
   .wort "slots", .wort "of", .ident "T", .zeichen ":", .wort "false", .ende]

private def elaborated : Except String UEns := do
  uBool context (← parseTop tokens)

public theorem exists_boolean_elaboration_zeuge :
    elaborated = .ok (.and .tru (.einige "T" "k" .fls)) := rfl

/-- The endpoint is the concrete canonical G constructor, including its table,
    body and access guard; success or an untyped intermediate shape would be weaker. -/
public theorem exists_boolean_concrete_term_zeuge :
    (do
      let predicate ← elaborated
      lowEns unit [] [] function none predicate) =
      .ok (Expr.and (D := declOf unit) Expr.tru
        (Expr.existsSlots (D := declOf unit) (0 : Fin unit.tabs.length) Expr.fls
          (by intro resource member; cases member))) := rfl

public theorem exists_boolean_binding_zeuge :
    (do
      let expression ← parseTop tokens
      let (statements, _) ← uAnwReihe unit.tabs [] 1000 context
        [.bind false "found" (some (.atom "bool")) expression]
      pure statements) = .ok [UStmt.bindB "found" (.and .tru (.einige "T" "k" .fls))] := rfl

end Gabbro.Grammatik.Parser.Uebersetze.ExistsWitness
