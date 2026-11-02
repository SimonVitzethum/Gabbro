module

import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Termination

namespace Gabbro.Grammatik.Parser.Uebersetze.FoldWitnesses
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private def table : UTab :=
  {name := "T", count := 3, cols := [("v", (1, 9)), ("open", (0, 1))], bools := ["open"]}

private def context : UCtx :=
  {names := [], kinds := [], types := [], tabs := [table], locks := [], held := [],
   res := none, fname := "sample", alias := [], lits := []}

private def value : SExpr := .field (.index (.variable "T") (.variable "k")) "v"

private def operands (kind : XKind) : List SExpr :=
  [.variable "T", .tru, value] ++ (if kind == .foldAdd then [] else [.lit 99])

private def tokens (word : String) (empty : List Token := []) : List Token :=
  [.wort word, .ident "k", .wort "in", .wort "slots", .wort "of", .ident "T",
   .zeichen ":", .ident "T", .zeichen "[", .ident "k", .zeichen "]", .zeichen ".", .ident "v"] ++
    empty ++ [.ende]

public theorem add_parser_zeuge :
    beqTop (parseTop (tokens "add")) (.ok (.ext .foldAdd ["k", "slots"] (operands .foldAdd))) = true := rfl

public theorem min_parser_zeuge :
    beqTop (parseTop (tokens "min" [.wort "else", .num 99]))
      (.ok (.ext .foldMin ["k", "slots"] (operands .foldMin))) = true := rfl

public theorem max_parser_zeuge :
    beqTop (parseTop (tokens "max" [.wort "else", .num 99]))
      (.ok (.ext .foldMax ["k", "slots"] (operands .foldMax))) = true := rfl

public theorem add_expansion_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.map (·.1) =
      some [.bindMut "#fold:0:acc" 0 27 (.lit 0),
        .loopBeg "k" "T" .tru, .ifBeg .tru,
        .bind "#fold:0:value" none (.tab "T" "v" (.param "k")),
        .setVar "#fold:0:acc" (.eng (.add (.param "#fold:0:acc") (.param "#fold:0:value")) 0 27),
        .ifElse, .blkEnd, .blkEnd,
        .bind "#fold:0:acc:result" none (.eng (.param "#fold:0:acc") 0 27)] := rfl

public theorem min_expansion_zeuge :
    (expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin)).toOption.map
      (fun result => result.2.1.types.head?) = some (some (.int 1 99)) := rfl

public theorem max_expansion_zeuge :
    (expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax)).toOption.map
      (fun result => result.2.1.types.head?) = some (some (.int 1 99)) := rfl

/-- The fallback is evaluated after the loop, inside the empty-only branch. -/
private def emptyOnly : List UStmt → Bool
  | code => match code.reverse with
    | .bind .. :: .blkEnd :: .ifElse :: .setVar _ (.lit 99) :: .ifBeg (.not (.var _)) :: .blkEnd :: _ => true
    | _ => false

public theorem extrema_empty_only_zeuge :
    (expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin)).toOption.map
      (fun result => emptyOnly result.1) = some true ∧
    (expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax)).toOption.map
      (fun result => emptyOnly result.1) = some true := ⟨rfl, rfl⟩

/-- The filter guards the element read, rather than filtering a completed sum. -/
public theorem filtered_add_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"]
      [.variable "T", .field (.index (.variable "T") (.variable "k")) "open", value]).toOption.map
      (fun result => result.1[2]?) = some (some (.ifBeg (.tabB "T" "open" (.param "k")))) := rfl

private def lowered (kind : XKind) : Bool :=
  match uAnwReihe [table] [] 1000 context
      [.bind false "total" none (.ext kind ["k", "slots"] (operands kind))] with
  | .error _ => false
  | .ok (body, _) =>
    let function : UFn := {name := "sample", params := [], kinds := [], res := none,
      held := [], puts := [], gives := [], body, ret := .empty}
    (lowerAllg {tabs := [table], locks := [], fns := [function]}).toOption.isSome

/-- Each integer form reaches generic machine-G lowering through the real statement path. -/
public theorem add_lowering_zeuge : lowered .foldAdd = true := rfl
public theorem min_lowering_zeuge : lowered .foldMin = true := rfl
public theorem max_lowering_zeuge : lowered .foldMax = true := rfl

public theorem missing_min_else_zeuge :
    beqTop (parseTop (tokens "min")) (.error "fold min/max: else is required") = true := rfl

public theorem missing_max_else_zeuge :
    beqTop (parseTop (tokens "max")) (.error "fold min/max: else is required") = true := rfl

public theorem unexpected_add_else_zeuge :
    beqTop (parseTop (tokens "add" [.wort "else", .num 99]))
      (.error "fold add: else is not allowed") = true := rfl

public theorem open_domain_refused_zeuge :
    (expandFold {context with tabs := [{table with count := 0, von := some "provider"}]}
      0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.isNone = true := rfl

public theorem second_table_refused_zeuge :
    (expandFold {context with tabs := [table, {table with name := "Other"}]}
      0 .foldAdd ["k", "slots"] [.variable "T", .tru,
        .field (.index (.variable "Other") (.lit 0)) "v"]).toOption.isNone = true := rfl

public theorem overflow_refused_zeuge :
    (expandFold {context with tabs := [{table with count := 2^64}]}
      0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.isNone = true := rfl

public theorem annotated_overflow_refused_zeuge :
    (expandFoldStmt context (.bind false "total" (some (.range (.atom "u8") (.lit 0) (.lit 9) false))
      (.ext .foldAdd ["k", "slots"] (operands .foldAdd)))).toOption.isNone = true := rfl

public theorem empty_sum_range_zeuge : foldSumRange 0 (-9, 12) = (0, 0) := rfl
public theorem signed_sum_range_zeuge : foldSumRange 3 (-9, 12) = (-27, 36) := rfl

/-- Floats are parsed without reassociation; the missing existing IEEE source export
    is a named refusal, not an integer conversion or a differently ordered fold. -/
public theorem float_syntax_zeuge :
    beqTop (parseTop [.wort "add", .ident "k", .wort "in", .wort "slots", .wort "of",
      .ident "T", .zeichen ":", .float "1.0", .ende])
      (.ok (.ext .foldAdd ["k", "slots"] [.variable "T", .tru, .float "1.0"])) = true := rfl

public theorem float_export_refused_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] [.variable "T", .tru, .float "1.0"]).toOption.isNone = true := rfl

end Gabbro.Grammatik.Parser.Uebersetze.FoldWitnesses
