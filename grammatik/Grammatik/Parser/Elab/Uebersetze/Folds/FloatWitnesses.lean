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

namespace Gabbro.Grammatik.Parser.Uebersetze.FloatFoldWitnesses
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private def table : UTab :=
  {name := "T", count := 3, cols := [("v", (0, 0)), ("open", (0, 1))],
    bools := ["open"], werte := [("v", uFloatTy)]}

private def context : UCtx :=
  {names := [], kinds := [], types := [], tabs := [table], locks := [], held := [],
    res := none, fname := "sample", alias := [], lits := []}

private def value : SExpr := .field (.index (.variable "T") (.variable "k")) "v"

private def operands (kind : XKind) : List SExpr :=
  [.variable "T", .tru, value] ++ (if kind == .foldAdd then [] else [.lit 0])

private def expectedAdd : List UStmt :=
  [.floatLit "#fold:0:acc" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .loopBeg "k" "T" .tru, .ifBeg .tru,
    .bindW "#fold:0:value" none (.tab "T" "v" (.param "k")),
    .float "#fold:0:next" .add (.param "#fold:0:acc") (.param "#fold:0:value")
      (-uFloatLimit, 1) (uFloatLimit, 1),
    .setVar "#fold:0:acc" (.param "#fold:0:next"), .ifElse, .blkEnd, .blkEnd,
    .bindW "#fold:0:acc:result" (some uFloatTy) (.param "#fold:0:acc")]

/-- Both source widths retain the existing canonical binary64 model cut. -/
public theorem f32_type_zeuge : uTyp [] [] (.atom "f32") = .ok uFloatTy := rfl
public theorem f64_type_zeuge : uTyp [] [] (.atom "f64") = .ok uFloatTy := rfl

/-- Three slots and a real float table read: one loop, left accumulator first,
    one IEEE addition and one assignment per selected slot, starting at +0.0. -/
public theorem add_slot_order_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.map (·.1) =
      some expectedAdd := rfl

public theorem add_result_type_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.map
      (fun expanded => expanded.2.1.types.head?) = some (some uFloatTy) := rfl

public theorem filtered_add_slot_order_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"]
      [.variable "T", .field (.index (.variable "T") (.variable "k")) "open", value]).toOption.map
      (fun expanded => expanded.1[2]?) =
      some (some (.ifBeg (.tabB "T" "open" (.param "k")))) := rfl

public theorem empty_add_still_initializes_positive_zero_zeuge :
    (expandFold {context with tabs := [{table with count := 0}]} 0 .foldAdd ["k", "slots"]
      (operands .foldAdd)).toOption.map (fun expanded => expanded.1.head?) =
      some (some (.floatLit "#fold:0:acc" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1))) := rfl

public theorem literal_rational_zeuge : uFloatRational "1.5e-3 rounded" = .ok (15, 10000) := rfl

private def expectedExtremum (kind : XKind) : List UStmt :=
  [.floatLit "#fold:0:acc" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .floatLit "#fold:0:one" (1, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .bindB "#fold:0:seen" .fls, .loopBeg "k" "T" .tru, .ifBeg .tru,
    .bindW "#fold:0:value" none (.tab "T" "v" (.param "k")),
    .ifBeg (.or (.not (.var "#fold:0:seen"))
      (.cmp (if kind == .foldMin then "<" else ">") (.param "#fold:0:value") (.param "#fold:0:acc"))),
    .float "#fold:0:next" .mul (.param "#fold:0:value") (.param "#fold:0:one")
      (-uFloatLimit, 1) (uFloatLimit, 1),
    .setVar "#fold:0:acc" (.param "#fold:0:next"), .setVarB "#fold:0:seen" .tru,
    .ifElse, .blkEnd, .ifElse, .blkEnd, .blkEnd,
    .ifBeg (.not (.var "#fold:0:seen")),
    .floatLit "#fold:0:empty:0" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .float "#fold:0:next" .mul (.param "#fold:0:empty:0") (.param "#fold:0:one")
      (-uFloatLimit, 1) (uFloatLimit, 1),
    .setVar "#fold:0:acc" (.param "#fold:0:next"), .ifElse, .blkEnd,
    .bindW "#fold:0:acc:result" (some uFloatTy) (.param "#fold:0:acc")]

public theorem min_order_and_empty_fallback_zeuge :
    (expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin)).toOption.map (·.1) =
      some (expectedExtremum .foldMin) := rfl

public theorem max_order_and_empty_fallback_zeuge :
    (expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax)).toOption.map (·.1) =
      some (expectedExtremum .foldMax) := rfl

/-- Exercise the connected generic G block lowering in a continuing branch.
    Endblock itself still lacks canonical IEEE introduction constructors. -/
private def lowered (kind : XKind) : Bool :=
  match uAnwReihe [table] [] 1000 context
      [.cond .tru (.block [.bind false "total" none (.ext kind ["k", "slots"] (operands kind))] none)
        [] none] with
  | .error _ => false
  | .ok (body, _) =>
    let function : UFn := {name := "sample", params := [], kinds := [], res := none,
      held := [], puts := [], gives := [], body, ret := .empty}
    (lowerAllg {tabs := [table], locks := [], fns := [function]}).toOption.isSome

public theorem add_continuing_lowering_zeuge : lowered .foldAdd = true := rfl
public theorem min_continuing_lowering_zeuge : lowered .foldMin = true := rfl
public theorem max_continuing_lowering_zeuge : lowered .foldMax = true := rfl

/-- Keep the remaining canonical Endblock boundary explicit in the witnesses. -/
public theorem top_level_endblock_refusal_zeuge :
    (lowerAllg {tabs := [table], locks := [], fns := [
      {name := "sample", params := [], kinds := [], res := none, held := [],
        puts := [], gives := [], body := expectedAdd, ret := .empty}]}).toOption.isNone = true := rfl

/-- IEEE unordered comparisons and signed-zero copies are the kernel model's
    computations, not a separate extrema policy. -/
public theorem nan_unordered_zeuge :
    Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nanQ Gleitkomma.f64)
      (Gleitkomma.ofInt Gleitkomma.f64 1) = false := by decide

public theorem copy_preserves_negative_zero_zeuge :
    Gleitkomma.mul Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.ofInt Gleitkomma.f64 1) = Gleitkomma.nullN Gleitkomma.f64 := by decide

end Gabbro.Grammatik.Parser.Uebersetze.FloatFoldWitnesses
