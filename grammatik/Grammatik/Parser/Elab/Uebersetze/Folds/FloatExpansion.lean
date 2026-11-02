module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil9

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Float leaves reuse the ordinary checked readers for local, aggregate and
    table access. Slot field types come from the table's canonical value metadata. -/
def foldFloatType (ctx : UCtx) (side : USide) : Option Ty :=
  match side with
  | .tab table field _ | .slot table field _ => do
    let table := match side with
      | .slot base _ _ =>
        (ctx.names.findIdx? (strEq · base)).bind fun j =>
          match ctx.kinds[j]? with
          | some (.ptr (.table number _ _)) => (ctx.tabs[number]?).map (·.name)
          | _ => none
      | _ => some table
    let table ← table
    let declaration ← ctx.tabs.find? (fun t => strEq t.name table)
    (declaration.werte.find? (fun entry => strEq entry.1 field)).map (·.2)
  | _ => uValueType ctx side

/-- Hoist IEEE operations in operand order. Each operation is still a G block
    introduction with its finite result check, never integer arithmetic. -/
def foldFloatValue : Nat → UCtx → String → Nat → SExpr →
    Except String (List UStmt × Nat × USide)
  | 0, _, _, _, _ => .error "fold: float expression nesting limit"
  | _ + 1, _, prefix, serial, .lit number =>
    let name := prefix ++ toString serial
    .ok ([.floatLit name (number, 1) (-uFloatLimit, 1) (uFloatLimit, 1)], serial + 1, .param name)
  | _ + 1, _, prefix, serial, .float text => do
    let rational ← uFloatRational text
    let name := prefix ++ toString serial
    pure ([.floatLit name rational (-uFloatLimit, 1) (uFloatLimit, 1)], serial + 1, .param name)
  | fuel + 1, ctx, prefix, serial, .bin operator left right => do
    let op ← match operator with
      | "+" => pure GleitOp.add | "-" => pure GleitOp.sub
      | "*" => pure GleitOp.mul | "/" => pure GleitOp.div
      | _ => throw "fold: unsupported float operator"
    let (before, serial, left) ← foldFloatValue fuel ctx prefix serial left
    let (after, serial, right) ← foldFloatValue fuel ctx prefix serial right
    let name := prefix ++ toString serial
    pure (before ++ after ++ [.float name op left right (-uFloatLimit, 1) (uFloatLimit, 1)],
      serial + 1, .param name)
  | fuel + 1, ctx, prefix, serial, .un "-" value => do
    let (code, serial, value) ← foldFloatValue fuel ctx prefix serial value
    let factor := prefix ++ toString serial
    let name := prefix ++ toString (serial + 1)
    pure (code ++ [.floatLit factor (-1, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
      .float name .mul value (.param factor) (-uFloatLimit, 1) (uFloatLimit, 1)],
      serial + 2, .param name)
  | _ + 1, ctx, _, serial, value => do
    let side ← uWertBody ctx value
    let some (.fl ..) := foldFloatType ctx side | throw "fold: float operand required"
    pure ([], serial, side)

/-- Slot-order IEEE addition starts at positive zero. The loop header and filter
    are exactly those used by the integer fold; there is one accumulator update
    per selected slot and no reassociation. Min/max use `Expr.fllt` (reversed for
    max): the kernel IEEE `flt` returns false for either NaN operand. Canonical
    `Gleit` values are finite, so NaN is rejected by the existing introduction's
    range check before comparison. Equal values, including signed zeros, retain
    the first selected value. Multiplication by one copies a selected value into
    the accumulator's bounds without changing its bits, including signed zero;
    it uses the ordinary checked IEEE block and contributes to its cost.
    All G finite/range checks remain; no NaN-skipping policy is introduced. -/
def expandFloatFold (ctx inner : UCtx) (serial : Nat) (kind : XKind)
    (header : UStmt) (predicate : UEns) (expression : SExpr) (fallback : List SExpr) :
    Except String (List UStmt × UCtx × SExpr) := do
  match kind, fallback with
  | .foldAdd, [] | .foldMin, [_] | .foldMax, [_] => pure ()
  | .foldAdd, _ => throw "fold add: else is not allowed"
  | _, _ => throw "fold min/max: else is required"
  let acc := foldName serial "acc"
  let seen := foldName serial "seen"
  let one := foldName serial "one"
  let value := foldName serial "value"
  let next := foldName serial "next"
  let result := acc ++ ":result"
  let (bodyCode, _, body) ← foldFloatValue 1000 inner (value ++ ":") 0 expression
  let step := if kind == .foldAdd then
      [UStmt.float next .add (.param acc) (.param value) (-uFloatLimit, 1) (uFloatLimit, 1),
        .setVar acc (.param next)]
    else
      [UStmt.ifBeg (.or (.not (.var seen))
          (.cmp (if kind == .foldMin then "<" else ">") (.param value) (.param acc))),
        .float next .mul (.param value) (.param one) (-uFloatLimit, 1) (uFloatLimit, 1),
        .setVar acc (.param next), .setVarB seen .tru, .ifElse, .blkEnd]
  let emptyCode ← match fallback with
    | [] => pure []
    | [empty] => do
      let (code, _, empty) ← foldFloatValue 1000 ctx (foldName serial "empty:") 0 empty
      pure ([UStmt.ifBeg (.not (.var seen))] ++ code ++
        [.float next .mul empty (.param one) (-uFloatLimit, 1) (uFloatLimit, 1),
          .setVar acc (.param next), .ifElse, .blkEnd])
    | _ => throw "fold min/max: else is required"
  let code := [UStmt.floatLit acc (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1)] ++
    (if kind == .foldAdd then [] else
      [.floatLit one (1, 1) (-uFloatLimit, 1) (uFloatLimit, 1), .bindB seen .fls]) ++
    [header, .ifBeg predicate] ++ bodyCode ++ [.bindW value none body] ++ step ++
    [.ifElse, .blkEnd, .blkEnd] ++ emptyCode ++ [.bindW result (some uFloatTy) (.param acc)]
  pure (code, uMitLokal ctx result .wert uFloatTy ctx.muts, .variable result)

end Gabbro.Grammatik.Parser.Uebersetze
