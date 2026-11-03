module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A record field chain belongs to a local only when its root has a nominal product type.
    Carrier fields continue through the existing guarded place exporter. -/
def uRecordLocal (ctx : UCtx) : SExpr → Option String
  | .variable name => do
    let position ← ctx.names.findIdx? (strEq · name)
    match ctx.types[position]? with
    | some (.prod ..) => some name
    | _ => none
  | .field base _ => uRecordLocal ctx base
  | _ => none

/-- Rebuild the containing value from the selected leaf outwards. Typed lowering resolves
    each field against its declared schema and emits `Expr.prodSet` at every level. -/
def uRecordReplacement (ctx : UCtx) : SExpr → USide → Except String USide
  | .variable _, value => pure value
  | .field base field, value => do
    let original ← uWertBody ctx base
    uRecordReplacement ctx base (.replace original field value)
  | _, _ => .error "source export: record update requires a local field path"

/-- Mutation preserves the complete local record; immutable roots are refused explicitly. -/
def uSetzeRecord (ctx : UCtx) (name : String) (target value : SExpr) : Except String UStmt := do
  if !ctx.muts.any (strEq · name) then throw "source export: record update requires a mutable local"
  let side ← uRecordSide ctx value (fun source _ => uWertBody ctx source)
  pure (.setVar name (← uRecordReplacement ctx target side))

end Gabbro.Grammatik.Parser.Uebersetze
