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

/-- The mutable local array at the root of an element place `x[i]`, `x[i][j]`, ... -/
def uArrayLocal (ctx : UCtx) : SExpr → Option String
  | .index (.variable name) _ => do
    let position ← ctx.names.findIdx? (strEq · name)
    match ctx.types[position]? with
    | some (.arr ..) => if ctx.muts.any (strEq · name) then some name else none
    | _ => none
  | .index base _ => uArrayLocal ctx base
  | _ => none

/-- `a[i] = v` on an array held by a mutable local: the local and its new value, the element at `i`
    replaced (`USide.upd`) at every level, as `uElemSchreib` does for a static. -/
def uElemLokal (ctx : UCtx) : SExpr → SExpr → USide → Except String (String × USide)
  | .variable x, i, v =>
    match uWertBody ctx (.variable x), uWertBody ctx i with
    | .ok cur, .ok y => .ok (x, .upd cur y v)
    | .error e, _ | _, .error e => .error e
  | .index a j, i, v =>
    match uWertBody ctx (.index a j), uWertBody ctx i with
    | .ok cur, .ok y => uElemLokal ctx a j (.upd cur y v)
    | .error e, _ | _, .error e => .error e
  | _, _, _ => .error "element write without G form"

/-- `x[i] = v;` on a mutable local array: the local is assigned the array with the element replaced. -/
def uSetzeElement (ctx : UCtx) (base index value : SExpr) : Except String UStmt :=
  match uWertBody ctx value with
  | .error e => .error e
  | .ok v =>
    match uElemLokal ctx base index v with
    | .error e => .error e
    | .ok (x, w) => .ok (.setVar x w)

end Gabbro.Grammatik.Parser.Uebersetze
