module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil8

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- A finite filtered traversal keeps its outer seed separate from the body's binder.
    A raw decreases/touches header has no source-duty binding here and stays refused. -/
def uUnvisitedLoopExport (ctx : UCtx) (binder : String) (origin : Option SExpr) (kind : String)
    (subject : SExpr) (mode raw : String) (invariant : Option SExpr) :
    Except String (UStmt × UCtx × Option UEns) :=
  if kind == "slots" then
    (uSchleifenKopf ctx binder origin kind subject mode invariant).map
      (fun (table, predicate, bodyContext) => (.loopBeg binder table predicate, bodyContext, none))
  else do
    if mode != "unvisited" then throw "traverse by consuming without G form"
    if raw != "" then throw "source export: traversal decreases/touches duties lack a checked source binding"
    let predicate ← match invariant with | none => .ok UEns.tru | some p => uBool ctx p
    if kind == "elems" then
      if origin.any (fun value => !beqSExpr value subject) then
        throw "source export: array traversal of subject disagrees with its domain"
      let (array, _, count) ← uArrayDomain ctx subject
      let (number, numberCount) ← uTabNr ctx.tabs (uArrayCarrierName count)
      if numberCount != (count : Int) then throw "source export: array iterator count disagrees with its value"
      if ctx.muts.any (strEq · binder) then
        throw "source export: array traversal binder shadows a mutable outer name"
      let context := {ctx with names := binder :: ctx.names, kinds := .int :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits, loops := binder :: ctx.loops}
      pure (.arrayLoopBeg binder array predicate, context, none)
    else
      if kind != "descendants" && kind != "ancestors" then
        throw "source export: traversal domain lacks a canonical G expansion"
      let (table, number, seed, edge) ← uTreeDomain ctx subject
      match seed with
      | .param name =>
          if name == binder || ctx.muts.any (strEq · name) then
            throw "source export: traversal seed must be immutable and distinct from its binder"
      | .lit _ => pure ()
      match origin with
      | some expression =>
          if (← uExportIndex ctx table number expression) != seed then
            throw "source export: traversal of seed disagrees with its domain"
      | none => pure ()
      let count := (ctx.tabs[number]?).map (·.count) |>.getD 0
      let context := {ctx with names := binder :: ctx.names, kinds := .index number :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits, loops := binder :: ctx.loops}
      let filter := if kind == "ancestors" then UEns.reach table edge (.param binder) seed
        else UEns.reach table edge seed (.param binder)
      pure (.loopBeg binder table predicate, context, some filter)

/-- A consuming traversal uses the same single declared optional-self child edge as A14.
    The predecessor name is private source metadata, never a new surface binder. -/
def uConsumingEdge (ctx : UCtx) (table : String) : Except String String := do
  let (number, _) ← uTabNr ctx.tabs table
  match ctx.tabs[number]? with
  | some declared =>
    if declared.von.isSome then throw "consuming traversal requires a finite table"
    match declared.kanten with
    | [("child", field)] =>
      if declared.opts.any (fun pair => pair.1 == field && pair.2 == number) then pure field
      else throw "consuming traversal edge must be option index into Self"
    | [] => throw "consuming traversal requires one declared child edge"
    | _ => throw "consuming traversal requires exactly one declared child edge"
  | none => throw "consuming traversal table is not declared"

/-- Read the existing decreases and touches clauses completely; neither is inferred or erased.
    The state-reading measure is elaborated in the outer scope, not under the selected index. -/
def uConsumingClauses (ctx : UCtx) (raw : String) : Except String (USide × String) := do
  let (expression, touches) ← ExportMetadata.consumingHeader raw
  let mass ← (uZSeite ctx expression).mapError ("consuming traversal decreases: " ++ ·)
  pure (mass, touches)

/-- Consuming keeps A14's domain predicate as a current-world member test. The declared
    edge is the canonical reach relation over its optional-self field, in predecessor/candidate
    order. Selection and strict decrease are performed by consumeTraverse, never a fixed sweep. -/
def uLoopExport (ctx : UCtx) (binder : String) (origin : Option SExpr) (kind : String)
    (subject : SExpr) (mode raw : String) (invariant : Option SExpr) :
    Except String (UStmt × UCtx × Option UEns) := do
  if mode != "consuming" then
    uUnvisitedLoopExport ctx binder origin kind subject mode raw invariant
  else
    let (mass, effects) ← uConsumingClauses ctx raw
    let (header, context, filter) ←
      uUnvisitedLoopExport ctx binder origin kind subject "unvisited" "" invariant
    let (table, inv) ← match header with
      | .loopBeg _ table inv => pure (table, inv)
      | _ => throw "consuming traversal requires a represented table domain"
    let field ← uConsumingEdge ctx table
    let predecessor := "#consume:predecessor"
    let edge := UEns.reach table field (.param predecessor) (.param binder)
    pure (.consumeLoopBeg binder table predecessor (filter.getD .tru) edge inv mass effects,
      {context with loops := ("#consume:" ++ binder) :: ctx.loops}, none)

/-- The existing conditional block carries leave/next/return unchanged on visited nodes. -/
def uFilteredBody (filter : Option UEns) (body : List UStmt) : List UStmt :=
  match filter with
  | none => body
  | some predicate => [.ifBeg predicate] ++ body ++ [.ifElse, .blkEnd]

/-- The body of an arm. -/
def uArmBody : SAnw → SAnw
  | .arm _ _ b => b
  | x => x

/-- The arm bodies of a reason match in the order of the reason's cases: exactly one arm per case. -/
def uWhyArme (cases : List String) (arms : List SAnw) : Option (List SAnw) :=
  if arms.length != cases.length then none
  else
    cases.mapM fun c =>
      (arms.find? (fun a => match a with | .arm n .none _ => strEq n c | _ => false)).map uArmBody

/-- The lists joined with the arm separator `ifElse`. -/
def uMitTrenner : List (List UStmt) → List UStmt
  | [] => []
  | [a] => a
  | a :: rest => a ++ [UStmt.ifElse] ++ uMitTrenner rest

/-- A field of a tagged type as a value, and the position of its type. -/
def uSumPlatz (ctx : UCtx) (e : SExpr) : Except String (USVal × Nat) :=
  match uZugriff ctx e with
  | .error x => .error x
  | .ok (b, tb, f, ix) =>
    match (ctx.tabs.find? (fun t => strEq t.name tb)).bind (fun t => t.sumFelder.find? (fun p => strEq p.1 f)) with
    | none => .error "match without G form"
    | some (_, k) =>
      match b with
      | .thru p => do
        uReadThrough ctx p
        pure (.slot p f ix, k)
      | .tabelle t => .ok (.tab t f ix, k)


/-- The statement ends the function on every path, looking through the last statement of each arm: an `if` with an
    `else`, or a `match` (every arm of a `match` the model accepts is there: `Arms`/`GrundArms` are indexed by the
    cases, an option match has both). Only then does a body without a trailing return get `URet.keins`. -/
def uEndetTief : Nat → SAnw → Bool
  | 0, _ => false
  | f + 1, .cond _ t ei els =>
    let arm : SAnw → Bool := fun b => match b with
      | .block ss e => e.isSome || (match ss.getLast? with | some s => uEndetTief f s | none => false)
      | _ => false
    arm t &&
      (match ei with
       | .elsif c2 b2 :: ei' => uEndetTief f (.cond c2 b2 ei' els)
       | [] => (match els with | some b => arm b | none => false)
       | _ => false)
  | f + 1, .cases _ arms =>
    !arms.isEmpty && arms.all (fun a => match a with
      | .arm _ _ (.block ss e) => e.isSome || (match ss.getLast? with | some s => uEndetTief f s | none => false)
      | _ => false)
  | _ + 1, _ => false

/-- The statement ends its block on every path: an `if` with an `else` whose arms end in a `return`, `leave` or
    `next` (an `else if` chain is the `if` in the `else`). Fuel for the chain. -/
def uEndetS : Nat → SAnw → Bool
  | 0, _ => false
  | f + 1, .cond _ (.block _ e) ei els =>
    let armEndet : SAnw → Bool := fun b => match b with
      | .block _ e' => e'.isSome
      | _ => false
    e.isSome &&
      (match ei with
       | .elsif c2 b2 :: ei' => uEndetS f (.cond c2 b2 ei' els)
       | [] => (match els with | some b => armEndet b | none => false)
       | _ => false)
  | _ + 1, _ => false

end Gabbro.Grammatik.Parser.Uebersetze
