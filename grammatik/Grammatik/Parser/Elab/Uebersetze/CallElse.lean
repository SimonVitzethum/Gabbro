module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Resolve the call before checking the reason channel, so a pointer's own
    signature controls arguments, effects, result and reasons. Handler locals
    never escape into the normal continuation. -/
def uCallElse (tabs : List UTab) (heads : List UFnKopf)
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (callee : String) (args : List SExpr) (reason : String)
    (body : SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) := do
  let pointer ← match uFnZeiger ctx heads callee with
    | none => pure none
    | some result => result.map some
  let (head, args) ← uRuf ctx tabs heads (pointer.map (·.name) |>.getD callee) args
  let marker : UStmt ← match pointer with
    | some _ =>
      if head.kanal.isNone then throw "indirect call else needs a fallible function pointer"
      if (uWertArt head).isNone then throw "indirect call else needs a result type"
      pure (.callIndElseBeg callee head.name args reason)
    | none =>
      if !head.ext then throw "call else needs an axiom callee"
      if head.kanal.isNone then throw "call else needs a fallible axiom callee"
      pure (.axCallElseBeg callee args reason)
  let some (num, count) := head.kanal | throw "call else needs a reason channel"
  let .block statements ending := body | throw "call else needs an ending block"
  let reasonCtx := uMitLokal ctx reason (UParamArt.why num) (Ty.why count)
    (ctx.muts.filter (fun name => !strEq name reason))
  let (errorBody, errorCtx) ← run reasonCtx statements
  let errorEnd ← uFoldEndeStmt errorCtx ending
  let (tail, finalCtx) ← run ctx rest
  pure ([marker] ++ errorBody ++ errorEnd ++ [.blkEnd] ++ tail, finalCtx)

/-- A source expression must denote an exported function pointer. Function
    references use the existing typed binding path, evaluated once. -/
def uCallIndElse (tabs : List UTab) (heads : List UFnKopf)
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (pointer : SExpr) (args : List SExpr) (reason : String)
    (body : SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) := do
  match pointer with
  | .variable name =>
    if (uFnZeiger ctx heads name).isNone then throw "call else needs a function pointer"
    uCallElse tabs heads run ctx name args reason body rest
  | .fnref _ =>
    let name := "#indelse" ++ toString ctx.names.length
    let (binding, bound) ← uBindWert ctx tabs heads false name none pointer
    let (code, finalCtx) ← uCallElse tabs heads run bound name args reason body rest
    pure (binding :: code, finalCtx)
  | _ => throw "indirect call else expression without G form"

end Gabbro.Grammatik.Parser.Uebersetze
