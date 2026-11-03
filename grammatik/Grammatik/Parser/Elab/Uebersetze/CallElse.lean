module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A statement handler shares the binding form's argument and reason checks, but
    never introduces the discarded success value into the following source scope. -/
def uCallElse (tabs : List UTab) (heads : List UFnKopf)
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (callee : String) (args : List SExpr) (reason : String)
    (body : SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) := do
  let (target, indirect) ← match uFnZeiger ctx heads callee with
    | some resolved => resolved.map fun head => (head.name, true)
    | none => pure (callee, false)
  let (head, args) ← uRuf ctx tabs heads target args
  if !indirect && !head.ext then throw "call else needs an axiom callee"
  let some (num, count) := head.kanal |
    throw (if indirect then "call else needs a fallible function-pointer callee"
      else "call else needs a fallible axiom callee")
  let .block statements ending := body | throw "call else needs an ending block"
  let reasonCtx := uMitLokal ctx reason (UParamArt.why num) (Ty.why count)
    (ctx.muts.filter (fun name => !strEq name reason))
  let (errorBody, errorCtx) ← run reasonCtx statements
  let errorEnd ← uFoldEndeStmt errorCtx ending
  let (tail, finalCtx) ← run ctx rest
  pure ([.axCallElseBeg callee args reason] ++ errorBody ++ errorEnd ++ [.blkEnd] ++ tail, finalCtx)

end Gabbro.Grammatik.Parser.Uebersetze
