module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Executable reader with the identical list specification and cached projections. -/
def uRufFast (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (c : String) (args : List SExpr) :
    Except String (UFnKopf × List UArg) :=
  match uHeadFind ctx koepfe c with
  | .none => .error ("call unknown: " ++ c)
  | .some callee =>
    if !(callee.held.all (fun l => ctx.held.any (strEq · l))) then .error "call without held guard"
    else
      match uOhneGriffArgs ctx callee.griffe 0 args with
      | .error e => .error e
      | .ok args' =>
        match uArgs ctx tabs callee.kinds args' with
        | .error e => .error e
        | .ok xs => .ok (callee, xs)

@[csimp] theorem uRuf_eq_fast : @uRuf = @uRufFast := by
  funext ctx tabs heads name args
  rfl

end Gabbro.Grammatik.Parser.Uebersetze
