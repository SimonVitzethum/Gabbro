module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Preserve every named invariant as a nested G scope. The G reader resolves
    every name against the unit declarations and retains restoration duties. -/
def uBreaking
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (names : List String) (body : SAnw) (rest : List SAnw) :
    Except String (List UStmt × UCtx) := do
  if names.isEmpty then throw "breaking without an invariant"
  let .block statements ending := body | throw "breaking without a block"
  let (body, bodyCtx) ← run ctx statements
  let exits ← uFoldEndeStmt bodyCtx ending
  let (tail, finalCtx) ← run ctx rest
  let enclosed := names.foldr (fun name inner => [.breakingBeg name] ++ inner ++ [.blkEnd])
    (body ++ exits)
  pure (enclosed ++ tail, finalCtx)

/-- Each source name keeps one opening and closing marker; body bindings do not
    escape the scope, and explicit exits remain inside all named scopes. -/
theorem uBreaking_exact
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx bodyCtx finalCtx : UCtx) (names : List String) (statements rest : List SAnw)
    (ending : Option SEnde) (body exits tail : List UStmt)
    (nonempty : names.isEmpty = false)
    (inside : run ctx statements = .ok (body, bodyCtx))
    (exit : uFoldEndeStmt bodyCtx ending = .ok exits)
    (outside : run ctx rest = .ok (tail, finalCtx)) :
    uBreaking run ctx names (.block statements ending) rest =
      .ok (names.foldr (fun name inner => [.breakingBeg name] ++ inner ++ [.blkEnd])
        (body ++ exits) ++ tail, finalCtx) := by
  simp [uBreaking, nonempty, inside, exit, outside, bind, Except.bind,
    pure, Except.pure]

end Gabbro.Grammatik.Parser.Uebersetze
