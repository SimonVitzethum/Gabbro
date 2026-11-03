module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Expansion

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Hoist folds at their point of evaluation, in operand order. The counter makes
    generated bindings distinct even when several folds share one expression. -/
def expandFoldExpr : Nat → UCtx → Nat → SExpr →
    Except String (List UStmt × UCtx × Nat × SExpr)
  | 0, _, _, _ => .error "fold: expression nesting limit"
  | fuel + 1, ctx, serial, .ext kind names args =>
    if isFold kind then do
      let (code, ctx, value) ← expandFold ctx serial kind names args
      pure (code, ctx, serial + 1, value)
    else pure ([], ctx, serial, .ext kind names args)
  | fuel + 1, ctx, serial, .bin op a b => do
    let (left, ctx, serial, a) ← expandFoldExpr fuel ctx serial a
    let (right, ctx, serial, b) ← expandFoldExpr fuel ctx serial b
    pure (left ++ right, ctx, serial, .bin op a b)
  | fuel + 1, ctx, serial, .un op e => do
    let (code, ctx, serial, e) ← expandFoldExpr fuel ctx serial e
    pure (code, ctx, serial, .un op e)
  | fuel + 1, ctx, serial, .call name args => do
    let (code, ctx, serial, args) ← args.foldlM (fun (code, ctx, serial, values) value => do
      let (more, ctx, serial, value) ← expandFoldExpr fuel ctx serial value
      pure (code ++ more, ctx, serial, values ++ [value])) ([], ctx, serial, [])
    pure (code, ctx, serial, .call name args)
  | fuel + 1, ctx, serial, .field e field => do
    let (code, ctx, serial, e) ← expandFoldExpr fuel ctx serial e
    pure (code, ctx, serial, .field e field)
  | fuel + 1, ctx, serial, .index a b => do
    let (left, ctx, serial, a) ← expandFoldExpr fuel ctx serial a
    let (right, ctx, serial, b) ← expandFoldExpr fuel ctx serial b
    pure (left ++ right, ctx, serial, .index a b)
  | _ + 1, ctx, serial, e => pure ([], ctx, serial, e)

/-- Report a fold's overflowing result at the source type boundary. Ordinary expressions
    retain the existing range diagnostics. -/
def foldCheckResult (ctx : UCtx) (code : List UStmt) (value : SExpr)
    (target : Option (Int × Int)) : Except String Unit := do
  if code.isEmpty then return ()
  if let some target := target then
    let side ← uWertBody ctx value
    let some range := foldRange ctx side | throw "fold: result has no exported integer range"
    if !(target.1 ≤ range.1 && range.2 ≤ target.2) then
      throw "fold: result range does not fit its integer type; narrow the operand first"

/-- Expand immediate operands only; nested blocks are visited with their own actual
    lexical contexts by `uAnwReihe`, including branches and traversal bodies. -/
def expandFoldStmt (ctx : UCtx) (statement : SAnw) :
    Except String (List UStmt × UCtx × SAnw) := do
  let serial := ctx.names.length
  match statement with
  | .bind mu name ty value =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx serial value
    let target ← if code.isEmpty then pure none else
      match ty with
      | none => pure none
      | some ty => do
        match ← uTyp ctx.alias ctx.tabs ty with
        | .fl .. => pure none
        | _ => (uErgBereich ctx.alias ty).map some
    foldCheckResult ctx code value target
    pure (code, ctx, .bind mu name ty value)
  | .set target op value =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx serial value
    pure (code, ctx, .set target op value)
  | .cond test body branches fallback =>
    let (code, ctx, _, test) ← expandFoldExpr 1000 ctx serial test
    pure (code, ctx, .cond test body branches fallback)
  | .cases value arms =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx serial value
    pure (code, ctx, .cases value arms)
  | .callIndElse pointer args reason body =>
    let (left, ctx, serial, pointer) ← expandFoldExpr 1000 ctx serial pointer
    let (right, ctx, _, value) ← expandFoldExpr 1000 ctx serial (.call "" args)
    let .call _ args := value | throw "fold: malformed indirect call expansion"
    pure (left ++ right, ctx, .callIndElse pointer args reason body)
  | .callElse name args reason body =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx serial (.call name args)
    let .call name args := value | throw "fold: malformed call expansion"
    pure (code, ctx, .callElse name args reason body)
  | .call name args =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx serial (.call name args)
    let .call name args := value | throw "fold: malformed call expansion"
    pure (code, ctx, .call name args)
  | .ret (some value) =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx serial value
    foldCheckResult ctx code value ctx.res
    pure (code, ctx, .ret (some value))
  | statement => pure ([], ctx, statement)

def expandFoldEnd (ctx : UCtx) (ending : Option SEnde) :
    Except String (List UStmt × UCtx × Option SEnde) := do
  match ending with
  | some (.ret (some value)) =>
    let (code, ctx, _, value) ← expandFoldExpr 1000 ctx ctx.names.length value
    foldCheckResult ctx code value ctx.res
    pure (code, ctx, some (.ret (some value)))
  | _ => pure ([], ctx, ending)

/-- Nested end blocks use the same expression expansion as a function return. -/
def uFoldEndeStmt (ctx : UCtx) (ending : Option SEnde) : Except String (List UStmt) := do
  let (code, ctx, ending) ← expandFoldEnd ctx ending
  pure (code ++ (← uEndeStmt ctx ending))

end Gabbro.Grammatik.Parser.Uebersetze
