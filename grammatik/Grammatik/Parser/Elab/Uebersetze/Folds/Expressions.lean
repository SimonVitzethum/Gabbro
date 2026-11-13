module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Expansion

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

mutual
/-- Detect folds only along the operand paths visited by `expandFoldExpr`.
    Array elements are traversed in order; other non-fold extensions stay opaque. -/
def needsFoldExpansion : SExpr → Bool
  | .ext .array [] args => needsFoldExpansionList args
  | .ext kind _ _ => isFold kind
  | .bin _ a b | .index a b => needsFoldExpansion a || needsFoldExpansion b
  | .un _ value | .field value _ => needsFoldExpansion value
  | .call _ args => needsFoldExpansionList args
  | _ => false

/-- Call arguments are visited in their original order. -/
def needsFoldExpansionList : List SExpr → Bool
  | [] => false
  | value :: rest => needsFoldExpansion value || needsFoldExpansionList rest
end

/-- Hoist folds at their point of evaluation, in operand order. The counter makes
    generated bindings distinct even when several folds share one expression. -/
def expandFoldExpr : Nat → UCtx → Nat → SExpr →
    Except String (List UStmt × UCtx × Nat × SExpr)
  | 0, _, _, _ => .error "fold: expression nesting limit"
  | fuel + 1, ctx, serial, .ext .array [] args => do
    let (code, ctx, serial, args) ← args.foldlM (fun (code, ctx, serial, values) value => do
      let (more, ctx, serial, value) ← expandFoldExpr fuel ctx serial value
      pure (code ++ more, ctx, serial, values ++ [value])) ([], ctx, serial, [])
    pure (code, ctx, serial, .ext .array [] args)
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

/-- Fold-free syntax needs no expansion budget. Actual folds retain the existing
    bounded traversal, including its evaluation order, range checks and refusals. -/
def expandFoldValue (ctx : UCtx) (serial : Nat) (value : SExpr) :
    Except String (List UStmt × UCtx × Nat × SExpr) :=
  if needsFoldExpansion value then expandFoldExpr 1000 ctx serial value
  else .ok ([], ctx, serial, value)

theorem expandFoldValue_no_work (ctx : UCtx) (serial : Nat) (value : SExpr)
    (h : needsFoldExpansion value = false) :
    expandFoldValue ctx serial value = .ok ([], ctx, serial, value) := by
  simp only [expandFoldValue, h, Bool.false_eq_true, ite_false]

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
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    let target ← if code.isEmpty then pure none else
      match ty with
      | none => pure none
      | some ty => do
        match ← uTyp ctx.alias ctx.tabs ctx.spaces ctx.eigner ty with
        | .fl .. => pure none
        | _ => (uErgBereich ctx.alias ty).map some
    foldCheckResult ctx code value target
    pure (code, ctx, .bind mu name ty value)
  | .set target op value =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    pure (code, ctx, .set target op value)
  | .cond test body branches fallback =>
    let (code, ctx, _, test) ← expandFoldValue ctx serial test
    pure (code, ctx, .cond test body branches fallback)
  | .cases value arms =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    pure (code, ctx, .cases value arms)
  | .callIndElse pointer args reason body =>
    let (left, ctx, serial, pointer) ← expandFoldValue ctx serial pointer
    let (right, ctx, _, value) ← expandFoldValue ctx serial (.call "" args)
    let .call _ args := value | throw "fold: malformed indirect call expansion"
    pure (left ++ right, ctx, .callIndElse pointer args reason body)
  | .callElse name args reason body =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial (.call name args)
    let .call name args := value | throw "fold: malformed call expansion"
    pure (code, ctx, .callElse name args reason body)
  | .call name args =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial (.call name args)
    let .call name args := value | throw "fold: malformed call expansion"
    pure (code, ctx, .call name args)
  | .ret (some value) =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    foldCheckResult ctx code value ctx.res
    pure (code, ctx, .ret (some value))
  | statement => pure ([], ctx, statement)

def expandFoldEnd (ctx : UCtx) (ending : Option SEnde) :
    Except String (List UStmt × UCtx × Option SEnde) := do
  match ending with
  | some (.ret (some value)) =>
    let (code, ctx, _, value) ← expandFoldValue ctx ctx.names.length value
    foldCheckResult ctx code value ctx.res
    pure (code, ctx, some (.ret (some value)))
  | _ => pure ([], ctx, ending)

def expandFoldStmtFast (ctx : UCtx) (statement : SAnw) :
    Except String (List UStmt × UCtx × SAnw) := do
  let serial := uLocalCount ctx
  match statement with
  | .bind mu name ty value =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    let target ← if code.isEmpty then pure none else
      match ty with
      | none => pure none
      | some ty => do
        match ← uTyp ctx.alias ctx.tabs ctx.spaces ctx.eigner ty with
        | .fl .. => pure none
        | _ => (uErgBereich ctx.alias ty).map some
    foldCheckResult ctx code value target
    pure (code, ctx, .bind mu name ty value)
  | .set target op value =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    pure (code, ctx, .set target op value)
  | .cond test body branches fallback =>
    let (code, ctx, _, test) ← expandFoldValue ctx serial test
    pure (code, ctx, .cond test body branches fallback)
  | .cases value arms =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    pure (code, ctx, .cases value arms)
  | .callIndElse pointer args reason body =>
    let (left, ctx, serial, pointer) ← expandFoldValue ctx serial pointer
    let (right, ctx, _, value) ← expandFoldValue ctx serial (.call "" args)
    let .call _ args := value | throw "fold: malformed indirect call expansion"
    pure (left ++ right, ctx, .callIndElse pointer args reason body)
  | .callElse name args reason body =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial (.call name args)
    let .call name args := value | throw "fold: malformed call expansion"
    pure (code, ctx, .callElse name args reason body)
  | .call name args =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial (.call name args)
    let .call name args := value | throw "fold: malformed call expansion"
    pure (code, ctx, .call name args)
  | .ret (some value) =>
    let (code, ctx, _, value) ← expandFoldValue ctx serial value
    foldCheckResult ctx code value ctx.res
    pure (code, ctx, .ret (some value))
  | statement => pure ([], ctx, statement)

def expandFoldEndFast (ctx : UCtx) (ending : Option SEnde) :
    Except String (List UStmt × UCtx × Option SEnde) := do
  match ending with
  | some (.ret (some value)) =>
    let (code, ctx, _, value) ← expandFoldValue ctx (uLocalCount ctx) value
    foldCheckResult ctx code value ctx.res
    pure (code, ctx, some (.ret (some value)))
  | _ => pure ([], ctx, ending)

@[csimp] theorem expandFoldStmt_eq_fast : @expandFoldStmt = @expandFoldStmtFast := by
  funext ctx statement
  rfl

@[csimp] theorem expandFoldEnd_eq_fast : @expandFoldEnd = @expandFoldEndFast := by
  funext ctx ending
  rfl

/-- Nested end blocks use the same expression expansion as a function return. -/
def uFoldEndeStmt (ctx : UCtx) (ending : Option SEnde) : Except String (List UStmt) := do
  let (code, ctx, ending) ← expandFoldEnd ctx ending
  pure (code ++ (← uEndeStmt ctx ending))

end Gabbro.Grammatik.Parser.Uebersetze
