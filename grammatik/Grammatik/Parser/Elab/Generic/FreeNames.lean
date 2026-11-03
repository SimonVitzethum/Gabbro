module
public import Grammatik.Parser.Item.ElementTief.FunctionArguments
public import Grammatik.Parser.Namen.References
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Literals have their own lexical scope. An unresolved free name is diagnosed before lifting. -/
def checkLiteralName (globals locals : List String) (name : String) : Except String Unit :=
  if locals.contains name || globals.contains name then pure ()
  else throw ("function-literal-capture: " ++ name)

def checkLiteralNames (globals locals : List String) (names : List String) : Except String Unit :=
  names.forM (checkLiteralName globals locals)

/-- Raw tails do not grant access to the surrounding function's locals. Member names after a dot
    are not free names; paths are checked as a single global item. -/
def checkLiteralTokens (globals locals : List String) : Nat → List Token → Except String Unit
  | 0, _ => .error "function literal name check exhausted its token budget"
  | _ + 1, [] => pure ()
  | fuel + 1, .zeichen "." :: _ :: rest => checkLiteralTokens globals locals fuel rest
  | fuel + 1, .ident name :: rest => do
    let (path, remaining) := sammleSegmente rest [name]
    checkLiteralName globals locals (String.intercalate "::" path)
    checkLiteralTokens globals locals fuel remaining
  | fuel + 1, _ :: rest => checkLiteralTokens globals locals fuel rest

def checkLiteralRaw (globals locals : List String) (text : String) : Except String Unit := do
  let ts ← match lex text with
    | .ok ts => pure ts
    | .error _ => throw "function literal name check cannot lex a raw tail"
  checkLiteralTokens globals locals (ts.length + 1) ts

/-- A nested literal owns a fresh scope and will be checked when its generic application is
    normalized. Its binders must not be mistaken for free names of the enclosing literal. -/
def checkLiteralArgument (globals locals : List String) (word : String) : Except String Unit := do
  match lex word with
  | .error _ => throw "function literal name check cannot lex a generic argument"
  | .ok ts =>
    match parseFunctionArgument (ts.length * 4 + 32) ts with
    | .ok (.literal _ _) => pure ()
    | _ => checkLiteralRaw globals locals word

mutual
def checkLiteralExpression (globals locals : List String) : SExpr → Except String Unit
  | .ext .instantiate (name :: words) args => do
    checkLiteralName globals locals name
    for word in words do checkLiteralArgument globals locals word
    checkLiteralExpressions globals locals args
  | .ext .all (binder :: _ :: names) args | .ext .any (binder :: _ :: names) args |
    .ext .count (binder :: _ :: names) args => do
    checkLiteralNames globals locals names
    checkLiteralQuantifier globals locals binder args
  | .field (.variable name) field =>
    if (istIntWort name || istZuckerBreite name) && (field == "min" || field == "max") then pure ()
    else checkLiteralName globals locals name
  | .field e _ | .arrow e _ | .un _ e | .old e => checkLiteralExpression globals locals e
  | .index a b | .bin _ a b => do
    checkLiteralExpression globals locals a
    checkLiteralExpression globals locals b
  | .call name args => do
    if name != "Some" && name != "None" && !istIntWort name && !istZuckerBreite name then
      checkLiteralName globals locals name
    checkLiteralExpressions globals locals args
  | .built _ args => checkLiteralExpressions globals locals args
  | .ext kind names args => do
    if kind == .mem then checkLiteralNames globals locals (names.drop 1)
    checkLiteralExpressions globals locals args
  | e => checkLiteralNames globals locals (Oeffentlich.namenA locals e)

def checkLiteralExpressions (globals locals : List String) : List SExpr → Except String Unit
  | [] => pure ()
  | expression :: rest => do
    checkLiteralExpression globals locals expression
    checkLiteralExpressions globals locals rest

def checkLiteralQuantifier (globals locals : List String) (binder : String) :
    List SExpr → Except String Unit
  | [] => pure ()
  | [body] => checkLiteralExpression globals (binder :: locals) body
  | operand :: rest => do
    checkLiteralExpression globals locals operand
    checkLiteralQuantifier globals locals binder rest
end

def checkLiteralType (globals locals : List String) : STyp → Except String Unit
  | .atom name =>
    if istTypWort name || istZuckerBreite name || name == "f32" || name == "f64" then pure ()
    else checkLiteralName globals locals name
  | .path path => checkLiteralName globals locals (String.intercalate "::" path)
  | .ptr _ _ ty | .wrap ty | .embed ty _ none => checkLiteralType globals locals ty
  | .range ty lo hi _ => do
    checkLiteralType globals locals ty
    checkLiteralExpression globals locals lo
    checkLiteralExpression globals locals hi
  | .array ty n | .embed ty _ (some n) => do
    checkLiteralType globals locals ty
    checkLiteralExpression globals locals n
  | .str n => checkLiteralExpression globals locals n
  | .raw raw => checkLiteralRaw globals locals raw
  | ty => checkLiteralNames globals locals (Oeffentlich.namenT ty)

def checkLiteralClause (globals locals : List String) : SKlausel → Except String Unit
  | .needs e | .gives e | .cost e | .drops e => checkLiteralExpression globals locals e
  | .induc raw | .quits raw | .limit raw => checkLiteralRaw globals locals raw
  | clause => checkLiteralNames globals locals (Oeffentlich.namenK locals clause)

mutual
def checkLiteralBody (globals locals : List String) : SAnw → Except String Unit
  | .bind _ _ ty e | .bindQ _ _ ty e | .bindAxiomOpt _ ty e | .await _ ty e _ | .swap _ ty e _ => do
    ty.toList.forM (checkLiteralType globals locals)
    checkLiteralExpression globals locals e
  | .bindElse _ ty e _ body | .bindAxiomOptElse _ ty e _ body => do
    ty.toList.forM (checkLiteralType globals locals)
    checkLiteralExpression globals locals e
    checkLiteralBody globals locals body
  | .bindLib _ _ ty call => do
    ty.toList.forM (checkLiteralType globals locals)
    checkLiteralExpressions globals locals call.args
  | .set place _ value | .emit place value _ => do
    checkLiteralExpression globals locals place
    checkLiteralExpression globals locals value
  | .shift place _ _ | .free place | .trimReq place _ => checkLiteralExpression globals locals place
  | .callElse name args reason body => do
    checkLiteralExpression globals locals (.call name args)
    checkLiteralBody globals (reason :: locals) body
  | .call name args | .callQ name args => checkLiteralExpression globals locals (.call name args)
  | .genericCall name words args =>
    checkLiteralExpression globals locals (.ext .instantiate (name :: words) args)
  | .lcall call => checkLiteralExpressions globals locals call.args
  | .cond e yes branches no => do
    checkLiteralExpression globals locals e
    checkLiteralBody globals locals yes
    checkLiteralBodies globals locals branches
    checkLiteralOptionalBody globals locals no
  | .cases e arms => do
    checkLiteralExpression globals locals e
    checkLiteralBodies globals locals arms
  | .arm _ binder body => checkLiteralBody globals (binder.toList ++ locals) body
  | .each binder start _ subject _ raw invariant body => do
    checkLiteralExpressions globals locals start.toList
    checkLiteralExpression globals locals subject
    checkLiteralRaw globals (binder :: locals) raw
    checkLiteralExpressions globals (binder :: locals) invariant.toList
    checkLiteralBody globals (binder :: locals) body
  | .elsif e body | .trim e _ body | .locks _ e body => do
    checkLiteralExpression globals locals e
    checkLiteralBody globals locals body
  | .retry _ body | .loop _ body | .waive _ body | .watch _ body | .child body =>
    checkLiteralBody globals locals body
  | .ret value => checkLiteralExpressions globals locals value.toList
  | .alloc _ _ ty arena count no => do
    ty.toList.forM (checkLiteralType globals locals)
    checkLiteralName globals locals arena
    checkLiteralExpression globals locals count
    checkLiteralOptionalBody globals locals no
  | .allocVon _ _ ty arena => do
    ty.toList.forM (checkLiteralType globals locals)
    checkLiteralName globals locals arena
  | .grow arena count body => do
    checkLiteralName globals locals arena
    checkLiteralExpression globals locals count
    checkLiteralBody globals locals body
  | .reset arena span => do
    checkLiteralName globals locals arena
    for (start, count) in span.toList do
      checkLiteralExpression globals locals start
      checkLiteralExpression globals locals count
  | .start names => checkLiteralNames globals locals names
  | .block statements ending => do
    let final ← checkLiteralStatements globals locals statements
    match ending with
    | some (.ret value) => checkLiteralExpressions globals final value.toList
    | _ => pure ()
  | .other raw => checkLiteralRaw globals locals raw
  | _ => pure ()

/-- Branches share the incoming scope; bindings do not flow between them. -/
def checkLiteralBodies (globals locals : List String) : List SAnw → Except String Unit
  | [] => pure ()
  | body :: rest => do
    checkLiteralBody globals locals body
    checkLiteralBodies globals locals rest

def checkLiteralOptionalBody (globals locals : List String) : Option SAnw → Except String Unit
  | some body => checkLiteralBody globals locals body
  | none => pure ()

def checkLiteralStatements (globals locals : List String) :
    List SAnw → Except String (List String)
  | [] => pure locals
  | statement :: rest => do
    checkLiteralBody globals locals statement
    checkLiteralStatements globals (Aufloesung.gebunden statement ++ locals) rest
end

def checkLiteral (globals : List String) (sig : FnSig) (body : SAnw) : Except String Unit := do
  let locals := sig.params.map Prod.fst
  sig.params.forM (fun p => checkLiteralType globals locals p.2)
  sig.res.toList.forM (checkLiteralType globals locals)
  sig.klauseln.forM (checkLiteralClause globals locals)
  checkLiteralBody globals locals body

end Gabbro.Grammatik.Parser.Generic
