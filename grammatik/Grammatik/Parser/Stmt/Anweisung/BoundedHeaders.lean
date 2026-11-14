module

public import Grammatik.Parser.Stmt.Anweisung.Kopf

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- The two bounded source forms share the existing retry model, but have no progress assumption. -/
inductive SBoundedHeader
  | whileLoop : SExpr → SExpr → String → SBoundedHeader
  | forRange : String → SExpr → SExpr → Option String → SBoundedHeader
  deriving Repr

/-- A handler may be qualified; its whole path must end the header. -/
def boundedHandlerName (tokens : List Token) : Option String :=
  match nimmPfad tokens with
  | .ok (path, [.ende]) => some (String.intercalate "::" path)
  | _ => none

/-- Read the whole header. In particular, no effects, progress clause or duplicate clause is dropped. -/
def readBoundedHeader (raw : String) : Except String SBoundedHeader := do
  let tokens ← match lex raw with
    | .ok ts => pure ts
    | .error _ => throw "loop.header.lex"
  match tokens with
  | .wort "while" :: rest =>
    let (condition, rest) ← match parseOr 10000 rest with
      | .ok value => pure value
      | .error _ => throw "while.condition"
    let rest ← match rest with
      | .wort "bounded" :: rest => pure rest
      | _ => throw "while.bound.missing"
    let (bound, rest) ← match parseOr 10000 rest with
      | .ok value => pure value
      | .error _ => throw "while.bound.static-natural-required"
    let rest ← match rest with
      | .wort "ops" :: rest => pure rest
      | _ => throw "while.bound.ops-required"
    match rest with
    | .wort "on_exceeded" :: rest =>
      match boundedHandlerName rest with
      | some name => pure (.whileLoop condition bound name)
      | none => throw "while.on_exceeded.name-required"
    | _ => throw "while.on_exceeded.required"
  | .wort "for" :: rest =>
    let (binder, rest) ← match nimmName rest with
      | .ok value => pure value
      | .error _ => throw "for.index.name-required"
    let rest ← match rest with
      | .wort "in" :: rest => pure rest
      | _ => throw "for.range.integer-required"
    let (lo, rest) ← match parseOr 10000 rest with
      | .ok value => pure value
      | .error _ => throw "for.range.integer-required"
    let rest ← match rest with
      | .zeichen "..<" :: rest => pure rest
      | _ => throw "for.range.half-open-required"
    let (hi, rest) ← match parseOr 10000 rest with
      | .ok value => pure value
      | .error _ => throw "for.range.integer-required"
    match rest with
    | [.ende] => pure (.forRange binder lo hi none)
    | .wort "on_exceeded" :: rest =>
      match boundedHandlerName rest with
      | some name => pure (.forRange binder lo hi (some name))
      | none => throw "for.on_exceeded.name-required"
    | _ => throw "for.header.trailing-clause"
  | _ => throw "loop.header.kind"

/-- The range index is local to its body in every source-tree visitor. -/
def boundedLoopLocals (raw : String) : List (String × STyp) :=
  match readBoundedHeader raw with
  | .ok (.forRange binder lo hi _) => [(binder, .range (.atom "i64") lo hi false)]
  | _ => []

/-- Expressions in header evaluation order, before the range binder enters scope. -/
def boundedLoopExpressions (raw : String) : List SExpr :=
  match readBoundedHeader raw with
  | .ok (.whileLoop condition bound _) => [condition, bound]
  | .ok (.forRange _ lo hi _) => [lo, hi]
  | _ => []

end Gabbro.Grammatik.Parser
