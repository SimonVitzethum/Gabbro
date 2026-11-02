module
public import Grammatik.Parser.Item.ElementTief.Defs1
@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- A static argument is a global path or a complete capture-free function body. The literal
    constructor is last; neither alternative adds a runtime expression or instruction. -/
inductive SFunctionArgument
  | path : List String → SFunctionArgument
  | literal : FnSig → SAnw → SFunctionArgument
  deriving Repr

/-- Read the argument by its declared kind, after the outer argument splitter has preserved
    nested delimiters. Literal heads and bodies reuse the ordinary function readers. -/
def parseFunctionArgument (fuel : Nat) (tokens : List Token) :
    Except String SFunctionArgument := do
  match tokens with
  | .wort "fn" :: rest =>
    let (sig, remaining) ← parseFnSig fuel "" (.wort "fn" :: .ident "$literal" :: rest)
    if sig.fehler.isSome then throw "function literal cannot declare a reason channel"
    let (body, remaining) ← parseBlock fuel remaining
    match remaining with
    | [.ende] => pure (.literal sig body)
    | _ => throw "function literal has trailing tokens"
  | _ =>
    let (path, remaining) ← nimmPfad tokens
    match remaining with
    | [.ende] => pure (.path path)
    | _ => throw "static function argument must be a path or function literal"

/-- Names bound anywhere inside a literal, used only to preserve their spelling during module
    qualification. The later free-name check follows lexical scopes rather than this overapproximation. -/
def literalLocals : SAnw → List String
  | .bind _ n _ _ | .bindLib _ n _ _ | .allocVon _ n _ _ | .await n _ _ _ |
    .swap n _ _ _ => [n]
  | .bindElse n _ _ _ body => n :: literalLocals body
  | .alloc _ n _ _ _ body => n :: body.toList.flatMap literalLocals
  | .cond _ yes branches no => literalLocals yes ++ branches.flatMap literalLocals ++
      no.toList.flatMap literalLocals
  | .cases _ arms => arms.flatMap literalLocals
  | .arm _ binder body => binder.toList ++ literalLocals body
  | .each binder _ _ _ _ _ _ body => binder :: literalLocals body
  | .elsif _ body | .retry _ body | .loop _ body | .waive _ body | .trim _ _ body |
    .locks _ _ body | .watch _ body | .grow _ _ body | .child body => literalLocals body
  | .block statements _ => statements.flatMap literalLocals
  | _ => []

end Gabbro.Grammatik.Parser
