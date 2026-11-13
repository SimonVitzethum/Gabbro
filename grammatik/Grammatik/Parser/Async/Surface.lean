module

public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Print.Item
public import Grammatik.Parser.Round.RundlaufLex.Teil1a

namespace Gabbro.Grammatik.Parser.AsyncSource

/-- Outer syntax only. Keeping the complete ordinary signature preserves
    contracts, effects and error channels until ordinary G elaboration.
    `.await` is the contextual suffix `.field future "await"`; it is
    interpreted as suspension only by the async elaborator. -/
public structure Function where
  signature : FnSig
  body : SAnw

public inductive Item where
  | ordinary (item : SItemTief)
  | asynchronous (function : Function)
  | nested (path : List String) (items : List Item)
  | exported (item : Item)

/-- `async` remains contextual: the existing lexer emits an identifier.
    Neither the canonical source AST nor machine G gains a constructor. -/
@[expose] public def parseFunction (fuel : Nat) (tokens : List Token) :
    Except String (Function × List Token) := do
  let rest ← match tokens with
    | .ident "async" :: rest | .wort "async" :: rest => pure rest
    | _ => throw "async: expected async fn"
  let (item, rest) ← parseItemTief fuel rest
  match item with
  | .fnT signature body => pure (⟨signature, body⟩, rest)
  | _ => throw "async: expected a function with a body"

@[expose] public def printFunction (function : Function) : List Token :=
  .ident "async" :: druckItem (.fnT function.signature function.body)

@[expose] public def printText (function : Function) : String := renderText (printFunction function)

mutual
/-- Ordinary modules and visibility remain outer structure. Generic module
    templates still go through the canonical reader: async in a template
    needs a subsequent instantiation-aware extension, never token stripping. -/
@[expose] public def parseItem : Nat → List Token → Except String (Item × List Token)
  | 0, _ => .error "async: out of fuel"
  | fuel + 1, tokens =>
    match tokens with
    | .ident "async" :: _ | .wort "async" :: _ => do
      let (function, rest) ← parseFunction fuel tokens
      pure (.asynchronous function, rest)
    | .wort "pub" :: rest => do
      let (item, rest) ← parseItem fuel rest
      pure (.exported item, rest)
    | .wort "module" :: rest => do
      let (path, afterPath) ← nimmPfad rest
      match afterPath with
      | .zeichen "[" :: _ => do
        let (item, rest) ← parseItemTief fuel tokens
        pure (.ordinary item, rest)
      | _ => do
        let rest ← fordereZeichen "{" afterPath
        let (items, rest) ← parseItems fuel rest
        let rest ← fordereZeichen "}" rest
        pure (.nested path items, rest)
    | _ => do
      let (item, rest) ← parseItemTief fuel tokens
      pure (.ordinary item, rest)

/-- Explicit fuel and delimiters prevent dropping trailing declarations. -/
@[expose] public def parseItems : Nat → List Token → Except String (List Item × List Token)
  | 0, _ => .error "async: out of fuel"
  | fuel + 1, tokens =>
    match tokens with
    | .ende :: _ | .zeichen "}" :: _ => pure ([], tokens)
    | _ => do
      let (item, rest) ← parseItem fuel tokens
      let (items, rest) ← parseItems fuel rest
      pure (item :: items, rest)
end

mutual
@[expose] public def printItem : Item → List Token
  | .ordinary item => druckItem item
  | .asynchronous function => printFunction function
  | .nested path items => [.wort "module"] ++ pfadToks path ++ [.zeichen "{"] ++
      printItems items ++ [.zeichen "}"]
  | .exported item => .wort "pub" :: printItem item
@[expose] public def printItems : List Item → List Token
  | [] => []
  | item :: rest => printItem item ++ printItems rest
end

mutual
@[expose] public def hasAsync : Item → Bool
  | .asynchronous _ => true
  | .nested _ items => anyAsync items
  | .exported item => hasAsync item
  | .ordinary _ => false
@[expose] public def anyAsync : List Item → Bool
  | [] => false
  | item :: rest => hasAsync item || anyAsync rest
end

@[expose] public def parse (tokens : List Token) : Except String (List Item) :=
  match parseItems (tokens.length * 8 + 32) tokens with
  | .ok (items, [.ende]) => pure items
  | .ok _ => .error "async: trailing tokens"
  | .error error => .error error

@[expose] public def parseText (text : String) : Except String (List Item) := do
  let tokens ← (lex text).mapError (fun _ => "async: lex")
  parse tokens

/-- The suffix round trip reuses the existing expression printer. -/
@[expose] public def printAwait (future : SExpr) : List Token := druckToks (.field future "await")

end Gabbro.Grammatik.Parser.AsyncSource
