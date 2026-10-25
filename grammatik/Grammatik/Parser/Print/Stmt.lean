/-
  File:      Grammatik/Parser/Print/Stmt.lean
  Subject:   Track P: the token printer of types, statements and blocks -- the inverse of `parseTyp`,
             `parseStmt`, `parseBlock` on the trees the reader builds.

  Total on every constructor of `SAnw` and `STyp`. Names print as `nameTok` -- the token the lexer
  reads for them, `wort` for a table word, `ident` otherwise (the reader takes both through `nameText`) --,
  keywords as `wort`, the raw words of a header (`retry`/`forever`, `decreases`/`touches`,
  payloads, `exchange` tails) are lexed back through `lex`. The expression parts use `druckToks`
  (`Round/Rundlauf`), whose `gut` shapes have the round-trip theorem; the statement level is measured, not
  proved: `Print/Proben` decides one witness per statement form and `Cover/Census` runs the round trip over
  every function body of the corpus (`rt=ok/total`).
-/
import Grammatik.Parser.Round.Rundlauf
import Grammatik.Parser.Stmt.Anweisung

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- The tokens of a raw header string (the words the reader kept as text): the lexer's tokens without the
    end marker. -/
def rohToks (s : String) : List Token :=
  match lex s with
  | .ok ts => ts.filter (fun t => match t with | .ende => false | _ => true)
  | .error _ => []

/-- A surface type as tokens (the inverse of `parseTyp`). -/
def druckTyp : STyp → List Token
  | .atom a => [nameTok a]
  | .path segs => pfadToks segs
  | .ptr r w t =>
    [.wort "ptr", .zeichen "<", nameTok r, .zeichen ","] ++ rohToks w ++ [.zeichen ">"] ++ druckTyp t
  | .index o t => (if o then [.wort "option"] else []) ++ [.wort "index", .wort "into", nameTok t]
  | .range b lo hi x =>
    druckTyp b ++ [.wort "in"] ++ druckToks lo ++ [.zeichen (if x then "..<" else "..")] ++ druckToks hi
  | .array t n => [.zeichen "["] ++ druckTyp t ++ [.zeichen ";"] ++ druckToks n ++ [.zeichen "]"]
  | .wrap t => druckTyp t ++ [.wort "wrapping"]
  | .embed b s o =>
    druckTyp b ++ [.wort "embeds", .zeichen "["] ++ rohToks s ++
      (match o with
        | some e => [.wort "scale"] ++ druckToks e
        | none => [])
  | .raw s => rohToks s
  | .str e => [.ident "string", .wort "max"] ++ druckToks e
  | .entry h o =>
    [.wort "entry", .wort "fn", .zeichen "("] ++ rohToks h ++
      (match o with
        | some t => [.zeichen "->"] ++ druckTyp t
        | none => [])

/-- `: T` of a `let`, when there is one. -/
def druckTypOpt : Option STyp → List Token
  | some t => [.zeichen ":"] ++ druckTyp t
  | none => []

/-- The ender of a block: `return`, `leave`, `next`. -/
def druckEnde : Option SEnde → List Token
  | none => []
  | some (.ret none) => [.wort "return", .zeichen ";"]
  | some (.ret (some e)) => [.wort "return"] ++ druckToks e ++ [.zeichen ";"]
  | some (.leave l) => [.wort "leave", nameTok l, .zeichen ";"]
  | some (.next l) => [.wort "next", nameTok l, .zeichen ";"]

/-- A path or a place text as tokens (a call name rides as the text of the place). -/
def druckNamen : List String → List Token
  | [] => []
  | [x] => [nameTok x]
  | x :: xs => [nameTok x, .zeichen ","] ++ druckNamen xs

/-- Root paths of a `start { … }`. -/
def druckWurzeln : List String → List Token
  | [] => []
  | [p] => rohToks p
  | p :: ps => rohToks p ++ [.zeichen ","] ++ druckWurzeln ps

mutual
/-- A statement as tokens (the inverse of `parseStmt`). -/
def druckAnw : SAnw → List Token
  | .bind m x ty e =>
    [.wort "let"] ++ (if m then [.wort "mut"] else []) ++ [nameTok x] ++ druckTypOpt ty ++
      [.zeichen "="] ++ druckToks e ++ [.zeichen ";"]
  | .bindElse x ty e f b =>
    [.wort "let", nameTok x] ++ druckTypOpt ty ++ [.zeichen "="] ++ druckToks e ++
      [.wort "else", .zeichen "(", nameTok f, .zeichen ")"] ++ druckAnw b
  | .bindLib m x ty l f =>
    [.wort "let"] ++ (if m then [.wort "mut"] else []) ++ [nameTok x] ++ druckTypOpt ty ++
      [.zeichen "=", .zeichen "@", nameTok l, .zeichen "#", nameTok f, .zeichen "(", .zeichen ")",
       .zeichen "{", .zeichen "}", .zeichen ";"]
  | .set z o w => druckToks z ++ [.zeichen o] ++ druckToks w ++ [.zeichen ";"]
  | .shift z a b =>
    [.wort "transition"] ++ druckToks z ++ [.zeichen ":", nameTok a, .zeichen "->", nameTok b, .zeichen ";"]
  | .call f xs => rohToks f ++ [.zeichen "("] ++ druckToksListe xs ++ [.zeichen ")", .zeichen ";"]
  | .lcall l f n =>
    [.zeichen "@", nameTok l, .zeichen "#", nameTok f, .zeichen "("] ++
      kommaToks (List.replicate n [.num 0]) ++ [.zeichen ")", .zeichen "{", .zeichen "}", .zeichen ";"]
  | .cond c t eis s =>
    [.wort "if"] ++ druckToks c ++ druckAnw t ++ druckAnwListe eis ++
      (match s with
        | some b => [.wort "else"] ++ druckAnw b
        | none => [])
  | .elsif c b => [.wort "else", .wort "if"] ++ druckToks c ++ druckAnw b
  | .cases g arms => [.wort "match"] ++ druckToks g ++ [.zeichen "{"] ++ druckAnwListe arms ++ [.zeichen "}"]
  | .arm v b t =>
    [nameTok v] ++
      (match b with
        | some x => [.zeichen "(", nameTok x, .zeichen ")"]
        | none => []) ++
      [.zeichen "=>"] ++ druckAnw t
  | .each b o k s m r i body =>
    [.wort "traverse", nameTok b] ++
      (match o with
        | some e => [.wort "of"] ++ druckToks e
        | none => []) ++
      [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ rohToks r ++
      (match i with
        | some e => [.wort "invariant"] ++ druckToks e
        | none => []) ++
      druckAnw body
  | .retry h b => [.wort "retry"] ++ rohToks h ++ druckAnw b
  | .loop h b => [.wort "forever"] ++ rohToks h ++ druckAnw b
  | .waive ns b => [.wort "breaking"] ++ druckNamen ns ++ druckAnw b
  | .trim o t b => [.wort "narrow"] ++ druckToks o ++ [.wort "to"] ++ rohToks t ++ [.wort "else"] ++ druckAnw b
  | .locks g o b => [.wort "locks"] ++ (if g then [.wort "shared"] else []) ++ druckToks o ++ druckAnw b
  | .watch d b => [.wort "observes", nameTok d] ++ druckAnw b
  | .leave l => [.wort "leave", nameTok l, .zeichen ";"]
  | .next l => [.wort "next", nameTok l, .zeichen ";"]
  | .emit z w p =>
    druckToks z ++ [.zeichen "="] ++ druckToks w ++ [.wort "publishes"] ++
      (if strEq p "nothing" then [.wort "nothing"] else [.zeichen "{"] ++ rohToks p ++ [.zeichen "}"]) ++
      [.zeichen ";"]
  | .await n q e =>
    [.wort "let", nameTok n, .zeichen "="] ++ druckToks q ++ [.wort "awaits", .zeichen "{"] ++ rohToks e ++
      [.zeichen "}", .zeichen ";"]
  | .swap n o k =>
    [.wort "let", nameTok n, .zeichen "="] ++ druckToks o ++ [.wort "exchange"] ++ rohToks k ++ [.zeichen ";"]
  | .step a b => [.wort "advances", nameTok a, .zeichen "->", nameTok b, .zeichen ";"]
  | .ret none => [.wort "return", .zeichen ";"]
  | .ret (some e) => [.wort "return"] ++ druckToks e ++ [.zeichen ";"]
  | .alloc m n ty t w s =>
    [.wort "let"] ++ (if m then [.wort "mut"] else []) ++ [nameTok n] ++ druckTypOpt ty ++
      [.zeichen "=", .wort "alloc", nameTok t, .zeichen "("] ++ druckToks w ++ [.zeichen ")"] ++
      (match s with
        | some b => [.wort "else"] ++ druckAnw b
        | none => []) ++
      [.zeichen ";"]
  | .allocVon m n ty t =>
    [.wort "let"] ++ (if m then [.wort "mut"] else []) ++ [nameTok n] ++ druckTypOpt ty ++
      [.zeichen "=", .wort "alloc", nameTok t, .zeichen ";"]
  | .reset a rg =>
    [.wort "reset", nameTok a] ++
      (match rg with
        | some (i, n) => [.wort "at"] ++ druckToks i ++ [.wort "count"] ++ druckToks n
        | none => []) ++
      [.zeichen ";"]
  | .grow a e b =>
    [.wort "grow", nameTok a, .wort "by"] ++ druckToks e ++ [.wort "else"] ++ druckAnw b ++ [.zeichen ";"]
  | .free a => [.wort "free"] ++ druckToks a ++ [.zeichen ";"]
  | .child a => [.wort "child"] ++ druckAnw a
  | .start ps => [.ident "start", .zeichen "{"] ++ druckWurzeln ps ++ [.zeichen "}", .zeichen ";"]
  | .other s => rohToks s
  | .block ss e => [.zeichen "{"] ++ druckAnwListe ss ++ druckEnde e ++ [.zeichen "}"]
/-- A statement list as tokens. -/
def druckAnwListe : List SAnw → List Token
  | [] => []
  | s :: ss => druckAnw s ++ druckAnwListe ss
end

/-- The round trip of one block: print, read back, compare by shape. -/
def rundlaufBlock (b : SAnw) : Bool :=
  beqTopBlock (parseTopBlock (druckAnw b ++ [.ende])) (.ok b)

end Gabbro.Grammatik.Parser
