/-
  File:      Grammatik/Parser/Expr/Tokens.lean
  Subject:   T3: the token-level helpers every reader shares (expect a word, a mark, a name; raw
             collection up to a stop word; balanced regions) and the small `Bool` equalities
             on options and word lists. They stood in `Anweisung.lean`; the type reader
             (`Typ.lean`) needs them before the statement reader exists.
-/
import Grammatik.Parser.Expr.Ausdruck

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

def beqOptExpr : Option SExpr → Option SExpr → Bool
  | none, none => true
  | some a, some b => beqSExpr a b
  | _, _ => false

def beqOptWort : Option String → Option String → Bool
  | none, none => true
  | some a, some b => strEq a b
  | _, _ => false

def beqWorte : List String → List String → Bool
  | [], [] => true
  | x :: xs, y :: ys => strEq x y && beqWorte xs ys
  | _, _ => false

/-- Expect the keyword `w` (a `wort` token with this text). -/
def nimmWort (w : String) : List Token → Except String (List Token)
  | .wort s :: rest => if strEq s w then .ok rest else .error ("wanted " ++ w)
  | _ => .error ("wanted " ++ w)

/-- Expect the punctuation `z` (a `zeichen` token with this text). -/
def fordereZeichen (z : String) : List Token → Except String (List Token)
  | .zeichen s :: rest => if strEq s z then .ok rest else .error ("wanted " ++ z)
  | _ => .error ("wanted " ++ z)

/-- Take one name (an identifier or a contextual keyword, as in
    `parse.rs` `erwarte_ident`). -/
def nimmName : List Token → Except String (String × List Token)
  | t :: rest => match nameText t with
    | some s => .ok (s, rest)
    | none => .error "name expected"
  | [] => .error "name expected"

/-- Is this token the head word `w` (a `wort` token with this text)?
    `parse.rs` `wort_ist_anweisungskopf` decides head-vs-place by the
    NEXT token; the dispatch below does the same (see
    `istKopfForm`). -/
def istWort (w : String) : List Token → Bool
  | .wort s :: _ => strEq s w
  | _ => false

/-- The place continuations of `parse.rs` `ist_ortfortsetzung`:
    after one of these a head word is a place, never a form. -/
def istOrtsFort (toks : List Token) : Bool :=
  match toks with
  | .zeichen "=" :: _ => true
  | .zeichen "+=" :: _ => true
  | .zeichen "-=" :: _ => true
  | .zeichen "&=" :: _ => true
  | .zeichen "|=" :: _ => true
  | .zeichen "." :: _ => true
  | .zeichen "->" :: _ => true
  | .zeichen "[" :: _ => true
  | .zeichen "::" :: _ => true
  | _ => false

/-- Head-word test: `w` opens its form unless a place continuation
    follows (`parse.rs` `wort_ist_anweisungskopf`). -/
def istKopfForm (w : String) : List Token → Bool
  | .wort s :: rest => strEq s w && !istOrtsFort rest
  | _ => false

/-- One token as raw text (for unsplit headers). -/
def zeigeTok : Token → String
  | .ident s => s
  | .wort s => s
  | .num n => toString n
  | .float s => s
  | .text s => "\"" ++ s ++ "\""
  | .zeichen s => s
  | .ende => "<ende>"

/-- Collect raw words until the stop word at depth zero (braces
    tracked). Used for loop headers and other unsplit prefixes. -/
def nimmBisWort (stopp : String) : List Token → Nat → Except String (String × List Token)
  | [], _ => .error ("wanted " ++ stopp)
  | (.wort s :: rest), tiefe =>
    if strEq s stopp && tiefe == 0 then .ok ("", .wort s :: rest)
    else match nimmBisWort stopp rest tiefe with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (.zeichen "{" :: rest), tiefe => match nimmBisWort stopp rest (tiefe + 1) with
    | .ok (h, r) => .ok ("{ " ++ h, r)
    | .error e => .error e
  | (.zeichen "}" :: rest), tiefe =>
    if tiefe == 0 then .error ("wanted " ++ stopp)
    else match nimmBisWort stopp rest (tiefe - 1) with
      | .ok (h, r) => .ok ("} " ++ h, r)
      | .error e => .error e
  | (t :: rest), tiefe => match nimmBisWort stopp rest tiefe with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- Collect raw words until the punctuation `stopp` at depth zero
    (braces tracked). Used for type ascriptions and loop headers. -/
def nimmBisZeichen (stopp : String) : List Token → Nat → Except String (String × List Token)
  | [], _ => .error ("wanted " ++ stopp)
  | (.zeichen s :: rest), tiefe =>
    if tiefe == 0 && strEq s stopp then .ok ("", .zeichen s :: rest)
    else if strEq s "{" then match nimmBisZeichen stopp rest (tiefe + 1) with
      | .ok (h, r) => .ok ("{ " ++ h, r)
      | .error e => .error e
    else if strEq s "}" then
      if tiefe == 0 then .error ("wanted " ++ stopp)
      else match nimmBisZeichen stopp rest (tiefe - 1) with
        | .ok (h, r) => .ok ("} " ++ h, r)
        | .error e => .error e
    else match nimmBisZeichen stopp rest tiefe with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (t :: rest), tiefe => match nimmBisZeichen stopp rest tiefe with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- Skip a brace-balanced `{ … }` region (the `libregion` of a
    library call, captured without interpreting, SYNTAX.md §7). -/
def nimmBereich : List Token → Nat → Except String (List Token)
  | [], _ => .error "wanted }"
  | (.zeichen "{" :: rest), tiefe => nimmBereich rest (tiefe + 1)
  | (.zeichen "}" :: rest), 1 => .ok rest
  | (.zeichen "}" :: rest), tiefe + 2 => nimmBereich rest (tiefe + 1)
  | (_ :: rest), tiefe => nimmBereich rest tiefe

/-- Raw words of a brace-balanced region (the caller consumed the
    opening `{`; depth counts the pending closes). Structural on the
    token list. -/
def nimmBereichWorte : List Token → Nat → Except String (String × List Token)
  | [], _ => .error "wanted }"
  | (.zeichen "{" :: rest), tiefe => match nimmBereichWorte rest (tiefe + 1) with
    | .ok (h, r) => .ok ("{ " ++ h, r)
    | .error e => .error e
  | (.zeichen "}" :: rest), 1 => .ok ("} ", rest)
  | (.zeichen "}" :: rest), tiefe + 2 => match nimmBereichWorte rest (tiefe + 1) with
    | .ok (h, r) => .ok ("} " ++ h, r)
    | .error e => .error e
  | (t :: rest), tiefe => match nimmBereichWorte rest tiefe with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- A loop header until the body `{`: the `effects {…}` clause of
    `retry`/`forever` is stepped over balanced (every other header
    clause is brace-free). Structural on the token list. -/
def schleifenKopf : List Token → Nat → Except String (String × List Token)
  | [], _ => .error "loop without body"
  | _, 0 => .error "out of fuel"
  | ((.wort s :: .zeichen "{" :: rest)), n + 1 =>
    if strEq s "effects" then match nimmBereichWorte rest 1 with
      | .ok (h, r) => match schleifenKopf r n with
        | .ok (h2, r2) => .ok ("effects { " ++ h ++ h2, r2)
        | .error e => .error e
      | .error e => .error e
    else .ok (s ++ " ", .zeichen "{" :: rest)
  | (.zeichen "{" :: rest), _ => .ok ("", .zeichen "{" :: rest)
  | (t :: rest), n + 1 => match schleifenKopf rest n with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

end Gabbro.Grammatik.Parser
