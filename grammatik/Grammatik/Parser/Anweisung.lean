/-
  File:      Grammatik/Parser/Anweisung.lean
  Subject:   T3 PART 2 (PLAN-UEBERSETZUNGSVALIDIERUNG.md section 1): Gabbro
              statements and blocks (SYNTAX.md section 7) over the Lean
              lexer and expression parser.

  The surface tree `SAnw`/`SEnde` with fuel-indexed readers
  (`parseStmt`, `parseBlock`, `parseTopStmt`, `parseTopBlock`).
  Probes live in `Parser/AnweisungProben.lean`.
-/
import Grammatik.Parser.Ausdruck

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/- A surface tree: SYNTAX.md section 7 `stmt`, `block` and
    `endblock` without types, spans or attribute checks. ONE
    inductive on purpose: kernel `decide` does not reduce recursive
    `Bool` equality over a MUTUAL family (measured 2026-09-13 --
    even comparing two empty blocks gets stuck), while
    the single-type form with a list helper reduces like
    `beqSExpr`/`beqSExprList`. A block is the `block` node: a
    statement list with an optional ender. A trailing
    `return`/`leave`/`next` statement is split off as the ender, so
    an `endblock` reads as `block pre (some …)` and a plain `block`
    as `block all none` (see `schliesseBlock`).

    Expressions ride as `SExpr`; headers the reader does not split
    store their raw words (`traverseS` etc. carry the header text).
    Against `ast.rs` `StmtArt`: `lass` = `Let`, `lassElse` =
    `LetSonst`, `zuweis` = `Zuweisung`, `wenn` = `Wenn`, `matchS` =
    `Match`, `traverseS`/`retryS`/`foreverS` = `Schleife`, `bricht`
    = `Bricht`, `narrowS` = `Narrow`, `sperrt` = `Sperrt`,
    `beobachtet` = `Observiert`, `verlasse` = `Leave`, `weiter` =
    `Next`, `publiziert` = `Publish`, `erwartet` = `AwaitLoad`,
    `tauscht` = `Exchange`, `rueck` = `Return`, `ruf` = `Ruf`,
    `libruf` = `LibraryCall`, `allocS` = `Alloc`, `resetS` =
    `ResetArena`; `uebergang` is the `stateassign`
    (`transition … : A -> B`), `schreitet` the `advstmt`
    (`advances a -> b`). An `else if` rides as a `sonstWenn` node
    in the `wenn` list, a `match` arm as an `arm` node in the
    `matchS` list -- pair-nodes instead of tuple lists, so the
    equality below stays a two-function block like
    `beqSExpr`/`beqSExprList` (see above). Against `parse.rs` `Block`: recovery and
    spans are dropped; a lone `;` (`P033`) is a parse error here. -/
/-- The `endstmt`: `return [expr]`, `leave l`, `next l`. Plain
    (no tree recursion), so plain equality reduces. It stands
    before `SAnw` so the `Repr` instance is in scope. -/
inductive SEnde
  | ret : Option SExpr → SEnde
  | fort : String → SEnde
  | naechst : String → SEnde
deriving Repr
inductive SAnw
  | lass : Bool → String → SExpr → SAnw
  | lassElse : String → String → String → SAnw → SAnw
  | lassLib : Bool → String → String → String → SAnw
  | zuweis : SExpr → String → SExpr → SAnw
  | uebergang : SExpr → String → String → SAnw
  | ruf : String → List SExpr → SAnw
  | libruf : String → String → Nat → SAnw
  | wenn : SExpr → SAnw → List SAnw → Option SAnw → SAnw
  | sonstWenn : SExpr → SAnw → SAnw
  | matchS : SExpr → List SAnw → SAnw
  | arm : String → Option String → SAnw → SAnw
  | traverseS : String → SAnw → SAnw
  | retryS : String → SAnw → SAnw
  | foreverS : String → SAnw → SAnw
  | bricht : List String → SAnw → SAnw
  | narrowS : SExpr → String → SAnw → SAnw
  | sperrt : Bool → SExpr → SAnw → SAnw
  | beobachtet : String → SAnw → SAnw
  | verlasse : String → SAnw
  | weiter : String → SAnw
  | publiziert : SExpr → SExpr → String → SAnw
  | erwartet : String → SExpr → String → SAnw
  | tauscht : String → SExpr → String → SAnw
  | schreitet : String → String → SAnw
  | rueck : Option SExpr → SAnw
  | allocS : Bool → String → String → SExpr → Option SAnw → SAnw
  | resetS : String → SAnw
  | sonst : String → SAnw
  | block : List SAnw → Option SEnde → SAnw
deriving Repr

-- Shape equality on surface trees, as a `Bool`: one recursive
-- function plus the list helper, exactly like
-- `beqSExpr`/`beqSExprList` (which reduce by kernel evaluation).
-- The small non-recursive equalities stand first so the mutual
-- block below can use them.
def beqOptExpr : Option SExpr → Option SExpr → Bool
  | none, none => true
  | some a, some b => beqSExpr a b
  | _, _ => false

/-- Equality on enders (plain: no tree recursion). -/
def beqSEnde : SEnde → SEnde → Bool
  | .ret x, .ret y => beqOptExpr x y
  | .fort a, .fort b => strEq a b
  | .naechst a, .naechst b => strEq a b
  | _, _ => false

def beqOptEnde : Option SEnde → Option SEnde → Bool
  | none, none => true
  | some a, some b => beqSEnde a b
  | _, _ => false

def beqOptWort : Option String → Option String → Bool
  | none, none => true
  | some a, some b => strEq a b
  | _, _ => false

def beqWorte : List String → List String → Bool
  | [], [] => true
  | x :: xs, y :: ys => strEq x y && beqWorte xs ys
  | _, _ => false

mutual
def beqSAnw : SAnw → SAnw → Bool
  | .lass m a x, .lass n b y => m == n && strEq a b && beqSExpr x y
  | .lassElse a f e b, .lassElse c g h d =>
    strEq a c && strEq f g && strEq e h && beqSAnw b d
  | .lassLib m a l f, .lassLib n b m2 g =>
    m == n && strEq a b && strEq l m2 && strEq f g
  | .zuweis z o x, .zuweis w p y =>
    beqSExpr z w && strEq o p && beqSExpr x y
  | .uebergang z a b, .uebergang w c d =>
    beqSExpr z w && strEq a c && strEq b d
  | .ruf f a, .ruf g b => strEq f g && beqSExprList a b
  | .libruf l f n, .libruf m g k =>
    strEq l m && strEq f g && n == k
  | .wenn c t ei s, .wenn d u fi v =>
    beqSExpr c d && beqSAnw t u && beqSAnwList ei fi && beqOptAnw s v
  | .sonstWenn c t, .sonstWenn d u => beqSExpr c d && beqSAnw t u
  | .matchS g a, .matchS h b => beqSExpr g h && beqSAnwList a b
  | .arm v b t, .arm w c u =>
    strEq v w && beqOptWort b c && beqSAnw t u
  | .traverseS h b, .traverseS i d => strEq h i && beqSAnw b d
  | .retryS h b, .retryS i d => strEq h i && beqSAnw b d
  | .foreverS h b, .foreverS i d => strEq h i && beqSAnw b d
  | .bricht inv b, .bricht jnv d =>
    beqWorte inv jnv && beqSAnw b d
  | .narrowS o z s, .narrowS p w t =>
    beqSExpr o p && strEq z w && beqSAnw s t
  | .sperrt g o b, .sperrt h p d =>
    g == h && beqSExpr o p && beqSAnw b d
  | .beobachtet d b, .beobachtet e c => strEq d e && beqSAnw b c
  | .verlasse l, .verlasse m => strEq l m
  | .weiter l, .weiter m => strEq l m
  | .publiziert z w p, .publiziert y v q =>
    beqSExpr z y && beqSExpr w v && strEq p q
  | .erwartet n q e, .erwartet m p f =>
    strEq n m && beqSExpr q p && strEq e f
  | .tauscht n o k, .tauscht m p l =>
    strEq n m && beqSExpr o p && strEq k l
  | .schreitet a b, .schreitet c d => strEq a c && strEq b d
  | .rueck x, .rueck y => beqOptExpr x y
  | .allocS m n t w s, .allocS k o u v r =>
    m == k && strEq n o && strEq t u && beqSExpr w v && beqOptAnw s r
  | .resetS a, .resetS b => strEq a b
  | .sonst a, .sonst b => strEq a b
  | .block ss e, .block ts f => beqSAnwList ss ts && beqOptEnde e f
  | _, _ => false
def beqSAnwList : List SAnw → List SAnw → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSAnw x y && beqSAnwList xs ys
  | _, _ => false
def beqOptAnw : Option SAnw → Option SAnw → Bool
  | none, none => true
  | some a, some b => beqSAnw a b
  | _, _ => false
end

-- The equality block above must STAY three functions: larger mutual
-- blocks compile to the irreducible `PSum` fixed point, which
-- `decide` cannot unfold (measured 2026-09-13 -- even comparing two
-- empty blocks gets stuck). Tuple lists would need their own
-- helpers, so `else if` branches ride as `sonstWenn` nodes and
-- `match` arms as `arm` nodes instead.

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
  | .zahl n => toString n
  | .gleit s => s
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

/-- Split a trailing `return`/`leave`/`next` off a statement list:
    an `endblock` reads as `block pre (some …)`, a plain `block` as
    `block all none`. -/
def schliesseBlock : List SAnw → SAnw
  | [] => .block [] none
  | ss => match ss.getLast? with
    | some (.rueck x) => .block ss.dropLast (some (.ret x))
    | some (.verlasse l) => .block ss.dropLast (some (.fort l))
    | some (.weiter l) => .block ss.dropLast (some (.naechst l))
    | _ => .block ss none

-- The statement levels of SYNTAX.md section 7 (`stmt`, `block`,
-- `endblock`), each with fuel: every call passes strictly less fuel,
-- so the block terminates by `f`. Against `parse.rs`: the head-word
-- dispatch (`wort_ist_anweisungskopf` via `istKopfForm`), the
-- `let`-form order (`alloc`/`@` before the expression, then
-- `awaits`/`exchange`/`else`), the call-or-assignment split
-- (`zuweisung_oder_ruf`) and the block-end rule (no trailing `;`
-- after a block form, `P033`) match one by one. Predicates, domains,
-- `xform` bodies, payload lists and type ascriptions ride as raw
-- words (see CUTS).
mutual
def parseStmt (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort w :: rest =>
      if istOrtsFort rest then parsePlatzStmt f toks
      else if strEq w "let" then parseLet f rest
      else if strEq w "if" then parseWenn f rest
      else if strEq w "match" then parseMatchS f rest
      else if strEq w "traverse" then parseSchleife f rest 0
      else if strEq w "retry" then parseSchleife f rest 1
      else if strEq w "forever" then parseSchleife f rest 2
      else if strEq w "breaking" then parseBricht f rest
      else if strEq w "narrow" then parseNarrow f rest
      else if strEq w "locks" then parseSperrt f rest
      else if strEq w "observes" then parseBeobachtet f rest
      else if strEq w "leave" then parseVerlasse f rest
      else if strEq w "next" then parseWeiter f rest
      else if strEq w "return" then parseRueck f rest
      else if strEq w "reset" then parseReset f rest
      else if strEq w "transition" then parseUebergang f rest
      else if strEq w "advances" then parseSchreitet f rest
      else parsePlatzStmt f toks
    | .zeichen "@" :: _ => parseLibStmt f toks
    | _ => parsePlatzStmt f toks
def parseLet (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 =>
    let (m, t1) := match toks with
      | .wort s :: rest => if strEq s "mut" then (true, rest) else (false, toks)
      | _ => (false, toks)
    match nimmName t1 with
    | .error e => .error e
    | .ok (name, rest) =>
      let rest' := match rest with
        | .zeichen ":" :: _ => match nimmBisZeichen "=" rest 0 with
          | .ok (_, r) => r
          | .error _ => rest
        | _ => rest
      match fordereZeichen "=" rest' with
      | .error e => .error e
      | .ok nach =>
        match nach with
        | .zeichen "@" :: _ => parseLetLib f m name nach
        | .wort s :: t :: .zeichen "(" :: _ =>
          if strEq s "alloc" then match nameText t with
            | some _ => parseLetAlloc f m name nach
            | none => parseLetExpr f m name nach
          else parseLetExpr f m name nach
        | _ => parseLetExpr f m name nach
def parseLetLib (f : Nat) (m : Bool) (name : String)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseLibRuf f toks with
    | .ok ((l, g, _), rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.lassLib m name l g, rest')
      | .error e => .error e
    | .error e => .error e
def parseLetAlloc (f : Nat) (m : Bool) (name : String)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort _ :: rest => match nimmName rest with
      | .ok (tisch, rest') => match fordereZeichen "(" rest' with
        | .ok rest'' => match parseOr f rest'' with
          | .ok (w, rest3) => match fordereZeichen ")" rest3 with
            | .ok rest4 =>
              let (sonst, rest5) : Option SAnw × List Token :=
                match rest4 with
                | .wort s :: _ =>
                  if strEq s "else" then match parseBlock f rest4.tail with
                    | .ok (b, r) => (some b, r)
                    | .error _ => (none, rest4)
                  else (none, rest4)
                | _ => (none, rest4)
              match sonst with
              | some _ => match fordereZeichen ";" rest5 with
                | .ok rest6 => .ok (.allocS m name tisch w sonst, rest6)
                | .error e => .error e
              | none => match fordereZeichen ";" rest5 with
                | .ok rest6 => .ok (.allocS m name tisch w none, rest6)
                | .error e => .error e
            | .error e => .error e
          | .error e => .error e
        | .error e => .error e
      | .error e => .error e
    | _ => .error "alloc without table"
def parseLetExpr (f : Nat) (m : Bool) (name : String)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseOr f toks with
    | .error e => .error e
    | .ok (e, rest) => match rest with
      | .wort s :: _ =>
        if strEq s "else" then match rest.tail with
          | .zeichen "(" :: rest' => match nimmName rest' with
            | .ok (fehler, rest'') => match fordereZeichen ")" rest'' with
              | .ok rest3 => match parseBlock f rest3 with
                | .ok (b, rest4) =>
                  .ok (.lassElse name (druck e) fehler b, rest4)
                | .error e => .error e
              | .error e => .error e
            | .error e => .error e
          | _ => .error "else without ("
        else if strEq s "awaits" then match rest.tail with
          | .zeichen "{" :: rest' => match nimmBisZeichen "}" rest' 0 with
            | .ok (pl, rest'') => match fordereZeichen "}" rest'' with
              | .ok rest3 => match fordereZeichen ";" rest3 with
                | .ok rest4 => .ok (.erwartet name e pl, rest4)
                | .error e => .error e
              | .error e => .error e
            | .error e => .error e
          | _ => .error "awaits without {"
        else if strEq s "exchange" then match nimmBisZeichen ";" rest.tail 0 with
          | .ok (k, rest') => match fordereZeichen ";" rest' with
            | .ok rest'' => .ok (.tauscht name e k, rest'')
            | .error e => .error e
          | .error e => .error e
        else match fordereZeichen ";" rest with
          | .ok rest' => .ok (.lass m name e, rest')
          | .error e => .error e
      | _ => match fordereZeichen ";" rest with
        | .ok rest' => .ok (.lass m name e, rest')
        | .error e => .error e
def parsePlatzStmt (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort w :: _ =>
      if strEq w "transition" then parseUebergang f toks.tail
      else parseKopfStmt f toks
    | _ => parseKopfStmt f toks
/-- After the head word: a call through a path or a place, or an
    assignment (`parse.rs` `zuweisung_oder_ruf`). -/
def parseKopfStmt (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseKopf f toks with
    | .error e => .error e
    | .ok (e, rest) => match e with
      | .ruf c args => match fordereZeichen ";" rest with
        | .ok rest' => .ok (.ruf c args, rest')
        | .error e => .error e
      | _ => match rest with
        | .zeichen "(" :: _ => match parseArgs f rest.tail with
          | .ok (args, rest') => match fordereZeichen ";" rest' with
            | .ok rest'' => .ok (.ruf (druck e) args, rest'')
            | .error e => .error e
          | .error e => .error e
        | .zeichen op :: _ =>
          if strEq op "=" || strEq op "+=" || strEq op "-=" ||
             strEq op "&=" || strEq op "|=" then
            match parseOr f rest.tail with
            | .error e => .error e
            | .ok (w, rest') => match rest' with
              | .wort s :: _ =>
                if strEq s "publishes" then
                  if strEq op "=" then match rest'.tail with
                    | .wort p :: rest'' =>
                      if strEq p "nothing" then match fordereZeichen ";" rest'' with
                        | .ok rest3 => .ok (.publiziert e w "nothing", rest3)
                        | .error e => .error e
                      else .error "publishes without payload"
                    | .zeichen "{" :: rest'' => match nimmBisZeichen "}" rest'' 0 with
                      | .ok (pl, rest3) => match fordereZeichen "}" rest3 with
                        | .ok rest4 => match fordereZeichen ";" rest4 with
                          | .ok rest5 => .ok (.publiziert e w pl, rest5)
                          | .error e => .error e
                        | .error e => .error e
                      | .error e => .error e
                    | _ => .error "publishes without payload"
                  else .error "a publication sits on `=`, not on a compound assignment"
                else match fordereZeichen ";" rest' with
                  | .ok rest'' => .ok (.zuweis e op w, rest'')
                  | .error e => .error e
              | _ => match fordereZeichen ";" rest' with
                | .ok rest'' => .ok (.zuweis e op w, rest'')
                | .error e => .error e
          else .error "assignment or call expected"
        | _ => .error "assignment or call expected"
/-- `@lib#fn(args) { region }` in statement position (`parse.rs`
    `library_call`): names, argument count, region skipped balanced. -/
def parseLibRuf (f : Nat) (toks : List Token) :
    Except String ((String × String × Nat) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match nimmName rest with
      | .ok (l, rest') => match fordereZeichen "#" rest' with
        | .ok rest'' => match nimmName rest'' with
          | .ok (g, rest3) => match fordereZeichen "(" rest3 with
            | .ok rest4 => match parseArgs f rest4 with
              | .ok (args, rest5) => match fordereZeichen "{" rest5 with
                | .ok rest6 => match nimmBereich rest6 1 with
                  | .ok rest7 => .ok ((l, g, args.length), rest7)
                  | .error e => .error e
                | .error e => .error e
              | .error e => .error e
            | .error e => .error e
          | .error e => .error e
        | .error e => .error e
      | .error e => .error e
    | _ => .error "@ without library"
def parseLibStmt (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseLibRuf f toks with
    | .ok ((l, g, n), rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.libruf l g n, rest')
      | .error e => .error e
    | .error e => .error e
def parseWenn (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseOr f toks with
    | .error e => .error e
    | .ok (c, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (t, rest') => match parseElseIfs f rest' [] with
        | .error e => .error e
        | .ok ((eis, s), rest'') => .ok (.wenn c t eis s, rest'')
def parseElseIfs (f : Nat) (toks : List Token)
    (acc : List SAnw) :
    Except String ((List SAnw × Option SAnw) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "else" then match rest with
        | .wort t :: _ =>
          if strEq t "if" then match parseOr f rest.tail with
            | .error e => .error e
            | .ok (c, rest') => match parseBlock f rest' with
              | .error e => .error e
              | .ok (b, rest'') => parseElseIfs f rest'' (acc ++ [.sonstWenn c b])
          else match parseBlock f rest with
            | .error e => .error e
            | .ok (b, rest') => .ok ((acc, some b), rest')
        | _ => match parseBlock f rest with
          | .error e => .error e
          | .ok (b, rest') => .ok ((acc, some b), rest')
      else .ok ((acc, none), toks)
    | _ => .ok ((acc, none), toks)
def parseMatchS (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseOr f toks with
    | .error e => .error e
    | .ok (g, rest) => match fordereZeichen "{" rest with
      | .error e => .error e
      | .ok rest' => match parseArme f rest' with
        | .error e => .error e
        | .ok (arms, rest'') => match fordereZeichen "}" rest'' with
          | .ok rest3 => .ok (.matchS g arms, rest3)
          | .error e => .error e
def parseArme (f : Nat) (toks : List Token) :
    Except String (List SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: _ => .ok ([], toks)
    | _ => match nimmName toks with
      | .error e => .error e
      | .ok (v, rest) =>
        let (binder, rest') : Option String × List Token :=
          match rest with
          | .zeichen "(" :: rest'' => match nimmName rest'' with
            | .ok (b, rest3) => match fordereZeichen ")" rest3 with
              | .ok rest4 => (some b, rest4)
              | .error _ => (none, rest)
            | .error _ => (none, rest)
          | _ => (none, rest)
        match fordereZeichen "=>" rest' with
        | .error e => .error e
        | .ok rest'' => match parseBlock f rest'' with
          | .error e => .error e
          | .ok (b, rest3) => match parseArme f rest3 with
            | .error e => .error e
            | .ok (arms, rest4) => .ok ((.arm v binder b) :: arms, rest4)
/-- `traverse` (0), `retry` (1), `forever` (2): the header rides raw
    (domains, bounds, invariants need the `pred` reader), the body is
    a block. -/
def parseSchleife (f : Nat) (toks : List Token) (art : Nat) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match schleifenKopf toks f with
    | .error e => .error e
    | .ok (h, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (b, rest') =>
        if art == 0 then .ok (.traverseS h b, rest')
        else if art == 1 then .ok (.retryS h b, rest')
        else .ok (.foreverS h b, rest')
def parseBricht (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmIdentList f toks with
    | .error e => .error e
    | .ok (inv, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (b, rest') => .ok (.bricht inv b, rest')
def nimmIdentList (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, rest) => match rest with
      | .zeichen "," :: rest' => match nimmIdentList f rest' with
        | .error e => .error e
        | .ok (ns, r) => .ok (n :: ns, r)
      | _ => .ok ([n], rest)
def parseNarrow (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseOrt f toks with
    | .error e => .error e
    | .ok (o, rest) => match rest with
      | .wort s :: rest' =>
        if strEq s "to" then match rest' with
          | .wort z :: rest'' =>
            if strEq z "finite" then match rest'' with
              | .wort e :: rest3 =>
                if strEq e "else" then match parseBlock f rest3 with
                  | .ok (b, rest4) => .ok (.narrowS o "finite" b, rest4)
                  | .error e => .error e
                else .error "narrow without else"
              | _ => .error "narrow without else"
            else match nimmBisWort "else" rest' 0 with
              | .ok (t, rest3) => match nimmWort "else" rest3 with
                | .ok rest4 => match parseBlock f rest4 with
                  | .ok (b, rest5) => .ok (.narrowS o t b, rest5)
                  | .error e => .error e
                | .error e => .error e
              | .error e => .error e
          | _ => match nimmBisWort "else" rest' 0 with
            | .ok (t, rest3) => match nimmWort "else" rest3 with
              | .ok rest4 => match parseBlock f rest4 with
                | .ok (b, rest5) => .ok (.narrowS o t b, rest5)
                | .error e => .error e
              | .error e => .error e
            | .error e => .error e
        else .error "narrow without to"
      | _ => .error "narrow without to"
def parseSperrt (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 =>
    let (g, t1) := match toks with
      | .wort s :: rest => if strEq s "shared" then (true, rest) else (false, toks)
      | _ => (false, toks)
    match parseOrt f t1 with
    | .error e => .error e
    | .ok (o, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (b, rest') => .ok (.sperrt g o b, rest')
def parseBeobachtet (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (d, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (b, rest') => .ok (.beobachtet d b, rest')
def parseVerlasse (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (l, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.verlasse l, rest')
      | .error e => .error e
def parseWeiter (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (l, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.weiter l, rest')
      | .error e => .error e
def parseRueck (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen ";" :: rest => .ok (.rueck none, rest)
    | _ => match parseOr f toks with
      | .error e => .error e
      | .ok (x, rest) => match fordereZeichen ";" rest with
        | .ok rest' => .ok (.rueck (some x), rest')
        | .error e => .error e
def parseReset (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (a, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.resetS a, rest')
      | .error e => .error e
def parseUebergang (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseOrt f toks with
    | .error e => .error e
    | .ok (z, rest) => match fordereZeichen ":" rest with
      | .error e => .error e
      | .ok rest' => match nimmName rest' with
        | .error e => .error e
        | .ok (von, rest'') => match fordereZeichen "->" rest'' with
          | .error e => .error e
          | .ok rest3 => match nimmName rest3 with
            | .error e => .error e
            | .ok (nach, rest4) => match fordereZeichen ";" rest4 with
              | .ok rest5 => .ok (.uebergang z von nach, rest5)
              | .error e => .error e
def parseSchreitet (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (a, rest) => match fordereZeichen "->" rest with
      | .error e => .error e
      | .ok rest' => match nimmName rest' with
        | .error e => .error e
        | .ok (b, rest'') => match fordereZeichen ";" rest'' with
          | .ok rest3 => .ok (.schreitet a b, rest3)
          | .error e => .error e
def parseBlock (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok rest => match parseStmts f rest with
      | .error e => .error e
      | .ok (ss, rest') => match fordereZeichen "}" rest' with
        | .ok rest'' => .ok (schliesseBlock ss, rest'')
        | .error e => .error e
def parseStmts (f : Nat) (toks : List Token) :
    Except String (List SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: _ => .ok ([], toks)
    | .ende :: _ => .error "wanted }"
    | [] => .error "wanted }"
    | _ => match parseStmt f toks with
      | .error e => .error e
      | .ok (s, rest) => match parseStmts f rest with
        | .error e => .error e
        | .ok (ss, rest') => .ok (s :: ss, rest')
/-- One statement: the token list must end here. -/
def parseTopStmt (toks : List Token) : Except String SAnw :=
  match parseStmt (toks.length * 8 + 32) toks with
  | .ok (s, [.ende]) => .ok s
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e
/-- One block: the token list must end here. -/
def parseTopBlock (toks : List Token) : Except String SAnw :=
  match parseBlock (toks.length * 8 + 32) toks with
  | .ok (b, [.ende]) => .ok b
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e
/-- Shape equality on statement outcomes, as a `Bool`. -/
def beqTopStmt : Except String SAnw → Except String SAnw → Bool
  | .ok a, .ok b => beqSAnw a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
/-- Shape equality on block outcomes, as a `Bool`. -/
def beqTopBlock : Except String SAnw → Except String SAnw → Bool
  | .ok a, .ok b => beqSAnw a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
end

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here, and every shape difference against
  `crates/gabbro-syntax` found by the probes.

  *Every difference below was found by reading `ast.rs`/`parse.rs`
  (`cargo` cannot run in this lane); each is a documented gap, not a
  silent one.*

  1. Predicates ride raw: loop headers (`traverse` domains,
     `retry … until`, invariants), `narrow` ranges, `xform` bodies,
     `awaits`/`publishes` payloads and `exchange` tails are raw
     words, never `pred`/`domain` trees. There is no `pred`
     reader (SYNTAX.md section 5) in this lane.
  2. Type ascriptions ride raw: `let x : T = …` skips `T`
     unchecked (`nimmBisZeichen "="`), so a malformed type reads
     as long as it holds no top-level `=`.
  3. `let … else` accepts any expression source; `parse.rs`
     refuses non-call non-place sources (`P016`).
  4. `fnStart` (like `schleifenKopf`) steps over an `effects {…}`
     group and stops at any other `word {` adjacency: a header
     brace inside parens (an anonymous `structty` in a signature)
     would stop it early. No corpus signature carries one.
  5. `nimmBisWort`/`nimmBisZeichen` track only braces: a `;` or
     `else` inside a string cannot occur (strings lex as one
     token), and parens/brackets need no tracking for the
     stoppers used.
  6. `schliesseBlock` splits a trailing `return`/`leave`/`next`
     off EVERY block: a mid-body `return` at the end of a loop
     body reads as an ender, where `parse.rs` keeps it a plain
     statement (`endblock` only at function/`else` level).
  7. `P033` (lone `;`), `P035` (abolished forms), error recovery
     (`synchronisiere_anweisung`) and spans: refused or dropped;
     this reader stops at the first error with no code.
  8. `beqSAnw`/`beqTopStmt`/`beqTopBlock` are not proved sound or
     complete: the probes compare by kernel `Bool` evaluation
     (see also the equality-shape finding below).
  9. `parseTopStmt`/`parseTopBlock` are total but not complete:
     fuel `length * 8 + 32` suffices for every probe (each
     `decide` checks its own fuel); a huge input may report
     out-of-fuel instead of parsing.
  10. No printer, no round trip: statements/blocks have no
      `druck`, so there is no `print_parse` for this level.
  11. EQUALITY SHAPE (measured 2026-09-13): kernel `decide` does
      not reduce recursive `Bool` equality over a MUTUAL
      inductive family -- even comparing two empty blocks gets
      stuck (not slow: 2M heartbeats still stuck). Larger mutual
      `def` blocks compile to the irreducible `PSum` fixed point
      (`#print` shows it), which `decide` cannot unfold; the
      two-function shape compiles to `brecOn`, which reduces.
      Consequence: statements AND blocks live in the ONE type
      `SAnw` (a block is a node), `else if` branches ride as
      `sonstWenn` nodes and `match` arms as `arm` nodes, and the
      equality block stays three functions. Any new tuple-list
      field on `SAnw` re-opens this trap.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopStmt
#print axioms Gabbro.Grammatik.Parser.parseTopBlock
