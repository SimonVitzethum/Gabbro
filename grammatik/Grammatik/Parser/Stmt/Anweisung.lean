/-
  File:      Grammatik/Parser/Anweisung.lean
  Subject:   T3 PART 2 (PLAN-TRANSLATION-VALIDATION.md section 1): Gabbro
              statements and blocks (SYNTAX.md section 7) over the Lean
              lexer and expression parser.

  The surface tree `SAnw`/`SEnde` with fuel-indexed readers
  (`parseStmt`, `parseBlock`, `parseTopStmt`, `parseTopBlock`).
  Probes live in `Parser/AnweisungProben.lean`.
-/
import Grammatik.Parser.Expr.Typ

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
    store their raw words (`each` etc. carry the header text).
    Against `ast.rs` `StmtArt`: `bind` = `Let`, `bindElse` =
    `LetSonst`, `set` = `Zuweisung`, `wenn` = `Wenn`, `cases` =
    `Match`, `each`/`retry`/`loop` = `Schleife`, `waive`
    = `Bricht`, `trim` = `Narrow`, `locks` = `Sperrt`,
    `watch` = `Observiert`, `leave` = `Leave`, `weiter` =
    `Next`, `emit` = `Publish`, `erwartet` = `AwaitLoad`,
    `swap` = `Exchange`, `rueck` = `Return`, `ruf` = `Ruf`,
    `lcall` = `LibraryCall`, `alloc` = `Alloc`, `reset` =
    `ResetArena`; `uebergang` is the `stateassign`
    (`transition … : A -> B`), `step` the `advstmt`
    (`advances a -> b`). An `else if` rides as a `elsif` node
    in the `wenn` list, a `match` arm as an `arm` node in the
    `cases` list -- pair-nodes instead of tuple lists, so the
    equality below stays a two-function block like
    `beqSExpr`/`beqSExprList` (see above). Against `parse.rs` `Block`: recovery and
    spans are dropped; a lone `;` (`P033`) is a parse error here. -/
/-- The `endstmt`: `return [expr]`, `leave l`, `next l`. Plain
    (no tree recursion), so plain equality reduces. It stands
    before `SAnw` so the `Repr` instance is in scope. -/
inductive SEnde
  | ret : Option SExpr → SEnde
  | leave : String → SEnde
  | next : String → SEnde
deriving Repr
inductive SAnw
  | bind : Bool → String → Option STyp → SExpr → SAnw
  | bindElse : String → Option STyp → SExpr → String → SAnw → SAnw
  | bindLib : Bool → String → Option STyp → String → String → SAnw
  | set : SExpr → String → SExpr → SAnw
  | shift : SExpr → String → String → SAnw
  | call : String → List SExpr → SAnw
  | lcall : String → String → Nat → SAnw
  | cond : SExpr → SAnw → List SAnw → Option SAnw → SAnw
  | elsif : SExpr → SAnw → SAnw
  | cases : SExpr → List SAnw → SAnw
  | arm : String → Option String → SAnw → SAnw
  /-- `traverse b [of e] over KIND of S by MODE [decreases …] [touches …] [invariant p] { … }`:
      binder, `of` start, domain kind word (`slots`, `ancestors`, …), domain subject, mode word,
      the raw words of `decreases`/`touches`, the invariant, the body. -/
  | each : String → Option SExpr → String → SExpr → String → String → Option SExpr → SAnw → SAnw
  | retry : String → SAnw → SAnw
  | loop : String → SAnw → SAnw
  | waive : List String → SAnw → SAnw
  | trim : SExpr → String → SAnw → SAnw
  | locks : Bool → SExpr → SAnw → SAnw
  | watch : String → SAnw → SAnw
  | leave : String → SAnw
  | next : String → SAnw
  | emit : SExpr → SExpr → String → SAnw
  | await : String → Option STyp → SExpr → String → SAnw
  | swap : String → Option STyp → SExpr → String → SAnw
  | step : String → String → SAnw
  | ret : Option SExpr → SAnw
  | alloc : Bool → String → Option STyp → String → SExpr → Option SAnw → SAnw
  /-- `reset A [at i count n];` -/
  | reset : String → Option (SExpr × SExpr) → SAnw
  /-- `grow A by e else { … };` -/
  | grow : String → SExpr → SAnw → SAnw
  /-- `free A[i];` -/
  | free : SExpr → SAnw
  /-- `child { … }` -/
  | child : SAnw → SAnw
  /-- `start { f, g };` -/
  | start : List String → SAnw
  | other : String → SAnw
  | block : List SAnw → Option SEnde → SAnw
  /-- `let [mut] x [: T] = alloc T;` -- the call of the provider of the open table `T` (`table T from p`). -/
  | allocVon : Bool → String → Option STyp → String → SAnw
deriving Repr

-- Shape equality on surface trees, as a `Bool`: one recursive
-- function plus the list helper, exactly like
-- `beqSExpr`/`beqSExprList` (which reduce by kernel evaluation).
-- The small non-recursive equalities stand first so the mutual
-- block below can use them.
/-- Equality on enders (plain: no tree recursion). -/
def beqSEnde : SEnde → SEnde → Bool
  | .ret x, .ret y => beqOptExpr x y
  | .leave a, .leave b => strEq a b
  | .next a, .next b => strEq a b
  | _, _ => false

def beqOptPaar : Option (SExpr × SExpr) → Option (SExpr × SExpr) → Bool
  | none, none => true
  | some (a, b), some (c, d) => beqSExpr a c && beqSExpr b d
  | _, _ => false

def beqOptEnde : Option SEnde → Option SEnde → Bool
  | none, none => true
  | some a, some b => beqSEnde a b
  | _, _ => false

mutual
def beqSAnw : SAnw → SAnw → Bool
  | .bind m a t x, .bind n b u y => m == n && strEq a b && beqSTypOpt t u && beqSExpr x y
  | .bindElse a t f e b, .bindElse c u g h d =>
    strEq a c && beqSTypOpt t u && beqSExpr f g && strEq e h && beqSAnw b d
  | .bindLib m a t l f, .bindLib n b u m2 g =>
    m == n && strEq a b && beqSTypOpt t u && strEq l m2 && strEq f g
  | .set z o x, .set w p y =>
    beqSExpr z w && strEq o p && beqSExpr x y
  | .shift z a b, .shift w c d =>
    beqSExpr z w && strEq a c && strEq b d
  | .call f a, .call g b => strEq f g && beqSExprList a b
  | .lcall l f n, .lcall m g k =>
    strEq l m && strEq f g && n == k
  | .cond c t ei s, .cond d u fi v =>
    beqSExpr c d && beqSAnw t u && beqSAnwList ei fi && beqOptAnw s v
  | .elsif c t, .elsif d u => beqSExpr c d && beqSAnw t u
  | .cases g a, .cases h b => beqSExpr g h && beqSAnwList a b
  | .arm v b t, .arm w c u =>
    strEq v w && beqOptWort b c && beqSAnw t u
  | .each b o k s m r i d, .each b2 o2 k2 s2 m2 r2 i2 d2 =>
    strEq b b2 && beqOptExpr o o2 && strEq k k2 && beqSExpr s s2 && strEq m m2 && strEq r r2 &&
      beqOptExpr i i2 && beqSAnw d d2
  | .retry h b, .retry i d => strEq h i && beqSAnw b d
  | .loop h b, .loop i d => strEq h i && beqSAnw b d
  | .waive inv b, .waive jnv d =>
    beqWorte inv jnv && beqSAnw b d
  | .trim o z s, .trim p w t =>
    beqSExpr o p && strEq z w && beqSAnw s t
  | .locks g o b, .locks h p d =>
    g == h && beqSExpr o p && beqSAnw b d
  | .watch d b, .watch e c => strEq d e && beqSAnw b c
  | .leave l, .leave m => strEq l m
  | .next l, .next m => strEq l m
  | .emit z w p, .emit y v q =>
    beqSExpr z y && beqSExpr w v && strEq p q
  | .await n t q e, .await m u p f =>
    strEq n m && beqSTypOpt t u && beqSExpr q p && strEq e f
  | .swap n t o k, .swap m u p l =>
    strEq n m && beqSTypOpt t u && beqSExpr o p && strEq k l
  | .step a b, .step c d => strEq a c && strEq b d
  | .ret x, .ret y => beqOptExpr x y
  | .alloc m n y t w s, .alloc k o z u v r =>
    m == k && strEq n o && beqSTypOpt y z && strEq t u && beqSExpr w v && beqOptAnw s r
  | .allocVon m n y t, .allocVon k o z u => m == k && strEq n o && beqSTypOpt y z && strEq t u
  | .reset a x, .reset b y => strEq a b && beqOptPaar x y
  | .grow a e b, .grow c f d => strEq a c && beqSExpr e f && beqSAnw b d
  | .free a, .free b => beqSExpr a b
  | .child a, .child b => beqSAnw a b
  | .start a, .start b => beqWorte a b
  | .other a, .other b => strEq a b
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
-- helpers, so `else if` branches ride as `elsif` nodes and
-- `match` arms as `arm` nodes instead.

/-- Split a trailing `return`/`leave`/`next` off a statement list:
    an `endblock` reads as `block pre (some …)`, a plain `block` as
    `block all none`. -/
def schliesseBlock : List SAnw → SAnw
  | [] => .block [] none
  | ss => match ss.getLast? with
    | some (.ret x) => .block ss.dropLast (some (.ret x))
    | some (.leave l) => .block ss.dropLast (some (.leave l))
    | some (.next l) => .block ss.dropLast (some (.next l))
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
/-- The raw words of a `traverse` header up to `invariant` or the body `{` (brace-free clauses). -/
def traverseRest : List Token → Except String (String × List Token)
  | [] => .error "loop without body"
  | (.zeichen "{" :: rest) => .ok ("", .zeichen "{" :: rest)
  | (.wort s :: rest) =>
    if strEq s "invariant" then .ok ("", .wort s :: rest)
    else match traverseRest rest with
      | .error e => .error e
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
  | (t :: rest) => match traverseRest rest with
    | .error e => .error e
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)

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
      else if strEq w "traverse" then parseTraverse f rest
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
      else if strEq w "grow" then parseGrow f rest
      else if strEq w "free" then parseFree f rest
      else if strEq w "child" then parseChild f rest
      else if strEq w "transition" then parseUebergang f rest
      else if strEq w "advances" then parseSchreitet f rest
      else parsePlatzStmt f toks
    | .ident "start" :: .zeichen "{" :: rest => parseStart f rest
    | .zeichen "@" :: _ => parseLibStmt f toks
    | _ => parsePlatzStmt f toks
/-- `let [mut] x [: T] = …` (behind the `let`): the optional type ascription is READ now (it was
    skipped as raw words), then the right side decides the form. -/
def parseLet (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (m, t1) : Bool × List Token := match toks with
      | .wort "mut" :: rest => (true, rest)
      | _ => (false, toks)
    let (name, r1) ← nimmName t1
    let (ty, r2) ← (match r1 with
      | .zeichen ":" :: r => do
        let (t, r') ← parseTyp f r
        pure (some t, r')
      | _ => pure (none, r1))
    let nach ← fordereZeichen "=" r2
    match nach with
    | .zeichen "@" :: _ => parseLetLib f m name ty nach
    | .wort s :: t :: .zeichen ";" :: rest =>
      if strEq s "alloc" then match nameText t with
        | some tisch => pure (.allocVon m name ty tisch, rest)
        | none => parseLetExpr f m name ty nach
      else parseLetExpr f m name ty nach
    | .wort s :: t :: .zeichen "(" :: _ =>
      if strEq s "alloc" then match nameText t with
        | some _ => parseLetAlloc f m name ty nach
        | none => parseLetExpr f m name ty nach
      else parseLetExpr f m name ty nach
    | _ => parseLetExpr f m name ty nach
def parseLetLib (f : Nat) (m : Bool) (name : String) (ty : Option STyp)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let ((l, g, _), rest) ← parseLibRuf f toks
    let rest' ← fordereZeichen ";" rest
    pure (.bindLib m name ty l g, rest')
def parseLetAlloc (f : Nat) (m : Bool) (name : String) (ty : Option STyp)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort _ :: rest => do
      let (tisch, rest') ← nimmName rest
      let rest'' ← fordereZeichen "(" rest'
      let (w, rest3) ← parseOr f rest''
      let rest4 ← fordereZeichen ")" rest3
      let (sonst, rest5) : Option SAnw × List Token ← (match rest4 with
        | .wort "else" :: r => do
          let (b, r') ← parseBlock f r
          pure (some b, r')
        | _ => pure (none, rest4))
      let rest6 ← fordereZeichen ";" rest5
      pure (.alloc m name ty tisch w sonst, rest6)
    | _ => .error "alloc without table"
def parseLetExpr (f : Nat) (m : Bool) (name : String) (ty : Option STyp)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (e, rest) ← parseOr f toks
    match rest with
    | .wort "else" :: .zeichen "(" :: rest' => do
      let (fehler, rest'') ← nimmName rest'
      let rest3 ← fordereZeichen ")" rest''
      let (b, rest4) ← parseBlock f rest3
      pure (.bindElse name ty e fehler b, rest4)
    | .wort "else" :: _ => .error "else without ("
    | .wort "awaits" :: .zeichen "{" :: rest' => do
      let (pl, rest'') ← nimmBisZeichen "}" rest' 0
      let rest3 ← fordereZeichen "}" rest''
      let rest4 ← fordereZeichen ";" rest3
      pure (.await name ty e pl, rest4)
    | .wort "awaits" :: _ => .error "awaits without {"
    | .wort "exchange" :: rest' => do
      let (k, rest'') ← nimmBisZeichen ";" rest' 0
      let rest3 ← fordereZeichen ";" rest''
      pure (.swap name ty e k, rest3)
    | _ => do
      let rest' ← fordereZeichen ";" rest
      pure (.bind m name ty e, rest')
/-- `grow A by e else { … } ;` (lane 257, SYNTAX.md 9.1), behind the `grow`. -/
def parseGrow (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (a, r1) ← nimmName toks
    let r2 ← nimmWort "by" r1
    let (e, r3) ← parseOr f r2
    let r4 ← nimmWort "else" r3
    let (b, r5) ← parseBlock f r4
    let r ← fordereZeichen ";" r5
    pure (.grow a e b, r)
/-- `free A[i] ;` (TODO 1-B, SYNTAX.md 9.1), behind the `free`: the place is read as a place. -/
def parseFree (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (p, r1) ← parseOrt f toks
    let r ← fordereZeichen ";" r1
    pure (.free p, r)
/-- `child { … }` (lane O-1, SYNTAX.md 12.1), behind the `child`. -/
def parseChild (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (b, r) ← parseBlock f toks
    pure (.child b, r)
/-- `start { f, g } ;` (lane 253; `start` is no keyword), behind the `start {`. A trailing comma is
    allowed, as in `parse.rs` `startform`. -/
def parseStart (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (ps, r1) ← parseStartRoots f toks
    let r ← fordereZeichen ";" r1
    pure (.start ps, r)
/-- The root paths of a `start { … }`, up to and including the `}`. -/
def parseStartRoots (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (n, r1) ← nimmName toks
    let (segs, r2) := sammleSegmente r1 [n]
    let p := "::".intercalate segs
    match r2 with
    | .zeichen "," :: .zeichen "}" :: r => pure ([p], r)
    | .zeichen "," :: r3 => do
      let (ps, r) ← parseStartRoots f r3
      pure (p :: ps, r)
    | _ => do
      let r ← fordereZeichen "}" r2
      pure ([p], r)
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
      | .call c args => match fordereZeichen ";" rest with
        | .ok rest' => .ok (.call c args, rest')
        | .error e => .error e
      | .ext .call _ (callee :: args) => match fordereZeichen ";" rest with
        | .ok rest' => .ok (.call (druck callee) args, rest')
        | .error e => .error e
      | _ => match rest with
        | .zeichen "(" :: _ => match parseArgs f rest.tail with
          | .ok (args, rest') => match fordereZeichen ";" rest' with
            | .ok rest'' => .ok (.call (druck e) args, rest'')
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
                        | .ok rest3 => .ok (.emit e w "nothing", rest3)
                        | .error e => .error e
                      else .error "publishes without payload"
                    | .zeichen "{" :: rest'' => match nimmBisZeichen "}" rest'' 0 with
                      | .ok (pl, rest3) => match fordereZeichen "}" rest3 with
                        | .ok rest4 => match fordereZeichen ";" rest4 with
                          | .ok rest5 => .ok (.emit e w pl, rest5)
                          | .error e => .error e
                        | .error e => .error e
                      | .error e => .error e
                    | _ => .error "publishes without payload"
                  else .error "a publication sits on `=`, not on a compound assignment"
                else match fordereZeichen ";" rest' with
                  | .ok rest'' => .ok (.set e op w, rest'')
                  | .error e => .error e
              | _ => match fordereZeichen ";" rest' with
                | .ok rest'' => .ok (.set e op w, rest'')
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
      | .ok rest' => .ok (.lcall l g n, rest')
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
        | .ok ((eis, s), rest'') => .ok (.cond c t eis s, rest'')
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
              | .ok (b, rest'') => parseElseIfs f rest'' (acc ++ [.elsif c b])
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
          | .ok rest3 => .ok (.cases g arms, rest3)
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
/-- `traverse` with a structured header (SYNTAX.md section 8). -/
def parseTraverse (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (b, r1) =>
      match (match r1 with
          | .wort "of" :: r => match parseOr f r with
            | .error e => .error e
            | .ok (e, r') => .ok (some e, r')
          | _ => .ok (none, r1) : Except String (Option SExpr × List Token)) with
      | .error e => .error e
      | .ok (o, r2) => match nimmWort "over" r2 with
        | .error e => .error e
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (k, r4) => match nimmWort "of" r4 with
            | .error e => .error e
            | .ok r5 => match parseOr f r5 with
              | .error e => .error e
              | .ok (s, r6) => match nimmWort "by" r6 with
                | .error e => .error e
                | .ok r7 => match nimmName r7 with
                  | .error e => .error e
                  | .ok (m, r8) => match traverseRest r8 with
                    | .error e => .error e
                    | .ok (raw, r9) =>
                      match (match r9 with
                          | .wort "invariant" :: r => match parsePred f r with
                            | .error e => .error e
                            | .ok (i, r') => .ok (some i, r')
                          | _ => .ok (none, r9) : Except String (Option SExpr × List Token)) with
                      | .error e => .error e
                      | .ok (inv, r10) => match parseBlock f r10 with
                        | .error e => .error e
                        | .ok (body, rest') => .ok (.each b o k s m raw inv body, rest')

/-- `retry` (1), `forever` (2): the header rides raw
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
        if art == 1 then .ok (.retry h b, rest')
        else .ok (.loop h b, rest')
def parseBricht (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmIdentList f toks with
    | .error e => .error e
    | .ok (inv, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (b, rest') => .ok (.waive inv b, rest')
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
                  | .ok (b, rest4) => .ok (.trim o "finite" b, rest4)
                  | .error e => .error e
                else .error "narrow without else"
              | _ => .error "narrow without else"
            else match nimmBisWort "else" rest' 0 with
              | .ok (t, rest3) => match nimmWort "else" rest3 with
                | .ok rest4 => match parseBlock f rest4 with
                  | .ok (b, rest5) => .ok (.trim o t b, rest5)
                  | .error e => .error e
                | .error e => .error e
              | .error e => .error e
          | _ => match nimmBisWort "else" rest' 0 with
            | .ok (t, rest3) => match nimmWort "else" rest3 with
              | .ok rest4 => match parseBlock f rest4 with
                | .ok (b, rest5) => .ok (.trim o t b, rest5)
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
      | .ok (b, rest') => .ok (.locks g o b, rest')
def parseBeobachtet (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (d, rest) => match parseBlock f rest with
      | .error e => .error e
      | .ok (b, rest') => .ok (.watch d b, rest')
def parseVerlasse (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (l, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.leave l, rest')
      | .error e => .error e
def parseWeiter (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (l, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.next l, rest')
      | .error e => .error e
def parseRueck (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen ";" :: rest => .ok (.ret none, rest)
    | _ => match parseOr f toks with
      | .error e => .error e
      | .ok (x, rest) => match fordereZeichen ";" rest with
        | .ok rest' => .ok (.ret (some x), rest')
        | .error e => .error e
/-- `reset A [at i count n] ;` (SYNTAX.md 9.1, the range form of M-ALLTAG C), behind the `reset`. -/
def parseReset (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (a, rest) ← nimmName toks
    let (rg, r1) ← (match rest with
      | .wort "at" :: r => do
        let (i, r2) ← parseOr f r
        let r3 ← nimmWort "count" r2
        let (n, r4) ← parseOr f r3
        pure (some (i, n), r4)
      | _ => pure (none, rest))
    let r ← fordereZeichen ";" r1
    pure (.reset a rg, r)
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
              | .ok rest5 => .ok (.shift z von nach, rest5)
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
          | .ok rest3 => .ok (.step a b, rest3)
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
      `elsif` nodes and `match` arms as `arm` nodes, and the
      equality block stays three functions. Any new tuple-list
      field on `SAnw` re-opens this trap.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopStmt
#print axioms Gabbro.Grammatik.Parser.parseTopBlock
