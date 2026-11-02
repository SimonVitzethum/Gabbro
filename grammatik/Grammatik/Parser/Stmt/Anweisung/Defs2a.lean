module

public import Grammatik.Parser.Expr.Typ
public import Grammatik.Parser.Stmt.Anweisung.Defs1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

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

/-- `child { … }` (lane O-1, SYNTAX.md 12.1), behind the `child`. -/
def parseChild (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (b, r) ← parseBlock f toks
    pure (.child b, r)

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

end


end Gabbro.Grammatik.Parser
