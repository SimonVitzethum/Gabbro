module

public import Grammatik.Parser.Expr.Typ
public import Grammatik.Parser.Stmt.Anweisung.Kopf

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

def parseWeiter (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (l, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.next l, rest')
      | .error e => .error e

/-- `@lib#fn(args) { region }`: retain ordered expressions and the balanced input tokens.
    Both names are `::` paths (`nimmPfad`); the reader never produces an empty path. -/
def parseLibRuf (f : Nat) (toks : List Token) :
    Except String (SLibraryCall × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match nimmPfad rest with
      | .ok (l, rest') => match fordereZeichen "#" rest' with
        | .ok rest'' => match nimmPfad rest'' with
          | .ok (g, rest3) => match fordereZeichen "(" rest3 with
            | .ok rest4 => match parseArgs f rest4 with
              | .ok (args, rest5) => match fordereZeichen "{" rest5 with
                | .ok rest6 => match libraryRegion rest6 1 with
                  | .ok (region, rest7) => .ok (⟨l, g, args, region⟩, rest7)
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
    | .ok (call, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.lcall call, rest')
      | .error e => .error e
    | .error e => .error e

def parseVerlasse (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (l, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (.leave l, rest')
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

def parseLetLib (f : Nat) (m : Bool) (name : String) (ty : Option STyp)
    (toks : List Token) : Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (call, rest) ← parseLibRuf f toks
    let rest' ← fordereZeichen ";" rest
    pure (.bindLib m name ty call, rest')

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

/-- `free A[i] ;` (TODO 1-B, SYNTAX.md 9.1), behind the `free`: the place is read as a place. -/
def parseFree (f : Nat) (toks : List Token) :
    Except String (SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (p, r1) ← parseOrt f toks
    let r ← fordereZeichen ";" r1
    pure (.free p, r)

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

/-- `;` or `?;` behind a call statement (`ABSTRACTION-SYNTAX-PLAN.md` §4.3): a trailing `?`
    keeps the call and marks it for reason propagation (the desugarer replaces it by the
    explicit `else` form); otherwise the plain call. -/
def parseRufSchwanz (c : String) (args : List SExpr) : List Token → Except String (SAnw × List Token)
  | .zeichen s :: rest0 =>
    if strEq s "?" then
      match rest0 with
      | .zeichen t :: rest => if strEq t ";" then .ok (.callQ c args, rest) else .error "? without ;"
      | _ => .error "? without ;"
    else match fordereZeichen ";" (.zeichen s :: rest0) with
      | .ok rest => .ok (.call c args, rest)
      | .error e => .error e
  | toks => match fordereZeichen ";" toks with
    | .ok rest => .ok (.call c args, rest)
    | .error e => .error e

theorem strEq_semi_frage : strEq ";" "?" = false := by decide

/-- Read the reason handler after a statement call, using the enclosing block reader.
    With no written binder the reason remains inaccessible to source identifiers. -/
def parseRufMitElse (block : List Token → Except String (SAnw × List Token))
    (c : String) (args : List SExpr) (toks : List Token) : Except String (SAnw × List Token) :=
  match toks with
  | .wort w :: rest =>
    if strEq w "else" then do
      let (reason, rest) ← match rest with
        | .zeichen s :: tail =>
          if strEq s "(" then do
            let (name, tail) ← nimmName tail
            let tail ← fordereZeichen ")" tail
            pure (name, tail)
          else pure ("", rest)
        | _ => pure ("", rest)
      let (body, rest) ← block rest
      let rest ← fordereZeichen ";" rest
      pure (.callElse c args reason body, rest)
    else parseRufSchwanz c args toks
  | _ => parseRufSchwanz c args toks

end Gabbro.Grammatik.Parser
