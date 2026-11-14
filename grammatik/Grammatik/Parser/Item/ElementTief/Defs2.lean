module

public import Grammatik.Parser.Item.ElementTief.Defs2a
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000
def parseTransRest (f : Nat) (tr : STrans) (toks : List Token) :
    Except String (STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "requires" then match parsePred f rest with
        | .error e => .error e
        | .ok (p, r) => parseTransRest f { tr with voraus := some p } r
      else if strEq s "effects" then match parseEffektBlock f rest with
        | .error e => .error e
        | .ok (es, r) => parseTransRest f { tr with wirkung := es } r
      else .ok (tr, toks)
    | _ => .ok (tr, toks)

def parseSchrittPlatzNach (f : Nat) (e : SExpr)
    (toks : List Token) : Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "." :: rest => match nimmName rest with
      | .error e => .error e
      | .ok (n, r) => parseSchrittPlatzNach f (.field e n) r
    | .zeichen "[" :: rest => match parseOr f rest with
      | .error e => .error e
      | .ok (i, r1) => match fordereZeichen "]" r1 with
        | .error e => .error e
        | .ok r => parseSchrittPlatzNach f (.index e i) r
    | _ => .ok (e, toks)

/-- A transition place: SYNTAX.md `shiftplace` (`ident` with `.`
    and `[…]` suffixes) -- a general `parseOr` would eat the
    `->` as an arrow field. -/
def parseSchrittPlatz (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r) => parseSchrittPlatzNach f (.variable n) r

/-- Tokens until the top-level `->` (parens, brackets and braces
    tracked): the `from` side of a step rides before it. A bare
    `parseOr` would eat `a -> b` as an arrow field. -/
def nimmBisPfeil : List Token → Nat → Nat → Nat →
    Except String (List Token × List Token)
  | [], _, _, _ => .error "-> expected"
  | (.zeichen s :: rest), pr, pk, pg =>
    if strEq s "->" && pr == 0 && pk == 0 && pg == 0 then
      .ok ([], rest)
    else if strEq s "(" then match nimmBisPfeil rest (pr + 1) pk pg with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
    else if strEq s ")" then
      if pr == 0 then .error "-> expected"
      else match nimmBisPfeil rest (pr - 1) pk pg with
        | .ok (h, r) => .ok (.zeichen s :: h, r)
        | .error e => .error e
    else if strEq s "[" then match nimmBisPfeil rest pr (pk + 1) pg with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
    else if strEq s "]" then
      if pk == 0 then .error "-> expected"
      else match nimmBisPfeil rest pr (pk - 1) pg with
        | .ok (h, r) => .ok (.zeichen s :: h, r)
        | .error e => .error e
    else if strEq s "{" then match nimmBisPfeil rest pr pk (pg + 1) with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
    else if strEq s "}" then
      if pg == 0 then .error "-> expected"
      else match nimmBisPfeil rest pr pk (pg - 1) with
        | .ok (h, r) => .ok (.zeichen s :: h, r)
        | .error e => .error e
    else match nimmBisPfeil rest pr pk pg with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
  | (t :: rest), pr, pk, pg => match nimmBisPfeil rest pr pk pg with
    | .ok (h, r) => .ok (t :: h, r)
    | .error e => .error e

def parseSchritte (f : Nat) (toks : List Token) :
    Except String (List (SExpr × SExpr × SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseSchrittPlatz f toks with
    | .error e => .error e
    | .ok (p, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match nimmBisPfeil r2 0 0 0 with
        | .error e => .error e
        | .ok (ft, r3) => match parseOr f ft with
          | .error e => .error e
          | .ok (a, []) => match parseOr f r3 with
            | .error e => .error e
            | .ok (b, r5) => match r5 with
              | .zeichen "," :: r6 => match parseSchritte f r6 with
                | .error e => .error e
                | .ok (ss, r) => .ok ((p, a, b) :: ss, r)
              | _ => .ok ([(p, a, b)], r5)
          | .ok (_, _ :: _) => .error "-> expected"

/-- One transition: `transition n { p : a -> b, … }
    [requires p] [effects {…}]`. -/
def parseTrans (f : Nat) (toks : List Token) :
    Except String (STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "transition" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseSchritte f r3 with
          | .error e => .error e
          | .ok (ss, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r5 => match parseTransRest f
                ({ tname := n, schritte := ss, voraus := none,
                   wirkung := [] } : STrans) r5 with
              | .error e => .error e
              | .ok (tr, r) => .ok (tr, r)

/-- The predicate and terminator of an invariant. -/
def parseInvRest (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen ":" toks with
    | .error e => .error e
    | .ok r1 => match parsePred f r1 with
      | .error e => .error e
      | .ok (p, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (p, r)

/-- One invariant: `invariant n : p ;`. -/
def parseGruppenInv (f : Nat) (toks : List Token) :
    Except String (SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "invariant" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseInvRest f r2 with
        | .error e => .error e
        | .ok (p, r) => .ok ({
            name := n
            pred := p }, r)

/-- A `{` … `}` place list (`protects`, `measures`, `reclaims`
    tails; trailing commas allowed). -/
def parsePlatzListe (f : Nat) (toks : List Token) :
    Except String (List SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parsePredListe f r with
        | .error e => .error e
        | .ok (ps, r1) => match r1 with
          | .zeichen "," :: r2 => match fordereZeichen "}" r2 with
            | .ok r' => .ok (ps, r')
            | .error _ => .error "} expected"
          | _ => match fordereZeichen "}" r1 with
            | .error e => .error e
            | .ok r' => .ok (ps, r')

def parseRegBind : List Token → Except String (SRegBind × List Token)
  | toks => match nimmName toks with
    | .error e => .error e
    | .ok (a, r) => match r with
      | .zeichen s :: r' =>
        if strEq s "=" || strEq s ":" then match nimmName r' with
          | .error e => .error e
          | .ok (b, r'') => .ok (.binds a b, r'')
        else .ok (.reg a, r)
      | _ => .ok (.reg a, r)
