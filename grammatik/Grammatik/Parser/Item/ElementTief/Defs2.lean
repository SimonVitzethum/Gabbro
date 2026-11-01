module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- One register bit field: `name @bitpos [class c]`. -/
def parseRegFeld (f : Nat) (toks : List Token) :
    Except String (SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | _f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen "@" r1 with
      | .error e => .error e
      | .ok r2 => match parseBitpos r2 with
        | .error e => .error e
        | .ok (b, r3) => match r3 with
          | .wort s :: r4 =>
            if strEq s "class" then match nimmName r4 with
              | .error e => .error e
              | .ok (c, r) => .ok ({ name := n, pos := b, klasse := some c }, r)
            else .ok ({ name := n, pos := b, klasse := none }, r3)
          | _ => .ok ({ name := n, pos := b, klasse := none }, r3)

/-- Register fields after the opening `{`. -/
def parseRegFeldFolge (f : Nat) (toks : List Token) :
    Except String (List SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseRegFeld f toks with
    | .error e => .error e
    | .ok (fd, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([fd], r3)
        | _ => match parseRegFeldFolge f r2 with
          | .error e => .error e
          | .ok (fds, r') => .ok (fd :: fds, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([fd], r')

def parseRegFeldListe (f : Nat) (toks : List Token) :
    Except String (List SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseRegFeldFolge f r with
        | .error e => .error e
        | .ok (fds, r') => .ok (fds, r')

def parsePhasenRest (f : Nat) : List Token →
    Except String (List String × List Token)
  | [] => .ok ([], [])
  | toks => match f with
    | 0 => .error "out of fuel"
    | f + 1 => match toks with
      | .zeichen "," :: rest => match nimmName rest with
        | .error e => .error e
        | .ok (k, r1) => match nimmWort "in" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (st, r3) => match parsePhasenRest f r3 with
              | .error e => .error e
              | .ok (ws, r) => .ok ("," :: k :: "in" :: st :: ws, r)
      | _ => .ok ([], toks)

/- The `in`-stage tail behind a register class. -/
def parsePhasen (f : Nat) : List Token →
    Except String (List String × List Token)
  | [] => .ok ([], [])
  | toks => match f with
    | 0 => .error "out of fuel"
    | f + 1 => match toks with
      | .wort s :: rest =>
        if strEq s "in" then match nimmName rest with
          | .error e => .error e
          | .ok (st, r) => match parsePhasenRest f r with
            | .error e => .error e
            | .ok (ws, r') => .ok ("in" :: st :: ws, r')
        else .ok ([], toks)
      | _ => .ok ([], toks)

def parseTraeger : List Token → Except String (List String × List Token)
  | toks => match nimmName toks with
    | .error e => .error e
    | .ok (a, r) => match r with
      | .zeichen "." :: r' => match nimmName r' with
        | .error e => .error e
        | .ok (b, r'') => .ok ([a, b], r'')
      | _ => .ok ([a], r)

/-- Carriers after the opening `{`. -/
def parseTraegerFolge (f : Nat) (toks : List Token) :
    Except String (List (List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseTraeger toks with
    | .error e => .error e
    | .ok (c, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([c], r3)
        | _ => match parseTraegerFolge f r2 with
          | .error e => .error e
          | .ok (cs, r') => .ok (c :: cs, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([c], r')

/-- A `depends`/carrier list: `{` … `}` of one- or two-segment
    names (trailing commas allowed). -/
def parseTraegerListe (f : Nat) (toks : List Token) :
    Except String (List (List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseTraegerFolge f r with
        | .error e => .error e
        | .ok (cs, r') => .ok (cs, r')

def parseRegRest (f : Nat) (rg : SReg) (toks : List Token) :
    Except String (SReg × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match parseOr f rest with
      | .error e => .error e
      | .ok (e, r) => parseRegRest f { rg with addr := e } r
    | .wort s :: rest =>
      if strEq s "class" then match nimmName rest with
        | .error e => .error e
        | .ok (c, r1) => match parsePhasen f r1 with
          | .error e => .error e
          | .ok (ph, r) =>
            parseRegRest f { rg with klasse := c, stage := ph } r
      else if strEq s "fields" then match parseRegFeldListe f rest with
        | .error e => .error e
        | .ok (fds, r) => parseRegRest f { rg with felder := fds } r
      else if strEq s "requires" then match parsePred f rest with
        | .error e => .error e
        | .ok (p, r1) => match r1 with
          | .wort t :: r2 =>
            if strEq t "else" then match nimmPfad r2 with
              | .error e => .error e
              | .ok ([a, b], r) => parseRegRest f
                { rg with voraus := some p,
                          elseF := some (a, b) } r
              | .ok _ => .error "else expected"
            else parseRegRest f { rg with voraus := some p } r1
          | _ => parseRegRest f { rg with voraus := some p } r1
      else if strEq s "depends" then match parseTraegerListe f rest with
        | .error e => .error e
        | .ok (cs, r) => parseRegRest f { rg with abhaengt := cs } r
      else .ok (rg, toks)
    | _ => .ok (rg, toks)

/-- One device register: `reg n : T [@ e] class c [phases]
    [fields {…}] [requires p [else A::B]] [depends {…}] ;`. -/
def parseReg (f : Nat) (toks : List Token) :
    Except String (SReg × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "reg" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen ":" r2 with
        | .error e => .error e
        | .ok r3 => match parseTyp f r3 with
          | .error e => .error e
          | .ok (t, r4) => match parseRegRest f
              ({ name := n, rtyp := t,
                 addr := .variable "", klasse := "", stage := [],
                 felder := [], voraus := none, elseF := none,
                 abhaengt := [] } : SReg) r4 with
            | .error e => .error e
            | .ok (rg, r) => .ok (rg, r)

/-- An `effects {…}` group behind `transition` (the `fndecl`
    clause reader covers the signature site). -/
def parseEffektBlock (f : Nat) (toks : List Token) :
    Except String (List SEffekt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r1 => match r1 with
      | .zeichen "}" :: r2 => .ok ([], r2)
      | _ => match parseEffektListe f r1 with
        | .error e => .error e
        | .ok (es, r2) => match fordereZeichen "}" r2 with
          | .error e => .error e
          | .ok r => .ok (es, r)

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

/-- The `O` of `cost O(e)`: a name in both lexers (`kw.rs`
    has no `O` keyword either), so either token shape reads. -/
def nimmKostenO : List Token → Except String (List Token)
  | t :: rest => match nameText t with
    | some s => if strEq s "O" then .ok rest else .error "cost O expected"
    | none => .error "cost O expected"
  | [] => .error "cost O expected"

def parseInvRest (f : Nat) (toks : List Token) :
    Except String ((Option String × SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "by" then match nimmBisZeichen ":" rest 0 with
        | .error e => .error e
        | .ok (h, r1) => match fordereZeichen ":" r1 with
          | .error e => .error e
          | .ok r2 => match parsePred f r2 with
            | .error e => .error e
            | .ok (p, r3) => match fordereZeichen ";" r3 with
              | .error e => .error e
              | .ok r => .ok (((some h, p)), r)
      else match fordereZeichen ":" toks with
        | .error e => .error e
        | .ok r1 => match parsePred f r1 with
          | .error e => .error e
          | .ok (p, r2) => match fordereZeichen ";" r2 with
            | .error e => .error e
            | .ok r => .ok (((none, p)), r)
    | _ => match fordereZeichen ":" toks with
      | .error e => .error e
      | .ok r1 => match parsePred f r1 with
        | .error e => .error e
        | .ok (p, r2) => match fordereZeichen ";" r2 with
          | .error e => .error e
          | .ok r => .ok (((none, p)), r)

/-- One invariant: `invariant n cost O(e) runs m [by …] : p ;`. -/
def parseGruppenInv (f : Nat) (toks : List Token) :
    Except String (SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "invariant" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "cost" r2 with
        | .error e => .error e
        | .ok r3 => match nimmKostenO r3 with
          | .error e => .error e
          | .ok r4 => match fordereZeichen "(" r4 with
            | .error e => .error e
            | .ok r5 => match parseOr f r5 with
              | .error e => .error e
              | .ok (c, r6) => match fordereZeichen ")" r6 with
                | .error e => .error e
                | .ok r7 => match nimmWort "runs" r7 with
                  | .error e => .error e
                  | .ok r8 => match r8 with
                    | .wort m :: r9 =>
                      if strEq m "online" || strEq m "offline" then
                        match parseInvRest f r9 with
                        | .error e => .error e
                        | .ok ((proof, p), r) => .ok
                          ({ name := n, kosten := c,
                             online := strEq m "online", proof := proof,
                             pred := p }, r)
                      else .error "runs expected"
                    | _ => .error "runs expected"

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
