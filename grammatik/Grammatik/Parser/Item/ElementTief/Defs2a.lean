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


end Gabbro.Grammatik.Parser
