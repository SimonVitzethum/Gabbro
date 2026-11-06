module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs5

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- `atomic n : T [publishes …] [order] [observed by a] ;`. -/
def parseAtomarTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "atomic" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen ":" r2 with
        | .error e => .error e
        | .ok r3 => match parseTyp f r3 with
          | .error e => .error e
          | .ok (t, r4) => match parseAtomarRest f
              (n, t, none, none, none) r4 with
            | .error e => .error e
            | .ok ((a, b, c, d, e), r) => .ok
              (.atomT a b c d e, r)

def parseKante : List Token → Except String ((String × String) × List Token)
  | .wort s :: rest =>
    if strEq s "parent" || strEq s "child" || strEq s "sibling" then
      match nimmName rest with
      | .error e => .error e
      | .ok (n, r) => .ok (((s, n)), r)
    else .error "edge expected"
  | _ => .error "edge expected"

def parseKanten (f : Nat) (toks : List Token) :
    Except String (List (String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseKante toks with
    | .error e => .error e
    | .ok (k, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: _ => .ok ([k], r2)
        | _ => match parseKanten f r2 with
          | .error e => .error e
          | .ok (ks, r) => .ok (k :: ks, r)
      | _ => .ok ([k], r1)

/-- `tree { parent a, child b, … }`. -/
def parseBaum (f : Nat) (toks : List Token) :
    Except String (List (String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match parseKanten f r with
      | .error e => .error e
      | .ok (ks, r1) => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok (ks, r')

/-- `const n : T = v ;` (behind the `const`). -/
def parseKonstNach (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseTyp f r2 with
        | .error e => .error e
        | .ok (t, r3) => match fordereZeichen "=" r3 with
          | .error e => .error e
          | .ok r4 => match parseKonstWert f r4 with
            | .error e => .error e
            | .ok (v, r5) => match fordereZeichen ";" r5 with
              | .error e => .error e
              | .ok r => .ok (.constT n t v, r)

def parseTabTeile (f : Nat) (toks : List Token) :
    Except String (List STabTeil × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "const" then match parseKonstNach f rest with
        | .error e => .error e
        | .ok (.constT n t v, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tConst n t v :: ps, r)
        | .ok _ => .error "const expected"
      else if strEq s "slot" then match parseFeldListe f rest with
        | .error e => .error e
        | .ok (fds, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tSlot fds :: ps, r)
      else if strEq s "invariant" then match parseGruppenInv f toks with
        | .error e => .error e
        | .ok (iv, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tInv iv :: ps, r)
      else if strEq s "ops" then match parseNamenListe f rest with
        | .error e => .error e
        | .ok (ns, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseTabTeile f r2 with
            | .error e => .error e
            | .ok (ps, r) => .ok (.tOps ns :: ps, r)
      else if strEq s "tree" then match parseBaum f rest with
        | .error e => .error e
        | .ok (ks, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tTree ks :: ps, r)
      else if strEq s "occupied" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseTabTeile f r2 with
            | .error e => .error e
            | .ok (ps, r) => .ok (.tBusy n :: ps, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)

def parseTabellenKopf (f : Nat) (toks : List Token) :
    Except String
      ((Option SExpr × Option String × Option String × Option String × Bool × Option String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "count" then match parseOr f rest with
        | .error e => .error e
        | .ok (e, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((_, v, b, o, g, space)), r) => .ok ((((some e, v, b, o, g, space))), r)
      else if strEq s "from" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((c, _, b, o, g, space)), r) => .ok ((((c, some n, b, o, g, space))), r)
      else if strEq s "backed" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((c, v, _, o, g, space)), r) => .ok ((((c, v, some n, o, g, space))), r)
      else if strEq s "owner" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((c, v, b, _, g, space)), r) => .ok ((((c, v, b, some n, g, space))), r)
      else if strEq s "space" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok ((c, v, b, o, g, none), r) => .ok ((c, v, b, o, g, some n), r)
          | .ok ((_, _, _, _, _, some _), _) => .error "duplicate table space binding"
      else if strEq s "shared" then match parseTabellenKopf f rest with
        | .error e => .error e
        | .ok (((c, v, b, o, _, space)), r) => .ok ((((c, v, b, o, true, space))), r)
      else .ok ((((none, none, none, none, false, none))), toks)
    | _ => .ok ((((none, none, none, none, false, none))), toks)

/-- `table n [count e] [from p] [backed b] [owner o] [space s] [shared] { parts }`; `from p` names the provider of an OPEN
    table (`Deklaration.anbieter`). -/
def parseTabellenTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "table" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseTabellenKopf f r2 with
        | .error e => .error e
        | .ok (((cnt, von, backed, owner, g, space)), r3) =>
          match fordereZeichen "{" r3 with
          | .error e => .error e
          | .ok r4 => match parseTabTeile f r4 with
            | .error e => .error e
            | .ok (ps, r5) => match fordereZeichen "}" r5 with
              | .error e => .error e
              | .ok r => .ok
                (.tableT n von cnt backed owner g ps space, r)

def parseProfEintraege (f : Nat) (toks : List Token) :
    Except String (List SProfEintrag × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "arch" || strEq s "rounding" ||
          strEq s "fp_contract" || strEq s "memory_model" ||
          strEq s "interrupt_routing" then match nimmName rest with
        | .error e => .error e
        | .ok (v, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseProfEintraege f r2 with
            | .error e => .error e
            | .ok (es, r) => .ok (.mode s v :: es, r)
      else if strEq s "assume" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseProfEintraege f r2 with
            | .error e => .error e
            | .ok (es, r) => .ok (.assum a :: es, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)


end Gabbro.Grammatik.Parser
