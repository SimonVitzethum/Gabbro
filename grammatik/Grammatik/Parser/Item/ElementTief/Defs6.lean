module

public import Grammatik.Parser.Item.ElementTief.Defs6a
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs5

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- `profile {…} ;` / `requires profile {…} ;` (section 12.2). -/
def parseProfilTief (f : Nat) (bedarf : Bool) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r1 => match parseProfEintraege f r1 with
      | .error e => .error e
      | .ok (es, r2) => match fordereZeichen "}" r2 with
        | .error e => .error e
        | .ok r3 => match fordereZeichen ";" r3 with
          | .error e => .error e
          | .ok r => .ok (.profT bedarf es, r)

/-- A `bank` member: the header rides raw up to `{`, the body
    balanced (registers inside are not split -- see CUTS). -/
def parseBank : List Token → Except String (String × List Token)
  | toks => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match nimmWort "at" r1 with
      | .error e => .error e
      | .ok r2 => match parseOr 50 r2 with
        | .error e => .error e
        | .ok (a, r3) => match nimmWort "stride" r3 with
          | .error e => .error e
          | .ok r4 => match parseOr 50 r4 with
            | .error e => .error e
            | .ok (s, r5) => match nimmWort "count" r5 with
              | .error e => .error e
              | .ok r6 => match parseOr 50 r6 with
                | .error e => .error e
                | .ok (c, r7) => match fordereZeichen "{" r7 with
                  | .error e => .error e
                  | .ok r8 => match nimmBereichWorte r8 1 with
                    | .error e => .error e
                    | .ok (h, r) => .ok
                      ("bank " ++ n ++ " at " ++ druck a ++
                       " stride " ++ druck s ++ " count " ++ druck c ++
                       " { " ++ h, r)

def parseGerTeile (f : Nat) (toks : List Token) :
    Except String (List SGerTeil × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "mirrors" then match parseOr f rest with
        | .error e => .error e
        | .ok (a, r1) => match nimmWort "from" r1 with
          | .error e => .error e
          | .ok r2 => match parseOr f r2 with
            | .error e => .error e
            | .ok (b, r3) => match fordereZeichen ";" r3 with
              | .error e => .error e
              | .ok r4 => match parseGerTeile f r4 with
                | .error e => .error e
                | .ok (ms, r) => .ok (.copy a b :: ms, r)
      else if strEq s "reg" then match parseReg f toks with
        | .error e => .error e
        | .ok (rg, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.reg rg :: ms, r)
      else if strEq s "bank" then match parseBank rest with
        | .error e => .error e
        | .ok (raw, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.bank raw :: ms, r)
      else if strEq s "transition" then match parseTrans f toks with
        | .error e => .error e
        | .ok (tr, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.trans tr :: ms, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)

def parseGeraetNach (f : Nat) (n : String) (ps : List (String × STyp))
    (toks : List Token) : Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "at" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (sp, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseGerTeile f r3 with
          | .error e => .error e
          | .ok (ms, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r => .ok (.devT n ps sp ms, r)

/-- `device n [(params)] at space { mirrors | reg | bank |
    transition }`. -/
def parseGeraetTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "device" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match r2 with
        | .zeichen "(" :: _ => match parseParams f r2 with
          | .error e => .error e
          | .ok (ps, r3) => match parseGeraetNach f n ps r3 with
            | .error e => .error e
            | .ok (it, r) => .ok (it, r)
        | _ => match parseGeraetNach f n [] r2 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)

def parseTypOrdnung (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "order" then match fordereZeichen "{" rest with
        | .error e => .error e
        | .ok r1 => match parseNamenListe f r1 with
          | .error e => .error e
          | .ok (ns, r2) => match r2 with
            | .zeichen "," :: r3 => match fordereZeichen "}" r3 with
              | .error e => .error e
              | .ok r => .ok (ns, r)
            | _ => match fordereZeichen "}" r2 with
              | .error e => .error e
              | .ok r => .ok (ns, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)

def parseTypArgListe (f : Nat) (toks : List Token) :
    Except String (List STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseTyp f toks with
    | .error e => .error e
    | .ok (t, r1) => match r1 with
      | .zeichen "," :: r2 => match parseTypArgListe f r2 with
        | .error e => .error e
        | .ok (ts, r) => .ok (t :: ts, r)
      | _ => .ok ([t], r1)

def parseTypArgs (f : Nat) (toks : List Token) :
    Except String (List STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "(" :: rest => match rest with
      | .zeichen ")" :: r => .ok ([], r)
      | _ => match parseTypArgListe f rest with
        | .error e => .error e
        | .ok (ts, r1) => match fordereZeichen ")" r1 with
          | .error e => .error e
          | .ok r => .ok (ts, r)
    | _ => .ok ([], toks)

/-- `[flags] type n [(args)] [order {…}] [= T] ;`. -/
def parseTypTief (f : Nat) (flags : List String) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "type" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseTypArgs f r2 with
        | .error e => .error e
        | .ok (args, r3) => match parseTypOrdnung f r3 with
          | .error e => .error e
          | .ok (ord, r4) => match r4 with
            | .zeichen "=" :: r5 => match parseTyp f r5 with
              | .error e => .error e
              | .ok (t, r6) => match fordereZeichen ";" r6 with
                | .error e => .error e
                | .ok r => .ok (.typeT flags n args ord (some t), r)
            | _ => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.typeT flags n args ord none, r)

def parseTransListe (f : Nat) (toks : List Token) :
    Except String (List STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if strEq s "transition" then match parseTrans f toks with
        | .error e => .error e
        | .ok (tr, r1) => match parseTransListe f r1 with
          | .error e => .error e
          | .ok (ts, r) => .ok (tr :: ts, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)

/-- `state n { transitions }`. -/
def parseZustandTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "state" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseTransListe f r3 with
          | .error e => .error e
          | .ok (ts, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r => .ok (.stateT n ts, r)
