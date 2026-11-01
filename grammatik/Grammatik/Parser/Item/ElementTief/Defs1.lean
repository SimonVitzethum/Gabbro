module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Kopf

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- One effect arm of `uses`. -/
def parseEffekt (f : Nat) (toks : List Token) :
    Except String (SEffekt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "reads" then match parseOr f rest with
        | .ok (p, r) => .ok (.reads p, r)
        | .error e => .error e
      else if strEq s "writes" then match parseOr f rest with
        | .ok (p, r) => .ok (.writes p, r)
        | .error e => .error e
      else if strEq s "locks" then match rest with
        | .wort t :: rest' =>
          if strEq t "shared" then match parseOr f rest' with
            | .ok (p, r) => .ok (.locks true p, r)
            | .error e => .error e
          else match parseOr f rest with
            | .ok (p, r) => .ok (.locks false p, r)
            | .error e => .error e
        | _ => match parseOr f rest with
          | .ok (p, r) => .ok (.locks false p, r)
          | .error e => .error e
      else if strEq s "masks" then match nimmName rest with
        | .ok (n, r) => .ok (.masks n, r)
        | .error e => .error e
      else if strEq s "allocs" then match nimmName rest with
        | .ok (n, r) => .ok (.allocs n, r)
        | .error e => .error e
      else if strEq s "consumes" then match parseOr f rest with
        | .ok (p, r) => .ok (.takes p, r)
        | .error e => .error e
      else if strEq s "publishes" then match parseOr f rest with
        | .ok (p, r) => .ok (.posts p, r)
        | .error e => .error e
      else if strEq s "diverges" then .ok (.loops, rest)
      else if strEq s "pure" then .ok (.pure, rest)
      else .error "effect expected"
    | _ => .error "effect expected"

/-- The comma-separated tail of an effect or predicate list
    (trailing commas allowed -- see CUTS). -/
def parseEffektListe (f : Nat) (toks : List Token) :
    Except String (List SEffekt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseEffekt f toks with
    | .error e => .error e
    | .ok (e, rest) => match rest with
      | .zeichen "," :: rest' =>
        if istZeichenZ "}" rest' then .ok ([e], rest')
        else match parseEffektListe f rest' with
          | .error e2 => .error e2
          | .ok (es, r) => .ok (e :: es, r)
      | _ => .ok ([e], rest)

def parsePredListe (f : Nat) (toks : List Token) :
    Except String (List SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parsePred f toks with
    | .error e => .error e
    | .ok (p, rest) => match rest with
      | .zeichen "," :: rest' =>
        match parsePred f rest' with
        | .ok _ =>
          match parsePredListe f rest' with
          | .error e2 => .error e2
          | .ok (ps, r) => .ok (p :: ps, r)
        | .error _ => .ok ([p], rest')
      | _ => .ok ([p], rest)

/-- One `fndecl` clause; `requires`/`ensures` yield one
    `SKlausel` per predicate. -/
def parseKlausel (f : Nat) (toks : List Token) :
    Except String (List SKlausel × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "requires" then match parsePredListe f rest with
        | .ok (ps, r) => .ok (ps.map .needs, r)
        | .error e => .error e
      else if strEq s "ensures" then match parsePredListe f rest with
        | .ok (ps, r) => .ok (ps.map .gives, r)
        | .error e => .error e
      else if strEq s "maintains" then match parseNamenListe f rest with
        | .ok (ns, r) => .ok ([.keeps ns], r)
        | .error e => .error e
      else if strEq s "refines" then match nimmPfad rest with
        | .ok (p, r) => .ok ([.refs p], r)
        | .error e => .error e
      else if strEq s "effects" then match fordereZeichen "{" rest with
        | .error e => .error e
        | .ok r1 => match r1 with
          | .zeichen "}" :: r2 => .ok ([.effs []], r2)
          | _ => match parseEffektListe f r1 with
            | .error e => .error e
            | .ok (es, r2) => match fordereZeichen "}" r2 with
              | .error e => .error e
              | .ok r => .ok ([.effs es], r)
      else if strEq s "costs" then match fordereZeichen "<=" rest with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (e, r2) => match nimmWort "ops" r2 with
            | .error e2 => .error e2
            | .ok r => .ok ([.cost e], r)
      else if strEq s "deadline" then match fordereZeichen "<=" rest with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (e, r2) => match nimmWort "ops" r2 with
            | .error e2 => .error e2
            | .ok r3 => match nimmWort "arch" r3 with
              | .error e3 => .error e3
              | .ok r4 => match nimmName r4 with
                | .error e4 => .error e4
                | .ok (a, r5) => match parseKlasse r5 with
                  | .error e5 => .error e5
                  | .ok (k, r) => match k with
                    | .probe n => .ok ([.limit
                      ("deadline <= " ++ druck e ++ " ops arch " ++ a ++
                       " falsifier " ++ n)], r)
                    | .trust t => .ok ([.limit
                      ("deadline <= " ++ druck e ++ " ops arch " ++ a ++
                       " unfalsifiable \"" ++ t ++ "\"")], r)
      else if strEq s "decreases" then match parseOr f rest with
        | .ok (e, r) => .ok ([.drops e], r)
        | .error e => .error e
      else if strEq s "by" then match nimmBisKopf rest with
        | .ok (h, r) => .ok ([.induc h], r)
        | .error e => .error e
      else if strEq s "section" then match nimmTextTok rest with
        | .ok (t, r) => .ok ([.part t], r)
        | .error e => .error e
      else if strEq s "arch" then match nimmName rest with
        | .ok (n, r) => .ok ([.arch n], r)
        | .error e => .error e
      else if strEq s "payload" then match nimmPfad rest with
        | .ok (p, r) => .ok ([.load p], r)
        | .error e => .error e
      else if strEq s "advances" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r1) => match fordereZeichen "->" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (b, r) => .ok ([.moves a b], r)
      else if strEq s "retires" then match nimmName rest with
        | .error e => .error e
        | .ok (m, r1) => match nimmWort "from" r1 with
          | .error e2 => .error e2
          | .ok r2 => match nimmName r2 with
            | .error e3 => .error e3
            | .ok (sp, r3) => match parseKlasse r3 with
              | .error e4 => .error e4
              | .ok (k, r) => match k with
                | .probe n => .ok ([.quits
                  (m ++ " from " ++ sp ++ " falsifier " ++ n)], r)
                | .trust t => .ok ([.quits
                  (m ++ " from " ++ sp ++ " unfalsifiable \"" ++ t ++ "\"")], r)
      else .error "clause expected"
    | _ => .error "clause expected"

/-- Every clause in source order, until the body (`{`, `;`,
    `=`) or the end. -/
def parseKlauseln (f : Nat) (toks : List Token) :
    Except String (List SKlausel × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if istKlauselKopf s then match parseKlausel f toks with
        | .error e => .error e
        | .ok (ks, rest) => match parseKlauseln f rest with
          | .error e => .error e
          | .ok (ks', r) => .ok (ks ++ ks', r)
      else .ok ([], toks)
    | _ => .ok ([], toks)

def parseParamListe (f : Nat) (toks : List Token) :
    Except String (List (String × STyp) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseTyp f r2 with
        | .error e => .error e
        | .ok (t, r3) => match r3 with
          -- The variadic marker `...` (lexed `..` `.`; C-free lane, C2): a fact about the
          -- foreign C prototype only -- every parameter behind it is declared and passed, so
          -- the parsed list keeps them all and the marker itself carries nothing into `D`.
          | .zeichen "," :: .zeichen ".." :: .zeichen "." :: .zeichen ")" :: r4 =>
            .ok ([(n, t)], .zeichen ")" :: r4)
          | .zeichen "," :: .zeichen ".." :: .zeichen "." :: .zeichen "," :: r4 =>
            match parseParamListe f r4 with
            | .error e => .error e
            | .ok (ps, r) => .ok ((n, t) :: ps, r)
          | .zeichen "," :: r4 => match parseParamListe f r4 with
            | .error e => .error e
            | .ok (ps, r) => .ok ((n, t) :: ps, r)
          | _ => .ok ([(n, t)], r3)

/-- The parameter list `(` … `)` of `fndecl` (shared with
    `device` and `axiom`). -/
def parseParams (f : Nat) (toks : List Token) :
    Except String (List (String × STyp) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "(" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen ")" :: r' => .ok ([], r')
      | _ => match parseParamListe f r with
        | .error e => .error e
        | .ok (ps, r') => match fordereZeichen ")" r' with
          | .error e => .error e
          | .ok r'' => .ok (ps, r'')

def parseFehler : List Token → Except String (Option String × List Token)
  | .wort s :: rest =>
    if strEq s "or" then match nimmName rest with
      | .ok (n, r) => .ok (some n, r)
      | .error e => .error e
    else .ok (none, .wort s :: rest)
  | toks => .ok (none, toks)

/-- The optional `-> T` result and `or R` channel behind a
    signature. -/
def parseErgebnis (f : Nat) (toks : List Token) :
    Except String (Option STyp × Option String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "->" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r) => match parseFehler r with
        | .ok (o, r') => .ok (some t, o, r')
        | .error e => .error e
    | _ => match parseFehler toks with
      | .ok (o, r) => .ok (none, o, r)
      | .error e => .error e

/-- A function head: `fn name(params) [-> T] [or R] clauses`
    (`art` rode in front). -/
def parseFnSig (f : Nat) (art : String) (toks : List Token) :
    Except String (FnSig × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "fn" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (name, r2) => match parseParams f r2 with
        | .error e => .error e
        | .ok (ps, r3) => match parseErgebnis f r3 with
          | .error e => .error e
          | .ok (erg, fehler, r4) => match parseKlauseln f r4 with
            | .error e => .error e
            | .ok (ks, r) =>
              .ok ({ art, name, params := ps, res := erg,
                     fehler, klauseln := ks }, r)

/-- Behind the head: a block body (`fnT`), `;`
    (`protoT`), `= pred ;` (`specT`) or `= asm {…} ;` (`asmT`). -/
def parseFnRest (f : Nat) (sig : FnSig) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "{" :: _ => match parseBlock f toks with
      | .error e => .error e
      | .ok (b, r) => .ok (.fnT sig b, r)
    | .zeichen ";" :: rest => .ok (.protoT sig, rest)
    | .zeichen "=" :: rest => match rest with
      | .wort s :: rest' =>
        if strEq s "asm" then match fordereZeichen "{" rest' with
          | .error e => .error e
          | .ok r1 => match nimmBereichWorte r1 1 with
            | .error e => .error e
            | .ok (h, r2) => match fordereZeichen ";" r2 with
              | .error e => .error e
              | .ok r => .ok (.asmT sig ("asm { " ++ h), r)
        else match parsePred f rest with
          | .error e => .error e
          | .ok (p, r1) => match fordereZeichen ";" r1 with
            | .error e => .error e
            | .ok r => .ok (.specT sig p, r)
      | _ => match parseOr f rest with
        | .error e => .error e
        | .ok (p, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r => .ok (.specT sig p, r)
    | _ => .error "fn without body"

/-- A raw `@bitpos`: one number or a `[hi:lo]` group. -/
def parseBitpos : List Token → Except String (String × List Token)
  | .zeichen "[" :: rest => match sammleAusgewogen rest 0 1 0 with
    | .error e => .error e
    | .ok (h, r) => .ok ("[ " ++ h, r)
  | t :: rest => match nameText t with
    | some _ => .ok (zeigeTok t, rest)
    | none => match t with
      | .num _ => .ok (zeigeTok t, rest)
      | _ => .error "bitpos expected"
  | [] => .error "bitpos expected"

def parseFeldRest (f : Nat) : List Token → Except String
    ((Option String × Option String × Option SExpr × Bool × Bool) × List Token)
  | toks => match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match parseBitpos rest with
      | .error e => .error e
      | .ok (b, r) => match parseFeldRest f r with
        | .error e => .error e
        | .ok ((_, bezug, wo, res, byo), r') =>
          .ok (((some b, bezug, wo, res, byo)), r')
    | .wort s :: rest =>
      if strEq s "offset_into" then match rest with
        | t :: r =>
          if strEq (zeigeTok t) "Self" then match parseFeldRest f r with
            | .error e => .error e
            | .ok ((pos, _, wo, res, byo), r') =>
              .ok (((pos, some "Self", wo, res, byo)), r')
          else match nameText t with
            | some n => match parseFeldRest f r with
              | .error e => .error e
              | .ok ((pos, _, wo, res, byo), r') =>
                .ok (((pos, some n, wo, res, byo)), r')
            | none => .error "offset_into expected"
        | _ => .error "offset_into expected"
      else if strEq s "where" then match parsePred f rest with
        | .ok (p, r) => match parseFeldRest f r with
          | .error e => .error e
          | .ok ((pos, bezug, _, res, byo), r') =>
            .ok (((pos, bezug, some p, res, byo)), r')
        | .error e => .error e
      else if strEq s "reserved" then match parseFeldRest f rest with
        | .error e => .error e
        | .ok ((pos, bezug, wo, _, byo), r) =>
          .ok (((pos, bezug, wo, true, byo)), r)
      else if strEq s "by" then match rest with
        | .wort t :: r =>
          if strEq t "ops" then match parseFeldRest f r with
            | .error e => .error e
            | .ok ((pos, bezug, wo, res, _), r') =>
              .ok (((pos, bezug, wo, res, true)), r')
          else .error "by ops expected"
        | _ => .error "by ops expected"
      else .ok (((none, none, none, false, false)), toks)
    | _ => .ok (((none, none, none, false, false)), toks)

/-- One slot/format field: `name : type [@bitpos]
    [offset_into t] [where p] [reserved] [by ops]`. -/
def parseFeld (f : Nat) (toks : List Token) :
    Except String (SFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseTyp f r2 with
        | .error e => .error e
        | .ok (t, r3) => match parseFeldRest f r3 with
          | .error e => .error e
          | .ok ((pos, bezug, wo, res, byo), r) =>
            .ok ({ fname := n, ftyp := t, pos, bezug := bezug, wo,
                   reserviert := res, byOps := byo }, r)

/-- Fields after the opening `{` (the opener is consumed). -/
def parseFeldFolge (f : Nat) (toks : List Token) :
    Except String (List SFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseFeld f toks with
    | .error e => .error e
    | .ok (fd, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([fd], r3)
        | _ => match parseFeldFolge f r2 with
          | .error e => .error e
          | .ok (fds, r') => .ok (fd :: fds, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([fd], r')

/-- A `{` … `}` field list (slots and formats share the shape). -/
def parseFeldListe (f : Nat) (toks : List Token) :
    Except String (List SFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseFeldFolge f r with
        | .error e => .error e
        | .ok (fds, r') => .ok (fds, r')
