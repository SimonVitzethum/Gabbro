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
      else if strEq s "borrows" then match nimmName rest with
        | .ok (n, r) => .ok (.borrows n, r)
        | .error e => .error e
      else if strEq s "publishes" then match parseOr f rest with
        | .ok (p, r) => .ok (.posts p, r)
        | .error e => .error e
      else if strEq s "diverges" then .ok (.loops, rest)
      else if strEq s "pure" then .ok (.pure, rest)
      else .error "effect expected"
    | .ident n :: .zeichen "[" :: rest => do
      let (ts, r) ← parseSpecTypes f rest
      let r ← fordereZeichen "]" r
      return (.instanceEffects n ts, r)
    | .ident n :: rest => .ok (.param n, rest)
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


end Gabbro.Grammatik.Parser
