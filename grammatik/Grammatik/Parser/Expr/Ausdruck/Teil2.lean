module

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Expr.Ausdruck.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

mutual
def parseOr (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseAnd f toks with
    | .ok (l, rest) => parseOrL f l rest
    | .error e => .error e
def parseOrL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opOder toks with
    | some rest => match parseAnd f rest with
      | .ok (r, rest') => parseOrL f (.bin "||" l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parseAnd (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseCmp f toks with
    | .ok (l, rest) => parseAndL f l rest
    | .error e => .error e
def parseAndL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opUnd toks with
    | some rest => match parseCmp f rest with
      | .ok (r, rest') => parseAndL f (.bin "&&" l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parseCmp (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseBit f toks with
    | .ok (l, rest) => match opVgl rest with
      | some (op, rest') => match parseBit f rest' with
        | .ok (r, rest'') => .ok (.bin op l r, rest'')
        | .error e => .error e
      | none => .ok (l, rest)
    | .error e => .error e
def parseBit (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseAdd f toks with
    | .ok (l, rest) => parseBitL f l rest
    | .error e => .error e
def parseBitL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opBit toks with
    | some (op, rest) => match parseAdd f rest with
      | .ok (r, rest') => parseBitL f (.bin op l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parseAdd (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseMul f toks with
    | .ok (l, rest) => parseAddL f l rest
    | .error e => .error e
def parseAddL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opAdd toks with
    | some (op, rest) => match parseMul f rest with
      | .ok (r, rest') => parseAddL f (.bin op l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parseMul (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseUnary f toks with
    | .ok (l, rest) => parseMulL f l rest
    | .error e => .error e
def parseMulL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opMul toks with
    | some (op, rest) => match parseUnary f rest with
      | .ok (r, rest') => parseMulL f (.bin op l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parseUnary (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "!" :: rest => match parsePrimary f rest with
      | .ok (e, rest') => .ok (.un "!" e, rest')
      | .error e => .error e
    | .zeichen "-" :: .zeichen "(" :: rest => match parsePrimary f (.zeichen "(" :: rest) with
      | .ok (e, rest') => .ok (if istLit e then .un "-()" e else .un "-" e, rest')
      | .error e => .error e
    | .zeichen "-" :: rest => match parsePrimary f rest with
      | .ok (e, rest') => .ok (.un "-" e, rest')
      | .error e => .error e
    | .zeichen "~" :: rest => match parsePrimary f rest with
      | .ok (e, rest') => .ok (.un "~" e, rest')
      | .error e => .error e
    | .zeichen "&" :: t :: rest => match nameText t with
      | some s =>
        let (segs, rest') := sammleSegmente rest [s]
        .ok (.fnref ("::".intercalate segs), rest')
      | none => .error "& expects a path"
    | _ => parsePrimary f toks
def parsePrimary (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .num v :: rest => .ok (.lit v, rest)
    | .text t :: rest => .ok (.ext .text [t] [], rest)
    | .wort "count" :: t :: .wort "in" :: rest => match nameText t with
      | some x => parseQuant f .count x rest
      | none => .error "count without a name"
    | .float s :: rest => match rest with
      | .wort "rounded" :: rest' =>
        .ok (.float (s ++ " rounded"), rest')
      | _ => .ok (.float s, rest)
    | .wort "true" :: rest => .ok (.tru, rest)
    | .wort "false" :: rest => .ok (.fls, rest)
    | .wort "Some" :: .zeichen "(" :: rest =>
      match parseOr f rest with
      | .ok (e, .zeichen ")" :: rest') => .ok (.call "Some" [e], rest')
      | .ok (_, _) => .error "Some without )"
      | .error e => .error e
    | .wort "None" :: rest => .ok (.call "None" [], rest)
    | .wort "Some" :: rest => .ok (.call "Some" [], rest)
    | .wort "result" :: rest => .ok (.res, rest)
    | .wort "old" :: .zeichen "(" :: rest =>
      match parseOrt f rest with
      | .ok (e, .zeichen ")" :: rest') => .ok (.old e, rest')
      | .ok (_, _) => .error "old without )"
      | .error e => .error e
    | .wort "sizeof" :: .zeichen "(" :: rest =>
      parseEingebaut f "sizeof" 1 rest
    | .wort "lenof" :: .zeichen "(" :: rest =>
      parseEingebaut f "lenof" 1 rest
    | .wort "aligned" :: .zeichen "(" :: rest =>
      parseEingebaut f "aligned" 2 rest
    | .zeichen "(" :: rest => match parseOr f rest with
      | .ok (e, .zeichen ")" :: rest') => .ok (e, rest')
      | .ok (_, _) => .error "( without )"
      | .error e => .error e
    | t :: _ => match nameText t with
      | some s =>
        if istKeinPlatz s then .error ("reserved head " ++ s)
        else parseKopf f toks
      | none => .error "expression expected"
    | [] => .error "expression expected"
def parseEingebaut (f : Nat) (w : String) (n : Nat)
    (toks : List Token) : Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 =>
    if n == 1 then match parseOrt f toks with
      | .ok (a, .zeichen ")" :: rest') =>
        match a with
        | .variable s =>
          if istTypWort s then .error (w ++ " over a type")
          else .ok (.built w [a], rest')
        | _ => .ok (.built w [a], rest')
      | .ok (_, _) => .error (w ++ " without )")
      | .error e => .error e
    else match parseOr f toks with
      | .ok (a, .zeichen "," :: rest) => match parseOr f rest with
        | .ok (b, .zeichen ")" :: rest') =>
          .ok (.built w [a, b], rest')
        | .ok (_, _) => .error (w ++ " without )")
        | .error e => .error e
      | .ok (_, _) => .error (w ++ " without ,")
      | .error e => .error e
def parseOrt (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | t :: rest => match nameText t with
      | some s =>
        if istKeinPlatz s then .error ("reserved head " ++ s)
        else parseSuffixe f (.variable s) rest
      | none => .error "place expected"
    | [] => .error "place expected"
def parseKopf (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | t :: rest => match nameText t with
      | some s =>
        match sammleSegmente rest [s] with
        | (segs, .zeichen "(" :: rest') =>
          match parseArgs f rest' with
          | .ok (args, rest'') =>
            .ok (.call ("::".intercalate segs) args, rest'')
          | .error e => .error e
        | ([a, b], rest') =>
          if istIntWort a || istZuckerBreite a then
            .ok (.field (.variable a) b, rest')
          else if strEq a "Self" then .error "Self:: is not a form"
          else .ok (.why a b, rest')
        | ([a], rest') => parseSuffixe f (.variable a) rest'
        -- A path of three or more segments names an item by its path (`Parser/Namen/Aufloesung.lean`):
        -- one place head, its segments joined as the parser joins call paths.
        | (segs, rest') => .ok (.variable ("::".intercalate segs), rest')
      | none => .error "expression expected"
    | [] => .error "expression expected"
def parseSuffixe (f : Nat) (e : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "." :: t :: rest => match nameText t with
      | some s => parseSuffixe f (.field e s) rest
      | none => .error "field name expected"
    | .zeichen "->" :: t :: rest => match nameText t with
      | some s => parseSuffixe f (.arrow e s) rest
      | none => .error "field name expected"
    | .zeichen "[" :: rest => match parseOr f rest with
      | .ok (i, .zeichen "]" :: rest') =>
        parseSuffixe f (.index e i) rest'
      | .ok (_, _) => .error "[ without ]"
      | .error e => .error e
    | .zeichen "(" :: rest => match e with
      | .variable _ => .ok (e, toks)
      | _ => match parseArgs f rest with
        | .ok (args, rest') => parseSuffixe f (.ext .call [] (e :: args)) rest'
        | .error e => .error e
    | _ => .ok (e, toks)
def parseArgs (f : Nat) (toks : List Token) :
    Except String (List SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen ")" :: rest => .ok ([], rest)
    | _ => match parseArg f toks with
      | .ok (e, .zeichen "," :: rest') => match parseArgs f rest' with
        | .ok (es, rest'') => .ok (e :: es, rest'')
        | .error e => .error e
      | .ok (e, .zeichen ")" :: rest') => .ok ([e], rest')
      | .ok (_, _) => .error "args without )"
      | .error e => .error e
def parseArg (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 =>
    let toks' := match toks with
      | t :: .zeichen ":" :: rest =>
        match nameText t with
        | some _ => rest
        | none => toks
      | _ => toks
    parseOr f toks'
/-- `q x in D : pred` behind the `in` (for `forall`, `exists` and `count`): the layout of `ext`. -/
def parseQuant (f : Nat) (k : XKind) (x : String) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseDomain f toks with
    | .error e => .error e
    | .ok ((dk, ns, ops), r1) => match r1 with
      | .zeichen ":" :: r2 => match parsePred f r2 with
        | .ok (body, r) => .ok (.ext k (x :: dk :: ns) (ops ++ [body]), r)
        | .error e => .error e
      | _ => .error "wanted :"
/-- A `domain` (SYNTAX.md section 5): its kind word, the names it carries and the places it takes. -/
def parseDomain (f : Nat) (toks : List Token) :
    Except String ((String × List String × List SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort "slots" :: .wort "of" :: r => domPlace f "slots" r
    | .wort "descendants" :: .wort "of" :: r => domPlace f "descendants" r
    | .wort "ancestors" :: .wort "of" :: r => domPlace f "ancestors" r
    | .wort "elems" :: .wort "of" :: r => domPlace f "elems" r
    | .wort "mappings" :: .wort "of" :: r => domPlace f "mappings" r
    | .wort "queue" :: r => domPlace f "queue" r
    | .wort "threads" :: r => .ok (("threads", [], []), r)
    | .wort "fields" :: .wort "of" :: t :: r => match nameText t with
      | some a =>
        let (segs, r') := sammleSegmente r [a]
        .ok (("fields", segs, []), r')
      | none => .error "path expected"
    | .wort "chain" :: .zeichen "(" :: a :: .zeichen "," :: b :: .zeichen ")" :: .wort "in" :: r =>
      match nameText a, nameText b with
      | some x, some y => match parseOrt f r with
        | .ok (p, r') => .ok (("chain", [x, y], [p]), r')
        | .error e => .error e
      | _, _ => .error "chain names expected"
    | _ => .error "domain expected"
def domPlace (f : Nat) (k : String) (toks : List Token) :
    Except String ((String × List String × List SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseOrt f toks with
    | .ok (p, r) => .ok ((k, [], [p]), r)
    | .error e => .error e
/-- `pred` (SYNTAX.md section 5): `orpred`; the quantified forms, `e in D`, `a reaches b via f`
    and `=>` ride as `ext` nodes. -/
def parsePred (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parsePredAnd f toks with
    | .ok (l, rest) => parsePredOrL f l rest
    | .error e => .error e
def parsePredOrL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opOder toks with
    | some rest => match parsePredAnd f rest with
      | .ok (r, rest') => parsePredOrL f (.bin "||" l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parsePredAnd (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parsePredNot f toks with
    | .ok (l, rest) => parsePredAndL f l rest
    | .error e => .error e
def parsePredAndL (f : Nat) (l : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match opUnd toks with
    | some rest => match parsePredNot f rest with
      | .ok (r, rest') => parsePredAndL f (.bin "&&" l r) rest'
      | .error e => .error e
    | none => .ok (l, toks)
def parsePredNot (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 =>
    let (neg, t1) : Bool × List Token := match toks with
      | .zeichen "!" :: rest => (true, rest)
      | _ => (false, toks)
    match parsePredAtom f t1 with
    | .error e => .error e
    | .ok (a, rest) =>
      let a' := if neg then SExpr.un "!" a else a
      match rest with
      | .zeichen "=>" :: rest' => match parsePred f rest' with
        | .ok (b, r) => .ok (.ext .imp [] [a', b], r)
        | .error e => .error e
      | _ => .ok (a', rest)
def parsePredAtom (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort "forall" :: t :: .wort "in" :: rest => match nameText t with
      | some x => parseQuant f .all x rest
      | none => .error "quantifier without a name"
    | .wort "exists" :: t :: .wort "in" :: rest => match nameText t with
      | some x => parseQuant f .any x rest
      | none => .error "quantifier without a name"
    | _ => match parseCmp f toks with
      | .ok (e, .wort "in" :: rest) => match parseDomain f rest with
        | .ok ((dk, ns, ops), r) => .ok (.ext .mem (dk :: ns) (e :: ops), r)
        | .error er => .error er
      | .ok (e, .wort "reaches" :: rest) => match parseOrt f rest with
        | .ok (b, .wort "via" :: t :: r) => match nameText t with
          | some fld => .ok (.ext .reach [fld] [e, b], r)
          | none => .error "via without a field"
        | .ok (_, _) => .error "wanted via"
        | .error er => .error er
      | .ok (e, rest) => .ok (e, rest)
      | .error er => match toks with
        | .zeichen "(" :: rest => match parsePred f rest with
          | .ok (p, .zeichen ")" :: r) => .ok (p, r)
          | .ok (_, _) => .error "( without )"
          | .error e2 => .error e2
        | _ => .error er
end

/-- Trees that print bare under a prefix operator. `fnref` is not
    among them: `!&f` is refused on both sides, so it prints
    parenthesised and stays stable. -/
def istAtom : SExpr → Bool
  | .bin .. => false
  | .un .. => false
  | .fnref _ => false
  | _ => true

-- The printer: binary operators fully parenthesised, so the
-- printed form parses back with the same shape regardless of
-- precedence or associativity. Mutual with `druckArgs` (not
-- `List.map`): the kernel reduces structural recursion, and the
-- `map` form forced well-founded recursion, which it does not.
mutual
def druck : SExpr → String
  | .lit n => toString n
  | .float s => s
  | .tru => "true"
  | .fls => "false"
  | .variable s => s
  | .field x f => druck x ++ "." ++ f
  | .index x i => druck x ++ "[" ++ druck i ++ "]"
  | .arrow x f => druck x ++ "->" ++ f
  | .un o x =>
    if strEq o "-()" then "-(" ++ druck x ++ ")"
    else if istAtom x then o ++ druck x else o ++ "(" ++ druck x ++ ")"
  | .bin o l r => "(" ++ druck l ++ " " ++ o ++ " " ++ druck r ++ ")"
  | .call f args =>
    match args with
    | [] => if strEq f "None" then "None" else f ++ "()"
    | _ :: _ => f ++ "(" ++ druckArgs args ++ ")"
  | .fnref p => "&" ++ p
  | .built f args => f ++ "(" ++ druckArgs args ++ ")"
  | .old x => "old(" ++ druck x ++ ")"
  | .res => "result"
  | .why g f => g ++ "::" ++ f
  | .ext .text ns _ => "\"" ++ ("".intercalate ns) ++ "\""
  | .ext _ _ _ => "<ext>"
def druckArgs : List SExpr → String
  | [] => ""
  | [x] => druck x
  | x :: xs => druck x ++ ", " ++ druckArgs xs
end

/-- A whole expression: the token list must end here. Fuel scales
    with the input; a huge input may report out-of-fuel instead of
    parsing (total, but not complete -- see CUTS). -/
end Gabbro.Grammatik.Parser
