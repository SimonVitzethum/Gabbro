/-
  File:      Grammatik/Parser/Ausdruck.lean
  Subject:   T3 PART 1 (PLAN-UEBERSETZUNGSVALIDIERUNG.md section 1): the
             Gabbro expression parser (SYNTAX.md section 4, `expr`) over
             the Lean lexer, step 1.

  Skeleton: the surface AST `SExpr` and a stub `parseExpr`. Levels,
  printer and round trip land in the next steps.
-/
import Grammatik.Parser.Lexer

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- A surface expression: SYNTAX.md section 4 `expr` without types,
    spans or sugar resolution. Operators ride as their spelling
    (`bin "+%"`), so the precedence table stays one function.
    Against `ast.rs` `ExprArt`: `Zahl/Wahr/Falsch/Ort/Ruf/Grund`
    carry over (spans dropped); `Some(x)`/`None` stay calls
    (`ruf "Some" [x]`, `ruf "None" []`, as `parse.rs` builds them);
    `FnWert` is `fnwert` with the path text; `Eingebaut` is
    `eingebaut` with the head word and the argument expressions;
    `Klammer` vanishes (the printer re-parenthesises); `Zaehle`,
    `ArrayLit` and `LibraryCall` are refused (see CUTS). -/
inductive SExpr
  | lit : Nat → SExpr
  | gleit : String → SExpr
  | wahr : SExpr
  | falsch : SExpr
  | variable : String → SExpr
  | feld : SExpr → String → SExpr
  | index : SExpr → SExpr → SExpr
  | pfeil : SExpr → String → SExpr
  | un : String → SExpr → SExpr
  | bin : String → SExpr → SExpr → SExpr
  | ruf : String → List SExpr → SExpr
  | fnwert : String → SExpr
  | eingebaut : String → List SExpr → SExpr
  | alt : SExpr → SExpr
  | ergebnis : SExpr
  | grund : String → String → SExpr
  deriving Repr

-- Structural equality on surface trees, as a `Bool`: core Lean
-- derives no `DecidableEq` through the `List SExpr` field, and the
-- agreement probes compare shapes by kernel evaluation.
mutual
def beqSExpr : SExpr → SExpr → Bool
  | .lit m, .lit n => m == n
  | .gleit a, .gleit b => strEq a b
  | .wahr, .wahr => true
  | .falsch, .falsch => true
  | .variable a, .variable b => strEq a b
  | .feld x f, .feld y g => beqSExpr x y && strEq f g
  | .index x i, .index y j => beqSExpr x y && beqSExpr i j
  | .pfeil x f, .pfeil y g => beqSExpr x y && strEq f g
  | .un o x, .un p y => strEq o p && beqSExpr x y
  | .bin o x1 x2, .bin p y1 y2 =>
    strEq o p && beqSExpr x1 y1 && beqSExpr x2 y2
  | .ruf f a, .ruf g b => strEq f g && beqSExprList a b
  | .fnwert f, .fnwert g => strEq f g
  | .eingebaut f a, .eingebaut g b => strEq f g && beqSExprList a b
  | .alt x, .alt y => beqSExpr x y
  | .ergebnis, .ergebnis => true
  | .grund g1 f1, .grund g2 f2 => strEq g1 g2 && strEq f1 f2
  | _, _ => false
def beqSExprList : List SExpr → List SExpr → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSExpr x y && beqSExprList xs ys
  | _, _ => false
end

/-- A name token (identifier or contextual keyword) with its text.
    `parse.rs` `erwarte_ident` takes the same two token shapes. -/
def nameText : Token → Option String
  | .ident s => some s
  | .wort s => some s
  | _ => none

/-- Words that never start a place: the reserved words without a
    dedicated primary arm and without `Self` (`parse.rs` reads
    `Self.slots[s]` as a place, and `old` stays a bare name outside
    `old(`). `true`/`false`/`Some`/`None`/`sizeof`/`lenof`/
    `aligned`/`result` never reach here except malformed, and are
    refused rather than misread as names. -/
def keinPlatzTafel : List (List Char) :=
  [['f','o','r','a','l','l'], ['e','x','i','s','t','s'], ['c','o','n','s','t'], ['s','t','a','t','i','c'], ['e','x','t','e','r','n'], ['i','f'], ['e','l','s','e'], ['r','e','t','u','r','n'], ['b','o','o','l'], ['s','i','z','e','o','f'], ['l','e','n','o','f'], ['a','l','i','g','n','e','d']]

def istKeinPlatz (s : String) : Bool :=
  keinPlatzTafel.contains s.toList

/-- Words that name a type, never a place: refused as `sizeof` /
    `lenof` arguments (`parse.rs` `typ_oder_ort` reads a type there,
    and this parser has no `typeexpr` reader). -/
def typWortTafel : List (List Char) :=
  [['u','8'], ['u','1','6'], ['u','3','2'], ['u','6','4'], ['i','8'], ['i','1','6'], ['i','3','2'], ['i','6','4'], ['b','o','o','l'], ['n','e','v','e','r'], ['p','t','r'], ['f','n']]

def istTypWort (s : String) : Bool :=
  typWortTafel.contains s.toList

/-- The eight standard integer words: `parse.rs` reads `u64::max`
    as a place and `u64(x)` as a conversion, never as a `Grund`. -/
def intWortTafel : List (List Char) :=
  [['u','8'], ['u','1','6'], ['u','3','2'], ['u','6','4'], ['i','8'], ['i','1','6'], ['i','3','2'], ['i','6','4']]

def istIntWort (s : String) : Bool :=
  intWortTafel.contains s.toList

/-- A sugared width (`u13`, `i37`): identifier head, `u`/`i` plus
    digits for `1 .. 64` (PLAN-BITS section 1; `u0(a)` stays a call
    to the name `u0`, as in `parse.rs` `zuckerbreite`). -/
def istZuckerBreite (s : String) : Bool :=
  match s.toList with
  | 'u' :: d :: ds => zuckerZahl (d :: ds)
  | 'i' :: d :: ds => zuckerZahl (d :: ds)
  | _ => false
where
  zuckerZahl : List Char → Bool
    | [] => false
    | ds =>
      ds.all istZiffer &&
      match String.ofList ds |>.toNat? with
      | some n => 1 ≤ n && n ≤ 64
      | none => false

/-- One spelled operator of the `||` level. -/
def opOder : List Token → Option (List Token)
  | .zeichen "||" :: rest => some rest
  | _ => none

/-- One spelled operator of the `&&` level. -/
def opUnd : List Token → Option (List Token)
  | .zeichen "&&" :: rest => some rest
  | _ => none

/-- The single comparison (`cmpexpr` takes at most one). -/
def opVgl : List Token → Option (String × List Token)
  | .zeichen "==" :: rest => some ("==", rest)
  | .zeichen "!=" :: rest => some ("!=", rest)
  | .zeichen "<=" :: rest => some ("<=", rest)
  | .zeichen ">=" :: rest => some (">=", rest)
  | .zeichen "<" :: rest => some ("<", rest)
  | .zeichen ">" :: rest => some (">", rest)
  | _ => none

/-- One spelled operator of the `bitexpr` level (`<<%` rides with
    the shifts, PLAN-BITS section 4). -/
def opBit : List Token → Option (String × List Token)
  | .zeichen "&" :: rest => some ("&", rest)
  | .zeichen "|" :: rest => some ("|", rest)
  | .zeichen "^" :: rest => some ("^", rest)
  | .zeichen "<<" :: rest => some ("<<", rest)
  | .zeichen ">>" :: rest => some (">>", rest)
  | .zeichen "<<%" :: rest => some ("<<%", rest)
  | _ => none

/-- One spelled operator of the `addexpr` level (`+%`, `-%` and
    `+|` ride with `+`/`-`). -/
def opAdd : List Token → Option (String × List Token)
  | .zeichen "+" :: rest => some ("+", rest)
  | .zeichen "-" :: rest => some ("-", rest)
  | .zeichen "+%" :: rest => some ("+%", rest)
  | .zeichen "-%" :: rest => some ("-%", rest)
  | .zeichen "+|" :: rest => some ("+|", rest)
  | _ => none

/-- One spelled operator of the `mulexpr` level (`*%` rides
    with `*`). -/
def opMul : List Token → Option (String × List Token)
  | .zeichen "*" :: rest => some ("*", rest)
  | .zeichen "/" :: rest => some ("/", rest)
  | .zeichen "%" :: rest => some ("%", rest)
  | .zeichen "*%" :: rest => some ("*%", rest)
  | _ => none

/-- One `::` segment run after a head name (pure: no fuel needed).
    Stops before the first non-`::` token, leaving it. -/
def sammleSegmente : List Token → List String → List String × List Token
  | .zeichen "::" :: t :: rest, acc => match nameText t with
    | some s => sammleSegmente rest (acc ++ [s])
    | none => (acc, .zeichen "::" :: t :: rest)
  | toks, acc => (acc, toks)

/-- A three-or-more segment non-call path as a field chain
    (`parse.rs` builds the same `Ort` with `Feld` suffixes). -/
def grundKette : List String → SExpr
  | [] => .variable ""
  | a :: rest => rest.foldl (fun e s => .feld e s) (.variable a)

-- The expression levels of SYNTAX.md section 4 (`expr` down to
-- `primary`), each with fuel: every call passes strictly less fuel,
-- so the block terminates by `f`. Against `parse.rs`: the level
-- order, the single comparison, the flat bit level and the riding
-- overflow operators match one by one.
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
    | .zeichen "-" :: rest => match parsePrimary f rest with
      | .ok (e, rest') => .ok (.un "-" e, rest')
      | .error e => .error e
    | .zeichen "~" :: rest => match parsePrimary f rest with
      | .ok (e, rest') => .ok (.un "~" e, rest')
      | .error e => .error e
    | .zeichen "&" :: t :: rest => match nameText t with
      | some s =>
        let (segs, rest') := sammleSegmente rest [s]
        .ok (.fnwert ("::".intercalate segs), rest')
      | none => .error "& expects a path"
    | _ => parsePrimary f toks
def parsePrimary (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zahl v :: rest => .ok (.lit v, rest)
    | .gleit s :: rest => match rest with
      | .wort "rounded" :: rest' =>
        .ok (.gleit (s ++ " rounded"), rest')
      | _ => .ok (.gleit s, rest)
    | .wort "true" :: rest => .ok (.wahr, rest)
    | .wort "false" :: rest => .ok (.falsch, rest)
    | .wort "Some" :: .zeichen "(" :: rest =>
      match parseOr f rest with
      | .ok (e, .zeichen ")" :: rest') => .ok (.ruf "Some" [e], rest')
      | .ok (_, _) => .error "Some without )"
      | .error e => .error e
    | .wort "None" :: rest => .ok (.ruf "None" [], rest)
    | .wort "Some" :: rest => .ok (.ruf "Some" [], rest)
    | .wort "result" :: rest => .ok (.ergebnis, rest)
    | .wort "old" :: .zeichen "(" :: rest =>
      match parseOrt f rest with
      | .ok (e, .zeichen ")" :: rest') => .ok (.alt e, rest')
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
          else .ok (.eingebaut w [a], rest')
        | _ => .ok (.eingebaut w [a], rest')
      | .ok (_, _) => .error (w ++ " without )")
      | .error e => .error e
    else match parseOr f toks with
      | .ok (a, .zeichen "," :: rest) => match parseOr f rest with
        | .ok (b, .zeichen ")" :: rest') =>
          .ok (.eingebaut w [a, b], rest')
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
            .ok (.ruf ("::".intercalate segs) args, rest'')
          | .error e => .error e
        | ([a, b], rest') =>
          if istIntWort a || istZuckerBreite a then
            .ok (.feld (.variable a) b, rest')
          else if strEq a "Self" then .error "Self:: is not a form"
          else .ok (.grund a b, rest')
        | ([a], rest') => parseSuffixe f (.variable a) rest'
        | (segs, rest') => .ok (grundKette segs, rest')
      | none => .error "expression expected"
    | [] => .error "expression expected"
def parseSuffixe (f : Nat) (e : SExpr) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "." :: t :: rest => match nameText t with
      | some s => parseSuffixe f (.feld e s) rest
      | none => .error "field name expected"
    | .zeichen "->" :: t :: rest => match nameText t with
      | some s => parseSuffixe f (.pfeil e s) rest
      | none => .error "field name expected"
    | .zeichen "[" :: rest => match parseOr f rest with
      | .ok (i, .zeichen "]" :: rest') =>
        parseSuffixe f (.index e i) rest'
      | .ok (_, _) => .error "[ without ]"
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
end

/-- Trees that print bare under a prefix operator. `fnwert` is not
    among them: `!&f` is refused on both sides, so it prints
    parenthesised and stays stable. -/
def istAtom : SExpr → Bool
  | .bin .. => false
  | .un .. => false
  | .fnwert _ => false
  | _ => true

-- The printer: binary operators fully parenthesised, so the
-- printed form parses back with the same shape regardless of
-- precedence or associativity. Mutual with `druckArgs` (not
-- `List.map`): the kernel reduces structural recursion, and the
-- `map` form forced well-founded recursion, which it does not.
mutual
def druck : SExpr → String
  | .lit n => toString n
  | .gleit s => s
  | .wahr => "true"
  | .falsch => "false"
  | .variable s => s
  | .feld x f => druck x ++ "." ++ f
  | .index x i => druck x ++ "[" ++ druck i ++ "]"
  | .pfeil x f => druck x ++ "->" ++ f
  | .un o x =>
    if istAtom x then o ++ druck x else o ++ "(" ++ druck x ++ ")"
  | .bin o l r => "(" ++ druck l ++ " " ++ o ++ " " ++ druck r ++ ")"
  | .ruf f args =>
    match args with
    | [] => if strEq f "None" then "None" else f ++ "()"
    | _ :: _ => f ++ "(" ++ druckArgs args ++ ")"
  | .fnwert p => "&" ++ p
  | .eingebaut f args => f ++ "(" ++ druckArgs args ++ ")"
  | .alt x => "old(" ++ druck x ++ ")"
  | .ergebnis => "result"
  | .grund g f => g ++ "::" ++ f
def druckArgs : List SExpr → String
  | [] => ""
  | [x] => druck x
  | x :: xs => druck x ++ ", " ++ druckArgs xs
end

/-- A whole expression: the token list must end here. Fuel scales
    with the input; a huge input may report out-of-fuel instead of
    parsing (total, but not complete -- see CUTS). -/
def parseTop (toks : List Token) : Except String SExpr :=
  match parseOr (toks.length * 8 + 32) toks with
  | .ok (e, [.ende]) => .ok e
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e

/-- From source text: lex, then parse the whole token list. -/
def parseTopAusText (s : String) : Except String SExpr :=
  match lex s with
  | .error e => .error ("lex: " ++ toString (repr e))
  | .ok toks => parseTop toks

/-- Shape equality on parse outcomes, as a `Bool`. -/
def beqTop : Except String SExpr → Except String SExpr → Bool
  | .ok a, .ok b => beqSExpr a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

/-- Print, then parse back. -/
def parsePrint (e : SExpr) : Except String SExpr :=
  parseTopAusText (druck e)

/-- The weaker round trip of the task: `parsePrint e = e` on a
    decided example set. The set is MICRO on purpose: composed
    `druck`-then-`lex`-then-`parse` kernel evaluation blows past
    the heartbeat limit at seven source characters (measured:
    `(1 + 2)` times out `whnf` at 200000 heartbeats, `(1)` and
    `1 + 2` are instant), so operator trees cannot round-trip by
    `decide`. Their shapes are covered at token level by the
    sondes in `Parser/AusdruckProben.lean` instead; here the five
    legs prove the pipeline mechanism end to end. The general
    `parse_expr_roundtrip` over all parser-produced trees is out
    of reach: it needs `beqSExpr` soundness, fuel sufficiency, and
    printer injectivity -- see CUTS. -/
theorem pp_lit : beqTop (parsePrint (.lit 5)) (.ok (.lit 5)) = true := by
  decide
theorem pp_var : beqTop (parsePrint (.variable "y"))
    (.ok (.variable "y")) = true := by
  decide
theorem pp_wahr : beqTop (parsePrint (.wahr)) (.ok (.wahr)) = true := by
  decide
theorem pp_falsch : beqTop (parsePrint (.falsch))
    (.ok (.falsch)) = true := by
  decide
theorem pp_not : beqTop (parsePrint (.un "!" (.variable "y")))
    (.ok (.un "!" (.variable "y"))) = true := by
  decide

/-- The round trip as one conjunction over the five legs above. -/
theorem print_parse :
    beqTop (parsePrint (.lit 5)) (.ok (.lit 5)) = true ∧
    beqTop (parsePrint (.variable "y")) (.ok (.variable "y")) = true ∧
    beqTop (parsePrint (.wahr)) (.ok (.wahr)) = true ∧
    beqTop (parsePrint (.falsch)) (.ok (.falsch)) = true ∧
    beqTop (parsePrint (.un "!" (.variable "y")))
      (.ok (.un "!" (.variable "y"))) = true :=
  ⟨pp_lit, pp_var, pp_wahr, pp_falsch, pp_not⟩

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here, and every shape difference against
  `crates/gabbro-syntax` found by the probes.

  *Every difference below was found by reading `ast.rs`/`parse.rs`
  (`cargo` cannot run in this lane); each is a documented gap, not a
  silent one.*

  1. Spans: every Rust node carries one (`span`, `bis_zu`); no
     `SExpr` does. Positions must be re-attached outside.
  2. `Klammer` vanishes: `(e)` parses to the inner tree. The printer
     re-parenthesises canonically, so `print_parse` still closes.
  3. Call labels (`marken`, «B7») are accepted and dropped: `P(a: 1)`
     parses to `ruf "P" [1]`. Rust keeps the key stream for the
     record check (`m1::verbundwert`).
  4. Floats keep canonical text (`gleit "0.0"`), not the `f64` bits,
     the dyadic flag or `rounded`-exactness `lex.rs`/`parse.rs`
     compute. Whether the literal is exact in its target type is an
     M1 question, not a parsing one.
  5. `result` and `old` read unconditionally. `parse.rs` gates them
     on `im_vertrag` (inside a contract); a context-free reader
     cannot see that flag, so a local named `result` in body
     position would misread (no corpus occurrence).
  6. `count k in D : p` («SG-24») is refused: it needs the `domain`
     and `pred` readers (SYNTAX.md section 5), which are not this
     file. A bare `count` stays a name, exactly as the failed
     lookahead in `parse.rs` does.
  7. `sizeof`/`lenof` over a TYPE (`sizeof(u32)`) is refused: there
     is no `typeexpr` reader here (`typ_oder_ort`). Over places
     (`lenof(Self)`) and `aligned(e, c)` the shape matches.
  8. `Zaehle`, `ArrayLit` (const-initializer only) and `LibraryCall`
     (`@lib#f`) have no constructor and are refused.
  9. String literals are refused in expression position (`P011` in
     `parse.rs` has no string arm either) -- same refusal.
  10. `&T` for a declared carrier reads as `fnwert "T"` here; Rust
      separates the `ptr` producer (`Expr.ptrOf`) by declaration
      context this reader does not have.
  11. `beqSExpr`/`beqTop` are not proved sound or complete: the
      probes compare by kernel `Bool` evaluation, not by a
      `beqSExpr a b = true <-> a = b` theorem.
  12. `parseTop` is total but not complete: fuel `length * 8 + 32`
      suffices for every probe (each `decide` checks its own fuel),
      and a huge input may report out-of-fuel instead of parsing.
  13. The general `parse_expr_roundtrip` (for every parser-produced
      tree) is not proved: it needs item 11 (`beqSExpr` soundness)
      plus fuel sufficiency and printer injectivity. `print_parse`
      is the decided set instead -- and the set is MICRO (atoms and
      one prefix) on purpose: composed `druck`-then-`lex`-then-
      `parse` kernel evaluation exhausts the `whnf` heartbeat
      budget (200000) at seven source characters -- measured
      2026-09-13: `(1)` and `1 + 2` decide instantly, `(1 + 2)`
      times out, `1 + 2 + 3` times out. Operator shapes round-trip
      nowhere by `decide`; they are covered at token level by the
      sondes in `Parser/AusdruckProben.lean` instead.
  14. Name predicates (`istKeinPlatz`, `istTypWort`, `istIntWort`)
      and `beqSExpr` compare through character lists (`strEq`,
      `Lexer.lean`): same kernel-speed reason as the keyword
      buckets, and the probes check every predicate leg that a
      corpus expression can reach (`Self`, type words, `R::F`).
  15. The `decide` probes themselves live in
      `Parser/AusdruckProben.lean`: one kernel evaluation per
      theorem keeps every worker small (see that file's header).
  16. `druck` prints a bare-`None` call as `None`, not `None()`:
      `None` parses without parentheses (`parse.rs`), so the
      naive print would not parse back. A `Some` call always
      carries exactly one argument from the parser, so it needs
      no such case.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopAusText
#print axioms Gabbro.Grammatik.Parser.druck
#print axioms Gabbro.Grammatik.Parser.print_parse
