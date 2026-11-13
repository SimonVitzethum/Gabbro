module

public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Item.ElementTief

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- A predicate at the top of a `spec fn` body: the reader sends a body that starts with `(` to the
    expression reader, so the outer parentheses of a predicate form stay off. -/
def druckPred (e : SExpr) : List Token :=
  match e with
  | .ext k _ _ =>
    match k with
    | .text => druckToks e
    | .call => druckToks e
    | .label | .instantiate | .dyn => druckToks e
    | _ => (druckToks e).drop 1 |>.dropLast
  | _ => druckToks e

/-- An effect arm. -/
def druckEffekt : SEffekt → List Token
  | .param n => rohToks n
  | .instanceEffects n ts => rohToks n ++ [.zeichen "["] ++ ((ts.map druckTyp).intersperse [.zeichen ","]).flatten ++ [.zeichen "]"]
  | .reads p => [.wort "reads"] ++ druckToks p
  | .writes p => [.wort "writes"] ++ druckToks p
  | .locks sh p => [.wort "locks"] ++ (if sh then [.wort "shared"] else []) ++ druckToks p
  | .masks n => [.wort "masks", nameTok n]
  | .allocs n => [.wort "allocs", nameTok n]
  | .takes p => [.wort "consumes"] ++ druckToks p
  | .borrows n => [.wort "borrows", nameTok n]
  | .moves n => [.wort "moves", nameTok n]
  | .mints n => [.wort "mints", nameTok n]
  | .posts p => [.wort "publishes"] ++ druckToks p
  | .loops => [.wort "diverges"]
  | .pure => [.wort "pure"]

def druckEffekte : List SEffekt → List Token
  | [] => []
  | [e] => druckEffekt e
  | e :: es => druckEffekt e ++ [.zeichen ","] ++ druckEffekte es

/-- One clause. `retires` and `deadline` ride as the printed text the reader built. -/
def druckKlausel : SKlausel → List Token
  | .needs p => [.wort "requires"] ++ druckToks p
  | .gives p => [.wort "ensures"] ++ druckToks p
  | .keeps ns => [.wort "maintains"] ++ druckNamen ns
  | .refs p => [.wort "refines"] ++ pfadToks p
  | .cost e => [.wort "costs", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
  | .drops e => [.wort "decreases"] ++ druckToks e
  | .induc h => [.wort "by"] ++ rohToks h
  | .load p => [.wort "payload"] ++ pfadToks p
  | .part s => [.wort "section", .text s]
  | .arch n => [.wort "arch", nameTok n]
  | .moves a b => [.wort "advances", nameTok a, .zeichen "->", nameTok b]
  | .quits s => [.wort "retires"] ++ rohToks s
  | .limit s => rohToks s
  | .effs es => [.wort "effects", .zeichen "{"] ++ druckEffekte es ++ [.zeichen "}"]

def druckKlauseln : List SKlausel → List Token
  | [] => []
  | k :: ks => druckKlausel k ++ druckKlauseln ks

def druckParam : String × STyp → List Token
  | (n, t) => [nameTok n, .zeichen ":"] ++ druckTyp t

def druckParams : List (String × STyp) → List Token
  | [] => []
  | [p] => druckParam p
  | p :: ps => druckParam p ++ [.zeichen ","] ++ druckParams ps

/-- Generic parameters print their declared kinds; constants use the explicit `const` spelling. -/
def druckGenericParam : SGenericParam → List Token
  | .type n bounds => [nameTok n] ++ (match bounds with
    | [] => []
    | b :: bs => [.zeichen ":", nameTok b] ++ bs.flatMap (fun x => [.zeichen "+", nameTok x]))
  | .constant n ty => [nameTok n, .zeichen ":", .wort "const"] ++ druckTyp ty
  | .function n ty => [nameTok n, .zeichen ":"] ++ druckTyp ty

def druckGenericParams : List SGenericParam → List Token
  | [] => []
  | p :: ps => [.zeichen "["] ++ druckGenericParam p ++
    ps.flatMap (fun q => .zeichen "," :: druckGenericParam q) ++ [.zeichen "]"]

/-- A function head: `[art] fn name (params) [-> T] [or R] clauses`. -/
def druckFnSig (s : FnSig) : List Token :=
  (if strEq s.art "" then [] else [.wort s.art]) ++ [.wort "fn", nameTok s.name] ++ druckGenericParams s.generics ++ [.zeichen "("] ++
    druckParams s.params ++ [.zeichen ")"] ++
    (match s.res with
      | some t => [.zeichen "->"] ++ druckTyp t
      | none => []) ++
    (match s.fehler with
      | some n => [.wort "or", nameTok n]
      | none => []) ++
    druckKlauseln s.klauseln

/-- A constant value or an array literal. -/
def druckKonstWert : SKonstWert → List Token
  | .one e => druckToks e
  | .rows xs => [.zeichen "["] ++ druckKonstWerte xs ++ [.zeichen "]"]
where
  druckKonstWerte : List SKonstWert → List Token
    | [] => []
    | [x] => druckKonstWert x
    | x :: xs => druckKonstWert x ++ [.zeichen ","] ++ druckKonstWerte xs

def druckFeld (f : SFeld) : List Token :=
  [nameTok f.fname, .zeichen ":"] ++ druckTyp f.ftyp ++
    (match f.pos with
      | some p => [.zeichen "@"] ++ rohToks p
      | none => []) ++
    (match f.bezug with
      | some n => [.wort "offset_into", nameTok n]
      | none => []) ++
    (match f.wo with
      | some p => [.wort "where"] ++ druckToks p
      | none => []) ++
    (if f.reserviert then [.wort "reserved"] else []) ++
    (if f.byOps then [.wort "by", .wort "ops"] else [])

def druckFelder : List SFeld → List Token
  | [] => []
  | [f] => druckFeld f
  | f :: fs => druckFeld f ++ [.zeichen ","] ++ druckFelder fs

def druckGruppenInv (i : SGruppenInv) : List Token :=
  [.wort "invariant", nameTok i.name, .zeichen ":"] ++ druckToks i.pred ++ [.zeichen ";"]

def druckKanten : List (String × String) → List Token
  | [] => []
  | [(a, b)] => [.wort a, nameTok b]
  | (a, b) :: ks => [.wort a, nameTok b, .zeichen ","] ++ druckKanten ks

def druckTabTeil : STabTeil → List Token
  | .tConst n t v => [.wort "const", nameTok n, .zeichen ":"] ++ druckTyp t ++ [.zeichen "="] ++ druckKonstWert v ++ [.zeichen ";"]
  | .tSlot fs => [.wort "slot", .zeichen "{"] ++ druckFelder fs ++ [.zeichen "}"]
  | .tInv i => druckGruppenInv i
  | .tOps ns => [.wort "ops"] ++ druckNamen ns ++ [.zeichen ";"]
  | .tTree ks => [.wort "tree", .zeichen "{"] ++ druckKanten ks ++ [.zeichen "}"]
  | .tBusy n => [.wort "occupied", nameTok n, .zeichen ";"]

def druckTabTeile : List STabTeil → List Token
  | [] => []
  | t :: ts => druckTabTeil t ++ druckTabTeile ts

/-- Place lists and paths in braces. -/
def druckPlaetze : List SExpr → List Token
  | [] => []
  | [p] => druckToks p
  | p :: ps => druckToks p ++ [.zeichen ","] ++ druckPlaetze ps

/-- The class of an assumption: `falsifier n` or `unfalsifiable "…"`. -/
def druckKlasse : SAnKlasse → List Token
  | .probe n => [.wort "falsifier", nameTok n]
  | .trust s => [.wort "unfalsifiable", .text s]

/-- One register binding (the reader takes `=` or `:`; the printer writes `=`). -/
def druckRegBind : SRegBind → List Token
  | .reg a => [nameTok a]
  | .binds a b => [nameTok a, .zeichen "=", nameTok b]

def druckRegBinds : List SRegBind → List Token
  | [] => []
  | [b] => druckRegBind b
  | b :: bs => druckRegBind b ++ [.zeichen ","] ++ druckRegBinds bs

/-- One adapter parameter (the inverse of `parseAdaptParamEinzel`). -/
def druckAdaptParam : SAdaptParam → List Token
  | .alle => [.zeichen ".."]
  | .ohne n => [.zeichen "-", nameTok n]
  | .neu n t => [nameTok n, .zeichen ":"] ++ druckTyp t

/-- Adapter parameters, comma separated (the inverse of `parseAdaptParams`). -/
def druckAdaptParams : List SAdaptParam → List Token
  | [] => []
  | [p] => druckAdaptParam p
  | p :: ps => druckAdaptParam p ++ [.zeichen ","] ++ druckAdaptParams ps


end Gabbro.Grammatik.Parser
