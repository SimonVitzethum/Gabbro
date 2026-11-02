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
    | .label => druckToks e
    | _ => (druckToks e).drop 1 |>.dropLast
  | _ => druckToks e

/-- An effect arm. -/
def druckEffekt : SEffekt → List Token
  | .reads p => [.wort "reads"] ++ druckToks p
  | .writes p => [.wort "writes"] ++ druckToks p
  | .locks sh p => [.wort "locks"] ++ (if sh then [.wort "shared"] else []) ++ druckToks p
  | .masks n => [.wort "masks", nameTok n]
  | .allocs n => [.wort "allocs", nameTok n]
  | .takes p => [.wort "consumes"] ++ druckToks p
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

/-- A function head: `[art] fn name (params) [-> T] [or R] clauses`. -/
def druckFnSig (s : FnSig) : List Token :=
  (if strEq s.art "" then [] else [.wort s.art]) ++ [.wort "fn", nameTok s.name, .zeichen "("] ++
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
  [.wort "invariant", nameTok i.name, .wort "cost", .ident "O", .zeichen "("] ++ druckToks i.kosten ++
    [.zeichen ")", .wort "runs", .wort (if i.online then "online" else "offline")] ++
    (match i.proof with
      | some h => [.wort "by"] ++ rohToks h
      | none => []) ++
    [.zeichen ":"] ++ druckToks i.pred ++ [.zeichen ";"]

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

/-- `{ a, b }` over names. -/
def druckNamenKlammer (ns : List String) : List Token :=
  [.zeichen "{"] ++ druckNamen ns ++ [.zeichen "}"]

def druckPredListe : List SExpr → List Token
  | [] => []
  | [p] => druckToks p
  | p :: ps => druckToks p ++ [.zeichen ","] ++ druckPredListe ps

def druckFehlerKarte : List (String × Option SExpr × String) → List Token
  | [] => []
  | [(a, n, b)] =>
    [nameTok a] ++ (match n with
      | some e => [.zeichen "="] ++ druckToks e
      | none => []) ++ [.zeichen "=>", nameTok b]
  | (a, n, b) :: xs =>
    [nameTok a] ++ (match n with
      | some e => [.zeichen "="] ++ druckToks e
      | none => []) ++ [.zeichen "=>", nameTok b, .zeichen ","] ++ druckFehlerKarte xs

/-- `sysbind`: `number e regs in {…} regs out {…} {stack r} clobbers {…} errors {…}`. -/
def druckBind (b : SBind) : List Token :=
  [.wort "number"] ++ druckToks b.id ++ [.wort "regs", .wort "in", .zeichen "{"] ++ druckRegBinds b.ins ++
    [.zeichen "}", .wort "regs", .wort "out", .zeichen "{"] ++ druckRegBinds b.outs ++ [.zeichen "}"] ++
    (b.stack.flatMap fun s => [.wort "stack", nameTok s]) ++
    [.wort "clobbers"] ++ druckNamenKlammer b.dirty ++
    [.wort "errors", .zeichen "{"] ++ druckFehlerKarte b.codes ++ [.zeichen "}"]

/-- `syscontract`. -/
def druckGate (g : SGate) : List Token :=
  (match g.pre with
    | [] => []
    | ps => [.wort "requires"] ++ druckPredListe ps) ++
  (match g.post with
    | [] => []
    | ps => [.wort "ensures"] ++ druckPredListe ps) ++
  [.wort "effects", .zeichen "{"] ++ druckEffekte g.uses ++ [.zeichen "}"] ++
  (match g.cost with
    | some e => [.wort "costs", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
    | none => [])

/-- `syspair`. -/
def druckHerkunft : SHerkunft → List Token
  | .assum a k => [.wort "assume", nameTok a] ++ druckKlasse k ++ [.zeichen ";"]
  | .core p => [.wort "kernel"] ++ pfadToks p ++ [.zeichen ";"]

def druckGoalBinds : List (String × SBind × SHerkunft) → List Token
  | [] => []
  | (v, b, h) :: rest => [nameTok v, .zeichen "="] ++ druckBind b ++ druckHerkunft h ++ druckGoalBinds rest

def druckGrundFaelle : List (String × SExpr × String) → List Token
  | [] => []
  | (c, n, s) :: rest => [nameTok c, .zeichen "="] ++ druckToks n ++ [.text s, .zeichen ","] ++ druckGrundFaelle rest

/-- An entry (`entry n [vector e] [via m] arch a { regs … dispatch p ; }`). -/
def druckEingang (e : SEingang) : List Token :=
  [.wort "entry", nameTok e.name] ++
    (match e.vektor with
      | some v => [.wort "vector"] ++ druckToks v
      | none => []) ++
    (match e.via with
      | some m => [.wort "via", nameTok m]
      | none => []) ++
    [.wort "arch", nameTok e.arch, .zeichen "{", .wort "regs", .wort "in", .zeichen "{"] ++
    druckRegBinds e.regIn ++ [.zeichen "}", .wort "regs", .wort "out", .zeichen "{"] ++
    druckRegBinds e.regOut ++ [.zeichen "}", .wort "preserves"] ++ druckNamenKlammer e.erhaelt ++
    [.wort "clobbers"] ++ druckNamenKlammer e.kills ++ [.wort "stack", nameTok e.stapel] ++
    (if e.perCpu then [.wort "per", .wort "cpu"] else []) ++
    (match e.ist with
      | some x => [.wort "ist"] ++ druckToks x
      | none => []) ++
    (match e.nest with
      | some n => [.wort "nested"] ++ rohToks n
      | none => []) ++
    [.wort "dispatch"] ++ pfadToks e.dispatch ++ [.zeichen ";", .zeichen "}"]

/-- One transition step `place : from -> to`. -/
def druckSchritte : List (SExpr × SExpr × SExpr) → List Token
  | [] => []
  | [(p, a, b)] => druckToks p ++ [.zeichen ":"] ++ druckToks a ++ [.zeichen "->"] ++ druckToks b
  | (p, a, b) :: rest =>
    druckToks p ++ [.zeichen ":"] ++ druckToks a ++ [.zeichen "->"] ++ druckToks b ++ [.zeichen ","] ++
      druckSchritte rest

/-- `transition n { steps } [requires p] [effects {…}]`. -/
def druckTrans (tr : STrans) : List Token :=
  [.wort "transition", nameTok tr.tname, .zeichen "{"] ++ druckSchritte tr.schritte ++ [.zeichen "}"] ++
    (match tr.voraus with
      | some p => [.wort "requires"] ++ druckToks p
      | none => []) ++
    (match tr.wirkung with
      | [] => []
      | es => [.wort "effects", .zeichen "{"] ++ druckEffekte es ++ [.zeichen "}"])

def druckTransListe : List STrans → List Token
  | [] => []
  | tr :: rest => druckTrans tr ++ druckTransListe rest

/-- The `in`-stage words of a register class, as the reader kept them. -/
def druckPhasen : List String → List Token
  | [] => []
  | w :: rest =>
    (if strEq w "in" then [Token.wort "in"] else if strEq w "," then [Token.zeichen ","] else [nameTok w]) ++
      druckPhasen rest

def druckRegFeld (f : SRegFeld) : List Token :=
  [nameTok f.name, .zeichen "@"] ++ rohToks f.pos ++
    (match f.klasse with
      | some c => [.wort "class", nameTok c]
      | none => [])

def druckRegFelder : List SRegFeld → List Token
  | [] => []
  | [f] => druckRegFeld f
  | f :: fs => druckRegFeld f ++ [.zeichen ","] ++ druckRegFelder fs

def druckTraeger : List (List String) → List Token
  | [] => []
  | [c] => (match c with
    | [a, b] => [nameTok a, .zeichen ".", nameTok b]
    | cs => druckNamen cs)
  | c :: cs =>
    (match c with
      | [a, b] => [nameTok a, .zeichen ".", nameTok b]
      | cs' => druckNamen cs') ++ [.zeichen ","] ++ druckTraeger cs

/-- The address of a register: `@ e`, or nothing for the reader's default `.variable ""`. -/
def druckRegAdresse : SExpr → List Token
  | .variable "" => []
  | e => [.zeichen "@"] ++ druckToks e

/-- The class of a register with its `in`-stage words, or nothing for the empty class. -/
def druckRegKlasse (k : String) (st : List String) : List Token :=
  if strEq k "" then [] else [.wort "class", nameTok k] ++ druckPhasen st

/-- The bit fields of a register, or nothing. -/
def druckRegFelderTeil : List SRegFeld → List Token
  | [] => []
  | fs => [.wort "fields", .zeichen "{"] ++ druckRegFelder fs ++ [.zeichen "}"]

/-- The precondition of a register with its falsifier, or nothing. -/
def druckRegVoraus : Option SExpr → Option (String × String) → List Token
  | some p, some (a, b) => [.wort "requires"] ++ druckToks p ++ [.wort "else", nameTok a, .zeichen "::", nameTok b]
  | some p, none => [.wort "requires"] ++ druckToks p
  | none, _ => []

/-- The carriers of a register, or nothing. -/
def druckRegAbhaengt : List (List String) → List Token
  | [] => []
  | cs => [.wort "depends", .zeichen "{"] ++ druckTraeger cs ++ [.zeichen "}"]

/-- `reg n : T [@ e] [class c phases] [fields {…}] [requires p [else A::B]] [depends {…}]` (no `;`). -/
def druckReg (r : SReg) : List Token :=
  [.wort "reg", nameTok r.name, .zeichen ":"] ++ druckTyp r.rtyp ++ druckRegAdresse r.addr ++
    druckRegKlasse r.klasse r.stage ++ druckRegFelderTeil r.felder ++ druckRegVoraus r.voraus r.elseF ++
    druckRegAbhaengt r.abhaengt

def druckGerTeil : SGerTeil → List Token
  | .copy a b => [.wort "mirrors"] ++ druckToks a ++ [.wort "from"] ++ druckToks b ++ [.zeichen ";"]
  | .reg r => druckReg r
  | .bank s => rohToks s
  | .trans tr => druckTrans tr

def druckGerTeile : List SGerTeil → List Token
  | [] => []
  | g :: rest => druckGerTeil g ++ druckGerTeile rest

def druckBootSchritt : SBootSchritt → List Token
  | .call p args => [.wort "step"] ++ pfadToks p ++ [.zeichen "("] ++ druckPredListe args ++ [.zeichen ")", .zeichen ";"]
  | .set n e => [.wort "step", nameTok n, .zeichen "="] ++ druckToks e ++ [.zeichen ";"]

def druckBootSchritte : List SBootSchritt → List Token
  | [] => []
  | s :: rest => druckBootSchritt s ++ druckBootSchritte rest

def druckProfEintrag : SProfEintrag → List Token
  | .mode s v => [.wort s, nameTok v, .zeichen ";"]
  | .assum a => [.wort "assume", nameTok a, .zeichen ";"]

def druckProfEintraege : List SProfEintrag → List Token
  | [] => []
  | e :: rest => druckProfEintrag e ++ druckProfEintraege rest

end Gabbro.Grammatik.Parser
