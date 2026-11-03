module
public import Grammatik.Parser.Print.Item.Teil1a

public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Item.ElementTief

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

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
    (match b.resultArea with
      | none => []
      | some register => [.wort "result", .wort "area", nameTok register]) ++
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
