/-
  File:      Grammatik/Parser/Print/Item.lean
  Subject:   Track P: the token printer of items -- the inverse of `parseItemTief` on every item kind
             (`module`, `use`, `fn` with its clauses and bodies, `const`, `type`, `static`, `table`, `lock`,
             `concurrent`, `entry`, `device`, `format`, `arena`, `reason`, `state`, `atomic`, `syscall`,
             `target`, `assume`, `axiom`, `check`, `group`, `rcu`, `accumulates`, `walk`, `boot`, `entrust`,
             `profile`, `translator`, the `when TESTBUILD` gate).

  `druckItem` is total on the 35 item kinds. Like the statement printer it is measured, not proved:
  `Cover/Census` runs the round trip over every leaf item of the corpus (`ri=`); the expression leaves ride
  `druckToks`, whose `gut` shapes have the round-trip theorem.
-/
import Grammatik.Parser.Print.Stmt
import Grammatik.Parser.Item.ElementTief

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

/-- `reg n : T [@ e] [class c phases] [fields {…}] [requires p [else A::B]] [depends {…}]` (no `;`). -/
def druckReg (r : SReg) : List Token :=
  [.wort "reg", nameTok r.name, .zeichen ":"] ++ druckTyp r.rtyp ++
    (match r.addr with
      | .variable "" => []
      | e => [.zeichen "@"] ++ druckToks e) ++
    (if strEq r.klasse "" then [] else [.wort "class", nameTok r.klasse] ++ druckPhasen r.stage) ++
    (match r.felder with
      | [] => []
      | fs => [.wort "fields", .zeichen "{"] ++ druckRegFelder fs ++ [.zeichen "}"]) ++
    (match r.voraus with
      | some p => [.wort "requires"] ++ druckToks p ++
        (match r.elseF with
          | some (a, b) => [.wort "else", nameTok a, .zeichen "::", nameTok b]
          | none => [])
      | none => []) ++
    (match r.abhaengt with
      | [] => []
      | cs => [.wort "depends", .zeichen "{"] ++ druckTraeger cs ++ [.zeichen "}"])

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

mutual
/-- An item as tokens (the inverse of `parseItemTief`; total on every kind). -/
def druckItem : SItemTief → List Token
  | .modT p its => [.wort "module"] ++ rohToks p ++ [.zeichen "{"] ++ druckItems its ++ [.zeichen "}"]
  | .useT p => ([.wort "use"] ++ pfadToks p ++ [.zeichen ";"])
  | .typeT fl n args ord t =>
    (fl.map (fun w => Token.wort w) ++ [.wort "type", nameTok n] ++
      (match args with
        | [] => []
        | _ => [.zeichen "("] ++ druckTypListe args ++ [.zeichen ")"]) ++
      (match ord with
        | [] => []
        | _ => [.wort "order", .zeichen "{"] ++ druckNamen ord ++ [.zeichen "}"]) ++
      (match t with
        | some ty => [.zeichen "="] ++ druckTyp ty
        | none => []) ++ [.zeichen ";"])
  | .constT n t v =>
    ([.wort "const", nameTok n, .zeichen ":"] ++ druckTyp t ++ [.zeichen "="] ++ druckKonstWert v ++ [.zeichen ";"])
  | .globT m n t v al s sh =>
    ([.wort "static"] ++ (if m then [.wort "mut"] else []) ++ [nameTok n, .zeichen ":"] ++ druckTyp t ++
      [.zeichen "="] ++ druckKonstWert v ++
      (match al with
        | some e => [.wort "aligned"] ++ druckToks e
        | none => []) ++
      (match s with
        | some x => [.wort "section", .text x]
        | none => []) ++
      (if sh then [.wort "shared"] else []) ++ [.zeichen ";"])
  | .fnT sig b => (druckFnSig sig ++ druckAnw b)
  | .protoT sig => (druckFnSig sig ++ [.zeichen ";"])
  | .specT sig p => (druckFnSig sig ++ [.zeichen "="] ++ druckPred p ++ [.zeichen ";"])
  | .asmT sig h => (druckFnSig sig ++ [.zeichen "="] ++ rohToks h ++ [.zeichen ";"])
  | .tableT n cnt backed owner sh parts =>
    ([.wort "table", nameTok n] ++
      (match cnt with
        | some e => [.wort "count"] ++ druckToks e
        | none => []) ++
      (match backed with
        | some b => [.wort "backed", nameTok b]
        | none => []) ++
      (match owner with
        | some o => [.wort "owner", nameTok o]
        | none => []) ++
      (if sh then [.wort "shared"] else []) ++ [.zeichen "{"] ++ druckTabTeile parts ++ [.zeichen "}"])
  | .lockT n ps rk h sh m inv =>
    ([.wort "lock", nameTok n, .wort "protects", .zeichen "{"] ++ druckPlaetze ps ++ [.zeichen "}", .wort "rank"] ++
      druckToks rk ++
      (match h with
        | some e => [.wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
        | none => []) ++
      (match sh with
        | some e => [.wort "shared", .wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
        | none => []) ++
      (match m with
        | some w => [.wort "masks", nameTok w]
        | none => []) ++
      (match inv with
        | some p => [.wort "invariant"] ++ druckToks p
        | none => []) ++ [.zeichen ";"])
  | .concT ps => ([.wort "concurrent", .zeichen "{"] ++ druckWurzeln (ps.map (fun p => "::".intercalate p)) ++ [.zeichen "}", .zeichen ";"])
  | .gateT it => [.wort "when", .ident "TESTBUILD"] ++ druckItem it
  | .assumT n a s k =>
    ([.wort "assume", nameTok n] ++
      (match a with
        | some x => [.wort "arch", nameTok x]
        | none => []) ++ [.text s] ++ druckKlasse k ++ [.zeichen ";"])
  | .whyT n cs ex =>
    ([.wort "reason", nameTok n, .zeichen "{"] ++ druckGrundFaelle cs ++
      (if ex then [.wort "exhaustive"] else []) ++ [.zeichen "}"])
  | .atomT n ty pub ord obs =>
    ([.wort "atomic", nameTok n, .zeichen ":"] ++ druckTyp ty ++
      (match pub with
        | some [] => [.wort "publishes", .wort "nothing"]
        | some ps => [.wort "publishes", .zeichen "{"] ++ druckPlaetze ps ++ [.zeichen "}"]
        | none => []) ++
      (match ord with
        | some o => [.wort o]
        | none => []) ++
      (match obs with
        | some o => [.wort "observed", .wort "by", nameTok o]
        | none => []) ++ [.zeichen ";"])
  | .varT n => [.wort "syscall", nameTok n, .zeichen ";"]
  | .callT c =>
    ([.wort "syscall", nameTok c.name, .zeichen "("] ++ druckParams c.params ++ [.zeichen ")"] ++
      (match c.res with
        | some ty => [.zeichen "->"] ++ druckTyp ty
        | none => []) ++
      (match c.fail with
        | some n => [.wort "or", nameTok n]
        | none => []) ++
      (match c.way with
        | .via v => [.wort "via", nameTok v] ++ druckGate c.gate ++ [.zeichen ";"]
        | .lit abi arch bd hk =>
          [.wort "abi", nameTok abi, .wort "arch", nameTok arch] ++ druckBind bd ++ druckGate c.gate ++
            druckHerkunft hk))
  | .goalT n none => [.wort "target", nameTok n, .zeichen ";"]
  | .goalT n (some (abi, arch, bs)) =>
    ([.wort "target", nameTok n, .wort "abi", nameTok abi, .wort "arch", nameTok arch, .zeichen "{"] ++
      druckGoalBinds bs ++ [.zeichen "}"])
  | .entryT e => (druckEingang e)
  | .stateT n ts => ([.wort "state", nameTok n, .zeichen "{"] ++ druckTransListe ts ++ [.zeichen "}"])
  | .devT n ps sp ms =>
    ([.wort "device", nameTok n] ++
      (match ps with
        | [] => []
        | _ => [.zeichen "("] ++ druckParams ps ++ [.zeichen ")"]) ++
      [.wort "at", nameTok sp, .zeichen "{"] ++ druckGerTeile ms ++ [.zeichen "}"])
  | .arenaT n lo hi mx ty pb =>
    ([.wort "arena", nameTok n, .wort "capacity"] ++ druckToks lo ++ [.zeichen ".."] ++ druckToks hi ++
      (match mx with
        | some m => [.wort "max"] ++ druckToks m
        | none => []) ++ [.wort "of"] ++ druckTyp ty ++
      (match pb with
        | some (p, e) => [.ident "pb"] ++ pfadToks p ++ [.ident "blw"] ++ druckToks e
        | none => []) ++ [.zeichen ";"])
  | .formatT n ver en fs =>
    ([.wort "format", nameTok n] ++
      (match ver with
        | some v => [.zeichen "@", .ident "version"] ++ druckToks v
        | none => []) ++
      (match en with
        | some m => [.wort "endian", .wort m]
        | none => []) ++ [.zeichen "{"] ++ druckFelder fs ++ [.zeichen "}"])
  | .transT g sig b =>
    ([.wort "translator", nameTok sig.name, .wort "for", nameTok g, .zeichen "("] ++ druckParams sig.params ++
      [.zeichen ")"] ++
      (match sig.res with
        | some ty => [.zeichen "->"] ++ druckTyp ty
        | none => []) ++
      (match sig.fehler with
        | some n => [.wort "or", nameTok n]
        | none => []) ++ druckKlauseln sig.klauseln ++ druckAnw b)
  | .rcuT n ps rec =>
    ([.wort "rcu", nameTok n, .wort "protects", .zeichen "{"] ++ druckPlaetze ps ++ [.zeichen "}"] ++
      (match rec with
        | some p => [.wort "reclaims"] ++ druckToks p
        | none => []) ++ [.zeichen ";"])
  | .groupT n ms ivs =>
    ([.wort "group", nameTok n, .wort "over"] ++ druckNamenKlammer ms ++
      (match ivs with
        | [] => [.zeichen ";"]
        | _ => [.zeichen "{"] ++ druckGruppenInvs ivs ++ [.zeichen "}"]))
  | .accT n ty m p =>
    ([.wort "accumulates", nameTok n, .zeichen ":"] ++ druckTyp ty ++ [.wort "merge", .wort m] ++
      (match p with
        | some e => [.wort "per", .wort "cpu"] ++ druckToks e
        | none => []) ++ [.zeichen ";"])
  | .walkT w =>
    ([.wort "walk", nameTok w.name, .wort "levels"] ++ druckToks w.stufen ++
      [.zeichen "{", .wort "node", .zeichen ":"] ++ druckTyp w.node ++
      [.zeichen ",", .wort "down", .zeichen ":", nameTok w.dname, .wort "when"] ++ druckToks w.dwhen ++
      [.zeichen ",", .wort "leaf", .zeichen ":"] ++ druckToks w.blatt ++
      (match w.invarianten with
        | [] => []
        | ivs => [.zeichen ","] ++ druckGruppenInvs ivs) ++ [.zeichen "}"])
  | .bootT n a ss dp =>
    ([.wort "boot", nameTok n, .wort "arch", nameTok a, .zeichen "{"] ++ druckBootSchritte ss ++
      [.wort "dispatch"] ++ pfadToks dp ++ [.zeichen ";", .zeichen "}"])
  | .trustT n m a ri st g =>
    ([.wort "entrust", nameTok n, .wort "at", nameTok m, .wort "arch", nameTok a, .zeichen "{",
      .wort "regs", .wort "in", .zeichen "{"] ++ druckRegBinds ri ++
      [.zeichen "}", .wort "stack", nameTok st, .wort "assume", nameTok g, .zeichen ";", .zeichen "}"])
  | .profT bedarf es =>
    ((if bedarf then [Token.wort "requires"] else []) ++ [.wort "profile", .zeichen "{"] ++
      druckProfEintraege es ++ [.zeichen "}", .zeichen ";"])
  | .axiomT n ps erg pre es k =>
    ([.wort "axiom", nameTok n, .zeichen "("] ++ druckParams ps ++ [.zeichen ")"] ++
      (match erg with
        | some ty => [.zeichen "->"] ++ druckTyp ty
        | none => []) ++
      (match pre with
        | some p => [.wort "requires"] ++ druckPred p
        | none => []) ++ [.wort "effects", .zeichen "{"] ++ druckEffekte es ++ [.zeichen "}"] ++
      druckKlasse k ++ [.zeichen ";"])
  | .checkT c =>
    ([.wort "check", nameTok c.cname, .zeichen "{", .wort "claim", .text c.claim, .wort "measures"] ++
      druckPredListe c.misst ++ [.wort "gates"] ++ druckNamen c.gates ++ [.wort "can_fail"] ++
      druckAnw c.canFail ++
      (match c.boden with
        | [] => []
        | ps => [.wort "floor"] ++ druckPredListe ps) ++
      (match c.sonde with
        | some (s, e) => [.wort "counterprobe", .text s, .wort "expects", nameTok e]
        | none => []) ++ [.zeichen "}"])
/-- A list of items as tokens. -/
def druckItems : List SItemTief → List Token
  | [] => []
  | it :: rest => druckItem it ++ druckItems rest
/-- Invariants of a group or a walk (each ends in `;`). -/
def druckGruppenInvs : List SGruppenInv → List Token
  | [] => []
  | i :: rest => druckGruppenInv i ++ druckGruppenInvs rest
/-- Type arguments of a `type`, comma separated. -/
def druckTypListe : List STyp → List Token
  | [] => []
  | [t] => druckTyp t
  | t :: ts => druckTyp t ++ [.zeichen ","] ++ druckTypListe ts
end

/-- The round trip of one item: print, read back as a whole program, compare by shape. -/
def rundlaufItem (it : SItemTief) : Bool :=
  beqTopTief (parseTopTief (druckItem it ++ [.ende])) (.ok [it])

end Gabbro.Grammatik.Parser
