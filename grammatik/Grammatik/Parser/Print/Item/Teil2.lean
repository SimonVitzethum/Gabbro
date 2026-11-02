module

public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Print.Item.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

mutual
/-- A start: the path, and its arguments in parentheses when it has any. -/
def druckStart (p : List String × List SExpr) : List Token :=
  rohToks ("::".intercalate p.1) ++
    (if p.2.isEmpty then [] else [.zeichen "("] ++ druckToksListe p.2 ++ [.zeichen ")"])

/-- The starts of a `concurrent` item, comma separated. -/
def druckStarts : List (List String × List SExpr) → List Token
  | [] => []
  | [p] => druckStart p
  | p :: ps => druckStart p ++ [.zeichen ","] ++ druckStarts ps

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
  | .tableT n von cnt backed owner sh parts =>
    ([.wort "table", nameTok n] ++
      (match cnt with
        | some e => [.wort "count"] ++ druckToks e
        | none => []) ++
      (match von with
        | some p => [.wort "from", nameTok p]
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
  | .concT ps => ([.wort "concurrent", .zeichen "{"] ++ druckStarts ps ++ [.zeichen "}", .zeichen ";"])
  | .gateT it => [.wort "when", .ident "TESTBUILD"] ++ druckItem it
  | .pubT it => .wort "pub" :: druckItem it
  | .adaptT sig ps a b =>
    ((if strEq sig.art "" then [] else [.wort sig.art]) ++ [.wort "fn", nameTok sig.name, .zeichen "("] ++
      druckAdaptParams ps ++ [.zeichen ")"] ++
      (match sig.res with
        | some t => [.zeichen "->"] ++ druckTyp t
        | none => []) ++
      (match sig.fehler with
        | some n => [.wort "or", nameTok n]
        | none => []) ++
      [.wort "from"] ++ rohToks a.quelle ++
      (match a.gebunden with
        | some g => [.wort "=>", nameTok g] ++ (match a.sonst with
          | some (e, blk) => [.wort "else", .zeichen "(", nameTok e, .zeichen ")"] ++ druckAnw blk
          | none => [])
        | none => []) ++
      druckKlauseln sig.klauseln ++
      (match a.vorspiel with
        | [] => []
        | ss => [.zeichen "["] ++ druckAnwListe ss ++ [.zeichen "]"]) ++
      (match b with
        | some blk => druckAnw blk
        | none => [.zeichen ";"])
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
    ([.wort "translator", nameTok sig.name, .wort "for"] ++ rohToks g ++ [.zeichen "("] ++ druckParams sig.params ++
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
