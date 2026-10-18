/-
  File:      Grammatik/Parser/Print/Item.lean
  Subject:   Track P: the token printer of items -- the inverse of `parseItemTief` on the item kinds the
             elaborator reads and on the forms around them: `module`, `use`, `fn` (signature, clauses,
             body; `;` and `= p ;` and `= asm {…} ;` bodies), `const`, `type`, `static`, `table`, `lock`,
             `concurrent` and the `when TESTBUILD` gate.

  `druckItem` is PARTIAL on purpose: a kind with no printer (`entry`, `device`, `format`, `arena`, `walk`, …)
  answers `none`, never a guess; `Cover/Census` counts how many items of the corpus have a printer and how
  many of those round-trip. Like the statement printer it is measured, not proved: the expression leaves
  ride `druckToks`, whose `gut` shapes have the round-trip theorem.
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
  | .masks n => [.wort "masks", .ident n]
  | .allocs n => [.wort "allocs", .ident n]
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
  | .arch n => [.wort "arch", .ident n]
  | .moves a b => [.wort "advances", .ident a, .zeichen "->", .ident b]
  | .quits s => [.wort "retires"] ++ rohToks s
  | .limit s => rohToks s
  | .effs es => [.wort "effects", .zeichen "{"] ++ druckEffekte es ++ [.zeichen "}"]

def druckKlauseln : List SKlausel → List Token
  | [] => []
  | k :: ks => druckKlausel k ++ druckKlauseln ks

def druckParam : String × STyp → List Token
  | (n, t) => [.ident n, .zeichen ":"] ++ druckTyp t

def druckParams : List (String × STyp) → List Token
  | [] => []
  | [p] => druckParam p
  | p :: ps => druckParam p ++ [.zeichen ","] ++ druckParams ps

/-- A function head: `[art] fn name (params) [-> T] [or R] clauses`. -/
def druckFnSig (s : FnSig) : List Token :=
  (if strEq s.art "" then [] else [.wort s.art]) ++ [.wort "fn", .ident s.name, .zeichen "("] ++
    druckParams s.params ++ [.zeichen ")"] ++
    (match s.res with
      | some t => [.zeichen "->"] ++ druckTyp t
      | none => []) ++
    (match s.fehler with
      | some n => [.wort "or", .ident n]
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
  [.ident f.fname, .zeichen ":"] ++ druckTyp f.ftyp ++
    (match f.pos with
      | some p => [.zeichen "@"] ++ rohToks p
      | none => []) ++
    (match f.bezug with
      | some n => [.wort "offset_into", .ident n]
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
  [.wort "invariant", .ident i.name, .wort "cost", .ident "O", .zeichen "("] ++ druckToks i.kosten ++
    [.zeichen ")", .wort "runs", .wort (if i.online then "online" else "offline")] ++
    (match i.proof with
      | some h => [.wort "by"] ++ rohToks h
      | none => []) ++
    [.zeichen ":"] ++ druckToks i.pred ++ [.zeichen ";"]

def druckKanten : List (String × String) → List Token
  | [] => []
  | [(a, b)] => [.wort a, .ident b]
  | (a, b) :: ks => [.wort a, .ident b, .zeichen ","] ++ druckKanten ks

def druckTabTeil : STabTeil → List Token
  | .tConst n t v => [.wort "const", .ident n, .zeichen ":"] ++ druckTyp t ++ [.zeichen "="] ++ druckKonstWert v ++ [.zeichen ";"]
  | .tSlot fs => [.wort "slot", .zeichen "{"] ++ druckFelder fs ++ [.zeichen "}"]
  | .tInv i => druckGruppenInv i
  | .tOps ns => [.wort "ops"] ++ druckNamen ns ++ [.zeichen ";"]
  | .tTree ks => [.wort "tree", .zeichen "{"] ++ druckKanten ks ++ [.zeichen "}"]
  | .tBusy n => [.wort "occupied", .ident n, .zeichen ";"]

def druckTabTeile : List STabTeil → List Token
  | [] => []
  | t :: ts => druckTabTeil t ++ druckTabTeile ts

/-- Place lists and paths in braces. -/
def druckPlaetze : List SExpr → List Token
  | [] => []
  | [p] => druckToks p
  | p :: ps => druckToks p ++ [.zeichen ","] ++ druckPlaetze ps

mutual
/-- An item as tokens; `none` for a kind without a printer. -/
def druckItem : SItemTief → Option (List Token)
  | .modT p its =>
    match druckItems its with
    | some ts => some ([.wort "module"] ++ rohToks p ++ [.zeichen "{"] ++ ts ++ [.zeichen "}"])
    | none => none
  | .useT p => some ([.wort "use"] ++ pfadToks p ++ [.zeichen ";"])
  | .typeT fl n args ord t =>
    some (fl.map (fun w => Token.wort w) ++ [.wort "type", .ident n] ++
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
    some ([.wort "const", .ident n, .zeichen ":"] ++ druckTyp t ++ [.zeichen "="] ++ druckKonstWert v ++ [.zeichen ";"])
  | .globT m n t v al s sh =>
    some ([.wort "static"] ++ (if m then [.wort "mut"] else []) ++ [.ident n, .zeichen ":"] ++ druckTyp t ++
      [.zeichen "="] ++ druckKonstWert v ++
      (match al with
        | some e => [.wort "aligned"] ++ druckToks e
        | none => []) ++
      (match s with
        | some x => [.wort "section", .text x]
        | none => []) ++
      (if sh then [.wort "shared"] else []) ++ [.zeichen ";"])
  | .fnT sig b => some (druckFnSig sig ++ druckAnw b)
  | .protoT sig => some (druckFnSig sig ++ [.zeichen ";"])
  | .specT sig p => some (druckFnSig sig ++ [.zeichen "="] ++ druckPred p ++ [.zeichen ";"])
  | .asmT sig h => some (druckFnSig sig ++ [.zeichen "="] ++ rohToks h ++ [.zeichen ";"])
  | .tableT n cnt backed owner sh parts =>
    some ([.wort "table", .ident n] ++
      (match cnt with
        | some e => [.wort "count"] ++ druckToks e
        | none => []) ++
      (match backed with
        | some b => [.wort "backed", .ident b]
        | none => []) ++
      (match owner with
        | some o => [.wort "owner", .ident o]
        | none => []) ++
      (if sh then [.wort "shared"] else []) ++ [.zeichen "{"] ++ druckTabTeile parts ++ [.zeichen "}"])
  | .lockT n ps rk h sh m inv =>
    some ([.wort "lock", .ident n, .wort "protects", .zeichen "{"] ++ druckPlaetze ps ++ [.zeichen "}", .wort "rank"] ++
      druckToks rk ++
      (match h with
        | some e => [.wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
        | none => []) ++
      (match sh with
        | some e => [.wort "shared", .wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
        | none => []) ++
      (match m with
        | some w => [.wort "masks", .ident w]
        | none => []) ++
      (match inv with
        | some p => [.wort "invariant"] ++ druckToks p
        | none => []) ++ [.zeichen ";"])
  | .concT ps => some ([.wort "concurrent", .zeichen "{"] ++ druckWurzeln (ps.map (fun p => "::".intercalate p)) ++ [.zeichen "}", .zeichen ";"])
  | .gateT it =>
    match druckItem it with
    | some ts => some ([.wort "when", .ident "TESTBUILD"] ++ ts)
    | none => none
  | _ => none
/-- A list of items as tokens; `none` as soon as one has no printer. -/
def druckItems : List SItemTief → Option (List Token)
  | [] => some []
  | it :: rest =>
    match druckItem it with
    | none => none
    | some ts =>
      match druckItems rest with
      | none => none
      | some us => some (ts ++ us)
/-- Type arguments of a `type`, comma separated. -/
def druckTypListe : List STyp → List Token
  | [] => []
  | [t] => druckTyp t
  | t :: ts => druckTyp t ++ [.zeichen ","] ++ druckTypListe ts
end

/-- The round trip of one item: print, read back as a whole program, compare by shape. `none` where the
    kind has no printer. -/
def rundlaufItem (it : SItemTief) : Option Bool :=
  match druckItem it with
  | none => none
  | some ts => some (beqTopTief (parseTopTief (ts ++ [.ende])) (.ok [it]))

end Gabbro.Grammatik.Parser
