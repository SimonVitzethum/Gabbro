module

public import Grammatik.Parser.Stmt.Anweisung

@[expose] public section



namespace Gabbro.Grammatik.Parser

/-- The pure prefix words before an item head (`parse.rs` `item`:
    `pub` plus the `fn`/`type` modifiers; `const` is NOT among them
    -- `const fn` splits on the next word, as in `parse.rs`). -/
def istMod (s : String) : Bool :=
  ["library", "spec", "impl", "raw", "divergent", "prim", "extern",
   "opaque", "linear", "ghost", "tagged"].any (strEq · s)

set_option maxRecDepth 100000

/- A surface effect: one arm of SYNTAX.md section 6 `eff`
    (`efflist`), the place arms as `SExpr` (`parse.rs` reads them
    as places; this reader has no `pred` reader, so contracts ride
    `SExpr` too -- see CUTS). `locks` carries the `shared` flag. -/
inductive SEffekt
  | reads : SExpr → SEffekt
  | writes : SExpr → SEffekt
  | locks : Bool → SExpr → SEffekt
  | masks : String → SEffekt
  | allocs : String → SEffekt
  | takes : SExpr → SEffekt
  | posts : SExpr → SEffekt
  | loops : SEffekt
  | pure : SEffekt
  deriving Repr

mutual
def beqSEffekt : SEffekt → SEffekt → Bool
  | .reads a, .reads b => beqSExpr a b
  | .writes a, .writes b => beqSExpr a b
  | .locks x a, .locks y b => (x == y) && beqSExpr a b
  | .masks a, .masks b => strEq a b
  | .allocs a, .allocs b => strEq a b
  | .takes a, .takes b => beqSExpr a b
  | .posts a, .posts b => beqSExpr a b
  | .loops, .loops => true
  | .pure, .pure => true
  | _, _ => false
def beqSEffektList : List SEffekt → List SEffekt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSEffekt x y && beqSEffektList xs ys
  | _, _ => false
end

/- One contract clause of SYNTAX.md section 6 `fndecl`: `voraus`
    and `gives` ride one `SExpr` each (a `pred` is an `expr`
    shape here -- no `pred` reader, see CUTS); `erhaelt` and
    `refs` ride name lists; `kosten` the `<= e ops`
    expression; `faellt` the `decreases` measure; `induktion` the
    raw `by` tail; `nutzlast` the `payload` path; `part` the
    `section` text; `arch` the `arch` name; `moves`
    the `advances a -> b` pair; `quits` the raw `retires`
    tail; `frist` the raw `deadline` tail (both raw tails are
    delimited, not interpreted -- see CUTS). -/
inductive SKlausel
  | needs : SExpr → SKlausel
  | gives : SExpr → SKlausel
  | keeps : List String → SKlausel
  | refs : List String → SKlausel
  | cost : SExpr → SKlausel
  | drops : SExpr → SKlausel
  | induc : String → SKlausel
  | load : List String → SKlausel
  | part : String → SKlausel
  | arch : String → SKlausel
  | moves : String → String → SKlausel
  | quits : String → SKlausel
  | limit : String → SKlausel
  | effs : List SEffekt → SKlausel
  deriving Repr

mutual
def beqSKlausel : SKlausel → SKlausel → Bool
  | .needs a, .needs b => beqSExpr a b
  | .gives a, .gives b => beqSExpr a b
  | .keeps a, .keeps b => beqWorte a b
  | .refs a, .refs b => beqWorte a b
  | .cost a, .cost b => beqSExpr a b
  | .drops a, .drops b => beqSExpr a b
  | .induc a, .induc b => strEq a b
  | .load a, .load b => beqWorte a b
  | .part a, .part b => strEq a b
  | .arch a, .arch b => strEq a b
  | .moves a b, .moves c d => strEq a c && strEq b d
  | .quits a, .quits b => strEq a b
  | .limit a, .limit b => strEq a b
  | .effs a, .effs b => beqSEffektList a b
  | _, _ => false
def beqSKlauselList : List SKlausel → List SKlausel → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSKlausel x y && beqSKlauselList xs ys
  | _, _ => false
end

/- A function head: SYNTAX.md section 6 `fndecl` up to the body.
    `art` is the modifier word (`impl`, `spec`, `library`,
    `const`, `raw`, `divergent`, `prim`, `extern`, else `""` for a
    plain `fn`); `fehler` the `or R` channel; `klauseln` every
    contract clause in source order. The body rides outside
    (`fnT`/`protoT`/`specT`/`asmT` below). -/
structure FnSig where
  art : String
  name : String
  params : List (String × STyp)
  res : Option STyp
  fehler : Option String
  klauseln : List SKlausel
  deriving Repr

def beqParam : (String × STyp) → (String × STyp) → Bool
  | (a, x), (b, y) => strEq a b && beqSTyp x y

def beqParamList : List (String × STyp) → List (String × STyp) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqParam x y && beqParamList xs ys
  | _, _ => false

def beqFnSig : FnSig → FnSig → Bool
  | s, t => strEq s.art t.art && strEq s.name t.name &&
    beqParamList s.params t.params && beqSTypOpt s.res t.res &&
    beqOptWort s.fehler t.fehler && beqSKlauselList s.klauseln t.klauseln

/- One slot/format field: SYNTAX.md sections 9-10 `slotfeld`
    and `field`. `pos` is the raw `@bitpos`, `bezug` the raw
    `offset_into` target, `wo` the `where` predicate, `reserviert`
    the `reserved` flag and `byOps` the `by ops` flag (slots
    only). -/
structure SFeld where
  fname : String
  ftyp : STyp
  pos : Option String
  bezug : Option String
  wo : Option SExpr
  reserviert : Bool
  byOps : Bool
  deriving Repr

def beqSFeld : SFeld → SFeld → Bool
  | a, b => strEq a.fname b.fname && beqSTyp a.ftyp b.ftyp &&
    beqOptWort a.pos b.pos && beqOptWort a.bezug b.bezug &&
    beqOptExpr a.wo b.wo && (a.reserviert == b.reserviert) &&
    (a.byOps == b.byOps)

def beqSFeldList : List SFeld → List SFeld → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSFeld x y && beqSFeldList xs ys
  | _, _ => false

/- One register bit field: SYNTAX.md section 10 `regfeld`. -/
structure SRegFeld where
  name : String
  pos : String
  klasse : Option String
  deriving Repr

def beqSRegFeld : SRegFeld → SRegFeld → Bool
  | a, b => strEq a.name b.name && strEq a.pos b.pos &&
    beqOptWort a.klasse b.klasse

def beqSRegFeldList : List SRegFeld → List SRegFeld → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSRegFeld x y && beqSRegFeldList xs ys
  | _, _ => false

def beqWortListe : List (List String) → List (List String) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqWorte x y && beqWortListe xs ys
  | _, _ => false

def beqStartListe : List (List String × List SExpr) → List (List String × List SExpr) → Bool
  | [], [] => true
  | (p, a) :: xs, (q, b) :: ys => beqWorte p q && beqSExprList a b && beqStartListe xs ys
  | _, _ => false

def beqOptPaarWort : Option (String × String) → Option (String × String) → Bool
  | none, none => true
  | some (a, b), some (c, d) => strEq a c && strEq b d
  | _, _ => false

/- One device register: SYNTAX.md section 10 `regdecl`. `stage`
    rides the raw `in`-stage words in order, `elseF` the
    `else A::B` falsifier and `abhaengt` the `depends` carriers
    (each one or two segments). -/
structure SReg where
  name : String
  rtyp : STyp
  addr : SExpr
  klasse : String
  stage : List String
  felder : List SRegFeld
  voraus : Option SExpr
  elseF : Option (String × String)
  abhaengt : List (List String)
  deriving Repr

def beqSReg : SReg → SReg → Bool
  | a, b => strEq a.name b.name && beqSTyp a.rtyp b.rtyp &&
    beqSExpr a.addr b.addr &&
    strEq a.klasse b.klasse && beqWorte a.stage b.stage &&
    beqSRegFeldList a.felder b.felder && beqOptExpr a.voraus b.voraus &&
    beqOptPaarWort a.elseF b.elseF &&
    beqWortListe a.abhaengt b.abhaengt

/- One state transition: SYNTAX.md sections 9-10 `transition`. A
    step is (place, from, to); every side rides `SExpr` (a
    `shiftplace` is a dotted/indexed name, which is an expression
    shape). -/
structure STrans where
  tname : String
  schritte : List (SExpr × SExpr × SExpr)
  voraus : Option SExpr
  wirkung : List SEffekt
  deriving Repr


end Gabbro.Grammatik.Parser
