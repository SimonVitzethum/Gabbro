/-
  File:      Grammatik/Parser/ElementTief.lean
  Subject:   T3 PART 3: Gabbro items in depth (SYNTAX.md sections 1-2,
               6, 9-14) over the Lean statement reader.

  The surface types `STyp`/`SEffekt`/`SKlausel`/`FnSig`/`SItemTief`
  with fuel-indexed readers (`parseItemTief`, `parseTopTief`).
  Probes live in `Parser/Item/ElementTiefProben1..7.lean`.
-/
import Grammatik.Parser.Stmt.Anweisung

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

def beqSchritt3 : (SExpr × SExpr × SExpr) → (SExpr × SExpr × SExpr) → Bool
  | (a, b, c), (d, e, f) => beqSExpr a d && beqSExpr b e && beqSExpr c f

def beqSchritt3List : List (SExpr × SExpr × SExpr) → List (SExpr × SExpr × SExpr) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSchritt3 x y && beqSchritt3List xs ys
  | _, _ => false

def beqSTrans : STrans → STrans → Bool
  | a, b => strEq a.tname b.tname &&
    beqSchritt3List a.schritte b.schritte &&
    beqOptExpr a.voraus b.voraus && beqSEffektList a.wirkung b.wirkung

def beqSTransList : List STrans → List STrans → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSTrans x y && beqSTransList xs ys
  | _, _ => false

/- One invariant: SYNTAX.md section 9 `invariant` (table and group
    share the production). `kosten` is the `O(…)` expression,
    `online` the `runs` mode and `proof` the raw `by` tail. -/
structure SGruppenInv where
  name : String
  kosten : SExpr
  online : Bool
  proof : Option String
  pred : SExpr
  deriving Repr

def beqSGruppenInv : SGruppenInv → SGruppenInv → Bool
  | a, b => strEq a.name b.name && beqSExpr a.kosten b.kosten &&
    (a.online == b.online) && beqOptWort a.proof b.proof &&
    beqSExpr a.pred b.pred

def beqSGruppenInvList : List SGruppenInv → List SGruppenInv → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSGruppenInv x y && beqSGruppenInvList xs ys
  | _, _ => false

/- A `const` value: SYNTAX.md section 1 `constwert` -- a plain
    expression or an array literal (lane 111). -/
inductive SKonstWert
  | one : SExpr → SKonstWert
  | rows : List SKonstWert → SKonstWert
  deriving Repr

mutual
def beqSKonstWert : SKonstWert → SKonstWert → Bool
  | .one a, .one b => beqSExpr a b
  | .rows a, .rows b => beqSKonstWertList a b
  | _, _ => false
def beqSKonstWertList : List SKonstWert → List SKonstWert → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSKonstWert x y && beqSKonstWertList xs ys
  | _, _ => false
end

/- One table member: SYNTAX.md section 9 `table` (`constdecl` /
    `slotdecl` / `invariant` / `opdecl` / `treedecl` / `occdecl`).
    A `tTree` pair is (edge kind, field). -/
inductive STabTeil
  | tConst : String → STyp → SKonstWert → STabTeil
  | tSlot : List SFeld → STabTeil
  | tInv : SGruppenInv → STabTeil
  | tOps : List String → STabTeil
  | tTree : List (String × String) → STabTeil
  | tBusy : String → STabTeil
  deriving Repr

def beqKanteList : List (String × String) → List (String × String) → Bool
  | [], [] => true
  | (a, b) :: xs, (c, d) :: ys =>
    strEq a c && strEq b d && beqKanteList xs ys
  | _, _ => false

mutual
def beqSTabTeil : STabTeil → STabTeil → Bool
  | .tConst a t v, .tConst b u w =>
    strEq a b && beqSTyp t u && beqSKonstWert v w
  | .tSlot a, .tSlot b => beqSFeldList a b
  | .tInv a, .tInv b => beqSGruppenInv a b
  | .tOps a, .tOps b => beqWorte a b
  | .tTree a, .tTree b => beqKanteList a b
  | .tBusy a, .tBusy b => strEq a b
  | _, _ => false
def beqSTabTeilList : List STabTeil → List STabTeil → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSTabTeil x y && beqSTabTeilList xs ys
  | _, _ => false
end

/- One device member: SYNTAX.md section 10 (`mirrors` / `regdecl` /
    `bank` / `transition`). A bank rides raw and balanced (see
    CUTS); registers and transitions ride in depth. -/
inductive SGerTeil
  | copy : SExpr → SExpr → SGerTeil
  | reg : SReg → SGerTeil
  | bank : String → SGerTeil
  | trans : STrans → SGerTeil
  deriving Repr

mutual
def beqSGerTeil : SGerTeil → SGerTeil → Bool
  | .copy a b, .copy c d => beqSExpr a c && beqSExpr b d
  | .reg a, .reg b => beqSReg a b
  | .bank a, .bank b => strEq a b
  | .trans a, .trans b => beqSTrans a b
  | _, _ => false
def beqSGerTeilList : List SGerTeil → List SGerTeil → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSGerTeil x y && beqSGerTeilList xs ys
  | _, _ => false
end

/- The assumption class: SYNTAX.md section 12 (`falsifier`
    vs `unfalsifiable`). Plain equality (no recursion). -/
inductive SAnKlasse
  | probe : String → SAnKlasse
  | trust : String → SAnKlasse
  deriving Repr

def beqSAnKlasse : SAnKlasse → SAnKlasse → Bool
  | .probe a, .probe b => strEq a b
  | .trust a, .trust b => strEq a b
  | _, _ => false

/- One profile entry: SYNTAX.md section 12.2 `profileentry` -- a
    keyed mode (`arch x86_64`) or an assumption reference. -/
inductive SProfEintrag
  | mode : String → String → SProfEintrag
  | assum : String → SProfEintrag
  deriving Repr

def beqSProfEintrag : SProfEintrag → SProfEintrag → Bool
  | .mode a b, .mode c d => strEq a c && strEq b d
  | .assum a, .assum b => strEq a b
  | _, _ => false

def beqSProfEintragList : List SProfEintrag → List SProfEintrag → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSProfEintrag x y && beqSProfEintragList xs ys
  | _, _ => false

/- One register binding: SYNTAX.md sections 12.1/14 `regbind` --
    `rdi = fd` binds, bare `rax` only names (the `:` spelling is
    accepted beside `=`, as the examples write both). -/
inductive SRegBind
  | binds : String → String → SRegBind
  | reg : String → SRegBind
  deriving Repr

def beqSRegBind : SRegBind → SRegBind → Bool
  | .binds a b, .binds c d => strEq a c && strEq b d
  | .reg a, .reg b => strEq a b
  | _, _ => false

def beqSRegBindList : List SRegBind → List SRegBind → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSRegBind x y && beqSRegBindList xs ys
  | _, _ => false

/- One boot step: SYNTAX.md section 14 `bootstep` -- a call or a
    `name = constexpr` assignment. -/
inductive SBootSchritt
  | call : List String → List SExpr → SBootSchritt
  | set : String → SExpr → SBootSchritt
  deriving Repr

def beqSBootSchritt : SBootSchritt → SBootSchritt → Bool
  | .call a b, .call c d =>
    beqWorte a c && beqSExprList b d
  | .set a b, .set c d => strEq a c && beqSExpr b d
  | _, _ => false

def beqSBootSchrittList : List SBootSchritt → List SBootSchritt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSBootSchritt x y && beqSBootSchrittList xs ys
  | _, _ => false

/- A `walk` declaration: SYNTAX.md section 9 `walkdecl`. -/
structure SWeg where
  name : String
  stufen : SExpr
  node : STyp
  dname : String
  dwhen : SExpr
  blatt : SExpr
  invarianten : List SGruppenInv
  deriving Repr

def beqSWeg : SWeg → SWeg → Bool
  | a, b => strEq a.name b.name && beqSExpr a.stufen b.stufen &&
    beqSTyp a.node b.node && strEq a.dname b.dname &&
    beqSExpr a.dwhen b.dwhen && beqSExpr a.blatt b.blatt &&
    beqSGruppenInvList a.invarianten b.invarianten

/- An `entry` declaration: SYNTAX.md section 1 `entrydecl`.
    `stapel`/`perCpu`/`ist`/`nest` are the `entryextra`
    tail; `dispatch` the dispatch path. -/
structure SEingang where
  name : String
  vektor : Option SExpr
  via : Option String
  arch : String
  regIn : List SRegBind
  regOut : List SRegBind
  erhaelt : List String
  kills : List String
  stapel : String
  perCpu : Bool
  ist : Option SExpr
  nest : Option String
  dispatch : List String
  deriving Repr

def beqSEingang : SEingang → SEingang → Bool
  | a, b => strEq a.name b.name && beqOptExpr a.vektor b.vektor &&
    beqOptWort a.via b.via && strEq a.arch b.arch &&
    beqSRegBindList a.regIn b.regIn &&
    beqSRegBindList a.regOut b.regOut &&
    beqWorte a.erhaelt b.erhaelt && beqWorte a.kills b.kills &&
    strEq a.stapel b.stapel && (a.perCpu == b.perCpu) &&
    beqOptExpr a.ist b.ist && beqOptWort a.nest b.nest &&
    beqWorte a.dispatch b.dispatch

/- A `check` declaration: SYNTAX.md section 13. The `can_fail`
    body rides `SAnw` (via `parseBlock`); `sonde` is the
    `counterprobe ... expects ...` pair. -/
structure SCheck where
  cname : String
  claim : String
  misst : List SExpr
  gates : List String
  canFail : SAnw
  boden : List SExpr
  sonde : Option (String × String)
  deriving Repr

def beqSCheck : SCheck → SCheck → Bool
  | a, b => strEq a.cname b.cname && strEq a.claim b.claim &&
    beqSExprList a.misst b.misst && beqWorte a.gates b.gates &&
    beqSAnw a.canFail b.canFail &&
    beqSExprList a.boden b.boden && beqOptPaarWort a.sonde b.sonde

/- Where a `syscall` rests: SYNTAX.md section 12.1 (a named
    assumption with its falsifier, or a `kernel` dispatch path). -/
inductive SHerkunft
  | assum : String → SAnKlasse → SHerkunft
  | core : List String → SHerkunft
  deriving Repr

def beqSHerkunft : SHerkunft → SHerkunft → Bool
  | .assum a b, .assum c d =>
    strEq a c && beqSAnKlasse b d
  | .core a, .core b => beqWorte a b
  | _, _ => false

/- The binding of a gate to one kernel ABI: SYNTAX.md section 12.1 `sysbind`. `codes` is the
    `errors` map (`errno [= n] => Ground`), `stack` the handed-stack registers. -/
structure SBind where
  id : SExpr
  ins : List SRegBind
  outs : List SRegBind
  stack : List String
  dirty : List String
  codes : List (String × Option SExpr × String)
  deriving Repr

def beqErrsList : List (String × Option SExpr × String) →
    List (String × Option SExpr × String) → Bool
  | [], [] => true
  | (a, n, b) :: xs, (c, m, d) :: ys =>
    strEq a c && beqOptExpr n m && strEq b d && beqErrsList xs ys
  | _, _ => false

def beqSBind : SBind → SBind → Bool
  | a, b => beqSExpr a.id b.id && beqSRegBindList a.ins b.ins &&
    beqSRegBindList a.outs b.outs && beqWorte a.stack b.stack &&
    beqWorte a.dirty b.dirty && beqErrsList a.codes b.codes

/- The contract of a gate: SYNTAX.md section 12.1 `syscontract`. -/
structure SGate where
  pre : List SExpr
  post : List SExpr
  uses : List SEffekt
  cost : Option SExpr
  deriving Repr

def beqSGate : SGate → SGate → Bool
  | a, b => beqSExprList a.pre b.pre && beqSExprList a.post b.post &&
    beqSEffektList a.uses b.uses && beqOptExpr a.cost b.cost

/- How a gate is bound: literally (`abi A arch X <sysbind> <pair>`) or through a variable
    (`via V`, SYNTAX.md section 12.3). -/
inductive SWay
  | lit : String → String → SBind → SHerkunft → SWay
  | via : String → SWay
  deriving Repr

def beqSWay : SWay → SWay → Bool
  | .lit a x b h, .lit c y d k => strEq a c && strEq x y && beqSBind b d && beqSHerkunft h k
  | .via a, .via b => strEq a b
  | _, _ => false

/- A `syscall` gate: SYNTAX.md section 12.1 `syscalldecl`. -/
structure SSyscall where
  name : String
  params : List (String × STyp)
  res : Option STyp
  fail : Option String
  way : SWay
  gate : SGate
  deriving Repr

def beqSSyscall : SSyscall → SSyscall → Bool
  | a, b => strEq a.name b.name &&
    beqParamList a.params b.params &&
    beqSTypOpt a.res b.res && beqOptWort a.fail b.fail &&
    beqSWay a.way b.way && beqSGate a.gate b.gate

def beqGoalBinds : List (String × SBind × SHerkunft) → List (String × SBind × SHerkunft) → Bool
  | [], [] => true
  | (a, b, h) :: xs, (c, d, k) :: ys =>
    strEq a c && beqSBind b d && beqSHerkunft h k && beqGoalBinds xs ys
  | _, _ => false

def beqGoalOpt : Option (String × String × List (String × SBind × SHerkunft)) →
    Option (String × String × List (String × SBind × SHerkunft)) → Bool
  | none, none => true
  | some (a, x, bs), some (b, y, cs) => strEq a b && strEq x y && beqGoalBinds bs cs
  | _, _ => false

def beqOptExprList : Option (List SExpr) → Option (List SExpr) → Bool
  | none, none => true
  | some a, some b => beqSExprList a b
  | _, _ => false

def beqGrundFallList : List (String × SExpr × String) → List (String × SExpr × String) → Bool
  | [], [] => true
  | (a, b, c) :: xs, (d, e, f) :: ys =>
    strEq a d && beqSExpr b e && strEq c f && beqGrundFallList xs ys
  | _, _ => false

/- A surface item in depth: SYNTAX.md section 1 `item`. Against
    `ast.rs` `ItemArt` (see also `SItem` in `Element.lean`, which
    shares the shape but skips every body): `modT` = `Modul`,
    `useT` = `Use`, `typeT` = `Typ`, `constT` = `Konst`, `globT` =
    `Statisch`, `fnT` = `Funktion`, `protoT` = a bodiless
    declaration (`fn …;`), `specT` = `spec fn … = pred;`,
    `asmT` = `= asm {…};`, `formatT` = `Format`, `tableT` =
    `Tabelle`, `arenaT` = `Arena`, `whyT` = `Reason`,
    `stateT` = `State`, `devT` = `Device`, `assumT` =
    `Assume`, `axiomT` = `Axiom`, `checkT` = `Check`,
    `atomT` = `Atomic`, `lockT` = `Lock`, `rcuT` = `Rcu`,
    `groupT` = `Gruppe`, `concT` = `Concurrent`, `accT` =
    `Accumulates`, `walkT` = `Walk`, `entryT` = `Entry`,
    `trustT` = `Entrust`, `startT` = `Boot`, `callT` =
    `Syscall`, `transT` = `Translator`, `profT` =
    `Profil` / `ProfilBedarf` (`bedarf` flag), `gateT` = the `when
    TESTBUILD` gate. -/
inductive SItemTief
  | modT : String → List SItemTief → SItemTief
  | useT : List String → SItemTief
  | typeT : List String → String → List STyp → List String → Option STyp → SItemTief
  | constT : String → STyp → SKonstWert → SItemTief
  | globT : Bool → String → STyp → SKonstWert → Option SExpr → Option String → Bool → SItemTief
  | fnT : FnSig → SAnw → SItemTief
  | protoT : FnSig → SItemTief
  | specT : FnSig → SExpr → SItemTief
  | asmT : FnSig → String → SItemTief
  | formatT : String → Option SExpr → Option String → List SFeld → SItemTief
  | tableT : String → Option SExpr → Option String → Option String → Bool → List STabTeil → SItemTief
  | arenaT : String → SExpr → SExpr → Option SExpr → STyp → Option (List String × SExpr) → SItemTief
  | whyT : String → List (String × SExpr × String) → Bool → SItemTief
  | stateT : String → List STrans → SItemTief
  | devT : String → List (String × STyp) → String → List SGerTeil → SItemTief
  | assumT : String → Option String → String → SAnKlasse → SItemTief
  | axiomT : String → List (String × STyp) → Option STyp → Option SExpr → List SEffekt → SAnKlasse → SItemTief
  | checkT : SCheck → SItemTief
  | atomT : String → STyp → Option (List SExpr) → Option String → Option String → SItemTief
  | lockT : String → List SExpr → SExpr → Option SExpr → Option SExpr → Option String → Option SExpr → SItemTief
  | rcuT : String → List SExpr → Option SExpr → SItemTief
  | groupT : String → List String → List SGruppenInv → SItemTief
  | concT : List (List String) → SItemTief
  | accT : String → STyp → String → Option SExpr → SItemTief
  | walkT : SWeg → SItemTief
  | entryT : SEingang → SItemTief
  | trustT : String → String → String → List SRegBind → String → String → SItemTief
  | bootT : String → String → List SBootSchritt → List String → SItemTief
  | callT : SSyscall → SItemTief
  /-- `syscall V;`: a system call as a named variable (SYNTAX.md 12.3). -/
  | varT : String → SItemTief
  /-- `target T;` (the selection) or `target T abi A arch X { V = … }` (the bindings). -/
  | goalT : String → Option (String × String × List (String × SBind × SHerkunft)) → SItemTief
  | transT : String → FnSig → SAnw → SItemTief
  | profT : Bool → List SProfEintrag → SItemTief
  | gateT : SItemTief → SItemTief
  deriving Repr

def beqOptPathExpr : Option (List String × SExpr) → Option (List String × SExpr) → Bool
  | none, none => true
  | some (a, x), some (b, y) => beqWorte a b && beqSExpr x y
  | _, _ => false

mutual
def beqSItemTief : SItemTief → SItemTief → Bool
  | .modT a b, .modT c d => strEq a c && beqSItemTiefList b d
  | .useT a, .useT b => beqWorte a b
  | .typeT f1 a t1 o1 r1, .typeT f2 b t2 o2 r2 =>
    beqWorte f1 f2 && strEq a b && beqSTypList t1 t2 &&
    beqWorte o1 o2 && beqSTypOpt r1 r2
  | .constT a t v, .constT b u w =>
    strEq a b && beqSTyp t u && beqSKonstWert v w
  | .globT m1 a t v l1 s1 g1, .globT m2 b u w l2 s2 g2 =>
    (m1 == m2) && strEq a b && beqSTyp t u && beqSKonstWert v w &&
    beqOptExpr l1 l2 && beqOptWort s1 s2 && (g1 == g2)
  | .fnT s b, .fnT t d => beqFnSig s t && beqSAnw b d
  | .protoT s, .protoT t => beqFnSig s t
  | .specT s p, .specT t q => beqFnSig s t && beqSExpr p q
  | .asmT s a, .asmT t b => beqFnSig s t && strEq a b
  | .formatT a v e f, .formatT b w g h =>
    strEq a b && beqOptExpr v w && beqOptWort e g && beqSFeldList f h
  | .tableT a c b o g p, .tableT d f e h i q =>
    strEq a d && beqOptExpr c f && beqOptWort b e &&
    beqOptWort o h && (g == i) && beqSTabTeilList p q
  | .arenaT a l h x t p, .arenaT b m i y u q =>
    strEq a b && beqSExpr l m && beqSExpr h i && beqOptExpr x y && beqSTyp t u &&
    beqOptPathExpr p q
  | .whyT a c e, .whyT b d f =>
    strEq a b && beqGrundFallList c d && (e == f)
  | .stateT a t, .stateT b u => strEq a b && beqSTransList t u
  | .devT a p s m, .devT b q t n =>
    strEq a b && beqParamList p q && strEq s t && beqSGerTeilList m n
  | .assumT a c t k, .assumT b d u l =>
    strEq a b && beqOptWort c d && strEq t u && beqSAnKlasse k l
  | .axiomT a p r q e k, .axiomT b s t u f l =>
    strEq a b && beqParamList p s && beqSTypOpt r t &&
    beqOptExpr q u && beqSEffektList e f && beqSAnKlasse k l
  | .checkT a, .checkT b => beqSCheck a b
  | .atomT a t p o b, .atomT c u q s d =>
    strEq a c && beqSTyp t u && beqOptExprList p q &&
    beqOptWort o s && beqOptWort b d
  | .lockT a p r h s m v, .lockT b q t i u n w =>
    strEq a b && beqSExprList p q && beqSExpr r t &&
    beqOptExpr h i && beqOptExpr s u && beqOptWort m n && beqOptExpr v w
  | .rcuT a p r, .rcuT b q s =>
    strEq a b && beqSExprList p q && beqOptExpr r s
  | .groupT a m i, .groupT b n j =>
    strEq a b && beqWorte m n && beqSGruppenInvList i j
  | .concT a, .concT b => beqWortListe a b
  | .accT a t m p, .accT b u n q =>
    strEq a b && beqSTyp t u && strEq m n && beqOptExpr p q
  | .walkT a, .walkT b => beqSWeg a b
  | .entryT a, .entryT b => beqSEingang a b
  | .trustT a b c r s t, .trustT d e f u v w =>
    strEq a d && strEq b e && strEq c f && beqSRegBindList r u &&
    strEq s v && strEq t w
  | .bootT a c s d, .bootT b e t f =>
    strEq a b && strEq c e && beqSBootSchrittList s t && beqWorte d f
  | .callT a, .callT b => beqSSyscall a b
  | .varT a, .varT b => strEq a b
  | .goalT a x, .goalT b y => strEq a b && beqGoalOpt x y
  | .transT f s b, .transT g t d =>
    strEq f g && beqFnSig s t && beqSAnw b d
  | .profT a e, .profT b f =>
    (a == b) && beqSProfEintragList e f
  | .gateT a, .gateT b => beqSItemTief a b
  | _, _ => false
def beqSItemTiefList : List SItemTief → List SItemTief → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSItemTief x y && beqSItemTiefList xs ys
  | _, _ => false
end

-- The deep readers of SYNTAX.md sections 2 (`typeexpr`), 6
-- (`fndecl` heads, `uses`, clauses) and 1/9-14 (items), each
-- with fuel: every call passes strictly less fuel, so the block
-- terminates by `f`. Against `parse.rs`: the clause order is
-- free (the loop dispatches on the head word), `requires` /
-- `ensures` take comma-separated `predlist`s, `effects` the
-- `efflist` and `costs` the `<= e ops` shape -- one by one.
-- Predicates ride `SExpr` (no `pred` reader, same cut as item 1
-- of `Anweisung.lean`); comma lists allow a trailing comma (see
-- CUTS).

/-- The assumption class: `falsifier n` or `unfalsifiable "…"`. -/
def parseKlasse : List Token → Except String (SAnKlasse × List Token)
  | .wort s :: rest =>
    if strEq s "falsifier" then match nimmName rest with
      | .ok (n, r) => .ok (.probe n, r)
      | .error e => .error e
    else if strEq s "unfalsifiable" then match nimmTextTok rest with
      | .ok (t, r) => .ok (.trust t, r)
      | .error e => .error e
    else .error "falsifier expected"
  | _ => .error "falsifier expected"

/-- A comma-separated name list (trailing commas allowed). -/
def parseNamenListe (f : Nat) : List Token →
    Except String (List String × List Token)
  | [] => .error "name expected"
  | toks => match f with
    | 0 => .error "out of fuel"
    | f + 1 => match nimmName toks with
      | .error e => .error e
      | .ok (n, rest) => match rest with
        | .zeichen "," :: rest' => match nimmName rest' with
          | .ok _ => match parseNamenListe f rest' with
            | .error e => .error e
            | .ok (ns, r) => .ok (n :: ns, r)
          | .error _ => .ok ([n], rest')
        | _ => .ok ([n], rest)

mutual
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
      else if strEq s "publishes" then match parseOr f rest with
        | .ok (p, r) => .ok (.posts p, r)
        | .error e => .error e
      else if strEq s "diverges" then .ok (.loops, rest)
      else if strEq s "pure" then .ok (.pure, rest)
      else .error "effect expected"
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
/-- The parameter list `(` … `)` of `fndecl` (shared with
    `device` and `axiom`). -/
def parseParams (f : Nat) (toks : List Token) :
    Except String (List (String × STyp) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "(" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen ")" :: r' => .ok ([], r')
      | _ => match parseParamListe f r with
        | .error e => .error e
        | .ok (ps, r') => match fordereZeichen ")" r' with
          | .error e => .error e
          | .ok r'' => .ok (ps, r'')
def parseParamListe (f : Nat) (toks : List Token) :
    Except String (List (String × STyp) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseTyp f r2 with
        | .error e => .error e
        | .ok (t, r3) => match r3 with
          -- The variadic marker `...` (lexed `..` `.`; C-free lane, C2): a fact about the
          -- foreign C prototype only -- every parameter behind it is declared and passed, so
          -- the parsed list keeps them all and the marker itself carries nothing into `D`.
          | .zeichen "," :: .zeichen ".." :: .zeichen "." :: .zeichen ")" :: r4 =>
            .ok ([(n, t)], .zeichen ")" :: r4)
          | .zeichen "," :: .zeichen ".." :: .zeichen "." :: .zeichen "," :: r4 =>
            match parseParamListe f r4 with
            | .error e => .error e
            | .ok (ps, r) => .ok ((n, t) :: ps, r)
          | .zeichen "," :: r4 => match parseParamListe f r4 with
            | .error e => .error e
            | .ok (ps, r) => .ok ((n, t) :: ps, r)
          | _ => .ok ([(n, t)], r3)
/-- A function head: `fn name(params) [-> T] [or R] clauses`
    (`art` rode in front). -/
def parseFnSig (f : Nat) (art : String) (toks : List Token) :
    Except String (FnSig × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "fn" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (name, r2) => match parseParams f r2 with
        | .error e => .error e
        | .ok (ps, r3) => match parseErgebnis f r3 with
          | .error e => .error e
          | .ok (erg, fehler, r4) => match parseKlauseln f r4 with
            | .error e => .error e
            | .ok (ks, r) =>
              .ok ({ art, name, params := ps, res := erg,
                     fehler, klauseln := ks }, r)
/-- The optional `-> T` result and `or R` channel behind a
    signature. -/
def parseErgebnis (f : Nat) (toks : List Token) :
    Except String (Option STyp × Option String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "->" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r) => match parseFehler r with
        | .ok (o, r') => .ok (some t, o, r')
        | .error e => .error e
    | _ => match parseFehler toks with
      | .ok (o, r) => .ok (none, o, r)
      | .error e => .error e
def parseFehler : List Token → Except String (Option String × List Token)
  | .wort s :: rest =>
    if strEq s "or" then match nimmName rest with
      | .ok (n, r) => .ok (some n, r)
      | .error e => .error e
    else .ok (none, .wort s :: rest)
  | toks => .ok (none, toks)
/-- Behind the head: a block body (`fnT`), `;`
    (`protoT`), `= pred ;` (`specT`) or `= asm {…} ;` (`asmT`). -/
def parseFnRest (f : Nat) (sig : FnSig) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "{" :: _ => match parseBlock f toks with
      | .error e => .error e
      | .ok (b, r) => .ok (.fnT sig b, r)
    | .zeichen ";" :: rest => .ok (.protoT sig, rest)
    | .zeichen "=" :: rest => match rest with
      | .wort s :: rest' =>
        if strEq s "asm" then match fordereZeichen "{" rest' with
          | .error e => .error e
          | .ok r1 => match nimmBereichWorte r1 1 with
            | .error e => .error e
            | .ok (h, r2) => match fordereZeichen ";" r2 with
              | .error e => .error e
              | .ok r => .ok (.asmT sig ("asm { " ++ h), r)
        else match parsePred f rest with
          | .error e => .error e
          | .ok (p, r1) => match fordereZeichen ";" r1 with
            | .error e => .error e
            | .ok r => .ok (.specT sig p, r)
      | _ => match parseOr f rest with
        | .error e => .error e
        | .ok (p, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r => .ok (.specT sig p, r)
    | _ => .error "fn without body"
/-- One slot/format field: `name : type [@bitpos]
    [offset_into t] [where p] [reserved] [by ops]`. -/
def parseFeld (f : Nat) (toks : List Token) :
    Except String (SFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseTyp f r2 with
        | .error e => .error e
        | .ok (t, r3) => match parseFeldRest f r3 with
          | .error e => .error e
          | .ok ((pos, bezug, wo, res, byo), r) =>
            .ok ({ fname := n, ftyp := t, pos, bezug := bezug, wo,
                   reserviert := res, byOps := byo }, r)
def parseFeldRest (f : Nat) : List Token → Except String
    ((Option String × Option String × Option SExpr × Bool × Bool) × List Token)
  | toks => match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match parseBitpos rest with
      | .error e => .error e
      | .ok (b, r) => match parseFeldRest f r with
        | .error e => .error e
        | .ok ((_, bezug, wo, res, byo), r') =>
          .ok (((some b, bezug, wo, res, byo)), r')
    | .wort s :: rest =>
      if strEq s "offset_into" then match rest with
        | t :: r =>
          if strEq (zeigeTok t) "Self" then match parseFeldRest f r with
            | .error e => .error e
            | .ok ((pos, _, wo, res, byo), r') =>
              .ok (((pos, some "Self", wo, res, byo)), r')
          else match nameText t with
            | some n => match parseFeldRest f r with
              | .error e => .error e
              | .ok ((pos, _, wo, res, byo), r') =>
                .ok (((pos, some n, wo, res, byo)), r')
            | none => .error "offset_into expected"
        | _ => .error "offset_into expected"
      else if strEq s "where" then match parsePred f rest with
        | .ok (p, r) => match parseFeldRest f r with
          | .error e => .error e
          | .ok ((pos, bezug, _, res, byo), r') =>
            .ok (((pos, bezug, some p, res, byo)), r')
        | .error e => .error e
      else if strEq s "reserved" then match parseFeldRest f rest with
        | .error e => .error e
        | .ok ((pos, bezug, wo, _, byo), r) =>
          .ok (((pos, bezug, wo, true, byo)), r)
      else if strEq s "by" then match rest with
        | .wort t :: r =>
          if strEq t "ops" then match parseFeldRest f r with
            | .error e => .error e
            | .ok ((pos, bezug, wo, res, _), r') =>
              .ok (((pos, bezug, wo, res, true)), r')
          else .error "by ops expected"
        | _ => .error "by ops expected"
      else .ok (((none, none, none, false, false)), toks)
    | _ => .ok (((none, none, none, false, false)), toks)
/-- A raw `@bitpos`: one number or a `[hi:lo]` group. -/
def parseBitpos : List Token → Except String (String × List Token)
  | .zeichen "[" :: rest => match sammleAusgewogen rest 0 1 0 with
    | .error e => .error e
    | .ok (h, r) => .ok ("[ " ++ h, r)
  | t :: rest => match nameText t with
    | some _ => .ok (zeigeTok t, rest)
    | none => match t with
      | .num _ => .ok (zeigeTok t, rest)
      | _ => .error "bitpos expected"
  | [] => .error "bitpos expected"
/-- A `{` … `}` field list (slots and formats share the shape). -/
def parseFeldListe (f : Nat) (toks : List Token) :
    Except String (List SFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseFeldFolge f r with
        | .error e => .error e
        | .ok (fds, r') => .ok (fds, r')
/-- Fields after the opening `{` (the opener is consumed). -/
def parseFeldFolge (f : Nat) (toks : List Token) :
    Except String (List SFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseFeld f toks with
    | .error e => .error e
    | .ok (fd, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([fd], r3)
        | _ => match parseFeldFolge f r2 with
          | .error e => .error e
          | .ok (fds, r') => .ok (fd :: fds, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([fd], r')
/-- One register bit field: `name @bitpos [class c]`. -/
def parseRegFeld (f : Nat) (toks : List Token) :
    Except String (SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | _f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen "@" r1 with
      | .error e => .error e
      | .ok r2 => match parseBitpos r2 with
        | .error e => .error e
        | .ok (b, r3) => match r3 with
          | .wort s :: r4 =>
            if strEq s "class" then match nimmName r4 with
              | .error e => .error e
              | .ok (c, r) => .ok ({ name := n, pos := b, klasse := some c }, r)
            else .ok ({ name := n, pos := b, klasse := none }, r3)
          | _ => .ok ({ name := n, pos := b, klasse := none }, r3)
def parseRegFeldListe (f : Nat) (toks : List Token) :
    Except String (List SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseRegFeldFolge f r with
        | .error e => .error e
        | .ok (fds, r') => .ok (fds, r')
/-- Register fields after the opening `{`. -/
def parseRegFeldFolge (f : Nat) (toks : List Token) :
    Except String (List SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseRegFeld f toks with
    | .error e => .error e
    | .ok (fd, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([fd], r3)
        | _ => match parseRegFeldFolge f r2 with
          | .error e => .error e
          | .ok (fds, r') => .ok (fd :: fds, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([fd], r')
/- The `in`-stage tail behind a register class. -/
def parsePhasen (f : Nat) : List Token →
    Except String (List String × List Token)
  | [] => .ok ([], [])
  | toks => match f with
    | 0 => .error "out of fuel"
    | f + 1 => match toks with
      | .wort s :: rest =>
        if strEq s "in" then match nimmName rest with
          | .error e => .error e
          | .ok (st, r) => match parsePhasenRest f r with
            | .error e => .error e
            | .ok (ws, r') => .ok ("in" :: st :: ws, r')
        else .ok ([], toks)
      | _ => .ok ([], toks)
def parsePhasenRest (f : Nat) : List Token →
    Except String (List String × List Token)
  | [] => .ok ([], [])
  | toks => match f with
    | 0 => .error "out of fuel"
    | f + 1 => match toks with
      | .zeichen "," :: rest => match nimmName rest with
        | .error e => .error e
        | .ok (k, r1) => match nimmWort "in" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (st, r3) => match parsePhasenRest f r3 with
              | .error e => .error e
              | .ok (ws, r) => .ok ("," :: k :: "in" :: st :: ws, r)
      | _ => .ok ([], toks)
/-- One device register: `reg n : T [@ e] class c [phases]
    [fields {…}] [requires p [else A::B]] [depends {…}] ;`. -/
def parseReg (f : Nat) (toks : List Token) :
    Except String (SReg × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "reg" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen ":" r2 with
        | .error e => .error e
        | .ok r3 => match parseTyp f r3 with
          | .error e => .error e
          | .ok (t, r4) => match parseRegRest f
              ({ name := n, rtyp := t,
                 addr := .variable "", klasse := "", stage := [],
                 felder := [], voraus := none, elseF := none,
                 abhaengt := [] } : SReg) r4 with
            | .error e => .error e
            | .ok (rg, r) => .ok (rg, r)
def parseRegRest (f : Nat) (rg : SReg) (toks : List Token) :
    Except String (SReg × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match parseOr f rest with
      | .error e => .error e
      | .ok (e, r) => parseRegRest f { rg with addr := e } r
    | .wort s :: rest =>
      if strEq s "class" then match nimmName rest with
        | .error e => .error e
        | .ok (c, r1) => match parsePhasen f r1 with
          | .error e => .error e
          | .ok (ph, r) =>
            parseRegRest f { rg with klasse := c, stage := ph } r
      else if strEq s "fields" then match parseRegFeldListe f rest with
        | .error e => .error e
        | .ok (fds, r) => parseRegRest f { rg with felder := fds } r
      else if strEq s "requires" then match parsePred f rest with
        | .error e => .error e
        | .ok (p, r1) => match r1 with
          | .wort t :: r2 =>
            if strEq t "else" then match nimmPfad r2 with
              | .error e => .error e
              | .ok ([a, b], r) => parseRegRest f
                { rg with voraus := some p,
                          elseF := some (a, b) } r
              | .ok _ => .error "else expected"
            else parseRegRest f { rg with voraus := some p } r1
          | _ => parseRegRest f { rg with voraus := some p } r1
      else if strEq s "depends" then match parseTraegerListe f rest with
        | .error e => .error e
        | .ok (cs, r) => parseRegRest f { rg with abhaengt := cs } r
      else .ok (rg, toks)
    | _ => .ok (rg, toks)
/-- A `depends`/carrier list: `{` … `}` of one- or two-segment
    names (trailing commas allowed). -/
def parseTraegerListe (f : Nat) (toks : List Token) :
    Except String (List (List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseTraegerFolge f r with
        | .error e => .error e
        | .ok (cs, r') => .ok (cs, r')
/-- Carriers after the opening `{`. -/
def parseTraegerFolge (f : Nat) (toks : List Token) :
    Except String (List (List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseTraeger toks with
    | .error e => .error e
    | .ok (c, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([c], r3)
        | _ => match parseTraegerFolge f r2 with
          | .error e => .error e
          | .ok (cs, r') => .ok (c :: cs, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([c], r')
def parseTraeger : List Token → Except String (List String × List Token)
  | toks => match nimmName toks with
    | .error e => .error e
    | .ok (a, r) => match r with
      | .zeichen "." :: r' => match nimmName r' with
        | .error e => .error e
        | .ok (b, r'') => .ok ([a, b], r'')
      | _ => .ok ([a], r)
/-- One transition: `transition n { p : a -> b, … }
    [requires p] [effects {…}]`. -/
def parseTrans (f : Nat) (toks : List Token) :
    Except String (STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "transition" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseSchritte f r3 with
          | .error e => .error e
          | .ok (ss, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r5 => match parseTransRest f
                ({ tname := n, schritte := ss, voraus := none,
                   wirkung := [] } : STrans) r5 with
              | .error e => .error e
              | .ok (tr, r) => .ok (tr, r)
def parseSchritte (f : Nat) (toks : List Token) :
    Except String (List (SExpr × SExpr × SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseSchrittPlatz f toks with
    | .error e => .error e
    | .ok (p, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match nimmBisPfeil r2 0 0 0 with
        | .error e => .error e
        | .ok (ft, r3) => match parseOr f ft with
          | .error e => .error e
          | .ok (a, []) => match parseOr f r3 with
            | .error e => .error e
            | .ok (b, r5) => match r5 with
              | .zeichen "," :: r6 => match parseSchritte f r6 with
                | .error e => .error e
                | .ok (ss, r) => .ok ((p, a, b) :: ss, r)
              | _ => .ok ([(p, a, b)], r5)
          | .ok (_, _ :: _) => .error "-> expected"
/-- Tokens until the top-level `->` (parens, brackets and braces
    tracked): the `from` side of a step rides before it. A bare
    `parseOr` would eat `a -> b` as an arrow field. -/
def nimmBisPfeil : List Token → Nat → Nat → Nat →
    Except String (List Token × List Token)
  | [], _, _, _ => .error "-> expected"
  | (.zeichen s :: rest), pr, pk, pg =>
    if strEq s "->" && pr == 0 && pk == 0 && pg == 0 then
      .ok ([], rest)
    else if strEq s "(" then match nimmBisPfeil rest (pr + 1) pk pg with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
    else if strEq s ")" then
      if pr == 0 then .error "-> expected"
      else match nimmBisPfeil rest (pr - 1) pk pg with
        | .ok (h, r) => .ok (.zeichen s :: h, r)
        | .error e => .error e
    else if strEq s "[" then match nimmBisPfeil rest pr (pk + 1) pg with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
    else if strEq s "]" then
      if pk == 0 then .error "-> expected"
      else match nimmBisPfeil rest pr (pk - 1) pg with
        | .ok (h, r) => .ok (.zeichen s :: h, r)
        | .error e => .error e
    else if strEq s "{" then match nimmBisPfeil rest pr pk (pg + 1) with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
    else if strEq s "}" then
      if pg == 0 then .error "-> expected"
      else match nimmBisPfeil rest pr pk (pg - 1) with
        | .ok (h, r) => .ok (.zeichen s :: h, r)
        | .error e => .error e
    else match nimmBisPfeil rest pr pk pg with
      | .ok (h, r) => .ok (.zeichen s :: h, r)
      | .error e => .error e
  | (t :: rest), pr, pk, pg => match nimmBisPfeil rest pr pk pg with
    | .ok (h, r) => .ok (t :: h, r)
    | .error e => .error e
/-- A transition place: SYNTAX.md `shiftplace` (`ident` with `.`
    and `[…]` suffixes) -- a general `parseOr` would eat the
    `->` as an arrow field. -/
def parseSchrittPlatz (f : Nat) (toks : List Token) :
    Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r) => parseSchrittPlatzNach f (.variable n) r
def parseSchrittPlatzNach (f : Nat) (e : SExpr)
    (toks : List Token) : Except String (SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "." :: rest => match nimmName rest with
      | .error e => .error e
      | .ok (n, r) => parseSchrittPlatzNach f (.field e n) r
    | .zeichen "[" :: rest => match parseOr f rest with
      | .error e => .error e
      | .ok (i, r1) => match fordereZeichen "]" r1 with
        | .error e => .error e
        | .ok r => parseSchrittPlatzNach f (.index e i) r
    | _ => .ok (e, toks)
def parseTransRest (f : Nat) (tr : STrans) (toks : List Token) :
    Except String (STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "requires" then match parsePred f rest with
        | .error e => .error e
        | .ok (p, r) => parseTransRest f { tr with voraus := some p } r
      else if strEq s "effects" then match parseEffektBlock f rest with
        | .error e => .error e
        | .ok (es, r) => parseTransRest f { tr with wirkung := es } r
      else .ok (tr, toks)
    | _ => .ok (tr, toks)
/-- An `effects {…}` group behind `transition` (the `fndecl`
    clause reader covers the signature site). -/
def parseEffektBlock (f : Nat) (toks : List Token) :
    Except String (List SEffekt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r1 => match r1 with
      | .zeichen "}" :: r2 => .ok ([], r2)
      | _ => match parseEffektListe f r1 with
        | .error e => .error e
        | .ok (es, r2) => match fordereZeichen "}" r2 with
          | .error e => .error e
          | .ok r => .ok (es, r)
/-- The `O` of `cost O(e)`: a name in both lexers (`kw.rs`
    has no `O` keyword either), so either token shape reads. -/
def nimmKostenO : List Token → Except String (List Token)
  | t :: rest => match nameText t with
    | some s => if strEq s "O" then .ok rest else .error "cost O expected"
    | none => .error "cost O expected"
  | [] => .error "cost O expected"
/-- One invariant: `invariant n cost O(e) runs m [by …] : p ;`. -/
def parseGruppenInv (f : Nat) (toks : List Token) :
    Except String (SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "invariant" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "cost" r2 with
        | .error e => .error e
        | .ok r3 => match nimmKostenO r3 with
          | .error e => .error e
          | .ok r4 => match fordereZeichen "(" r4 with
            | .error e => .error e
            | .ok r5 => match parseOr f r5 with
              | .error e => .error e
              | .ok (c, r6) => match fordereZeichen ")" r6 with
                | .error e => .error e
                | .ok r7 => match nimmWort "runs" r7 with
                  | .error e => .error e
                  | .ok r8 => match r8 with
                    | .wort m :: r9 =>
                      if strEq m "online" || strEq m "offline" then
                        match parseInvRest f r9 with
                        | .error e => .error e
                        | .ok ((proof, p), r) => .ok
                          ({ name := n, kosten := c,
                             online := strEq m "online", proof := proof,
                             pred := p }, r)
                      else .error "runs expected"
                    | _ => .error "runs expected"
def parseInvRest (f : Nat) (toks : List Token) :
    Except String ((Option String × SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "by" then match nimmBisZeichen ":" rest 0 with
        | .error e => .error e
        | .ok (h, r1) => match fordereZeichen ":" r1 with
          | .error e => .error e
          | .ok r2 => match parsePred f r2 with
            | .error e => .error e
            | .ok (p, r3) => match fordereZeichen ";" r3 with
              | .error e => .error e
              | .ok r => .ok (((some h, p)), r)
      else match fordereZeichen ":" toks with
        | .error e => .error e
        | .ok r1 => match parsePred f r1 with
          | .error e => .error e
          | .ok (p, r2) => match fordereZeichen ";" r2 with
            | .error e => .error e
            | .ok r => .ok (((none, p)), r)
    | _ => match fordereZeichen ":" toks with
      | .error e => .error e
      | .ok r1 => match parsePred f r1 with
        | .error e => .error e
        | .ok (p, r2) => match fordereZeichen ";" r2 with
          | .error e => .error e
          | .ok r => .ok (((none, p)), r)
/-- A `{` … `}` place list (`protects`, `measures`, `reclaims`
    tails; trailing commas allowed). -/
def parsePlatzListe (f : Nat) (toks : List Token) :
    Except String (List SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parsePredListe f r with
        | .error e => .error e
        | .ok (ps, r1) => match r1 with
          | .zeichen "," :: r2 => match fordereZeichen "}" r2 with
            | .ok r' => .ok (ps, r')
            | .error _ => .error "} expected"
          | _ => match fordereZeichen "}" r1 with
            | .error e => .error e
            | .ok r' => .ok (ps, r')
/-- A `{` … `}` register map (`regs in` / `regs out`). -/
def parseRegBindListe (f : Nat) (toks : List Token) :
    Except String (List SRegBind × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseRegBindFolge f r with
        | .error e => .error e
        | .ok (bs, r') => .ok (bs, r')
/-- Register bindings after the opening `{`. -/
def parseRegBindFolge (f : Nat) (toks : List Token) :
    Except String (List SRegBind × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseRegBind toks with
    | .error e => .error e
    | .ok (b, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([b], r3)
            | _ => match parseRegBindFolge f r2 with
              | .error e => .error e
              | .ok (bs, r') => .ok (b :: bs, r')
          | _ => match fordereZeichen "}" r1 with
            | .error e => .error e
            | .ok r' => .ok ([b], r')
def parseRegBind : List Token → Except String (SRegBind × List Token)
  | toks => match nimmName toks with
    | .error e => .error e
    | .ok (a, r) => match r with
      | .zeichen s :: r' =>
        if strEq s "=" || strEq s ":" then match nimmName r' with
          | .error e => .error e
          | .ok (b, r'') => .ok (.binds a b, r'')
        else .ok (.reg a, r)
      | _ => .ok (.reg a, r)
/-- A `{` … `}` path list (`concurrent`, `group over`;
    trailing commas allowed). -/
def parsePfadListe (f : Nat) (toks : List Token) :
    Except String (List (List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parsePfadFolge f r with
        | .error e => .error e
        | .ok (ps, r') => .ok (ps, r')
/-- Paths after the opening `{`. -/
def parsePfadFolge (f : Nat) (toks : List Token) :
    Except String (List (List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmPfad toks with
    | .error e => .error e
    | .ok (p, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: r3 => .ok ([p], r3)
        | _ => match parsePfadFolge f r2 with
          | .error e => .error e
          | .ok (ps, r') => .ok (p :: ps, r')
      | _ => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok ([p], r')
/-- One boot step: `step f(args) ;` or `step n = e ;`. -/
def parseBootSchritt (f : Nat) (toks : List Token) :
    Except String (SBootSchritt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "step" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (p, r2) => match r2 with
        | .zeichen "(" :: r3 => match r3 with
          | .zeichen ")" :: r4 => match fordereZeichen ";" r4 with
            | .error e => .error e
            | .ok r => .ok (.call p [], r)
          | _ => match parsePredListe f r3 with
            | .error e => .error e
            | .ok (as, r4) => match fordereZeichen ")" r4 with
              | .error e => .error e
              | .ok r5 => match fordereZeichen ";" r5 with
                | .error e => .error e
                | .ok r => .ok (.call p as, r)
        | .zeichen "=" :: r3 => match parseOr f r3 with
          | .error e => .error e
          | .ok (e, r4) => match fordereZeichen ";" r4 with
            | .error e => .error e
            | .ok r => match p with
              | [n] => .ok (.set n e, r)
              | _ => .error "step expected"
        | _ => .error "step expected"
/-- A `{` … `}` name list that may stand empty (`preserves`,
    `clobbers`, `gates`). -/
def parseNamenEingeklammert (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseNamenListe f r with
        | .error e => .error e
        | .ok (ns, r1) => match r1 with
          | .zeichen "," :: r2 => match fordereZeichen "}" r2 with
            | .ok r' => .ok (ns, r')
            | .error _ => .error "} expected"
          | _ => match fordereZeichen "}" r1 with
            | .error e => .error e
            | .ok r' => .ok (ns, r')
/-- `module path { items }`. -/
def parseModulTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "module" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (p, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseItemsTief f r3 with
          | .error e => .error e
          | .ok (its, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r => .ok (.modT ("::".intercalate p) its, r)
/-- `use path ;`. -/
def parseUseTief : List Token → Except String (SItemTief × List Token)
  | toks => match nimmWort "use" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (p, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (.useT p, r)
/-- `[flags] type n [(args)] [order {…}] [= T] ;`. -/
def parseTypTief (f : Nat) (flags : List String) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "type" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseTypArgs f r2 with
        | .error e => .error e
        | .ok (args, r3) => match parseTypOrdnung f r3 with
          | .error e => .error e
          | .ok (ord, r4) => match r4 with
            | .zeichen "=" :: r5 => match parseTyp f r5 with
              | .error e => .error e
              | .ok (t, r6) => match fordereZeichen ";" r6 with
                | .error e => .error e
                | .ok r => .ok (.typeT flags n args ord (some t), r)
            | _ => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.typeT flags n args ord none, r)
def parseTypArgs (f : Nat) (toks : List Token) :
    Except String (List STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "(" :: rest => match rest with
      | .zeichen ")" :: r => .ok ([], r)
      | _ => match parseTypArgListe f rest with
        | .error e => .error e
        | .ok (ts, r1) => match fordereZeichen ")" r1 with
          | .error e => .error e
          | .ok r => .ok (ts, r)
    | _ => .ok ([], toks)
def parseTypArgListe (f : Nat) (toks : List Token) :
    Except String (List STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseTyp f toks with
    | .error e => .error e
    | .ok (t, r1) => match r1 with
      | .zeichen "," :: r2 => match parseTypArgListe f r2 with
        | .error e => .error e
        | .ok (ts, r) => .ok (t :: ts, r)
      | _ => .ok ([t], r1)
def parseTypOrdnung (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "order" then match fordereZeichen "{" rest with
        | .error e => .error e
        | .ok r1 => match parseNamenListe f r1 with
          | .error e => .error e
          | .ok (ns, r2) => match r2 with
            | .zeichen "," :: r3 => match fordereZeichen "}" r3 with
              | .error e => .error e
              | .ok r => .ok (ns, r)
            | _ => match fordereZeichen "}" r2 with
              | .error e => .error e
              | .ok r => .ok (ns, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- `const n : T = v ;` (behind the `const`). -/
def parseKonstNach (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseTyp f r2 with
        | .error e => .error e
        | .ok (t, r3) => match fordereZeichen "=" r3 with
          | .error e => .error e
          | .ok r4 => match parseKonstWert f r4 with
            | .error e => .error e
            | .ok (v, r5) => match fordereZeichen ";" r5 with
              | .error e => .error e
              | .ok r => .ok (.constT n t v, r)
/-- A `constwert`: an expression or an array literal, whose rows may nest (lanes 111, 170). -/
def parseKonstWert (f : Nat) (toks : List Token) :
    Except String (SKonstWert × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "[" :: rest => do
      let (xs, r) ← parseConstRows f rest
      pure (.rows xs, r)
    | _ => do
      let (e, r) ← parseOr f toks
      pure (.one e, r)
/-- The elements of an array literal behind its `[`, up to and including the `]`
    (a trailing comma is allowed). -/
def parseConstRows (f : Nat) (toks : List Token) :
    Except String (List SKonstWert × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "]" :: r => .ok ([], r)
    | _ => do
      let (v, r1) ← parseKonstWert f toks
      match r1 with
      | .zeichen "," :: r2 => do
        let (vs, r3) ← parseConstRows f r2
        pure (v :: vs, r3)
      | .zeichen "]" :: r => pure ([v], r)
      | _ => .error "wanted ]"
/-- `static [mut] n : T = e [section s] [shared] ;`. -/
def parseGlobTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "static" toks with
    | .error e => .error e
    | .ok r1 => match r1 with
      | .wort s :: r2 =>
        if strEq s "mut" then match parseGlobAfter f true r2 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
        else match parseGlobAfter f false r1 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
      | _ => match parseGlobAfter f false r1 with
        | .error e => .error e
        | .ok (it, r) => .ok (it, r)
def parseGlobAfter (f : Nat) (ver : Bool) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (n, r1) ← nimmName toks
    let r2 ← fordereZeichen ":" r1
    let (t, r3) ← parseTyp f r2
    let r4 ← fordereZeichen "=" r3
    let (v, r5) ← parseKonstWert f r4
    let ((al, sec, sh), r) ← parseGlobTail f r5
    pure (.globT ver n t v al sec sh, r)
/-- Behind the initialiser: `[aligned e] [section "s"] [shared] ;`, in this order. -/
def parseGlobTail (f : Nat) (toks : List Token) :
    Except String ((Option SExpr × Option String × Bool) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (al, r1) ← (match toks with
      | .wort "aligned" :: rest => do
        let (e, r) ← parseOr f rest
        pure (some e, r)
      | _ => pure (none, toks))
    let (sec, r2) ← (match r1 with
      | .wort "section" :: rest => do
        let (t, r) ← nimmTextTok rest
        pure (some t, r)
      | _ => pure (none, r1))
    let (sh, r3) : Bool × List Token := match r2 with
      | .wort "shared" :: rest => (true, rest)
      | _ => (false, r2)
    let r ← fordereZeichen ";" r3
    pure ((al, sec, sh), r)
/-- `translator n for g(params) [-> T] clauses block`. -/
def parseTranslatorTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "translator" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "for" r2 with
        | .error e => .error e
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (g, r4) => match parseParams f r4 with
            | .error e => .error e
            | .ok (ps, r5) => match parseErgebnis f r5 with
              | .error e => .error e
              | .ok (erg, fehler, r6) => match parseKlauseln f r6 with
                | .error e => .error e
                | .ok (ks, r7) => match parseBlock f r7 with
                  | .error e => .error e
                  | .ok (b, r) => .ok (.transT g
                    ({ art := "", name := n, params := ps,
                       res := erg, fehler, klauseln := ks } : FnSig) b, r)
/-- `format n [@version e] [endian m] { fields }`. -/
def parseFormatTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "format" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseFormatRest f r2 with
        | .error e => .error e
        | .ok ((ver, e), r3) => match parseFeldListe f r3 with
          | .error e => .error e
          | .ok (fds, r) => .ok (.formatT n ver e fds, r)
def parseFormatRest (f : Nat) (toks : List Token) :
    Except String ((Option SExpr × Option String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match rest with
      | .ident s :: r1 =>
        if strEq s "version" then match parseOr f r1 with
          | .error e => .error e
          | .ok (v, r2) => match parseFormatRest f r2 with
            | .error e => .error e
            | .ok ((_, e), r) => .ok (((some v, e)), r)
        else .error "@version expected"
      | _ => .error "@version expected"
    | .wort s :: rest =>
      if strEq s "endian" then match rest with
        | .wort m :: r1 =>
          if strEq m "little" || strEq m "big" then
            match parseFormatRest f r1 with
            | .error e => .error e
            | .ok ((v, _), r) => .ok (((v, some m)), r)
          else .error "endian expected"
        | _ => .error "endian expected"
      else .ok (((none, none)), toks)
    | _ => .ok (((none, none)), toks)
/-- `table n [count e] [backed b] [owner o] [shared] { parts }`. -/
def parseTabellenTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "table" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseTabellenKopf f r2 with
        | .error e => .error e
        | .ok (((cnt, backed, owner, g)), r3) =>
          match fordereZeichen "{" r3 with
          | .error e => .error e
          | .ok r4 => match parseTabTeile f r4 with
            | .error e => .error e
            | .ok (ps, r5) => match fordereZeichen "}" r5 with
              | .error e => .error e
              | .ok r => .ok
                (.tableT n cnt backed owner g ps, r)
def parseTabellenKopf (f : Nat) (toks : List Token) :
    Except String
      ((Option SExpr × Option String × Option String × Bool) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "count" then match parseOr f rest with
        | .error e => .error e
        | .ok (e, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((_, b, o, g)), r) => .ok ((((some e, b, o, g))), r)
      else if strEq s "backed" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((c, _, o, g)), r) => .ok ((((c, some n, o, g))), r)
      else if strEq s "owner" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match parseTabellenKopf f r1 with
          | .error e => .error e
          | .ok (((c, b, _, g)), r) => .ok ((((c, b, some n, g))), r)
      else if strEq s "shared" then match parseTabellenKopf f rest with
        | .error e => .error e
        | .ok (((c, b, o, _)), r) => .ok ((((c, b, o, true))), r)
      else .ok ((((none, none, none, false))), toks)
    | _ => .ok ((((none, none, none, false))), toks)
def parseTabTeile (f : Nat) (toks : List Token) :
    Except String (List STabTeil × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "const" then match parseKonstNach f rest with
        | .error e => .error e
        | .ok (.constT n t v, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tConst n t v :: ps, r)
        | .ok _ => .error "const expected"
      else if strEq s "slot" then match parseFeldListe f rest with
        | .error e => .error e
        | .ok (fds, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tSlot fds :: ps, r)
      else if strEq s "invariant" then match parseGruppenInv f toks with
        | .error e => .error e
        | .ok (iv, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tInv iv :: ps, r)
      else if strEq s "ops" then match parseNamenListe f rest with
        | .error e => .error e
        | .ok (ns, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseTabTeile f r2 with
            | .error e => .error e
            | .ok (ps, r) => .ok (.tOps ns :: ps, r)
      else if strEq s "tree" then match parseBaum f rest with
        | .error e => .error e
        | .ok (ks, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tTree ks :: ps, r)
      else if strEq s "occupied" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseTabTeile f r2 with
            | .error e => .error e
            | .ok (ps, r) => .ok (.tBusy n :: ps, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- `tree { parent a, child b, … }`. -/
def parseBaum (f : Nat) (toks : List Token) :
    Except String (List (String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match parseKanten f r with
      | .error e => .error e
      | .ok (ks, r1) => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r' => .ok (ks, r')
def parseKanten (f : Nat) (toks : List Token) :
    Except String (List (String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseKante toks with
    | .error e => .error e
    | .ok (k, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen "}" :: _ => .ok ([k], r2)
        | _ => match parseKanten f r2 with
          | .error e => .error e
          | .ok (ks, r) => .ok (k :: ks, r)
      | _ => .ok ([k], r1)
def parseKante : List Token → Except String ((String × String) × List Token)
  | .wort s :: rest =>
    if strEq s "parent" || strEq s "child" || strEq s "sibling" then
      match nimmName rest with
      | .error e => .error e
      | .ok (n, r) => .ok (((s, n)), r)
    else .error "edge expected"
  | _ => .error "edge expected"
/-- `arena n capacity lo .. hi [max m] of T [pb path blw e] ;` (`pb`/`blw` read as names: the
    sampling clause of the unbounded heap, TODO 1-B). -/
def parseArenaTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "arena" toks
    let (n, r2) ← nimmName r1
    let r3 ← nimmWort "capacity" r2
    let (lo, r4) ← parseOr f r3
    let r5 ← fordereZeichen ".." r4
    let (hi, r6) ← parseOr f r5
    let (mx, r7) ← (match r6 with
      | .wort "max" :: rest => do
        let (e, r) ← parseOr f rest
        pure (some e, r)
      | _ => pure (none, r6))
    let r8 ← nimmWort "of" r7
    let (t, r9) ← parseTyp f r8
    let (pb, r10) ← (match r9 with
      | .zeichen ";" :: _ => pure (none, r9)
      | t1 :: rest => match nameText t1 with
        | some w =>
          if strEq w "pb" then do
            let (p, ra) ← nimmPfad rest
            let (b, rb) ← nimmName ra
            if strEq b "blw" then do
              let (e, rc) ← parseOr f rb
              pure (some (p, e), rc)
            else .error "blw expected"
          else .error "wanted ;"
        | none => .error "wanted ;"
      | [] => .error "wanted ;")
    let r ← fordereZeichen ";" r10
    pure (.arenaT n lo hi mx t pb, r)
/-- `reason n { c = num "text" … [exhaustive] }` (cases are
    whitespace-separated, commas allowed). -/
def parseGrundTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "reason" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseGrundFaelle f r3 with
          | .error e => .error e
          | .ok ((cs, ex), r) => .ok (.whyT n cs ex, r)
def parseGrundFaelle (f : Nat) (toks : List Token) :
    Except String ((List (String × SExpr × String) × Bool) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "exhaustive" then match fordereZeichen "}" rest with
        | .error e => .error e
        | .ok r => .ok ((([], true)), r)
      else match parseGrundFall f toks with
        | .error e => .error e
        | .ok ((c, num, t), r4) => match r4 with
          | .zeichen "," :: r5 => match parseGrundFaelle f r5 with
            | .error e => .error e
            | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
          | _ => match parseGrundFaelle f r4 with
            | .error e => .error e
            | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
    | .ident _ :: _ => match parseGrundFall f toks with
      | .error e => .error e
      | .ok ((c, num, t), r4) => match r4 with
        | .zeichen "," :: r5 => match parseGrundFaelle f r5 with
          | .error e => .error e
          | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
        | _ => match parseGrundFaelle f r4 with
          | .error e => .error e
          | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
    | .zeichen "}" :: rest => .ok ((([], false)), rest)
    | _ => .error "reason expected"
/-- One reason case: `name = num "text"`. -/
def parseGrundFall (f : Nat) (toks : List Token) :
    Except String ((String × SExpr × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (c, r1) => match fordereZeichen "=" r1 with
      | .error e => .error e
      | .ok r2 => match parseOr f r2 with
        | .error e => .error e
        | .ok (num, r3) => match nimmTextTok r3 with
          | .error e => .error e
          | .ok (t, r) => .ok (((c, num, t)), r)
/-- `state n { transitions }`. -/
def parseZustandTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "state" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseTransListe f r3 with
          | .error e => .error e
          | .ok (ts, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r => .ok (.stateT n ts, r)
def parseTransListe (f : Nat) (toks : List Token) :
    Except String (List STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if strEq s "transition" then match parseTrans f toks with
        | .error e => .error e
        | .ok (tr, r1) => match parseTransListe f r1 with
          | .error e => .error e
          | .ok (ts, r) => .ok (tr :: ts, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- `device n [(params)] at space { mirrors | reg | bank |
    transition }`. -/
def parseGeraetTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "device" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match r2 with
        | .zeichen "(" :: _ => match parseParams f r2 with
          | .error e => .error e
          | .ok (ps, r3) => match parseGeraetNach f n ps r3 with
            | .error e => .error e
            | .ok (it, r) => .ok (it, r)
        | _ => match parseGeraetNach f n [] r2 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
def parseGeraetNach (f : Nat) (n : String) (ps : List (String × STyp))
    (toks : List Token) : Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "at" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (sp, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseGerTeile f r3 with
          | .error e => .error e
          | .ok (ms, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r => .ok (.devT n ps sp ms, r)
def parseGerTeile (f : Nat) (toks : List Token) :
    Except String (List SGerTeil × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "mirrors" then match parseOr f rest with
        | .error e => .error e
        | .ok (a, r1) => match nimmWort "from" r1 with
          | .error e => .error e
          | .ok r2 => match parseOr f r2 with
            | .error e => .error e
            | .ok (b, r3) => match fordereZeichen ";" r3 with
              | .error e => .error e
              | .ok r4 => match parseGerTeile f r4 with
                | .error e => .error e
                | .ok (ms, r) => .ok (.copy a b :: ms, r)
      else if strEq s "reg" then match parseReg f toks with
        | .error e => .error e
        | .ok (rg, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.reg rg :: ms, r)
      else if strEq s "bank" then match parseBank rest with
        | .error e => .error e
        | .ok (raw, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.bank raw :: ms, r)
      else if strEq s "transition" then match parseTrans f toks with
        | .error e => .error e
        | .ok (tr, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.trans tr :: ms, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- A `bank` member: the header rides raw up to `{`, the body
    balanced (registers inside are not split -- see CUTS). -/
def parseBank : List Token → Except String (String × List Token)
  | toks => match nimmName toks with
    | .error e => .error e
    | .ok (n, r1) => match nimmWort "at" r1 with
      | .error e => .error e
      | .ok r2 => match parseOr 50 r2 with
        | .error e => .error e
        | .ok (a, r3) => match nimmWort "stride" r3 with
          | .error e => .error e
          | .ok r4 => match parseOr 50 r4 with
            | .error e => .error e
            | .ok (s, r5) => match nimmWort "count" r5 with
              | .error e => .error e
              | .ok r6 => match parseOr 50 r6 with
                | .error e => .error e
                | .ok (c, r7) => match fordereZeichen "{" r7 with
                  | .error e => .error e
                  | .ok r8 => match nimmBereichWorte r8 1 with
                    | .error e => .error e
                    | .ok (h, r) => .ok
                      ("bank " ++ n ++ " at " ++ druck a ++
                       " stride " ++ druck s ++ " count " ++ druck c ++
                       " { " ++ h, r)
/-- `assume n [arch a] "text" (falsifier | unfalsifiable) ;`. -/
def parseAnnahmeTief : List Token → Except String (SItemTief × List Token)
  | toks => match nimmWort "assume" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match r2 with
        | .wort s :: r3 =>
          if strEq s "arch" then match nimmName r3 with
            | .error e => .error e
            | .ok (a, r4) => match nimmTextTok r4 with
              | .error e => .error e
              | .ok (t, r5) => match parseKlasse r5 with
                | .error e => .error e
                | .ok (k, r6) => match fordereZeichen ";" r6 with
                  | .error e => .error e
                  | .ok r => .ok (.assumT n (some a) t k, r)
          else match nimmTextTok r2 with
            | .error e => .error e
            | .ok (t, r3) => match parseKlasse r3 with
              | .error e => .error e
              | .ok (k, r4) => match fordereZeichen ";" r4 with
                | .error e => .error e
                | .ok r => .ok (.assumT n none t k, r)
        | _ => match nimmTextTok r2 with
          | .error e => .error e
          | .ok (t, r3) => match parseKlasse r3 with
            | .error e => .error e
            | .ok (k, r4) => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.assumT n none t k, r)
/-- `axiom n(params) [-> T] [requires p] effects {…} klasse ;`. -/
def parseAxiomTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "axiom" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseParams f r2 with
        | .error e => .error e
        | .ok (ps, r3) => match parseAxiomErg f r3 with
          | .error e => .error e
          | .ok ((erg, pre), r4) => match nimmWort "effects" r4 with
            | .error e => .error e
            | .ok r5 => match parseEffektBlock f r5 with
              | .error e => .error e
              | .ok (es, r6) => match parseKlasse r6 with
                | .error e => .error e
                | .ok (k, r7) => match fordereZeichen ";" r7 with
                  | .error e => .error e
                  | .ok r => .ok (.axiomT n ps erg pre es k, r)
def parseAxiomErg (f : Nat) (toks : List Token) :
    Except String ((Option STyp × Option SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "->" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r1) => match r1 with
        | .wort s :: r2 =>
          if strEq s "requires" then match parsePred f r2 with
            | .error e => .error e
            | .ok (p, r) => .ok (((some t, some p)), r)
          else .ok (((some t, none)), r1)
        | _ => .ok (((some t, none)), r1)
    | .wort s :: rest =>
      if strEq s "requires" then match parsePred f rest with
        | .error e => .error e
        | .ok (p, r) => .ok (((none, some p)), r)
      else .ok (((none, none)), toks)
    | _ => .ok (((none, none)), toks)
/-- `check n { claim … measures … gates … can_fail … [floor …]
    [counterprobe …] }`. -/
def parsePruefungTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "check" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match nimmWort "claim" r3 with
          | .error e => .error e
          | .ok r4 => match nimmTextTok r4 with
            | .error e => .error e
            | .ok (c, r5) => match nimmWort "measures" r5 with
              | .error e => .error e
              | .ok r6 => match parsePredListe f r6 with
                | .error e => .error e
                | .ok (ms, r7) => match nimmWort "gates" r7 with
                  | .error e => .error e
                  | .ok r8 => match parseNamenListe f r8 with
                    | .error e => .error e
                    | .ok (gs, r9) => match nimmWort "can_fail" r9 with
                      | .error e => .error e
                      | .ok r10 => match parseBlock f r10 with
                        | .error e => .error e
                        | .ok (b, r11) => match parsePruefungRest f r11 with
                          | .error e => .error e
                          | .ok (((boden, sonde)), r) => .ok (.checkT
                            ({ cname := n, claim := c, misst := ms,
                               gates := gs, canFail := b, boden,
                               sonde } : SCheck), r)
def parsePruefungRest (f : Nat) (toks : List Token) :
    Except String ((List SExpr × Option (String × String)) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "floor" then match parsePredListe f rest with
        | .error e => .error e
        | .ok (ps, r1) => match parsePruefungRest f r1 with
          | .error e => .error e
          | .ok (((qs, so)), r) => .ok (((ps ++ qs, so)), r)
      else if strEq s "counterprobe" then match nimmTextTok rest with
        | .error e => .error e
        | .ok (t, r1) => match nimmWort "expects" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (e, r3) => match fordereZeichen "}" r3 with
              | .error e => .error e
              | .ok r => .ok ((([], some (t, e))), r)
      else match fordereZeichen "}" toks with
        | .error e => .error e
        | .ok r => .ok ((([], none)), r)
    | _ => match fordereZeichen "}" toks with
      | .error e => .error e
      | .ok r => .ok ((([], none)), r)
/-- `atomic n : T [publishes …] [order] [observed by a] ;`. -/
def parseAtomarTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "atomic" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen ":" r2 with
        | .error e => .error e
        | .ok r3 => match parseTyp f r3 with
          | .error e => .error e
          | .ok (t, r4) => match parseAtomarRest f
              (n, t, none, none, none) r4 with
            | .error e => .error e
            | .ok ((a, b, c, d, e), r) => .ok
              (.atomT a b c d e, r)
def parseAtomarRest (f : Nat)
    (acc : String × STyp × Option (List SExpr) × Option String × Option String)
    (toks : List Token) :
    Except String
      ((String × STyp × Option (List SExpr) × Option String × Option String) ×
       List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "publishes" then match rest with
        | .wort t :: r1 =>
          if strEq t "nothing" then
            match acc with
            | (a, b, _, d, e) =>
              parseAtomarRest f (a, b, some [], d, e) r1
          else match parsePlatzListe f rest with
            | .error e => .error e
            | .ok (ps, r) => match acc with
              | (a, b, _, d, e) =>
                parseAtomarRest f (a, b, some ps, d, e) r
        | _ => match parsePlatzListe f rest with
          | .error e => .error e
          | .ok (ps, r) => match acc with
            | (a, b, _, d, e) =>
              parseAtomarRest f (a, b, some ps, d, e) r
      else if strEq s "acquire" || strEq s "release" ||
          strEq s "seq" || strEq s "relaxed" then match acc with
        | (a, b, c, _, e) =>
          parseAtomarRest f (a, b, c, some s, e) rest
      else if strEq s "observed" then match nimmWort "by" rest with
        | .error e => .error e
        | .ok r1 => match nimmName r1 with
          | .error e => .error e
          | .ok (o, r2) => match acc with
            | (a, b, c, d, _) =>
              parseAtomarRest f (a, b, c, d, some o) r2
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok (acc, r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok (acc, r)
/-- `lock n protects {…} rank e [held <= e ops] [shared held <= e ops] [masks m]
    [invariant p] ;`, the clauses in this order (`parse.rs` `lockdecl`). -/
def parseSperreTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "lock" toks
    let (n, r2) ← nimmName r1
    let r3 ← nimmWort "protects" r2
    let (ps, r4) ← parsePlatzListe f r3
    let r5 ← nimmWort "rank" r4
    let (rk, r6) ← parseOr f r5
    let (h, r7) ← (match r6 with
      | .wort "held" :: rest => do
        let r ← fordereZeichen "<=" rest
        let (e, ra) ← parseOr f r
        let rb ← nimmWort "ops" ra
        pure (some e, rb)
      | _ => pure (none, r6))
    let (sh, r8) ← (match r7 with
      | .wort "shared" :: rest => do
        let r0 ← nimmWort "held" rest
        let r ← fordereZeichen "<=" r0
        let (e, ra) ← parseOr f r
        let rb ← nimmWort "ops" ra
        pure (some e, rb)
      | _ => pure (none, r7))
    let (m, r9) ← (match r8 with
      | .wort "masks" :: rest => do
        let (w, r) ← nimmName rest
        pure (some w, r)
      | _ => pure (none, r8))
    let (inv, r10) ← (match r9 with
      | .wort "invariant" :: rest => do
        let (p, r) ← parsePred f rest
        pure (some p, r)
      | _ => pure (none, r9))
    let r ← fordereZeichen ";" r10
    pure (.lockT n ps rk h sh m inv, r)
/-- `rcu n protects {…} [reclaims p] ;`. -/
def parseRcuTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "rcu" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "protects" r2 with
        | .error e => .error e
        | .ok r3 => match parsePlatzListe f r3 with
          | .error e => .error e
          | .ok (ps, r4) => match r4 with
            | .wort s :: r5 =>
              if strEq s "reclaims" then match parseOr f r5 with
                | .error e => .error e
                | .ok (p, r6) => match fordereZeichen ";" r6 with
                  | .error e => .error e
                  | .ok r => .ok (.rcuT n ps (some p), r)
              else match fordereZeichen ";" r4 with
                | .error e => .error e
                | .ok r => .ok (.rcuT n ps none, r)
            | _ => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.rcuT n ps none, r)
/-- `group n over {…} ({ invariants } | ;)`. -/
def parseGruppeTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "group" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "over" r2 with
        | .error e => .error e
        | .ok r3 => match fordereZeichen "{" r3 with
          | .error e => .error e
          | .ok r4 => match parseNamenListe f r4 with
            | .error e => .error e
            | .ok (ms, r5) => match r5 with
              | .zeichen "," :: r6 => match fordereZeichen "}" r6 with
                | .error e => .error e
                | .ok r7 => match parseGruppeRest f r7 with
                  | .error e => .error e
                  | .ok (ivs, r) => .ok (.groupT n ms ivs, r)
              | _ => match fordereZeichen "}" r5 with
                | .error e => .error e
                | .ok r6 => match parseGruppeRest f r6 with
                  | .error e => .error e
                  | .ok (ivs, r) => .ok (.groupT n ms ivs, r)
def parseGruppeRest (f : Nat) (toks : List Token) :
    Except String (List SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "{" :: rest => match parseGruppenInvListe f rest with
      | .error e => .error e
      | .ok (ivs, r1) => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r => .ok (ivs, r)
    | .zeichen ";" :: rest => .ok ([], rest)
    | _ => .error "group expected"
def parseGruppenInvListe (f : Nat) (toks : List Token) :
    Except String (List SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if strEq s "invariant" then match parseGruppenInv f toks with
        | .error e => .error e
        | .ok (iv, r1) => match parseGruppenInvListe f r1 with
          | .error e => .error e
          | .ok (ivs, r) => .ok (iv :: ivs, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- `concurrent { paths } ;`. -/
def parseNebenTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "concurrent" toks with
    | .error e => .error e
    | .ok r1 => match parsePfadListe f r1 with
      | .error e => .error e
      | .ok (ps, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (.concT ps, r)
/-- `accumulates n : T merge op [per cpu e] ;`. -/
def parseAkkumTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "accumulates" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen ":" r2 with
        | .error e => .error e
        | .ok r3 => match parseTyp f r3 with
          | .error e => .error e
          | .ok (t, r4) => match nimmWort "merge" r4 with
            | .error e => .error e
            | .ok r5 => match r5 with
              | .wort m :: r6 =>
                if strEq m "max" || strEq m "min" || strEq m "add" ||
                    strEq m "or" || strEq m "and" then
                  match parseAkkumRest f r6 with
                  | .error e => .error e
                  | .ok (p, r) => .ok (.accT n t m p, r)
                else .error "merge expected"
              | _ => .error "merge expected"
def parseAkkumRest (f : Nat) (toks : List Token) :
    Except String (Option SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "per" then match nimmWort "cpu" rest with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (e, r2) => match fordereZeichen ";" r2 with
            | .error e => .error e
            | .ok r => .ok (some e, r)
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok (none, r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok (none, r)
/-- `walk n levels e { node : T, down : f when p, leaf : q,
    invariants }`. -/
def parseWegTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "walk" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "levels" r2 with
        | .error e => .error e
        | .ok r3 => match parseOr f r3 with
          | .error e => .error e
          | .ok (lv, r4) => match fordereZeichen "{" r4 with
            | .error e => .error e
            | .ok r5 => match nimmWort "node" r5 with
              | .error e => .error e
              | .ok r6 => match fordereZeichen ":" r6 with
                | .error e => .error e
                | .ok r7 => match parseTyp f r7 with
                  | .error e => .error e
                  | .ok (kn, r8) => match fordereZeichen "," r8 with
                    | .error e => .error e
                    | .ok r9 => match nimmWort "down" r9 with
                      | .error e => .error e
                      | .ok r10 => match fordereZeichen ":" r10 with
                        | .error e => .error e
                        | .ok r11 => match nimmName r11 with
                          | .error e => .error e
                          | .ok (dn, r12) => match nimmWort "when" r12 with
                            | .error e => .error e
                            | .ok r13 => match parsePred f r13 with
                              | .error e => .error e
                              | .ok (dp, r14) =>
                                match fordereZeichen "," r14 with
                                | .error e => .error e
                                | .ok r15 => match nimmWort "leaf" r15 with
                                  | .error e => .error e
                                  | .ok r16 => match fordereZeichen ":" r16 with
                                    | .error e => .error e
                                    | .ok r17 => match parsePred f r17 with
                                      | .error e => .error e
                                      | .ok (lf, r18) => match r18 with
                                        | .zeichen "," :: r19 =>
                                          match parseGruppenInvListe f r19 with
                                          | .error e => .error e
                                          | .ok (ivs, r20) =>
                                            match fordereZeichen "}" r20 with
                                            | .error e => .error e
                                            | .ok r => .ok (.walkT
                                              ({ name := n, stufen := lv,
                                                 node := kn,
                                                 dname := dn,
                                                 dwhen := dp, blatt := lf,
                                                 invarianten := ivs } : SWeg), r)
                                        | _ =>
                                          match fordereZeichen "}" r18 with
                                          | .error e => .error e
                                          | .ok r => .ok (.walkT
                                            ({ name := n, stufen := lv,
                                               node := kn,
                                               dname := dn,
                                               dwhen := dp, blatt := lf,
                                               invarianten := [] } : SWeg), r)
/-- `entry n [vector e] [via m] arch a { regs … dispatch … }`. -/
def parseEingangTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "entry" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseEingangKopf f r2 with
        | .error e => .error e
        | .ok (((vek, via, arch)), r3) =>
          match fordereZeichen "{" r3 with
          | .error e => .error e
          | .ok r4 => match nimmWort "regs" r4 with
            | .error e => .error e
            | .ok r5 => match nimmWort "in" r5 with
              | .error e => .error e
              | .ok r6 => match parseRegBindListe f r6 with
                | .error e => .error e
                | .ok (ri, r7) => match nimmWort "regs" r7 with
                  | .error e => .error e
                  | .ok r8 => match nimmWort "out" r8 with
                    | .error e => .error e
                    | .ok r9 => match parseRegBindListe f r9 with
                      | .error e => .error e
                      | .ok (ro, r10) =>
                        match nimmWort "preserves" r10 with
                        | .error e => .error e
                        | .ok r11 =>
                          match parseNamenEingeklammert f r11 with
                          | .error e => .error e
                          | .ok (ph, r12) =>
                            match nimmWort "clobbers" r12 with
                            | .error e => .error e
                            | .ok r13 =>
                              match parseNamenEingeklammert f r13 with
                              | .error e => .error e
                              | .ok (cb, r14) =>
                                match parseEingangRest f r14 with
                                | .error e => .error e
                                | .ok (((st, cpu, ist, ve, dp)), r15) =>
                                  match fordereZeichen "}" r15 with
                                  | .error e => .error e
                                  | .ok r => .ok (.entryT
                                    ({ name := n, vektor := vek, via,
                                       arch, regIn := ri, regOut := ro,
                                       erhaelt := ph, kills := cb,
                                       stapel := st, perCpu := cpu, ist,
                                       nest := ve,
                                       dispatch := dp } : SEingang), r)
def parseEingangKopf (f : Nat) (toks : List Token) :
    Except String
      ((Option SExpr × Option String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "vector" then match parseOr f rest with
        | .error e => .error e
        | .ok (v, r1) => match parseEingangKopf f r1 with
          | .error e => .error e
          | .ok (((_, via, arch)), r) => .ok ((((some v, via, arch))), r)
      else if strEq s "via" then match nimmName rest with
        | .error e => .error e
        | .ok (m, r1) => match parseEingangKopf f r1 with
          | .error e => .error e
          | .ok (((vek, _, arch)), r) => .ok ((((vek, some m, arch))), r)
      else if strEq s "arch" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r) => .ok ((((none, none, a))), r)
      else .error "arch expected"
    | _ => .error "arch expected"
def parseEingangRest (f : Nat) (toks : List Token) :
    Except String
      ((String × Bool × Option SExpr × Option String × List String) ×
       List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "stack" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (st, r2) => match r2 with
        | .wort s :: r3 =>
          if strEq s "per" then match nimmWort "cpu" r3 with
            | .error e => .error e
            | .ok r4 => match parseEingangRestNach f r4 with
              | .error e => .error e
              | .ok (((ist, ve, dp)), r) =>
                .ok ((((st, true, ist, ve, dp))), r)
          else match parseEingangRestNach f r2 with
            | .error e => .error e
            | .ok (((ist, ve, dp)), r) =>
              .ok ((((st, false, ist, ve, dp))), r)
        | _ => match parseEingangRestNach f r2 with
          | .error e => .error e
          | .ok (((ist, ve, dp)), r) =>
            .ok ((((st, false, ist, ve, dp))), r)
def parseEingangRestNach (f : Nat)
    (toks : List Token) :
    Except String
      ((Option SExpr × Option String × List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "ist" then match parseOr f rest with
        | .error e => .error e
        | .ok (e, r1) => match parseEingangNested f r1 with
          | .error e => .error e
          | .ok (((ve, dp)), r) => .ok ((((some e, ve, dp))), r)
      else match parseEingangNested f toks with
        | .error e => .error e
        | .ok (((ve, dp)), r) => .ok ((((none, ve, dp))), r)
    | _ => match parseEingangNested f toks with
      | .error e => .error e
      | .ok (((ve, dp)), r) => .ok ((((none, ve, dp))), r)
def parseEingangNested (f : Nat)
    (toks : List Token) :
    Except String ((Option String × List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseEingangNestedOpt f toks with
    | .error e => .error e
    | .ok (ve, r1) => match parseEingangDispatch f r1 with
      | .error e => .error e
      | .ok (dp, r) => .ok (((ve, dp)), r)
/-- The optional `nested …` tail (the `bounded e` measure rides
    printed, as in the `frist`/`quits` clauses). -/
def parseEingangNestedOpt (f : Nat)
    (toks : List Token) :
    Except String (Option String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "nested" then match rest with
        | .wort m :: r1 =>
          if strEq m "never" || strEq m "masked" then
            .ok (some m, r1)
          else if strEq m "bounded" then match parseOr f r1 with
            | .error e => .error e
            | .ok (e, r2) => .ok (some ("bounded " ++ druck e), r2)
          else .error "nested expected"
        | _ => .error "nested expected"
      else .ok (none, toks)
    | _ => .ok (none, toks)
def parseEingangDispatch (f : Nat)
    (toks : List Token) :
    Except String ((List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | _f + 1 => match nimmWort "dispatch" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (dp, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (dp, r)
/-- `entrust n at m arch a { regs in {…} stack s assume g ; }`. -/
def parseAnvertrautTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "entrust" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "at" r2 with
        | .error e => .error e
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (m, r4) => match nimmWort "arch" r4 with
            | .error e => .error e
            | .ok r5 => match nimmName r5 with
              | .error e => .error e
              | .ok (a, r6) => match fordereZeichen "{" r6 with
                | .error e => .error e
                | .ok r7 => match nimmWort "regs" r7 with
                  | .error e => .error e
                  | .ok r8 => match nimmWort "in" r8 with
                    | .error e => .error e
                    | .ok r9 => match parseRegBindListe f r9 with
                      | .error e => .error e
                      | .ok (ri, r10) => match nimmWort "stack" r10 with
                        | .error e => .error e
                        | .ok r11 => match nimmName r11 with
                          | .error e => .error e
                          | .ok (st, r12) =>
                            match nimmWort "assume" r12 with
                            | .error e => .error e
                            | .ok r13 => match nimmName r13 with
                              | .error e => .error e
                              | .ok (g, r14) =>
                                match fordereZeichen ";" r14 with
                                | .error e => .error e
                                | .ok r15 =>
                                  match fordereZeichen "}" r15 with
                                  | .error e => .error e
                                  | .ok r => .ok
                                    (.trustT n m a ri st g, r)
/-- `boot n arch a { steps dispatch p ; }`. -/
def parseStartTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "boot" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "arch" r2 with
        | .error e => .error e
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (a, r4) => match fordereZeichen "{" r4 with
            | .error e => .error e
            | .ok r5 => match parseBootSchritte f r5 with
              | .error e => .error e
              | .ok (ss, r6) => match nimmWort "dispatch" r6 with
                | .error e => .error e
                | .ok r7 => match nimmPfad r7 with
                  | .error e => .error e
                  | .ok (dp, r8) => match fordereZeichen ";" r8 with
                    | .error e => .error e
                    | .ok r9 => match fordereZeichen "}" r9 with
                      | .error e => .error e
                      | .ok r => .ok (.bootT n a ss dp, r)
def parseBootSchritte (f : Nat) (toks : List Token) :
    Except String (List SBootSchritt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if strEq s "step" then match parseBootSchritt f toks with
        | .error e => .error e
        | .ok (st, r1) => match parseBootSchritte f r1 with
          | .error e => .error e
          | .ok (ss, r) => .ok (st :: ss, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- `syscall V ;` (a variable) or a gate: `syscall g(params) [-> T] [or R]` then either the literal
    binding `abi A arch X <sysbind> <contract> <pair>` or `via V <contract> ;` (SYNTAX.md 12.1, 12.3). -/
def parseSysrufTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "syscall" toks
    let (n, r2) ← nimmName r1
    match r2 with
    | .zeichen ";" :: r => pure (.varT n, r)
    | _ => do
      let (ps, r3) ← parseParams f r2
      let (erg, fehler, r4) ← parseErgebnis f r3
      match r4 with
      | .wort "via" :: r5 => do
        let (v, r6) ← nimmName r5
        let (cv, r7) ← parseGate f r6
        let r ← fordereZeichen ";" r7
        pure (.callT { name := n, params := ps, res := erg, fail := fehler,
                         way := .via v, gate := cv }, r)
      | _ => do
        let r5 ← nimmWort "abi" r4
        let (abi, r6) ← nimmName r5
        let r7 ← nimmWort "arch" r6
        let (arch, r8) ← nimmName r7
        let (bd, r9) ← parseBind f r8
        let (cv, r10) ← parseGate f r9
        let (hk, r) ← parsePair r10
        pure (.callT { name := n, params := ps, res := erg, fail := fehler,
                         way := .lit abi arch bd hk, gate := cv }, r)
/-- `sysbind` (SYNTAX.md 12.1): `number e regs in {…} regs out {…} {stack r} clobbers {…} errors {…}`. -/
def parseBind (f : Nat) (toks : List Token) :
    Except String (SBind × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "number" toks
    let (num, r2) ← parseOr f r1
    let r3 ← nimmWort "regs" r2
    let r4 ← nimmWort "in" r3
    let (ri, r5) ← parseRegBindListe f r4
    let r6 ← nimmWort "regs" r5
    let r7 ← nimmWort "out" r6
    let (ro, r8) ← parseRegBindListe f r7
    let (sk, r9) ← parseStackClauses f r8
    let r10 ← nimmWort "clobbers" r9
    let (cb, r11) ← parseNamenEingeklammert f r10
    let r12 ← nimmWort "errors" r11
    let (em, r) ← parseErrs f r12
    pure ({ id := num, ins := ri, outs := ro, stack := sk, dirty := cb, codes := em }, r)
/-- `{ "stack" ident }` between `regs out` and `clobbers`. -/
def parseStackClauses (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort "stack" :: rest => do
      let (n, r1) ← nimmName rest
      let (ns, r) ← parseStackClauses f r1
      pure (n :: ns, r)
    | _ => pure ([], toks)
/-- The `errors {…}` map: `errno [= n] => Ground` pairs. -/
def parseErrs (f : Nat) (toks : List Token) :
    Except String (List (String × Option SExpr × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r ← fordereZeichen "{" toks
    parseErrsRest f r
/-- The pairs of an `errors` map behind its `{`, up to and including the `}`. -/
def parseErrsRest (f : Nat) (toks : List Token) :
    Except String (List (String × Option SExpr × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: r => .ok ([], r)
    | _ => do
      let (a, r1) ← nimmName toks
      let (num, r2) ← (match r1 with
        | .zeichen "=" :: r => do
          let (e, r') ← parseOr f r
          pure (some e, r')
        | _ => pure (none, r1))
      let r3 ← fordereZeichen "=>" r2
      let (b, r4) ← nimmName r3
      match r4 with
      | .zeichen "," :: r5 => do
        let (xs, r6) ← parseErrsRest f r5
        pure ((a, num, b) :: xs, r6)
      | _ => do
        let r5 ← fordereZeichen "}" r4
        pure ([(a, num, b)], r5)
/-- `syscontract`: `[requires p,…] [ensures p,…] effects {…} [costs <= e ops]`. -/
def parseGate (f : Nat) (toks : List Token) :
    Except String (SGate × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (rq, r1) ← (match toks with
      | .wort "requires" :: rest => parsePredListe f rest
      | _ => pure ([], toks))
    let (en, r2) ← (match r1 with
      | .wort "ensures" :: rest => parsePredListe f rest
      | _ => pure ([], r1))
    let r3 ← nimmWort "effects" r2
    let (ef, r4) ← parseEffektBlock f r3
    let (ko, r5) ← (match r4 with
      | .wort "costs" :: rest => do
        let r ← fordereZeichen "<=" rest
        let (e, ra) ← parseOr f r
        let rb ← nimmWort "ops" ra
        pure (some e, rb)
      | _ => pure (none, r4))
    pure ({ pre := rq, post := en, uses := ef, cost := ko }, r5)
/-- `syspair`: `assume a (falsifier s | unfalsifiable "…") ;` or `kernel path ;`. -/
def parsePair (toks : List Token) :
    Except String (SHerkunft × List Token) :=
  match toks with
  | .wort "assume" :: rest => do
    let (a, r1) ← nimmName rest
    let (k, r2) ← parseKlasse r1
    let r ← fordereZeichen ";" r2
    pure (.assum a k, r)
  | .wort "kernel" :: rest => do
    let (p, r1) ← nimmPfad rest
    let r ← fordereZeichen ";" r1
    pure (.core p, r)
  | _ => .error "syscall expected"
/-- `target T ;` (the selection) or `target T abi A arch X { V = <sysbind> <pair> … }` (SYNTAX.md 12.3). -/
def parseGoal (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "target" toks
    let (n, r2) ← nimmName r1
    match r2 with
    | .zeichen ";" :: r => pure (.goalT n none, r)
    | _ => do
      let r3 ← nimmWort "abi" r2
      let (abi, r4) ← nimmName r3
      let r5 ← nimmWort "arch" r4
      let (arch, r6) ← nimmName r5
      let r7 ← fordereZeichen "{" r6
      let (bs, r) ← parseGoalBinds f r7
      pure (.goalT n (some (abi, arch, bs)), r)
/-- The bindings `V = sysbind syspair` of a target body, up to and including its `}`. -/
def parseGoalBinds (f : Nat) (toks : List Token) :
    Except String (List (String × SBind × SHerkunft) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: r => .ok ([], r)
    | _ => do
      let (v, r1) ← nimmName toks
      let r2 ← fordereZeichen "=" r1
      let (bd, r3) ← parseBind f r2
      let (hk, r4) ← parsePair r3
      let (bs, r) ← parseGoalBinds f r4
      pure ((v, bd, hk) :: bs, r)
/-- `profile {…} ;` / `requires profile {…} ;` (section 12.2). -/
def parseProfilTief (f : Nat) (bedarf : Bool) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r1 => match parseProfEintraege f r1 with
      | .error e => .error e
      | .ok (es, r2) => match fordereZeichen "}" r2 with
        | .error e => .error e
        | .ok r3 => match fordereZeichen ";" r3 with
          | .error e => .error e
          | .ok r => .ok (.profT bedarf es, r)
def parseProfEintraege (f : Nat) (toks : List Token) :
    Except String (List SProfEintrag × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "arch" || strEq s "rounding" ||
          strEq s "fp_contract" || strEq s "memory_model" ||
          strEq s "interrupt_routing" then match nimmName rest with
        | .error e => .error e
        | .ok (v, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseProfEintraege f r2 with
            | .error e => .error e
            | .ok (es, r) => .ok (.mode s v :: es, r)
      else if strEq s "assume" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseProfEintraege f r2 with
            | .error e => .error e
            | .ok (es, r) => .ok (.assum a :: es, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
/-- The item levels of SYNTAX.md section 1 (`item`) in depth:
    every body rides structured. Against `parse.rs` `item`: the
    `when TESTBUILD` gate, the `pub` prefix, the `const fn`
    split and the head-word dispatch match one by one; the
    `fn`/`type` modifiers ride `art`/`flags` (see CUTS). -/
def parseItemsTief (f : Nat) (toks : List Token) :
    Except String (List SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: _ => .ok ([], toks)
    | .ende :: _ => .ok ([], toks)
    | [] => .ok ([], [])
    | _ => match parseItemTief f toks with
      | .error e => .error e
      | .ok (it, rest) => match parseItemsTief f rest with
        | .error e => .error e
        | .ok (its, r) => .ok (it :: its, r)
def parseItemTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "when" then match rest with
        | t :: rest' => match nameText t with
          | some u =>
            if strEq u "TESTBUILD" then match parseItemTief f rest' with
              | .ok (it, r) => .ok (.gateT it, r)
              | .error e => .error e
            else .error "when without TESTBUILD"
          | none => .error "when without TESTBUILD"
        | _ => .error "when without TESTBUILD"
      else if strEq s "pub" then parseItemTief f rest
      else parseItemKopfTief f toks
    | _ => parseItemKopfTief f toks
def parseItemKopfTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match sammleModifikatoren toks with
    | (mods, nach) => match nach with
      | .wort s :: rest =>
        if strEq s "module" then parseModulTief f nach
        else if strEq s "use" then parseUseTief nach
        else if strEq s "fn" then match parseFnSig f (letzteArt mods) nach with
          | .error e => .error e
          | .ok (sig, r) => parseFnRest f sig r
        else if strEq s "translator" then parseTranslatorTief f nach
        else if strEq s "profile" then parseProfilTief f false rest
        else if strEq s "requires" then match rest with
          | .wort t :: rest' =>
            if strEq t "profile" then parseProfilTief f true rest'
            else .error "requires without profile"
          | _ => .error "requires without profile"
        else if strEq s "concurrent" then parseNebenTief f nach
        else if strEq s "type" then parseTypTief f mods nach
        else if strEq s "const" then match rest with
          | .wort t :: _ =>
            if strEq t "fn" then match parseFnSig f "const" rest with
              | .error e => .error e
              | .ok (sig, r) => parseFnRest f sig r
            else match nimmWort "const" nach with
              | .error e => .error e
              | .ok r1 => parseKonstNach f r1
          | _ => match nimmWort "const" nach with
            | .error e => .error e
            | .ok r1 => parseKonstNach f r1
        else if strEq s "static" then parseGlobTief f nach
        else if strEq s "format" then parseFormatTief f nach
        else if strEq s "table" then parseTabellenTief f nach
        else if strEq s "arena" then parseArenaTief f nach
        else if strEq s "reason" then parseGrundTief f nach
        else if strEq s "state" then parseZustandTief f nach
        else if strEq s "device" then parseGeraetTief f nach
        else if strEq s "assume" then parseAnnahmeTief nach
        else if strEq s "axiom" then parseAxiomTief f nach
        else if strEq s "check" then parsePruefungTief f nach
        else if strEq s "atomic" then parseAtomarTief f nach
        else if strEq s "lock" then parseSperreTief f nach
        else if strEq s "rcu" then parseRcuTief f nach
        else if strEq s "group" then parseGruppeTief f nach
        else if strEq s "accumulates" then parseAkkumTief f nach
        else if strEq s "walk" then parseWegTief f nach
        else if strEq s "entry" then parseEingangTief f nach
        else if strEq s "entrust" then parseAnvertrautTief f nach
        else if strEq s "boot" then parseStartTief f nach
        else if strEq s "syscall" then parseSysrufTief f nach
        else if strEq s "target" then parseGoal f nach
        else .error "item expected"
      | _ => .error "item expected"
/-- The leading `fn`/`type` modifiers (`parse.rs` `item`); `const`
    is NOT among them (`const fn` splits on the next word). -/
def sammleModifikatoren : List Token → List String × List Token
  | .wort s :: rest =>
    if istMod s then
      let (ms, r) := sammleModifikatoren rest
      (s :: ms, r)
    else ([], .wort s :: rest)
  | toks => ([], toks)
/-- The `art` of a function: the last modifier, `""` for plain. -/
def letzteArt : List String → String
  | [] => ""
  | [a] => a
  | _ :: rest => letzteArt rest
/-- A whole program in depth: the token list must end here. -/
def parseTopTief (toks : List Token) : Except String (List SItemTief) :=
  match parseItemsTief (toks.length * 8 + 32) toks with
  | .ok (its, [.ende]) => .ok its
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e
/-- Shape equality on program outcomes, as a `Bool`. -/
def beqTopTief : Except String (List SItemTief) →
    Except String (List SItemTief) → Bool
  | .ok a, .ok b => beqSItemTiefList a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
end

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here, and every shape difference against
  `crates/gabbro-syntax` found by the probes.

  *Every difference below was found by reading `ast.rs`/`parse.rs`
  (`cargo` cannot run in this lane); each is a documented gap, not a
  silent one. Against `parse.rs`, this reader accepts a SUPERSET in
  the rows marked [SUPERSET]: a program it accepts and `parse.rs`
  refuses is a soundness-side gap of this reader, never of the
  checker.*

  1. No `pred` reader (SYNTAX.md section 5): contract and invariant
     bodies ride `SExpr`, so `forall`/`exists`, `e in domain`,
     `reaches … via …`, `=>` and `Held(L, shared)` have no shape
     and are refused. Every corpus invariant quantifies
     (beispiele/01 `wurzel_ohne_vorgaenger`, `baum_bleibt_baum`;
     beispiele/17 `wartende_haben_grund`;
     beispiele/07 `wx_getrennt`; beispiele/50 `boot_ende`
     ensures); the probes pin the member shapes with
     quantifier-free bodies (t30, t34). `Held(L)` rides
     `ruf "Held" [l]` (shape-compatible); a two-argument
     `Held(L, shared)` would ride the same call shape unchecked.
  2. `structty`, `variants` and `fnptr` ride `roh`: balanced but
     uninterpreted (t09). A misspelled field type inside reads
     clean here and falls in `parse.rs`.
  3. The `by`, `retires` and `deadline` tails ride printed/raw
     strings (`induktion`, `quits`, `frist`), not split
     (t54). A misspelled word inside reads clean here.
  4. [SUPERSET] Trailing commas are allowed in every comma list
     this reader takes (`effects`, predicate lists, name lists,
     field lists, carrier/binding/path lists, error maps,
     reason cases, edges) and empty `effects {}` is allowed;
     `parse.rs` (`efflist`, `placelist`, `identlist`, all without
     trailing commas) refuses them. Reason case numbers ride
     general expressions (`parseOr`); `parse.rs` takes a `Zahl`
     only (`erwarte_zahl`). A repeated `exhaustive` is refused
     here (the first one closes the list) and skipped there
     (`continue`).
  5. The `fn`/`type` modifiers ride one `art` (the last) and one
     flag list; `pub` is dropped, never recorded (the same `P041`
     cut as item 4 of `Element.lean`). Whether `payload` stands
     on a `library fn` (`P043`), whether `effects` is present
     (`pure` by default is a refusal, not a default), and every
     other clause-presence rule (`N200`-`N204`, `P044`) are NOT
     held -- shapes only, no checks.
  6. `= asm {…}` rides raw and balanced (t17); the `in`/`out`/
     `clobbers` maps inside are not split.
  7. A `bank` body rides raw and balanced; registers inside are
     not split (t45).
  8. `use` paths ride split (`List String`); `SItem.useS` keeps
     them raw.
  9. `cost O(e)` takes the name `O` in either token shape: `O`
     is an identifier in both lexers (`kw.rs` has no `O`
     keyword), not a keyword (t30).
  10. `regdecl` takes no trailing `;` (grammar and corpus agree);
     the first cut wrongly demanded one (t03/t46).
  11. `check` takes bare `measures`/`gates` lists (no braces),
     exactly as `parse.rs` `placelist`/`identlist` read them
     (t26); the first cut wrongly demanded braces.
  12. Reason cases are whitespace-separated (commas allowed);
     the first cut took only commas or the closing brace (t22).
  13. A transition step splits at the top-level `->`
     (`nimmBisPfeil`): the place rides the restricted
     `shiftplace` shape and the `from` side is parsed alone,
     because a bare `parseOr` eats `a -> b` as an arrow field
     (t23/t46).
  14. `beqSItemTief`/`beqTopTief` are not proved sound or
     complete (same cut as item 8 of `Anweisung.lean`).
  15. `parseTopTief` is total but not complete: fuel
     `length * 8 + 32` suffices for every probe (each `decide`
     checks its own fuel); a huge input may report out-of-fuel
     instead of parsing.
  16. No printer, no round trip: items have no `druck`, so there
     is no `print_parse` for this level.
  17. Supported but sight-unseen (no corpus occurrence, reader
     present): table `owner`/`shared` flags, entry `ist`/`bounded`
    /`via` tails, `uN` widths in signatures, float ranges with
     `rounded`.
  18. equally unprobed: a `translator` with contracts, an `axiom`
     with `requires` or a result type, `accumulates` without
     `per cpu`, `walk` with invariants, `atomic` with
     `publishes nothing`, `group … ;` without a body.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopTief
