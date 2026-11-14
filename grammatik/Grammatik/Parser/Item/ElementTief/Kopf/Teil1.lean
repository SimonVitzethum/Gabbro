module

public import Grammatik.Parser.Item.ElementTief.Kopf.Teil1a

public import Grammatik.Parser.Stmt.Anweisung

@[expose] public section



namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000
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
    share the production). Its evaluation is covered by the writer's costs. -/
structure SGruppenInv where
  name : String
  pred : SExpr
  deriving Repr

def beqSGruppenInv : SGruppenInv → SGruppenInv → Bool
  | a, b => strEq a.name b.name && beqSExpr a.pred b.pred

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

end Gabbro.Grammatik.Parser
