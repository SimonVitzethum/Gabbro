/-
  File:      Grammatik/Parser/ElementTief.lean
  Subject:   T3 PART 3: Gabbro items in depth (SYNTAX.md sections 1-2,
               6, 9-14) over the Lean statement reader.

  The surface types `STyp`/`SEffekt`/`SKlausel`/`FnSig`/`SItemTief`
  with fuel-indexed readers (`parseItemTief`, `parseTopTief`).
  Probes live in `Parser/ElementTiefProben.lean`.
-/
import Grammatik.Parser.Element

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/- A surface type: SYNTAX.md section 2 `typeexpr` without spans or
    checks. `atom` is one name, `pfad` a `::` path, `ptr` a
    `ptr<space, rights>` capability, `index` an `[option] index
    into T`, `bereich` a `base in lo .. hi` range (`exkl` for
    `..<`), `reihe` an array, `wickelnd` a `wrapping` width and
    `einbettet` an `embeds [hi:lo] [scale e]` field. A brace or
    `fn(…)` group (`structty`, `variants`, `fnptr`) rides `roh`,
    balanced but uninterpreted (see CUTS). -/
inductive STyp
  | atom : String → STyp
  | pfad : List String → STyp
  | ptr : String → String → STyp → STyp
  | index : Bool → String → STyp
  | bereich : STyp → SExpr → SExpr → Bool → STyp
  | reihe : STyp → SExpr → STyp
  | wickelnd : STyp → STyp
  | einbettet : STyp → String → Option SExpr → STyp
  | roh : String → STyp
  deriving Repr

-- Shape equality on surface types, as a `Bool`: one recursive
-- function plus the list helper, exactly like
-- `beqSExpr`/`beqSExprList` (which reduce by kernel evaluation).
mutual
def beqSTyp : STyp → STyp → Bool
  | .atom a, .atom b => strEq a b
  | .pfad a, .pfad b => beqWorte a b
  | .ptr r1 w1 t1, .ptr r2 w2 t2 =>
    strEq r1 r2 && strEq w1 w2 && beqSTyp t1 t2
  | .index o1 t1, .index o2 t2 => (o1 == o2) && strEq t1 t2
  | .bereich b1 l1 h1 x1, .bereich b2 l2 h2 x2 =>
    beqSTyp b1 b2 && beqSExpr l1 l2 && beqSExpr h1 h2 && (x1 == x2)
  | .reihe t1 n1, .reihe t2 n2 => beqSTyp t1 t2 && beqSExpr n1 n2
  | .wickelnd t1, .wickelnd t2 => beqSTyp t1 t2
  | .einbettet b1 s1 x1, .einbettet b2 s2 x2 =>
    beqSTyp b1 b2 && strEq s1 s2 && beqOptExpr x1 x2
  | .roh a, .roh b => strEq a b
  | _, _ => false
def beqSTypList : List STyp → List STyp → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSTyp x y && beqSTypList xs ys
  | _, _ => false
end

/- A surface effect: one arm of SYNTAX.md section 6 `eff`
    (`efflist`), the place arms as `SExpr` (`parse.rs` reads them
    as places; this reader has no `pred` reader, so contracts ride
    `SExpr` too -- see CUTS). `sperrt` carries the `shared` flag. -/
inductive SEffekt
  | liest : SExpr → SEffekt
  | schreibt : SExpr → SEffekt
  | sperrt : Bool → SExpr → SEffekt
  | maskiert : String → SEffekt
  | belegt : String → SEffekt
  | verbraucht : SExpr → SEffekt
  | veroeffentlicht : SExpr → SEffekt
  | weichtAb : SEffekt
  | rein : SEffekt
  deriving Repr

mutual
def beqSEffekt : SEffekt → SEffekt → Bool
  | .liest a, .liest b => beqSExpr a b
  | .schreibt a, .schreibt b => beqSExpr a b
  | .sperrt x a, .sperrt y b => (x == y) && beqSExpr a b
  | .maskiert a, .maskiert b => strEq a b
  | .belegt a, .belegt b => strEq a b
  | .verbraucht a, .verbraucht b => beqSExpr a b
  | .veroeffentlicht a, .veroeffentlicht b => beqSExpr a b
  | .weichtAb, .weichtAb => true
  | .rein, .rein => true
  | _, _ => false
def beqSEffektList : List SEffekt → List SEffekt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSEffekt x y && beqSEffektList xs ys
  | _, _ => false
end

/- One contract clause of SYNTAX.md section 6 `fndecl`: `voraus`
    and `sichert` ride one `SExpr` each (a `pred` is an `expr`
    shape here -- no `pred` reader, see CUTS); `erhaelt` and
    `verfeinert` ride name lists; `kosten` the `<= e ops`
    expression; `faellt` the `decreases` measure; `induktion` the
    raw `by` tail; `nutzlast` the `payload` path; `abschnitt` the
    `section` text; `rechenart` the `arch` name; `schreitetVor`
    the `advances a -> b` pair; `ziehtZurueck` the raw `retires`
    tail; `frist` the raw `deadline` tail (both raw tails are
    delimited, not interpreted -- see CUTS). -/
inductive SKlausel
  | voraus : SExpr → SKlausel
  | sichert : SExpr → SKlausel
  | erhaelt : List String → SKlausel
  | verfeinert : List String → SKlausel
  | kosten : SExpr → SKlausel
  | faellt : SExpr → SKlausel
  | induktion : String → SKlausel
  | nutzlast : List String → SKlausel
  | abschnitt : String → SKlausel
  | rechenart : String → SKlausel
  | schreitetVor : String → String → SKlausel
  | ziehtZurueck : String → SKlausel
  | frist : String → SKlausel
  | wirkung : List SEffekt → SKlausel
  deriving Repr

mutual
def beqSKlausel : SKlausel → SKlausel → Bool
  | .voraus a, .voraus b => beqSExpr a b
  | .sichert a, .sichert b => beqSExpr a b
  | .erhaelt a, .erhaelt b => beqWorte a b
  | .verfeinert a, .verfeinert b => beqWorte a b
  | .kosten a, .kosten b => beqSExpr a b
  | .faellt a, .faellt b => beqSExpr a b
  | .induktion a, .induktion b => strEq a b
  | .nutzlast a, .nutzlast b => beqWorte a b
  | .abschnitt a, .abschnitt b => strEq a b
  | .rechenart a, .rechenart b => strEq a b
  | .schreitetVor a b, .schreitetVor c d => strEq a c && strEq b d
  | .ziehtZurueck a, .ziehtZurueck b => strEq a b
  | .frist a, .frist b => strEq a b
  | .wirkung a, .wirkung b => beqSEffektList a b
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
    (`funktionT`/`protoT`/`specT`/`asmT` below). -/
structure FnSig where
  art : String
  name : String
  params : List (String × STyp)
  ergebnis : Option STyp
  fehler : Option String
  klauseln : List SKlausel
  deriving Repr

def beqParam : (String × STyp) → (String × STyp) → Bool
  | (a, x), (b, y) => strEq a b && beqSTyp x y

def beqParamList : List (String × STyp) → List (String × STyp) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqParam x y && beqParamList xs ys
  | _, _ => false

def beqOptTyp : Option STyp → Option STyp → Bool
  | none, none => true
  | some a, some b => beqSTyp a b
  | _, _ => false

def beqFnSig : FnSig → FnSig → Bool
  | s, t => strEq s.art t.art && strEq s.name t.name &&
    beqParamList s.params t.params && beqOptTyp s.ergebnis t.ergebnis &&
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
  rfname : String
  pos : String
  klasse : Option String
  deriving Repr

def beqSRegFeld : SRegFeld → SRegFeld → Bool
  | a, b => strEq a.rfname b.rfname && strEq a.pos b.pos &&
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

/- One device register: SYNTAX.md section 10 `regdecl`. `phasen`
    rides the raw `in`-stage words in order, `vorausSonst` the
    `else A::B` falsifier and `abhaengt` the `depends` carriers
    (each one or two segments). -/
structure SReg where
  rname : String
  rtyp : STyp
  adresse : SExpr
  klasse : String
  phasen : List String
  felder : List SRegFeld
  voraus : Option SExpr
  vorausSonst : Option (String × String)
  abhaengt : List (List String)
  deriving Repr

def beqSReg : SReg → SReg → Bool
  | a, b => strEq a.rname b.rname && beqSTyp a.rtyp b.rtyp &&
    beqSExpr a.adresse b.adresse &&
    strEq a.klasse b.klasse && beqWorte a.phasen b.phasen &&
    beqSRegFeldList a.felder b.felder && beqOptExpr a.voraus b.voraus &&
    beqOptPaarWort a.vorausSonst b.vorausSonst &&
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
    `online` the `runs` mode and `dabei` the raw `by` tail. -/
structure SGruppenInv where
  gname : String
  kosten : SExpr
  online : Bool
  dabei : Option String
  aussage : SExpr
  deriving Repr

def beqSGruppenInv : SGruppenInv → SGruppenInv → Bool
  | a, b => strEq a.gname b.gname && beqSExpr a.kosten b.kosten &&
    (a.online == b.online) && beqOptWort a.dabei b.dabei &&
    beqSExpr a.aussage b.aussage

def beqSGruppenInvList : List SGruppenInv → List SGruppenInv → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSGruppenInv x y && beqSGruppenInvList xs ys
  | _, _ => false

/- A `const` value: SYNTAX.md section 1 `constwert` -- a plain
    expression or an array literal (lane 111). -/
inductive SKonstWert
  | einzeln : SExpr → SKonstWert
  | reihe : List SExpr → SKonstWert
  deriving Repr

mutual
def beqSKonstWert : SKonstWert → SKonstWert → Bool
  | .einzeln a, .einzeln b => beqSExpr a b
  | .reihe a, .reihe b => beqSExprList a b
  | _, _ => false
end

/- One table member: SYNTAX.md section 9 `table` (`constdecl` /
    `slotdecl` / `invariant` / `opdecl` / `treedecl` / `occdecl`).
    A `tBaum` pair is (edge kind, field). -/
inductive STabTeil
  | tKonst : String → STyp → SKonstWert → STabTeil
  | tPlatz : List SFeld → STabTeil
  | tInvariante : SGruppenInv → STabTeil
  | tOps : List String → STabTeil
  | tBaum : List (String × String) → STabTeil
  | tBelegt : String → STabTeil
  deriving Repr

def beqKanteList : List (String × String) → List (String × String) → Bool
  | [], [] => true
  | (a, b) :: xs, (c, d) :: ys =>
    strEq a c && strEq b d && beqKanteList xs ys
  | _, _ => false

mutual
def beqSTabTeil : STabTeil → STabTeil → Bool
  | .tKonst a t v, .tKonst b u w =>
    strEq a b && beqSTyp t u && beqSKonstWert v w
  | .tPlatz a, .tPlatz b => beqSFeldList a b
  | .tInvariante a, .tInvariante b => beqSGruppenInv a b
  | .tOps a, .tOps b => beqWorte a b
  | .tBaum a, .tBaum b => beqKanteList a b
  | .tBelegt a, .tBelegt b => strEq a b
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
  | spiegel : SExpr → SExpr → SGerTeil
  | regTief : SReg → SGerTeil
  | bankRoh : String → SGerTeil
  | uebergangTief : STrans → SGerTeil
  deriving Repr

mutual
def beqSGerTeil : SGerTeil → SGerTeil → Bool
  | .spiegel a b, .spiegel c d => beqSExpr a c && beqSExpr b d
  | .regTief a, .regTief b => beqSReg a b
  | .bankRoh a, .bankRoh b => strEq a b
  | .uebergangTief a, .uebergangTief b => beqSTrans a b
  | _, _ => false
def beqSGerTeilList : List SGerTeil → List SGerTeil → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSGerTeil x y && beqSGerTeilList xs ys
  | _, _ => false
end

/- The assumption class: SYNTAX.md section 12 (`falsifier`
    vs `unfalsifiable`). Plain equality (no recursion). -/
inductive SAnKlasse
  | widerlegbar : String → SAnKlasse
  | unwiderlegbar : String → SAnKlasse
  deriving Repr

def beqSAnKlasse : SAnKlasse → SAnKlasse → Bool
  | .widerlegbar a, .widerlegbar b => strEq a b
  | .unwiderlegbar a, .unwiderlegbar b => strEq a b
  | _, _ => false

/- One profile entry: SYNTAX.md section 12.2 `profileentry` -- a
    keyed mode (`arch x86_64`) or an assumption reference. -/
inductive SProfEintrag
  | modusEintrag : String → String → SProfEintrag
  | annahmeEintrag : String → SProfEintrag
  deriving Repr

def beqSProfEintrag : SProfEintrag → SProfEintrag → Bool
  | .modusEintrag a b, .modusEintrag c d => strEq a c && strEq b d
  | .annahmeEintrag a, .annahmeEintrag b => strEq a b
  | _, _ => false

def beqSProfEintragList : List SProfEintrag → List SProfEintrag → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSProfEintrag x y && beqSProfEintragList xs ys
  | _, _ => false

/- One register binding: SYNTAX.md sections 12.1/14 `regbind` --
    `rdi = fd` binds, bare `rax` only names (the `:` spelling is
    accepted beside `=`, as the examples write both). -/
inductive SRegBind
  | bindet : String → String → SRegBind
  | register : String → SRegBind
  deriving Repr

def beqSRegBind : SRegBind → SRegBind → Bool
  | .bindet a b, .bindet c d => strEq a c && strEq b d
  | .register a, .register b => strEq a b
  | _, _ => false

def beqSRegBindList : List SRegBind → List SRegBind → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSRegBind x y && beqSRegBindList xs ys
  | _, _ => false

/- One boot step: SYNTAX.md section 14 `bootstep` -- a call or a
    `name = constexpr` assignment. -/
inductive SBootSchritt
  | rufSchritt : List String → List SExpr → SBootSchritt
  | setztSchritt : String → SExpr → SBootSchritt
  deriving Repr

def beqSBootSchritt : SBootSchritt → SBootSchritt → Bool
  | .rufSchritt a b, .rufSchritt c d =>
    beqWorte a c && beqSExprList b d
  | .setztSchritt a b, .setztSchritt c d => strEq a c && beqSExpr b d
  | _, _ => false

def beqSBootSchrittList : List SBootSchritt → List SBootSchritt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSBootSchritt x y && beqSBootSchrittList xs ys
  | _, _ => false

/- A `walk` declaration: SYNTAX.md section 9 `walkdecl`. -/
structure SWeg where
  wname : String
  stufen : SExpr
  knoten : STyp
  runterName : String
  runterWann : SExpr
  blatt : SExpr
  invarianten : List SGruppenInv
  deriving Repr

def beqSWeg : SWeg → SWeg → Bool
  | a, b => strEq a.wname b.wname && beqSExpr a.stufen b.stufen &&
    beqSTyp a.knoten b.knoten && strEq a.runterName b.runterName &&
    beqSExpr a.runterWann b.runterWann && beqSExpr a.blatt b.blatt &&
    beqSGruppenInvList a.invarianten b.invarianten

/- An `entry` declaration: SYNTAX.md section 1 `entrydecl`.
    `stapel`/`proCPU`/`ist`/`verschachtelt` are the `entryextra`
    tail; `dispatch` the dispatch path. -/
structure SEingang where
  ename : String
  vektor : Option SExpr
  via : Option String
  arch : String
  regRein : List SRegBind
  regRaus : List SRegBind
  erhaelt : List String
  zerstoert : List String
  stapel : String
  proCPU : Bool
  ist : Option SExpr
  verschachtelt : Option String
  dispatch : List String
  deriving Repr

def beqSEingang : SEingang → SEingang → Bool
  | a, b => strEq a.ename b.ename && beqOptExpr a.vektor b.vektor &&
    beqOptWort a.via b.via && strEq a.arch b.arch &&
    beqSRegBindList a.regRein b.regRein &&
    beqSRegBindList a.regRaus b.regRaus &&
    beqWorte a.erhaelt b.erhaelt && beqWorte a.zerstoert b.zerstoert &&
    strEq a.stapel b.stapel && (a.proCPU == b.proCPU) &&
    beqOptExpr a.ist b.ist && beqOptWort a.verschachtelt b.verschachtelt &&
    beqWorte a.dispatch b.dispatch

/- A `check` declaration: SYNTAX.md section 13. The `can_fail`
    body rides `SAnw` (via `parseBlock`); `sonde` is the
    `counterprobe ... expects ...` pair. -/
structure SCheck where
  cname : String
  behauptung : String
  misst : List SExpr
  tore : List String
  kannScheitern : SAnw
  boden : List SExpr
  sonde : Option (String × String)
  deriving Repr

def beqSCheck : SCheck → SCheck → Bool
  | a, b => strEq a.cname b.cname && strEq a.behauptung b.behauptung &&
    beqSExprList a.misst b.misst && beqWorte a.tore b.tore &&
    beqSAnw a.kannScheitern b.kannScheitern &&
    beqSExprList a.boden b.boden && beqOptPaarWort a.sonde b.sonde

/- Where a `syscall` rests: SYNTAX.md section 12.1 (a named
    assumption with its falsifier, or a `kernel` dispatch path). -/
inductive SHerkunft
  | annahmeHerkunft : String → SAnKlasse → SHerkunft
  | kernHerkunft : List String → SHerkunft
  deriving Repr

def beqSHerkunft : SHerkunft → SHerkunft → Bool
  | .annahmeHerkunft a b, .annahmeHerkunft c d =>
    strEq a c && beqSAnKlasse b d
  | .kernHerkunft a, .kernHerkunft b => beqWorte a b
  | _, _ => false

/- A `syscall` declaration: SYNTAX.md section 12.1 `syscalldecl`.
    `sfehlerAbb` is the `errors` map; `svoraus`/`ssichert` the
    contract lists. -/
structure SSyscall where
  sname : String
  sparams : List (String × STyp)
  sergebnis : Option STyp
  sfehler : Option String
  abi : String
  sarch : String
  nummer : SExpr
  sregRein : List SRegBind
  sregRaus : List SRegBind
  szerstoert : List String
  sfehlerAbb : List (String × String)
  svoraus : List SExpr
  ssichert : List SExpr
  swirkung : List SEffekt
  sherkunft : SHerkunft
  deriving Repr

def beqSSyscall : SSyscall → SSyscall → Bool
  | a, b => strEq a.sname b.sname &&
    beqParamList a.sparams b.sparams &&
    beqOptTyp a.sergebnis b.sergebnis && beqOptWort a.sfehler b.sfehler &&
    strEq a.abi b.abi && strEq a.sarch b.sarch &&
    beqSExpr a.nummer b.nummer &&
    beqSRegBindList a.sregRein b.sregRein &&
    beqSRegBindList a.sregRaus b.sregRaus &&
    beqWorte a.szerstoert b.szerstoert &&
    beqKanteList a.sfehlerAbb b.sfehlerAbb &&
    beqSExprList a.svoraus b.svoraus &&
    beqSExprList a.ssichert b.ssichert &&
    beqSEffektList a.swirkung b.swirkung &&
    beqSHerkunft a.sherkunft b.sherkunft

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
    shares the shape but skips every body): `modulT` = `Modul`,
    `useT` = `Use`, `typT` = `Typ`, `konstT` = `Konst`, `statikT` =
    `Statisch`, `funktionT` = `Funktion`, `protoT` = a bodiless
    declaration (`fn …;`), `specT` = `spec fn … = pred;`,
    `asmT` = `= asm {…};`, `formatT` = `Format`, `tabelleT` =
    `Tabelle`, `arenaT` = `Arena`, `grundT` = `Reason`,
    `zustandT` = `State`, `geraetT` = `Device`, `annahmeT` =
    `Assume`, `axiomaT` = `Axiom`, `pruefungT` = `Check`,
    `atomarT` = `Atomic`, `sperreT` = `Lock`, `rcuT` = `Rcu`,
    `gruppeT` = `Gruppe`, `nebenT` = `Concurrent`, `akkumT` =
    `Accumulates`, `wegT` = `Walk`, `eingangT` = `Entry`,
    `anvertrautT` = `Entrust`, `startT` = `Boot`, `sysrufT` =
    `Syscall`, `uebersetzerT` = `Translator`, `profilT` =
    `Profil` / `ProfilBedarf` (`bedarf` flag), `torT` = the `when
    TESTBUILD` gate. -/
inductive SItemTief
  | modulT : String → List SItemTief → SItemTief
  | useT : List String → SItemTief
  | typT : List String → String → List STyp → List String → Option STyp → SItemTief
  | konstT : String → STyp → SKonstWert → SItemTief
  | statikT : Bool → String → STyp → SExpr → Option String → Bool → SItemTief
  | funktionT : FnSig → SAnw → SItemTief
  | protoT : FnSig → SItemTief
  | specT : FnSig → SExpr → SItemTief
  | asmT : FnSig → String → SItemTief
  | formatT : String → Option SExpr → Option String → List SFeld → SItemTief
  | tabelleT : String → Option SExpr → Option String → Option String → Bool → List STabTeil → SItemTief
  | arenaT : String → SExpr → SExpr → STyp → SItemTief
  | grundT : String → List (String × SExpr × String) → Bool → SItemTief
  | zustandT : String → List STrans → SItemTief
  | geraetT : String → List (String × STyp) → String → List SGerTeil → SItemTief
  | annahmeT : String → Option String → String → SAnKlasse → SItemTief
  | axiomaT : String → List (String × STyp) → Option STyp → Option SExpr → List SEffekt → SAnKlasse → SItemTief
  | pruefungT : SCheck → SItemTief
  | atomarT : String → STyp → Option (List SExpr) → Option String → Option String → SItemTief
  | sperreT : String → List SExpr → SExpr → Option SExpr → Option SExpr → Option String → SItemTief
  | rcuT : String → List SExpr → Option SExpr → SItemTief
  | gruppeT : String → List String → List SGruppenInv → SItemTief
  | nebenT : List (List String) → SItemTief
  | akkumT : String → STyp → String → Option SExpr → SItemTief
  | wegT : SWeg → SItemTief
  | eingangT : SEingang → SItemTief
  | anvertrautT : String → String → String → List SRegBind → String → String → SItemTief
  | startT : String → String → List SBootSchritt → List String → SItemTief
  | sysrufT : SSyscall → SItemTief
  | uebersetzerT : String → FnSig → SAnw → SItemTief
  | profilT : Bool → List SProfEintrag → SItemTief
  | torT : SItemTief → SItemTief
  deriving Repr

mutual
def beqSItemTief : SItemTief → SItemTief → Bool
  | .modulT a b, .modulT c d => strEq a c && beqSItemTiefList b d
  | .useT a, .useT b => beqWorte a b
  | .typT f1 a t1 o1 r1, .typT f2 b t2 o2 r2 =>
    beqWorte f1 f2 && strEq a b && beqSTypList t1 t2 &&
    beqWorte o1 o2 && beqOptTyp r1 r2
  | .konstT a t v, .konstT b u w =>
    strEq a b && beqSTyp t u && beqSKonstWert v w
  | .statikT m1 a t v s1 g1, .statikT m2 b u w s2 g2 =>
    (m1 == m2) && strEq a b && beqSTyp t u && beqSExpr v w &&
    beqOptWort s1 s2 && (g1 == g2)
  | .funktionT s b, .funktionT t d => beqFnSig s t && beqSAnw b d
  | .protoT s, .protoT t => beqFnSig s t
  | .specT s p, .specT t q => beqFnSig s t && beqSExpr p q
  | .asmT s a, .asmT t b => beqFnSig s t && strEq a b
  | .formatT a v e f, .formatT b w g h =>
    strEq a b && beqOptExpr v w && beqOptWort e g && beqSFeldList f h
  | .tabelleT a c b o g p, .tabelleT d f e h i q =>
    strEq a d && beqOptExpr c f && beqOptWort b e &&
    beqOptWort o h && (g == i) && beqSTabTeilList p q
  | .arenaT a l h t, .arenaT b m i u =>
    strEq a b && beqSExpr l m && beqSExpr h i && beqSTyp t u
  | .grundT a c e, .grundT b d f =>
    strEq a b && beqGrundFallList c d && (e == f)
  | .zustandT a t, .zustandT b u => strEq a b && beqSTransList t u
  | .geraetT a p s m, .geraetT b q t n =>
    strEq a b && beqParamList p q && strEq s t && beqSGerTeilList m n
  | .annahmeT a c t k, .annahmeT b d u l =>
    strEq a b && beqOptWort c d && strEq t u && beqSAnKlasse k l
  | .axiomaT a p r q e k, .axiomaT b s t u f l =>
    strEq a b && beqParamList p s && beqOptTyp r t &&
    beqOptExpr q u && beqSEffektList e f && beqSAnKlasse k l
  | .pruefungT a, .pruefungT b => beqSCheck a b
  | .atomarT a t p o b, .atomarT c u q s d =>
    strEq a c && beqSTyp t u && beqOptExprList p q &&
    beqOptWort o s && beqOptWort b d
  | .sperreT a p r h s m, .sperreT b q t i u n =>
    strEq a b && beqSExprList p q && beqSExpr r t &&
    beqOptExpr h i && beqOptExpr s u && beqOptWort m n
  | .rcuT a p r, .rcuT b q s =>
    strEq a b && beqSExprList p q && beqOptExpr r s
  | .gruppeT a m i, .gruppeT b n j =>
    strEq a b && beqWorte m n && beqSGruppenInvList i j
  | .nebenT a, .nebenT b => beqWortListe a b
  | .akkumT a t m p, .akkumT b u n q =>
    strEq a b && beqSTyp t u && strEq m n && beqOptExpr p q
  | .wegT a, .wegT b => beqSWeg a b
  | .eingangT a, .eingangT b => beqSEingang a b
  | .anvertrautT a b c r s t, .anvertrautT d e f u v w =>
    strEq a d && strEq b e && strEq c f && beqSRegBindList r u &&
    strEq s v && strEq t w
  | .startT a c s d, .startT b e t f =>
    strEq a b && strEq c e && beqSBootSchrittList s t && beqWorte d f
  | .sysrufT a, .sysrufT b => beqSSyscall a b
  | .uebersetzerT f s b, .uebersetzerT g t d =>
    strEq f g && beqFnSig s t && beqSAnw b d
  | .profilT a e, .profilT b f =>
    (a == b) && beqSProfEintragList e f
  | .torT a, .torT b => beqSItemTief a b
  | _, _ => false
def beqSItemTiefList : List SItemTief → List SItemTief → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSItemTief x y && beqSItemTiefList xs ys
  | _, _ => false
end

-- The deep readers of SYNTAX.md sections 2 (`typeexpr`), 6
-- (`fndecl` heads, `eff`, clauses) and 1/9-14 (items), each
-- with fuel: every call passes strictly less fuel, so the block
-- terminates by `f`. Against `parse.rs`: the clause order is
-- free (the loop dispatches on the head word), `requires` /
-- `ensures` take comma-separated `predlist`s, `effects` the
-- `efflist` and `costs` the `<= e ops` shape -- one by one.
-- Predicates ride `SExpr` (no `pred` reader, same cut as item 1
-- of `Anweisung.lean`); comma lists allow a trailing comma (see
-- CUTS).

/-- The clause head words of `fndecl` (SYNTAX.md section 6). -/
def istKlauselKopf (s : String) : Bool :=
  ["requires", "ensures", "maintains", "refines", "effects",
   "costs", "deadline", "decreases", "by", "section", "arch",
   "payload", "advances", "retires"].any (strEq · s)

/-- A `::` path: one name plus `sammleSegmente`. -/
def nimmPfad : List Token → Except String (List String × List Token)
  | t :: rest => match nameText t with
    | some s => let (segs, r) := sammleSegmente rest [s]; .ok (segs, r)
    | none => .error "path expected"
  | [] => .error "path expected"

/-- A string literal token (claims, sections, assumptions). -/
def nimmTextTok : List Token → Except String (String × List Token)
  | .text s :: rest => .ok (s, rest)
  | _ => .error "string expected"

/-- Is the next token this punctuation? -/
def istZeichenZ (z : String) : List Token → Bool
  | .zeichen s :: _ => strEq s z
  | _ => false

/-- Raw words of a balanced group whose opener is already
    counted (`pr`/`pk`/`pg` are the pending `)`/`]`/`}`).
    Structural on the token list. -/
def sammleAusgewogen : List Token → Nat → Nat → Nat →
    Except String (String × List Token)
  | [], _, _, _ => .error "unbalanced group"
  | (.zeichen s :: rest), pr, pk, pg =>
    if strEq s "(" then match sammleAusgewogen rest (pr + 1) pk pg with
      | .ok (h, r) => .ok ("( " ++ h, r)
      | .error e => .error e
    else if strEq s ")" then
      if pr == 0 then .error "unbalanced group"
      else if pr == 1 && pk == 0 && pg == 0 then .ok (") ", rest)
      else match sammleAusgewogen rest (pr - 1) pk pg with
        | .ok (h, r) => .ok (") " ++ h, r)
        | .error e => .error e
    else if strEq s "[" then match sammleAusgewogen rest pr (pk + 1) pg with
      | .ok (h, r) => .ok ("[ " ++ h, r)
      | .error e => .error e
    else if strEq s "]" then
      if pk == 0 then .error "unbalanced group"
      else if pr == 0 && pk == 1 && pg == 0 then .ok ("] ", rest)
      else match sammleAusgewogen rest pr (pk - 1) pg with
        | .ok (h, r) => .ok ("] " ++ h, r)
        | .error e => .error e
    else if strEq s "{" then match sammleAusgewogen rest pr pk (pg + 1) with
      | .ok (h, r) => .ok ("{ " ++ h, r)
      | .error e => .error e
    else if strEq s "}" then
      if pg == 0 then .error "unbalanced group"
      else if pr == 0 && pk == 0 && pg == 1 then .ok ("} ", rest)
      else match sammleAusgewogen rest pr pk (pg - 1) with
        | .ok (h, r) => .ok ("} " ++ h, r)
        | .error e => .error e
    else match sammleAusgewogen rest pr pk pg with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (t :: rest), pr, pk, pg => match sammleAusgewogen rest pr pk pg with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- Raw words until a clause head, a body `{`, `;`, `=` or the
    end (the `by` tail). Structural on the token list. -/
def nimmBisKopf : List Token → Except String (String × List Token)
  | [] => .ok ("", [])
  | (.wort s :: rest) =>
    if istKlauselKopf s then .ok ("", .wort s :: rest)
    else match nimmBisKopf rest with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (.zeichen s :: rest) =>
    if strEq s "{" || strEq s ";" || strEq s "=" then
      .ok ("", .zeichen s :: rest)
    else match nimmBisKopf rest with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (.ende :: rest) => .ok ("", .ende :: rest)
  | (t :: rest) => match nimmBisKopf rest with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- The assumption class: `falsifier n` or `unfalsifiable "…"`. -/
def parseKlasse : List Token → Except String (SAnKlasse × List Token)
  | .wort s :: rest =>
    if strEq s "falsifier" then match nimmName rest with
      | .ok (n, r) => .ok (.widerlegbar n, r)
      | .error e => .error e
    else if strEq s "unfalsifiable" then match nimmTextTok rest with
      | .ok (t, r) => .ok (.unwiderlegbar t, r)
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
def parseTyp (f : Nat) (toks : List Token) :
    Except String (STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "ptr" then match fordereZeichen "<" rest with
        | .error e => .error e
        | .ok r1 => match nimmName r1 with
          | .error e => .error e
          | .ok (raum, r2) => match fordereZeichen "," r2 with
            | .error e => .error e
            | .ok r3 => match nimmName r3 with
              | .error e => .error e
              | .ok (rechte, r4) => match fordereZeichen ">" r4 with
                | .error e => .error e
                | .ok r5 => match parseTyp f r5 with
                  | .error e => .error e
                  | .ok (ziel, r) => .ok (.ptr raum rechte ziel, r)
      else if strEq s "option" then match rest with
        | .wort t :: rest' =>
          if strEq t "index" then match nimmWort "into" rest' with
            | .error e => .error e
            | .ok r => match nimmName r with
              | .error e => .error e
              | .ok (n, r') => .ok (.index true n, r')
          else .error "type expected"
        | _ => .error "type expected"
      else if strEq s "index" then match nimmWort "into" rest with
        | .error e => .error e
        | .ok r => match nimmName r with
          | .error e => .error e
          | .ok (n, r') => .ok (.index false n, r')
      else if strEq s "fn" then match fordereZeichen "(" rest with
        | .error e => .error e
        | .ok r => match sammleAusgewogen r 1 0 0 with
          | .error e => .error e
          | .ok (h, r') =>
            match nimmBisKopf r' with
            | .error e => .error e
            | .ok (t, r'') => .ok (.roh ("fn ( " ++ h ++ t), r'')
      else match nimmPfad toks with
        | .error e => .error e
        | .ok (segs, r) => match segs with
          | [] => .error "type expected"
          | [a] => parseTypNach f (.atom a) r
          | _ => parseTypNach f (.pfad segs) r
    | .zeichen "{" :: rest => match nimmBereichWorte rest 1 with
      | .error e => .error e
      | .ok (h, r) => .ok (.roh ("{ " ++ h), r)
    | .zeichen "[" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r1) => match fordereZeichen ";" r1 with
        | .error e => .error e
        | .ok r2 => match parseOr f r2 with
          | .error e => .error e
          | .ok (n, r3) => match fordereZeichen "]" r3 with
            | .error e => .error e
            | .ok r => .ok (.reihe t n, r)
    | _ => .error "type expected"
/-- The `in range` / `wrapping` / `embeds` suffixes behind a base
    type (`intty`, `slottype`, `fieldty`). -/
def parseTypNach (f : Nat) (basis : STyp) (toks : List Token) :
    Except String (STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "in" then match parseOr f rest with
        | .error e => .error e
        | .ok (lo, r1) => match r1 with
          | .zeichen o :: r2 =>
            if strEq o ".." || strEq o "..<" then
              match parseOr f r2 with
              | .error e => .error e
              | .ok (hi, r) =>
                parseTypNach f (.bereich basis lo hi (strEq o "..<")) r
            else .error "range expected"
          | _ => .error "range expected"
      else if strEq s "wrapping" then
        parseTypNach f (.wickelnd basis) rest
      else if strEq s "embeds" then match fordereZeichen "[" rest with
        | .error e => .error e
        | .ok r1 => match sammleAusgewogen r1 0 1 0 with
          | .error e => .error e
          | .ok (h, r2) => match r2 with
            | .wort t :: r3 =>
              if strEq t "scale" then match parseOr f r3 with
                | .error e => .error e
                | .ok (e, r) =>
                  parseTypNach f (.einbettet basis h (some e)) r
              else parseTypNach f (.einbettet basis h none) r2
            | _ => parseTypNach f (.einbettet basis h none) r2
      else .ok (basis, toks)
    | _ => .ok (basis, toks)
/-- One effect arm of `eff`. -/
def parseEffekt (f : Nat) (toks : List Token) :
    Except String (SEffekt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "reads" then match parseOr f rest with
        | .ok (p, r) => .ok (.liest p, r)
        | .error e => .error e
      else if strEq s "writes" then match parseOr f rest with
        | .ok (p, r) => .ok (.schreibt p, r)
        | .error e => .error e
      else if strEq s "locks" then match rest with
        | .wort t :: rest' =>
          if strEq t "shared" then match parseOr f rest' with
            | .ok (p, r) => .ok (.sperrt true p, r)
            | .error e => .error e
          else match parseOr f rest with
            | .ok (p, r) => .ok (.sperrt false p, r)
            | .error e => .error e
        | _ => match parseOr f rest with
          | .ok (p, r) => .ok (.sperrt false p, r)
          | .error e => .error e
      else if strEq s "masks" then match nimmName rest with
        | .ok (n, r) => .ok (.maskiert n, r)
        | .error e => .error e
      else if strEq s "allocs" then match nimmName rest with
        | .ok (n, r) => .ok (.belegt n, r)
        | .error e => .error e
      else if strEq s "consumes" then match parseOr f rest with
        | .ok (p, r) => .ok (.verbraucht p, r)
        | .error e => .error e
      else if strEq s "publishes" then match parseOr f rest with
        | .ok (p, r) => .ok (.veroeffentlicht p, r)
        | .error e => .error e
      else if strEq s "diverges" then .ok (.weichtAb, rest)
      else if strEq s "pure" then .ok (.rein, rest)
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
  | f + 1 => match parseOr f toks with
    | .error e => .error e
    | .ok (p, rest) => match rest with
      | .zeichen "," :: rest' =>
        match parseOr f rest' with
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
        | .ok (ps, r) => .ok (ps.map .voraus, r)
        | .error e => .error e
      else if strEq s "ensures" then match parsePredListe f rest with
        | .ok (ps, r) => .ok (ps.map .sichert, r)
        | .error e => .error e
      else if strEq s "maintains" then match parseNamenListe f rest with
        | .ok (ns, r) => .ok ([.erhaelt ns], r)
        | .error e => .error e
      else if strEq s "refines" then match nimmPfad rest with
        | .ok (p, r) => .ok ([.verfeinert p], r)
        | .error e => .error e
      else if strEq s "effects" then match fordereZeichen "{" rest with
        | .error e => .error e
        | .ok r1 => match r1 with
          | .zeichen "}" :: r2 => .ok ([.wirkung []], r2)
          | _ => match parseEffektListe f r1 with
            | .error e => .error e
            | .ok (es, r2) => match fordereZeichen "}" r2 with
              | .error e => .error e
              | .ok r => .ok ([.wirkung es], r)
      else if strEq s "costs" then match fordereZeichen "<=" rest with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (e, r2) => match nimmWort "ops" r2 with
            | .error e2 => .error e2
            | .ok r => .ok ([.kosten e], r)
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
                    | .widerlegbar n => .ok ([.frist
                      ("deadline <= " ++ druck e ++ " ops arch " ++ a ++
                       " falsifier " ++ n)], r)
                    | .unwiderlegbar t => .ok ([.frist
                      ("deadline <= " ++ druck e ++ " ops arch " ++ a ++
                       " unfalsifiable \"" ++ t ++ "\"")], r)
      else if strEq s "decreases" then match parseOr f rest with
        | .ok (e, r) => .ok ([.faellt e], r)
        | .error e => .error e
      else if strEq s "by" then match nimmBisKopf rest with
        | .ok (h, r) => .ok ([.induktion h], r)
        | .error e => .error e
      else if strEq s "section" then match nimmTextTok rest with
        | .ok (t, r) => .ok ([.abschnitt t], r)
        | .error e => .error e
      else if strEq s "arch" then match nimmName rest with
        | .ok (n, r) => .ok ([.rechenart n], r)
        | .error e => .error e
      else if strEq s "payload" then match nimmPfad rest with
        | .ok (p, r) => .ok ([.nutzlast p], r)
        | .error e => .error e
      else if strEq s "advances" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r1) => match fordereZeichen "->" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (b, r) => .ok ([.schreitetVor a b], r)
      else if strEq s "retires" then match nimmName rest with
        | .error e => .error e
        | .ok (m, r1) => match nimmWort "from" r1 with
          | .error e2 => .error e2
          | .ok r2 => match nimmName r2 with
            | .error e3 => .error e3
            | .ok (sp, r3) => match parseKlasse r3 with
              | .error e4 => .error e4
              | .ok (k, r) => match k with
                | .widerlegbar n => .ok ([.ziehtZurueck
                  (m ++ " from " ++ sp ++ " falsifier " ++ n)], r)
                | .unwiderlegbar t => .ok ([.ziehtZurueck
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
              .ok ({ art, name, params := ps, ergebnis := erg,
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
/-- Behind the head: a block body (`funktionT`), `;`
    (`protoT`), `= pred ;` (`specT`) or `= asm {…} ;` (`asmT`). -/
def parseFnRest (f : Nat) (sig : FnSig) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "{" :: _ => match parseBlock f toks with
      | .error e => .error e
      | .ok (b, r) => .ok (.funktionT sig b, r)
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
        else match parseOr f rest with
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
      else if strEq s "where" then match parseOr f rest with
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
      | .zahl _ => .ok (zeigeTok t, rest)
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
      | _ => match parseFeld f r with
        | .error e => .error e
        | .ok (fd, r1) => match r1 with
          | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([fd], r3)
            | _ => match parseFeldListe f r2 with
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
              | .ok (c, r) => .ok ({ rfname := n, pos := b, klasse := some c }, r)
            else .ok ({ rfname := n, pos := b, klasse := none }, r3)
          | _ => .ok ({ rfname := n, pos := b, klasse := none }, r3)
def parseRegFeldListe (f : Nat) (toks : List Token) :
    Except String (List SRegFeld × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseRegFeld f r with
        | .error e => .error e
        | .ok (fd, r1) => match r1 with
          | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([fd], r3)
            | _ => match parseRegFeldListe f r2 with
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
              ({ rname := n, rtyp := t,
                 adresse := .variable "", klasse := "", phasen := [],
                 felder := [], voraus := none, vorausSonst := none,
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
      | .ok (e, r) => parseRegRest f { rg with adresse := e } r
    | .wort s :: rest =>
      if strEq s "class" then match nimmName rest with
        | .error e => .error e
        | .ok (c, r1) => match parsePhasen f r1 with
          | .error e => .error e
          | .ok (ph, r) =>
            parseRegRest f { rg with klasse := c, phasen := ph } r
      else if strEq s "fields" then match parseRegFeldListe f rest with
        | .error e => .error e
        | .ok (fds, r) => parseRegRest f { rg with felder := fds } r
      else if strEq s "requires" then match parseOr f rest with
        | .error e => .error e
        | .ok (p, r1) => match r1 with
          | .wort t :: r2 =>
            if strEq t "else" then match nimmPfad r2 with
              | .error e => .error e
              | .ok ([a, b], r) => parseRegRest f
                { rg with voraus := some p,
                          vorausSonst := some (a, b) } r
              | .ok _ => .error "else expected"
            else parseRegRest f { rg with voraus := some p } r1
          | _ => parseRegRest f { rg with voraus := some p } r1
      else if strEq s "depends" then match parseTraegerListe f rest with
        | .error e => .error e
        | .ok (cs, r) => parseRegRest f { rg with abhaengt := cs } r
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok (rg, r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok (rg, r)
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
      | _ => match parseTraeger r with
        | .error e => .error e
        | .ok (c, r1) => match r1 with
          | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([c], r3)
            | _ => match parseTraegerListe f r2 with
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
  | f + 1 => match parseOr f toks with
    | .error e => .error e
    | .ok (p, r1) => match fordereZeichen ":" r1 with
      | .error e => .error e
      | .ok r2 => match parseOr f r2 with
        | .error e => .error e
        | .ok (a, r3) => match fordereZeichen "->" r3 with
          | .error e => .error e
          | .ok r4 => match parseOr f r4 with
            | .error e => .error e
            | .ok (b, r5) => match r5 with
              | .zeichen "," :: r6 => match parseSchritte f r6 with
                | .error e => .error e
                | .ok (ss, r) => .ok ((p, a, b) :: ss, r)
              | _ => .ok ([(p, a, b)], r5)
def parseTransRest (f : Nat) (tr : STrans) (toks : List Token) :
    Except String (STrans × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "requires" then match parseOr f rest with
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
        | .ok r3 => match nimmWort "O" r3 with
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
                        | .ok ((dabei, p), r) => .ok
                          ({ gname := n, kosten := c,
                             online := strEq m "online", dabei := dabei,
                             aussage := p }, r)
                      else .error "runs expected"
                    | _ => .error "runs expected"
def parseInvRest (f : Nat) (toks : List Token) :
    Except String ((Option String × SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "by" then match nimmBisKopf rest with
        | .error e => .error e
        | .ok (h, r1) => match fordereZeichen ":" r1 with
          | .error e => .error e
          | .ok r2 => match parseOr f r2 with
            | .error e => .error e
            | .ok (p, r3) => match fordereZeichen ";" r3 with
              | .error e => .error e
              | .ok r => .ok (((some h, p)), r)
      else match fordereZeichen ":" toks with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (p, r2) => match fordereZeichen ";" r2 with
            | .error e => .error e
            | .ok r => .ok (((none, p)), r)
    | _ => match fordereZeichen ":" toks with
      | .error e => .error e
      | .ok r1 => match parseOr f r1 with
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
      | _ => match parseRegBind r with
        | .error e => .error e
        | .ok (b, r1) => match r1 with
          | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([b], r3)
            | _ => match parseRegBindListe f r2 with
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
          | .ok (b, r'') => .ok (.bindet a b, r'')
        else .ok (.register a, r)
      | _ => .ok (.register a, r)
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
      | _ => match nimmPfad r with
        | .error e => .error e
        | .ok (p, r1) => match r1 with
          | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([p], r3)
            | _ => match parsePfadListe f r2 with
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
            | .ok r => .ok (.rufSchritt p [], r)
          | _ => match parsePredListe f r3 with
            | .error e => .error e
            | .ok (as, r4) => match fordereZeichen ")" r4 with
              | .error e => .error e
              | .ok r5 => match fordereZeichen ";" r5 with
                | .error e => .error e
                | .ok r => .ok (.rufSchritt p as, r)
        | .zeichen "=" :: r3 => match parseOr f r3 with
          | .error e => .error e
          | .ok (e, r4) => match fordereZeichen ";" r4 with
            | .error e => .error e
            | .ok r => match p with
              | [n] => .ok (.setztSchritt n e, r)
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
            | .ok r => .ok (.modulT ("::".intercalate p) its, r)
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
                | .ok r => .ok (.typT flags n args ord (some t), r)
            | _ => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.typT flags n args ord none, r)
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
              | .ok r => .ok (.konstT n t v, r)
/-- A `constwert`: an expression or an array literal (lane 111). -/
def parseKonstWert (f : Nat) (toks : List Token) :
    Except String (SKonstWert × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "[" :: rest => match rest with
      | .zeichen "]" :: r => .ok (.reihe [], r)
      | _ => match parsePredListe f rest with
        | .error e => .error e
        | .ok (es, r1) => match r1 with
          | .zeichen "," :: r2 => match fordereZeichen "]" r2 with
            | .error e => .error e
            | .ok r => .ok (.reihe es, r)
          | _ => match fordereZeichen "]" r1 with
            | .error e => .error e
            | .ok r => .ok (.reihe es, r)
    | _ => match parseOr f toks with
      | .error e => .error e
      | .ok (e, r) => .ok (.einzeln e, r)
/-- `static [mut] n : T = e [section s] [shared] ;`. -/
def parseStatikTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "static" toks with
    | .error e => .error e
    | .ok r1 => match r1 with
      | .wort s :: r2 =>
        if strEq s "mut" then match parseStatikNach f true r2 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
        else match parseStatikNach f false r1 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
      | _ => match parseStatikNach f false r1 with
        | .error e => .error e
        | .ok (it, r) => .ok (it, r)
def parseStatikNach (f : Nat) (ver : Bool) (toks : List Token) :
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
          | .ok r4 => match parseOr f r4 with
            | .error e => .error e
            | .ok (e, r5) => match parseStatikRest r5 with
              | .error e => .error e
              | .ok ((sec, g), r) => .ok
                (.statikT ver n t e sec g, r)
def parseStatikRest : List Token →
    Except String ((Option String × Bool) × List Token)
  | toks => match toks with
    | .wort s :: rest =>
      if strEq s "section" then match nimmTextTok rest with
        | .error e => .error e
        | .ok (t, r1) => match r1 with
          | .wort u :: r2 =>
            if strEq u "shared" then match fordereZeichen ";" r2 with
              | .error e => .error e
              | .ok r => .ok (((some t, true)), r)
            else match fordereZeichen ";" r1 with
              | .error e => .error e
              | .ok r => .ok (((some t, false)), r)
          | _ => match fordereZeichen ";" r1 with
            | .error e => .error e
            | .ok r => .ok (((some t, false)), r)
      else if strEq s "shared" then match fordereZeichen ";" rest with
        | .error e => .error e
        | .ok r => .ok (((none, true)), r)
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok (((none, false)), r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok (((none, false)), r)
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
                  | .ok (b, r) => .ok (.uebersetzerT g
                    ({ art := "", name := n, params := ps,
                       ergebnis := erg, fehler, klauseln := ks } : FnSig) b, r)
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
      | .wort s :: r1 =>
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
                (.tabelleT n cnt backed owner g ps, r)
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
        | .ok (.konstT n t v, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tKonst n t v :: ps, r)
        | .ok _ => .error "const expected"
      else if strEq s "slot" then match parseFeldListe f rest with
        | .error e => .error e
        | .ok (fds, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tPlatz fds :: ps, r)
      else if strEq s "invariant" then match parseGruppenInv f toks with
        | .error e => .error e
        | .ok (iv, r1) => match parseTabTeile f r1 with
          | .error e => .error e
          | .ok (ps, r) => .ok (.tInvariante iv :: ps, r)
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
          | .ok (ps, r) => .ok (.tBaum ks :: ps, r)
      else if strEq s "occupied" then match nimmName rest with
        | .error e => .error e
        | .ok (n, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseTabTeile f r2 with
            | .error e => .error e
            | .ok (ps, r) => .ok (.tBelegt n :: ps, r)
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
/-- `arena n capacity lo .. hi of T ;`. -/
def parseArenaTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "arena" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "capacity" r2 with
        | .error e => .error e
        | .ok r3 => match parseOr f r3 with
          | .error e => .error e
          | .ok (lo, r4) => match fordereZeichen ".." r4 with
            | .error e => .error e
            | .ok r5 => match parseOr f r5 with
              | .error e => .error e
              | .ok (hi, r6) => match nimmWort "of" r6 with
                | .error e => .error e
                | .ok r7 => match parseTyp f r7 with
                  | .error e => .error e
                  | .ok (t, r8) => match fordereZeichen ";" r8 with
                    | .error e => .error e
                    | .ok r => .ok (.arenaT n lo hi t, r)
/-- `reason n { c = num "text", … [exhaustive] }`. -/
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
          | .ok ((cs, ex), r) => .ok (.grundT n cs ex, r)
def parseGrundFaelle (f : Nat) (toks : List Token) :
    Except String ((List (String × SExpr × String) × Bool) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "exhaustive" then match fordereZeichen "}" rest with
        | .error e => .error e
        | .ok r => .ok ((([], true)), r)
      else match nimmName toks with
        | .error e => .error e
        | .ok (c, r1) => match fordereZeichen "=" r1 with
          | .error e => .error e
          | .ok r2 => match parseOr f r2 with
            | .error e => .error e
            | .ok (num, r3) => match nimmTextTok r3 with
              | .error e => .error e
              | .ok (t, r4) => match r4 with
                | .zeichen "," :: r5 => match parseGrundFaelle f r5 with
                  | .error e => .error e
                  | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
                | _ => match fordereZeichen "}" r4 with
                  | .error e => .error e
                  | .ok r => .ok ((([(c, num, t)], false)), r)
    | .zeichen "}" :: rest => .ok ((([], false)), rest)
    | _ => .error "reason expected"
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
            | .ok r => .ok (.zustandT n ts, r)
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
            | .ok r => .ok (.geraetT n ps sp ms, r)
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
                | .ok (ms, r) => .ok (.spiegel a b :: ms, r)
      else if strEq s "reg" then match parseReg f toks with
        | .error e => .error e
        | .ok (rg, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.regTief rg :: ms, r)
      else if strEq s "bank" then match parseBank rest with
        | .error e => .error e
        | .ok (raw, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.bankRoh raw :: ms, r)
      else if strEq s "transition" then match parseTrans f toks with
        | .error e => .error e
        | .ok (tr, r1) => match parseGerTeile f r1 with
          | .error e => .error e
          | .ok (ms, r) => .ok (.uebergangTief tr :: ms, r)
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
                  | .ok r => .ok (.annahmeT n (some a) t k, r)
          else match nimmTextTok r2 with
            | .error e => .error e
            | .ok (t, r3) => match parseKlasse r3 with
              | .error e => .error e
              | .ok (k, r4) => match fordereZeichen ";" r4 with
                | .error e => .error e
                | .ok r => .ok (.annahmeT n none t k, r)
        | _ => match nimmTextTok r2 with
          | .error e => .error e
          | .ok (t, r3) => match parseKlasse r3 with
            | .error e => .error e
            | .ok (k, r4) => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.annahmeT n none t k, r)
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
          | .ok ((erg, req), r4) => match nimmWort "effects" r4 with
            | .error e => .error e
            | .ok r5 => match parseEffektBlock f r5 with
              | .error e => .error e
              | .ok (es, r6) => match parseKlasse r6 with
                | .error e => .error e
                | .ok (k, r7) => match fordereZeichen ";" r7 with
                  | .error e => .error e
                  | .ok r => .ok (.axiomaT n ps erg req es k, r)
def parseAxiomErg (f : Nat) (toks : List Token) :
    Except String ((Option STyp × Option SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "->" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r1) => match r1 with
        | .wort s :: r2 =>
          if strEq s "requires" then match parseOr f r2 with
            | .error e => .error e
            | .ok (p, r) => .ok (((some t, some p)), r)
          else .ok (((some t, none)), r1)
        | _ => .ok (((some t, none)), r1)
    | .wort s :: rest =>
      if strEq s "requires" then match parseOr f rest with
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
              | .ok r6 => match parsePlatzListe f r6 with
                | .error e => .error e
                | .ok (ms, r7) => match nimmWort "gates" r7 with
                  | .error e => .error e
                  | .ok r8 => match parseNamenEingeklammert f r8 with
                    | .error e => .error e
                    | .ok (gs, r9) => match nimmWort "can_fail" r9 with
                      | .error e => .error e
                      | .ok r10 => match parseBlock f r10 with
                        | .error e => .error e
                        | .ok (b, r11) => match parsePruefungRest f r11 with
                          | .error e => .error e
                          | .ok (((boden, sonde)), r) => .ok (.pruefungT
                            ({ cname := n, behauptung := c, misst := ms,
                               tore := gs, kannScheitern := b, boden,
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
              (.atomarT a b c d e, r)
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
/-- `lock n protects {…} rank e [held <= e ops]
    [shared held <= e ops] [masks m] ;`. -/
def parseSperreTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "lock" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "protects" r2 with
        | .error e => .error e
        | .ok r3 => match parsePlatzListe f r3 with
          | .error e => .error e
          | .ok (ps, r4) => match nimmWort "rank" r4 with
            | .error e => .error e
            | .ok r5 => match parseOr f r5 with
              | .error e => .error e
              | .ok (rk, r6) => match parseSperreRest f r6 with
                | .error e => .error e
                | .ok (((h, sh, m)), r) => .ok
                  (.sperreT n ps rk h sh m, r)
def parseSperreRest (f : Nat) (toks : List Token) :
    Except String
      ((Option SExpr × Option SExpr × Option String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "held" then match fordereZeichen "<=" rest with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (e, r2) => match nimmWort "ops" r2 with
            | .error e => .error e
            | .ok r3 => match parseSperreRest f r3 with
              | .error e => .error e
              | .ok (((_, sh, m)), r) => .ok ((((some e, sh, m))), r)
      else if strEq s "shared" then match nimmWort "held" rest with
        | .error e => .error e
        | .ok r1 => match fordereZeichen "<=" r1 with
          | .error e => .error e
          | .ok r2 => match parseOr f r2 with
            | .error e => .error e
            | .ok (e, r3) => match nimmWort "ops" r3 with
              | .error e => .error e
              | .ok r4 => match parseSperreRest f r4 with
                | .error e => .error e
                | .ok (((h, _, m)), r) => .ok ((((h, some e, m))), r)
      else if strEq s "masks" then match nimmName rest with
        | .error e => .error e
        | .ok (m, r1) => match parseSperreRest f r1 with
          | .error e => .error e
          | .ok (((h, sh, _)), r) => .ok ((((h, sh, some m))), r)
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok ((((none, none, none))), r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok ((((none, none, none))), r)
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
                  | .ok (ivs, r) => .ok (.gruppeT n ms ivs, r)
              | _ => match fordereZeichen "}" r5 with
                | .error e => .error e
                | .ok r6 => match parseGruppeRest f r6 with
                  | .error e => .error e
                  | .ok (ivs, r) => .ok (.gruppeT n ms ivs, r)
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
        | .ok r => .ok (.nebenT ps, r)
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
                  | .ok (p, r) => .ok (.akkumT n t m p, r)
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
                            | .ok r13 => match parseOr f r13 with
                              | .error e => .error e
                              | .ok (dp, r14) =>
                                match fordereZeichen "," r14 with
                                | .error e => .error e
                                | .ok r15 => match nimmWort "leaf" r15 with
                                  | .error e => .error e
                                  | .ok r16 => match fordereZeichen ":" r16 with
                                    | .error e => .error e
                                    | .ok r17 => match parseOr f r17 with
                                      | .error e => .error e
                                      | .ok (lf, r18) =>
                                        match fordereZeichen "," r18 with
                                        | .error e => .error e
                                        | .ok r19 =>
                                          match parseGruppenInvListe f r19 with
                                          | .error e => .error e
                                          | .ok (ivs, r20) =>
                                            match fordereZeichen "}" r20 with
                                            | .error e => .error e
                                            | .ok r => .ok (.wegT
                                              ({ wname := n, stufen := lv,
                                                 knoten := kn,
                                                 runterName := dn,
                                                 runterWann := dp, blatt := lf,
                                                 invarianten := ivs } : SWeg), r)
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
                                  | .ok r => .ok (.eingangT
                                    ({ ename := n, vektor := vek, via,
                                       arch, regRein := ri, regRaus := ro,
                                       erhaelt := ph, zerstoert := cb,
                                       stapel := st, proCPU := cpu, ist,
                                       verschachtelt := ve,
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
    printed, as in the `frist`/`ziehtZurueck` clauses). -/
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
                                    (.anvertrautT n m a ri st g, r)
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
                      | .ok r => .ok (.startT n a ss dp, r)
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
/-- A `syscall` declaration (SYNTAX.md section 12.1). -/
def parseSysrufTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "syscall" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseParams f r2 with
        | .error e => .error e
        | .ok (ps, r3) => match parseErgebnis f r3 with
          | .error e => .error e
          | .ok (erg, fehler, r4) => match nimmWort "abi" r4 with
            | .error e => .error e
            | .ok r5 => match nimmName r5 with
              | .error e => .error e
              | .ok (abi, r6) => match nimmWort "arch" r6 with
                | .error e => .error e
                | .ok r7 => match nimmName r7 with
                  | .error e => .error e
                  | .ok (arch, r8) => match nimmWort "number" r8 with
                    | .error e => .error e
                    | .ok r9 => match parseOr f r9 with
                      | .error e => .error e
                      | .ok (num, r10) => match nimmWort "regs" r10 with
                        | .error e => .error e
                        | .ok r11 => match nimmWort "in" r11 with
                          | .error e => .error e
                          | .ok r12 => match parseRegBindListe f r12 with
                            | .error e => .error e
                            | .ok (ri, r13) =>
                              match nimmWort "regs" r13 with
                              | .error e => .error e
                              | .ok r14 => match nimmWort "out" r14 with
                                | .error e => .error e
                                | .ok r15 =>
                                  match parseRegBindListe f r15 with
                                  | .error e => .error e
                                  | .ok (ro, r16) =>
                                    match nimmWort "clobbers" r16 with
                                    | .error e => .error e
                                    | .ok r17 =>
                                      match parseNamenEingeklammert f r17 with
                                      | .error e => .error e
                                      | .ok (cb, r18) =>
                                        match nimmWort "errors" r18 with
                                        | .error e => .error e
                                        | .ok r19 =>
                                          match parseFehlerAbb f r19 with
                                          | .error e => .error e
                                          | .ok (em, r20) =>
                                            match parseSysrufRest f r20 with
                                            | .error e => .error e
                                            | .ok (((rq, en, ef, hk)), r) =>
                                              .ok (.sysrufT
                                                ({ sname := n,
                                                   sparams := ps,
                                                   sergebnis := erg,
                                                   sfehler := fehler,
                                                   abi, sarch := arch,
                                                   nummer := num,
                                                   sregRein := ri,
                                                   sregRaus := ro,
                                                   szerstoert := cb,
                                                   sfehlerAbb := em,
                                                   svoraus := rq,
                                                   ssichert := en,
                                                   swirkung := ef,
                                                   sherkunft := hk } :
                                                  SSyscall), r)
/-- The `errors {…}` map: `errno => Ground` pairs. -/
def parseFehlerAbb (f : Nat) (toks : List Token) :
    Except String (List (String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match nimmName r with
        | .error e => .error e
        | .ok (a, r1) => match fordereZeichen "=>" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (b, r3) => match r3 with
              | .zeichen "," :: r4 => match r4 with
                | .zeichen "}" :: r5 => .ok ([(a, b)], r5)
                | _ => match parseFehlerAbbRest f r4 with
                  | .error e => .error e
                  | .ok (ps, r') => .ok ((a, b) :: ps, r')
              | _ => match fordereZeichen "}" r3 with
                | .error e => .error e
                | .ok r' => .ok ([(a, b)], r')
def parseFehlerAbbRest (f : Nat) (toks : List Token) :
    Except String (List (String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (a, r1) => match fordereZeichen "=>" r1 with
      | .error e => .error e
      | .ok r2 => match nimmName r2 with
        | .error e => .error e
        | .ok (b, r3) => match r3 with
          | .zeichen "," :: r4 => match r4 with
            | .zeichen "}" :: r5 => .ok ([(a, b)], r5)
            | _ => match parseFehlerAbbRest f r4 with
              | .error e => .error e
              | .ok (ps, r') => .ok ((a, b) :: ps, r')
          | _ => match fordereZeichen "}" r3 with
            | .error e => .error e
            | .ok r' => .ok ([(a, b)], r')
/-- Behind the `errors` map: contracts, effects, assumption. -/
def parseSysrufRest (f : Nat) (toks : List Token) :
    Except String
      ((List SExpr × List SExpr × List SEffekt × SHerkunft) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "requires" then match parsePredListe f rest with
        | .error e => .error e
        | .ok (ps, r1) => match parseSysrufRest f r1 with
          | .error e => .error e
          | .ok (((qs, en, ef, hk)), r) => .ok ((((ps ++ qs, en, ef, hk))), r)
      else if strEq s "ensures" then match parsePredListe f rest with
        | .error e => .error e
        | .ok (ps, r1) => match parseSysrufRest f r1 with
          | .error e => .error e
          | .ok (((rq, qs, ef, hk)), r) => .ok ((((rq, ps ++ qs, ef, hk))), r)
      else if strEq s "effects" then match parseEffektBlock f rest with
        | .error e => .error e
        | .ok (es, r1) => match parseSysrufRest f r1 with
          | .error e => .error e
          | .ok (((rq, en, _, hk)), r) => .ok ((((rq, en, es, hk))), r)
      else if strEq s "assume" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r1) => match parseKlasse r1 with
          | .error e => .error e
          | .ok (k, r2) => match fordereZeichen ";" r2 with
            | .error e => .error e
            | .ok r => .ok (((([], [], [],
              .annahmeHerkunft a k))), r)
      else if strEq s "kernel" then match nimmPfad rest with
        | .error e => .error e
        | .ok (p, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r => .ok (((([], [], [], .kernHerkunft p))), r)
      else .error "syscall expected"
    | _ => .error "syscall expected"
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
          | .ok r => .ok (.profilT bedarf es, r)
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
            | .ok (es, r) => .ok (.modusEintrag s v :: es, r)
      else if strEq s "assume" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r1) => match fordereZeichen ";" r1 with
          | .error e => .error e
          | .ok r2 => match parseProfEintraege f r2 with
            | .error e => .error e
            | .ok (es, r) => .ok (.annahmeEintrag a :: es, r)
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
              | .ok (it, r) => .ok (.torT it, r)
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
        else if strEq s "static" then parseStatikTief f nach
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
