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
  wrapping : Bool
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
    (a.wrapping == b.wrapping) && beqSExpr a.adresse b.adresse &&
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
end

end Gabbro.Grammatik.Parser
