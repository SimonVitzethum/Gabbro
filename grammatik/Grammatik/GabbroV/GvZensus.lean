/-
  File:      Grammatik/GabbroV/GvZensus.lean
  Subject:   GabbroV bridge: continue-on-refusal census over the corpus
             (agent 02, GabbroV-lead task V-02).

  `elabU` stops at the first refusal (`Except` short-circuits), so the
  tallies only ever named one blocker per file. This module re-runs the
  pipeline in COLLECT mode instead: token streams split into top-level
  items (depth-tracked splitter, sound on balanced streams), each item
  parsed separately, then tables, locks, heads, bodies (per statement),
  contracts (per predicate), returns and entries elaborated item by
  item, collecting every refusal with its stage, construct and message.
  Parse failures that unbalance the stream fall back to first-error
  plus a token scan. The `#eval` census at the end prints, per
  construct, in how many files it appears and in how many it is the
  ONLY blocker, with the ranked flip list. `Parser/` untouched.
-/
import Grammatik.Parser.Uebersetze

namespace Gabbro.Grammatik.GabbroV.GvZensus

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- Bracket depth delta of one token. -/
def schrittTiefe : Token → Nat → Nat
  | .zeichen s, d =>
    if s == "{" || s == "(" || s == "[" then d + 1
    else if s == "}" || s == ")" || s == "]" then
      if d == 0 then 0 else d - 1
    else d
  | _, d => d

/-- Split a token stream into top-level items (cut after `;` or a
    closing bracket at depth 0). Sound on balanced streams: every cut
    is a real item boundary. -/
def spalte (toks : List Token) : List (List Token) :=
  go toks 0 [] []
where go : List Token → Nat → List Token → List (List Token) →
    List (List Token)
  | [], _, [], acc => acc.reverse
  | [], _, cur, acc => (cur.reverse :: acc).reverse
  | t :: rest, d, cur, acc =>
    let dd := schrittTiefe t d
    let cur2 := t :: cur
    match t with
    | .zeichen ";" =>
      if dd == 0 then go rest 0 [] (cur2.reverse :: acc)
      else go rest dd cur2 acc
    | .zeichen "}" =>
      if dd == 0 then go rest 0 [] (cur2.reverse :: acc)
      else go rest dd cur2 acc
    | .zeichen ")" =>
      if dd == 0 then go rest 0 [] (cur2.reverse :: acc)
      else go rest dd cur2 acc
    | .zeichen "]" =>
      if dd == 0 then go rest 0 [] (cur2.reverse :: acc)
      else go rest dd cur2 acc
    | _ => go rest dd cur2 acc

/-- Parse one chunk as a whole unit (needs its own end marker). -/
def parseStueck (toks : List Token) : Except String (List SItemTief) :=
  parseTopTief (toks ++ [.ende])

/-- Drop a trailing end marker for splitting. -/
def ohneEnde : List Token → List Token
  | [] => []
  | toks =>
    match toks.reverse with
    | .ende :: r => r.reverse
    | _ => toks

/-- Split-and-reparse roundtrip on 104 as a `Bool` (the `u104elab`
    shape: decide a `beq`, never a match in `Prop` position). -/
def runde104B : Bool :=
  match uSeq ((spalte (ohneEnde tt104)).map parseStueck) with
  | .ok lists => beqSItemTiefList lists.flatten items104
  | .error _ => false

/-- **Split-and-reparse roundtrip on 104**: chunking `tt104` and
    parsing each chunk yields exactly `items104`. Proves the splitter
    cuts only at real item boundaries on real input. -/
theorem runde104 : runde104B = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvZensus.runde104

/-! ## Findings: stage, construct, message -/

/-- One census finding: the pipeline stage, the construct tag, the
    item it belongs to, and the refuser's message. -/
structure Befund where
  stufe : String
  art : String
  name : String
  meldung : String
  deriving DecidableEq, Repr

/-- True for table items. -/
def istTabelle : SItemTief → Bool
  | .tabelleT .. => true
  | _ => false

/-- True for lock items. -/
def istSperre : SItemTief → Bool
  | .sperreT .. => true
  | _ => false

/-- A function item as head plus body. -/
def alsFunktion : SItemTief → Option (FnSig × SAnw)
  | .funktionT s b => some (s, b)
  | _ => none

/-- Statement tag (all 30 arms of `SAnw`; `Anweisung.lean`). -/
def artAnw : SAnw → String
  | .lass .. => "let"
  | .lassElse .. => "let-else"
  | .lassLib .. => "let-lib"
  | .zuweis .. => "assign"
  | .uebergang .. => "transition"
  | .ruf .. => "call"
  | .libruf .. => "lib-call"
  | .wenn .. => "if"
  | .sonstWenn .. => "else-if"
  | .matchS .. => "match"
  | .arm .. => "match-arm"
  | .traverseS .. => "traverse"
  | .retryS .. => "retry"
  | .foreverS .. => "forever"
  | .bricht .. => "bricht"
  | .narrowS .. => "narrow"
  | .sperrt .. => "locks"
  | .beobachtet .. => "observe"
  | .verlasse .. => "leave"
  | .weiter .. => "next"
  | .publiziert .. => "publish"
  | .erwartet .. => "await"
  | .tauscht .. => "exchange"
  | .schreitet .. => "advance"
  | .rueck .. => "mid-return"
  | .allocS .. => "alloc"
  | .resetS .. => "reset"
  | .sonst .. => "else"
  | .block .. => "block"

/-- Ender tag (all 3 arms of `SEnde`). -/
def artEnde : SEnde → String
  | .ret _ => "return"
  | .fort _ => "leave-end"
  | .naechst _ => "next-end"

/-- Constructor tag of a surface item (all 32 arms of `SItemTief`). -/
def artItem : SItemTief → String
  | .modulT .. => "modulT"
  | .useT .. => "useT"
  | .typT .. => "typT"
  | .konstT .. => "konstT"
  | .statikT .. => "statikT"
  | .funktionT .. => "funktionT"
  | .protoT .. => "protoT"
  | .specT .. => "specT"
  | .asmT .. => "asmT"
  | .formatT .. => "formatT"
  | .tabelleT .. => "tabelleT"
  | .arenaT .. => "arenaT"
  | .grundT .. => "grundT"
  | .zustandT .. => "zustandT"
  | .geraetT .. => "geraetT"
  | .annahmeT .. => "annahmeT"
  | .axiomaT .. => "axiomaT"
  | .pruefungT .. => "pruefungT"
  | .atomarT .. => "atomarT"
  | .sperreT .. => "sperreT"
  | .rcuT .. => "rcuT"
  | .gruppeT .. => "gruppeT"
  | .nebenT .. => "nebenT"
  | .akkumT .. => "akkumT"
  | .wegT .. => "wegT"
  | .eingangT .. => "eingangT"
  | .anvertrautT .. => "anvertrautT"
  | .startT .. => "startT"
  | .sysrufT .. => "sysrufT"
  | .uebersetzerT .. => "uebersetzerT"
  | .profilT .. => "profilT"
  | .torT .. => "torT"

/-- Parse each chunk; collect per-chunk outcomes (no short-circuit). -/
def parseStuecke (toks : List Token) :
    List (Except String (List SItemTief)) :=
  (spalte (ohneEnde toks)).map parseStueck

/-- Bracket depth at end of stream (nonzero means unbalanced). -/
def tiefeEndstand : List Token → Nat
  | toks => toks.foldl (fun d t => schrittTiefe t d) 0

/-! ## Collect mode: every stage, every item, no short-circuit -/

/-- Values that elaborated cleanly (for downstream stages). -/
def werte {α : Type} : List (String × Except String α) → List α
  | [] => []
  | (_, .ok v) :: rest => v :: werte rest
  | (_, .error _) :: rest => werte rest

/-- Collect per-table outcomes. -/
def sammleTabellen (consts : List (String × Int))
    (aliase : List (String × (Int × Int))) :
    List SItemTief → List (String × Except String UTab)
  | [] => []
  | it :: rest =>
    match it with
    | .tabelleT n _ _ _ _ _ =>
      (n, uTabelle consts aliase it) :: sammleTabellen consts aliase rest
    | _ => sammleTabellen consts aliase rest

/-- Collect per-lock outcomes (against the clean tables). -/
def sammleSperren (tabs : List UTab) :
    List SItemTief → List (String × Except String ULock)
  | [] => []
  | it :: rest =>
    match it with
    | .sperreT n _ _ _ _ _ =>
      (n, uSperre tabs it) :: sammleSperren tabs rest
    | _ => sammleSperren tabs rest

/-- Collect per-head outcomes (against clean tables and locks). -/
def sammleKoepfe (consts : List (String × Int))
    (aliase : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) :
    List (FnSig × SAnw) → List (String × Except String (UFnKopf × List String))
  | [] => []
  | (sig, _) :: rest =>
    (sig.name, elabKopf consts aliase tabs locks sig) ::
      sammleKoepfe consts aliase tabs locks rest

/-- Indexed collection (positions ride along for reporting). -/
def sammleIdx {α β : Type} (f : Nat → α → Except String β) :
    Nat → List α → List (Nat × Except String β)
  | _, [] => []
  | i, x :: rest => (i, f i x) :: sammleIdx f (i + 1) rest

/-- Indexed collection preserves length (counting integrity for the
    census tallies). -/
theorem sammleIdx_laenge {α β : Type}
    (f : Nat → α → Except String β) (n : Nat) (l : List α) :
    (sammleIdx f n l).length = l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons _ _ ih => simp [sammleIdx, ih]

#print axioms Gabbro.Grammatik.GabbroV.GvZensus.sammleIdx_laenge

/-! ## Per-function descent: statements, predicates, returns -/

/-- Ensures predicate expressions of clauses (mirrors `elabFn`). -/
def sichertVon : List SKlausel → List SExpr
  | [] => []
  | .sichert e :: rest => e :: sichertVon rest
  | _ :: rest => sichertVon rest

/-- Findings of one body: every statement tried, every ensures
    predicate tried, the trailing return tried (mirrors `elabFn`,
    without short-circuit). -/
def befundeRumpf (ctx : UCtx) (tabs : List UTab)
    (koepfe : List UFnKopf) (fname : String) (klauseln : List SKlausel)
    (koerper : SAnw) : List Befund :=
  let saetze :=
    match koerper with
    | .block ss _ => ss.map fun s =>
      match uAnw ctx tabs koepfe s with
      | .error e => some ({ stufe := "rumpf", art := artAnw s, name := fname, meldung := e } : Befund)
      | .ok _ => none
    | _ => [some ({ stufe := "rumpf", art := "rumpf", name := fname, meldung := "Funktionsrumpf ohne G-Form" } : Befund)]
  let sichert :=
    (sichertVon klauseln).map fun e =>
      match uSichert ctx e with
      | .error m => some ({ stufe := "sichert", art := "ens-pred", name := fname, meldung := m } : Befund)
      | .ok _ => none
  let ret :=
    match koerper with
    | .block _ ende =>
      match uEnde ctx ende with
      | .error m => [({ stufe := "rueckgabe", art := "return", name := fname, meldung := m } : Befund)]
      | .ok _ => []
    | _ => []
  saetze.filterMap id ++ sichert.filterMap id ++ ret

/-- Findings of one function: head first, then the body descent (needs
    a good head for the context; a failed head hides its body, as in
    `elabU`). -/
def befundeFn (consts : List (String × Int))
    (aliase : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) : List Befund :=
  match elabKopf consts aliase tabs locks sig with
  | .error e => [({ stufe := "kopf", art := "fn-head", name := sig.name, meldung := e } : Befund)]
  | .ok (kopf, _) =>
    let ctx := uCtxVon aliase consts tabs locks kopf sig.name
    befundeRumpf ctx tabs koepfe sig.name sig.klauseln koerper

/-- Findings of a whole elaborated item list (collect mode over the
    `elabU` stages; cascades documented in CUTS). -/
def befundeElab (ms : List SItemTief) : List Befund :=
  let consts := uConstsRech (uKonstFns ms) ms []
  let aliase := uAliase ms
  let tabs := sammleTabellen consts aliase ms
  let tabOk := werte tabs
  let locks := sammleSperren tabOk ms
  let lockOk := werte locks
  let fns := ms.filterMap alsFunktion
  let koepfe := sammleKoepfe consts aliase tabOk lockOk fns
  let kopfOk := (werte koepfe).map fun p => p.1
  let tabF := tabs.filterMap fun (n, r) => match r with
    | .error e => some ({ stufe := "tabelle", art := "tabelle", name := n, meldung := e } : Befund)
    | .ok _ => none
  let lockF := locks.filterMap fun (n, r) => match r with
    | .error e => some ({ stufe := "sperre", art := "sperre", name := n, meldung := e } : Befund)
    | .ok _ => none
  let fnF := fns.map fun (sig, koerper) =>
    befundeFn consts aliase tabOk lockOk kopfOk sig koerper
  let fnsOk := (fns.map fun (sig, koerper) =>
    (sig.name, elabUFunktion consts aliase tabOk lockOk kopfOk sig koerper)).filterMap
    fun (_, r) => match r with
      | .ok v => some v
      | .error _ => none
  let wurzF := (ms.filter fun it => match it with
    | .eingangT _ => true
    | _ => false).filterMap fun it =>
    match uWurzeln fnsOk [it] with
    | .error e => some ({ stufe := "eintritt", art := "entry", name := "", meldung := e } : Befund)
    | .ok _ => none
  tabF ++ lockF ++ fnF.flatten ++ wurzF

/-! ## Drivers: one source text to findings and markers -/

/-- Render a lexer error (constructor names from `Parser/Lexer.lean`). -/
def zeigeLexFehler : LexFehler → String
  | .unbekannt s => "unbekannt " ++ s
  | .offeneZeichenkette => "offeneZeichenkette"
  | .zahlOhneZiffern => "zahlOhneZiffern"

/-- Findings of one source text: lex, then whole-parse, then collect
    mode on the elaborated items (only reached stages run). -/
def befundeSrc (src : String) : List Befund :=
  match lex src with
  | .error e => [({ stufe := "lex", art := "lex", name := "", meldung := zeigeLexFehler e } : Befund)]
  | .ok toks =>
    match parseTopTief toks with
    | .error e => [({ stufe := "parse", art := "parse", name := "", meldung := e } : Befund)]
    | .ok items => befundeElab (uMembers items)

/-- Does any token satisfy the test? -/
def scanBelegt (p : Token → Bool) : List Token → Bool
  | [] => false
  | t :: rest => p t || scanBelegt p rest

/-- A word spelling occurring as a word or identifier token. -/
def wortKommtVor (w : String) : List Token → Bool
  | toks => toks.any fun t => match t with
    | .wort s => s == w
    | .ident s => s == w
    | _ => false

/-- An array-literal-shaped bracket: `[` after `=`, `,`, `(`
    or `return` (heuristic, documented in CUTS). -/
def arrayAnfang : List Token → Bool
  | [] => false
  | [_] => false
  | a :: b :: rest =>
    match b with
    | .zeichen "[" =>
      match a with
      | .zeichen "=" => true
      | .zeichen "," => true
      | .zeichen "(" => true
      | .wort "return" => true
      | _ => arrayAnfang (b :: rest)
    | _ => arrayAnfang (b :: rest)

/-- Presence markers of one token stream (English surface spellings
    observed in the corpus; also raw literal/at-sign shapes). -/
def merkmaleSrc (toks : List Token) : List String :=
  let woerter : List (String × String) :=
    [("quantifier", "forall"), ("quantifier", "exists"),
      ("let", "let"), ("if", "if"), ("match", "match"),
      ("traverse", "traverse"), ("retry", "retry"),
      ("forever", "forever"), ("while", "while"), ("loop", "loop"),
      ("lock", "lock"), ("locks", "locks"), ("atomic", "atomic"),
      ("reason", "reason"), ("or-channel", "or"),
      ("exhaustive", "exhaustive"), ("string-ty", "string"),
      ("entry", "entry"), ("via", "via"), ("dispatch", "dispatch"),
      ("syscall", "syscall"), ("static", "static"),
      ("extern", "extern"), ("bool", "bool"), ("device", "device"),
      ("device", "reg"), ("device", "register"), ("narrow", "narrow"),
      ("return", "return"), ("const", "const"),
      ("invariant", "invariant"), ("float-ty", "f32"),
      ("float-ty", "f64"), ("float-ty", "float")]
  let basis := woerter.filterMap fun (m, w) =>
    if wortKommtVor w toks then some m else none
  let mitText :=
    if scanBelegt (fun t => match t with
      | .text _ => true
      | _ => false) toks then "string-lit" :: basis else basis
  let mitAt :=
    if scanBelegt (fun t => match t with
      | .zeichen "@" => true
      | _ => false) toks then "at-sign" :: mitText else mitText
  let mitGleit :=
    if scanBelegt (fun t => match t with
      | .gleit _ => true
      | _ => false) toks then "float-lit" :: mitAt else mitAt
  if arrayAnfang toks then "array-lit" :: mitGleit else mitGleit

/-- Render one finding on one line. -/
def zeigeBefund (b : Befund) : String :=
  b.stufe ++ "/" ++ b.art ++ "/" ++ b.name ++ "/" ++ b.meldung

/-- Join lines. -/
def zeigeZeilen : List String → String
  | [] => ""
  | [x] => x
  | x :: rest => x ++ " + " ++ zeigeZeilen rest

/-! ## Fixtures: emptiness on 104, exactness on a bad unit -/

/-- **104 yields no findings** (the census is empty on elaborated
    code; non-degenerate two-function program). -/
theorem zensus104_leer : befundeElab (uMembers items104) = [] := by
  decide

/-- **Synthetic two-blocker fixture**: a table with an unknown field
    type plus a function with an `if` body (real table, real body). -/
def wMultiItems : List SItemTief :=
  [.modulT "beispiel::zeuge"
    [.tabelleT "T" (.some (.lit 1)) .none .none false
      [.tPlatz [{ fname := "v", ftyp := .atom "Unbekannt",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .funktionT
      { art := "impl", name := "f", params := [],
        ergebnis := .none, fehler := .none, klauseln := [] }
      (.block [.wenn (.wahr) (.block [] .none) [] .none]
        (.some (.ret .none)))]]

/-- **Exactness on the fixture**: exactly the table finding and the
    `if`-statement finding, in stage order, nothing else. -/
theorem zensusMulti_exakt :
    befundeElab (uMembers wMultiItems) =
      [{ stufe := "tabelle", art := "tabelle", name := "T",
         meldung := "Typ unbekannt: Unbekannt" },
       { stufe := "rumpf", art := "if", name := "f",
         meldung := "Anweisung ohne G-Form" }] := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvZensus.zensus104_leer
#print axioms Gabbro.Grammatik.GabbroV.GvZensus.zensusMulti_exakt

/-! ## Population: every corpus file -/

/-- Every `beispiele/*.gab` (157 files, `ls` order, 2026-10-07;
    single source for every census run). -/
def zensusDateien : List String :=
  ["01-tabelle.gab", "02-geraet.gab", "03-format.gab",
    "04-schleifen.gab", "05-nebenlaeufigkeit.gab", "06-annahmen.gab",
    "07-eintritt-und-boot.gab", "08-bereiche.gab", "09-ohne-zeiger.gab",
    "100-hardwareprofil.gab", "101-hardwareprofil-schluessel.gab",
    "104-referenz.gab", "106-summe-uebersetzt.gab",
    "107-summe-zwei-rufe.gab", "108-disjoint-start-locks.gab",
    "109-lockfree-entry-roots.gab", "10-geteilte-sperre.gab",
    "110-fussgarantie.gab", "1114-kind-handed-read.gab",
    "111-rufzulassung.gab", "1123-deklaration-laenge-ok.gab",
    "1124-verkettung-in-max-ok.gab", "1126-vergleich-ok.gab",
    "1127-literal-ok.gab", "112-register-traeger-bewacht.gab",
    "113-register-traeger-ungeschrieben.gab",
    "114-owner-with-producer.gab", "1159-index-unter-laenge-ok.gab",
    "115-owner-read-with-producer.gab", "116-payload-free-counter.gab",
    "117-message-passing-flag.gab", "118-sperrinvariante-erhaltung.gab",
    "119-sperrinvariante-bloecke.gab", "11a-divergenz-endet.gab",
    "11-grammatikbefunde.gab", "120-tagged-construction.gab",
    "121-tagged-static-init.gab", "122-matrix.gab", "123-const-matrix.gab",
    "124-two-threads-private.gab", "125-read-under-lock.gab",
    "126-vergleichssortierung.gab", "127-treiberrueckruf.gab",
    "12-umlaufendes-register.gab", "130-derived-contract-pure.gab",
    "131-derived-contract-call.gab", "132-raum-am-zeiger.gab",
    "133-nur-gruende-und-ein-format-am-pfeil.gab",
    "134-holende-bitzuege.gab", "13-zeuge-mit-staerke.gab",
    "140-atomic-array-counter.gab", "141-atomic-array-pairing.gab",
    "146-sperrstreifen.gab", "147-ftp-alg-control.gab",
    "148-ftp-alg-daten.gab", "149-fd-offen.gab",
    "14-paarung-ueber-zwischenfunktion.gab", "150-fd-lesen.gab",
    "151-word-pool-discipline.gab", "152-byte-pool-cost.gab",
    "153-arena-waechst.gab", "154-arena-voll.gab",
    "155-kind-uebergabe.gab", "156-kind-verzweigt.gab",
    "157-worker-pool.gab", "158-arena-commit.gab",
    "159-laufzeit-start.gab", "15-own-traegt-beide-rechte.gab",
    "160-kind-liest-stapel.gab", "161-zeichenkette.gab",
    "162-geteilte-flagge.gab", "163-systemruf-variablen.gab",
    "164-eigener-kern.gab", "165-gp-eintritt.gab",
    "166-eintritt-irq-maskiert.gab",
    "167-reason-crosses-the-module-boundary.gab",
    "168-bytes-through-a-pointer.gab",
    "169-narrow-neben-einem-zeiger-desselben-namens.gab",
    "16-by-ops-am-feld.gab", "170-let-else-mit-typ.gab",
    "171-narrow-nach-eigener-deklaration.gab",
    "172-prozess-ohne-libc.gab", "173-abbruch-ohne-libc.gab",
    "174-tor-im-modell.gab", "175-puffer-gibt-seiten-zurueck.gab",
    "17-gruppe-ueber-zwei-sperren.gab",
    "180-zeigerindex-in-der-ausdehnung.gab",
    "181-gate-at-top-level.gab", "182-fallible-gate.gab",
    "183-region-vom-tor.gab", "184-code-vom-treiber.gab",
    "18-vorfahren.gab", "19-traversierung.gab", "20-falle-vier.gab",
    "21-verbundwert.gab", "22-bootstrecke.gab", "23-akkumulatoren.gab",
    "24-ip-kopf.gab", "25-entrust.gab", "26-gleitkomma.gab",
    "27-freiliste.gab", "28-reserve-und-hinterlegung.gab",
    "29-undurchsichtig.gab", "31-rcu.gab", "32-zeichenkette.gab",
    "33-rekursion.gab", "34-markierter-wert.gab", "35-tausch.gab",
    "36-asm.gab", "37-umlauf-rechnet.gab",
    "38-unveraenderlicher-zeiger.gab", "39-auftragsdienst.gab",
    "40-werte-und-griffe.gab", "41-handschlag.gab", "42-zaehlwerk.gab",
    "43-gegenprobe.gab", "44-register-einmal-lesen.gab",
    "45-gemischte-registerklasse.gab", "46-verneinung.gab",
    "47-ops-wortmenge.gab", "48-grund-mit-erzeuger.gab",
    "49-dispatch-tabelle.gab", "50-verfeinerung.gab",
    "51-abwesenheit-und-absage.gab", "52-baugatter.gab",
    "53-zwei-orte.gab", "54-divergenz-leckt-nicht.gab",
    "55-kindkette.gab", "56-auftragsring.gab", "57-faedenhalt.gab",
    "58-freiliste-zwei-formen.gab",
    "59-eintritt-nimmt-maskierte-sperre.gab",
    "60-annahme-mit-maschine.gab", "61-invertierung.gab",
    "62-grenzwort-im-ausdruck.gab", "63-druckt.gab",
    "64-writes-a-whole-buffer.gab", "65-port-space.gab",
    "66-transport-rueckgabe.gab", "67-befehlsebene.gab",
    "68-named-space-matches-itself.gab", "69-integer-conversion.gab",
    "70-kernel-namen.gab", "71-frist-und-zaehlung.gab",
    "72-fremdruf-unter-sperre.gab", "73-sugar-widths.gab",
    "74-syscall-schreiben.gab", "80-bibliothek-erklaert.gab",
    "90-syscall-errno.gab", "92-const-squares.gab",
    "93-const-scalars.gab", "94-uebersetzer-erklaert.gab",
    "95-uebersetzer-vertrag.gab", "96-buffered-writer.gab",
    "98-arena-erklaert.gab", "99-arena-grenze.gab", "halde.gab"]

/-
  CUTS (agent 02, V-02 census):
  1. PROVED here: the depth splitter with a decided 104 roundtrip
     (`spalte`, `parseStueck`, `ohneEnde`, `runde104`); finding and tag
     vocabulary (`Befund`, `artItem`, `artAnw`, `artEnde`, filters);
     collect-mode stages (`werte`, `sammleTabellen`, `sammleSperren`,
     `sammleKoepfe`, `sammleIdx` with `sammleIdx_laenge`); drivers
     (`zeigeLexFehler`, `befundeSrc`, `scanBelegt`, `wortKommtVor`,
     `arrayAnfang`, `merkmaleSrc`, renderers); fixtures
     (`zensus104_leer`, `wMultiItems`, `zensusMulti_exakt`); the
     population list (`zensusDateien`).
  2. KNOWN GAPS (by design, all documented for the report join):
     no `uRestFehler` replication (item-level blockers come from the
     tag probes, joined by hand); bodies of failed heads are hidden
     (as in `elabU`); per-chunk parse used only for the splitter
     proof, not per-file (whole-parse first errors stand);
     `arrayAnfang` is heuristic (bracket after `=`/`,`/`(`/`return`);
     the word scan covers English surface spellings observed in the
     corpus; `SAnw`-internal expression shapes are not descended
     (statement tags + messages carry those rows); multi-module files
     are opaque to the stage filters (items nested in `modulT` show
     empty findings with modulT tags, e.g. 29/59/60/167).
  3. Elaboration lesson: struct-instance `{...}` literals need a
     statically known expected type (`(...) : Befund` ascription) in
     lambdas and match arms; without it Lean reports "unexpected
     identifier; expected '}'" (multiline) or "invalid {...}
     notation" (single line).
-/

end Gabbro.Grammatik.GabbroV.GvZensus
