module

public import Grammatik.Parser.Elab.Uebersetze
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



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
  | .tableT .. => true
  | _ => false

/-- True for lock items. -/
def istSperre : SItemTief → Bool
  | .lockT .. => true
  | _ => false

/-- A function item as head plus body. -/
def alsFunktion : SItemTief → Option (FnSig × SAnw)
  | .fnT s b => some (s, b)
  | _ => none

/-- Statement tag (all 31 arms of `SAnw`; `Anweisung.lean`). -/
def artAnw : SAnw → String
  | .bind .. => "let"
  | .bindElse .. => "let-else"
  | .bindAxiomOpt .. => "let?"
  | .bindAxiomOptElse .. => "let?-else"
  | .bindLib .. => "let-lib"
  | .set .. => "assign"
  | .shift .. => "transition"
  | .call .. => "call"
  | .lcall .. => "lib-call"
  | .cond .. => "if"
  | .elsif .. => "else-if"
  | .cases .. => "match"
  | .arm .. => "match-arm"
  | .each .. => "traverse"
  | .retry .. => "retry"
  | .loop .. => "forever"
  | .waive .. => "waive"
  | .trim .. => "narrow"
  | .locks .. => "locks"
  | .watch .. => "observe"
  | .leave .. => "leave"
  | .next .. => "next"
  | .emit .. => "publish"
  | .await .. => "await"
  | .swap .. => "exchange"
  | .step .. => "advance"
  | .ret .. => "mid-return"
  | .alloc .. => "alloc"
  | .reset .. => "reset"
  | .grow .. => "grow"
  | .free .. => "free"
  | .child .. => "child"
  | .start .. => "start"
  | .other .. => "else"
  | .block .. => "block"
  | .allocVon .. => "alloc-from"

/-- Ender tag (all 3 arms of `SEnde`). -/
def artEnde : SEnde → String
  | .ret _ => "return"
  | .leave _ => "leave-end"
  | .next _ => "next-end"

/-- Constructor tag of a surface item (all 32 arms of `SItemTief`). -/
def artItem : SItemTief → String
  | .modT .. => "modT"
  | .useT .. => "useT"
  | .typeT .. => "typeT"
  | .constT .. => "constT"
  | .globT .. => "globT"
  | .fnT .. => "fnT"
  | .protoT .. => "protoT"
  | .specT .. => "specT"
  | .asmT .. => "asmT"
  | .formatT .. => "formatT"
  | .tableT .. => "tableT"
  | .arenaT .. => "arenaT"
  | .whyT .. => "whyT"
  | .stateT .. => "stateT"
  | .devT .. => "devT"
  | .assumT .. => "assumT"
  | .axiomT .. => "axiomT"
  | .checkT .. => "checkT"
  | .atomT .. => "atomT"
  | .lockT .. => "lockT"
  | .rcuT .. => "rcuT"
  | .groupT .. => "groupT"
  | .concT .. => "concT"
  | .accT .. => "accT"
  | .walkT .. => "walkT"
  | .entryT .. => "entryT"
  | .trustT .. => "trustT"
  | .bootT .. => "startT"
  | .callT .. => "callT"
  | .varT .. => "varT"
  | .goalT .. => "goalT"
  | .transT .. => "transT"
  | .profT .. => "profT"
  | .gateT .. => "gateT"
  | .pubT .. => "pubT"
  | .taggedByT .. => "taggedByT"
  | .specGroupT .. => "specGroupT"
  | .implGroupT .. => "implGroupT"

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
    (alias : List (String × (Int × Int))) (tnames : List String) :
    List SItemTief → List (String × Except String UTab)
  | [] => []
  | it :: rest =>
    match it with
    | .tableT n _ _ _ _ _ _ =>
      (n, uTabelle consts alias tnames it) :: sammleTabellen consts alias tnames rest
    | _ => sammleTabellen consts alias tnames rest

/-- Collect per-lock outcomes (against the clean tables). -/
def sammleSperren (consts : List (String × Int)) (alias : List (String × (Int × Int))) (globs : List UGlob)
    (tabs : List UTab) :
    List SItemTief → List (String × Except String ULock)
  | [] => []
  | it :: rest =>
    match it with
    | .lockT n _ _ _ _ _ _ =>
      (n, uSperre globs tabs it) :: sammleSperren consts alias globs tabs rest
    | _ => sammleSperren consts alias globs tabs rest

/-- Collect per-head outcomes (against clean tables and locks). -/
def sammleKoepfe (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (sums : List USum) :
    List (FnSig × SAnw) → List (String × Except String (UFnKopf × List String))
  | [] => []
  | (sig, _) :: rest =>
    (sig.name, elabKopf consts alias tabs locks globs whys sums sig) ::
      sammleKoepfe consts alias tabs locks globs whys sums rest

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
  | cons _ _ ih => simp only [sammleIdx, List.length_cons, ih, Nat.add_left_cancel_iff]

#print axioms Gabbro.Grammatik.GabbroV.GvZensus.sammleIdx_laenge

/-! ## Per-function descent: statements, predicates, returns -/

/-- Ensures predicate expressions of clauses (mirrors `elabFn`). -/
def sichertVon : List SKlausel → List SExpr
  | [] => []
  | .gives e :: rest => e :: sichertVon rest
  | _ :: rest => sichertVon rest

/-- The findings of a run of statements, every one tried alone (no short-circuit); a statement that
    elaborates hands its context on (a `let` binds for the rest), one that fails leaves it unchanged.
    Also returns the context after the run, for the trailing return. -/
def befundeReihe (tabs : List UTab) (koepfe : List UFnKopf) (fname : String) :
    UCtx → List SAnw → List Befund × UCtx
  | ctx, [] => ([], ctx)
  | ctx, s :: rest =>
    match uAnwReihe tabs koepfe 1000000 ctx [s] with
    | .error e =>
      let (bs, cE) := befundeReihe tabs koepfe fname ctx rest
      (({ stufe := "rumpf", art := artAnw s, name := fname, meldung := e } : Befund) :: bs, cE)
    | .ok (_, ctx') => befundeReihe tabs koepfe fname ctx' rest

/-- Findings of one body: every statement tried, every ensures
    predicate tried, the trailing return tried (mirrors `elabFn`,
    without short-circuit). -/
def befundeRumpf (ctx : UCtx) (tabs : List UTab)
    (koepfe : List UFnKopf) (fname : String) (klauseln : List SKlausel)
    (koerper : SAnw) : List Befund :=
  let lauf :=
    match koerper with
    | .block ss _ => befundeReihe tabs koepfe fname ctx ss
    | _ => ([({ stufe := "rumpf", art := "rumpf", name := fname, meldung := "fn body without G form" } : Befund)], ctx)
  let body := lauf.1
  let gives :=
    (sichertVon klauseln).map fun e =>
      match uSichert ctx e with
      | .error m => some ({ stufe := "gives", art := "ens-pred", name := fname, meldung := m } : Befund)
      | .ok _ => none
  let ret :=
    match koerper with
    | .block _ ende =>
      match uEnde lauf.2 ende with
      | .error m => [({ stufe := "rueckgabe", art := "return", name := fname, meldung := m } : Befund)]
      | .ok _ => []
    | _ => []
  body ++ gives.filterMap id ++ ret

/-- Findings of one function: head first, then the body descent (needs
    a good head for the context; a failed head hides its body, as in
    `elabU`). -/
def befundeFn (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (sums : List USum) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) : List Befund :=
  match elabKopf consts alias tabs locks globs whys sums sig with
  | .error e => [({ stufe := "kopf", art := "fn-head", name := sig.name, meldung := e } : Befund)]
  | .ok (kopf, _) =>
    let ctx := uCtxVon alias consts tabs locks globs kopf sig.name [] whys sums
    befundeRumpf ctx tabs koepfe sig.name sig.klauseln koerper

/-- Findings of a whole elaborated item list (collect mode over the
    `elabU` stages; cascades documented in CUTS). -/
def befundeElab (ms : List SItemTief) : List Befund :=
  let consts := uConstsRech (uKonstFns ms) ms []
  let alias := uAliase consts ms ++ consts.map (fun c => (c.1, (c.2, c.2)))
  let sumOk := match uSums alias ms with | .ok w => w | .error _ => []
  -- a field of an unknown type is read as a tagged type and refused there, as `elabU` does (`uSumTabs`)
  let tabs := (sammleTabellen consts alias (ms.filterMap (fun | .tableT n _ _ _ _ _ _ => some n | _ => none)) ms).map
    fun (n, r) => (n, match r with
      | .ok t => (match uSumTabs sumOk [t] with
        | .ok [t'] => .ok t'
        | .ok _ => .ok t
        | .error e => .error e)
      | .error e => .error e)
  let tabOk := werte tabs
  let globR := uGlobs consts alias ms
  let globOk := match globR with | .ok gs => gs | .error _ => []
  let locks := sammleSperren consts alias globOk tabOk ms
  let lockOk := werte locks
  let fns := ms.filterMap alsFunktion
  let whyOk := match uWhys ms with | .ok w => w | .error _ => []
  let koepfe := sammleKoepfe consts alias tabOk lockOk globOk whyOk sumOk fns
  let kopfOk := (werte koepfe).map fun p => p.1
  let tabF := tabs.filterMap fun (n, r) => match r with
    | .error e => some ({ stufe := "tabelle", art := "tabelle", name := n, meldung := e } : Befund)
    | .ok _ => none
  let lockF := locks.filterMap fun (n, r) => match r with
    | .error e => some ({ stufe := "sperre", art := "sperre", name := n, meldung := e } : Befund)
    | .ok _ => none
  let globF := match globR with
    | .error e => [({ stufe := "static", art := "static", name := "", meldung := e } : Befund)]
    | .ok _ => []
  let fnF := fns.map fun (sig, koerper) =>
    befundeFn consts alias tabOk lockOk globOk whyOk sumOk kopfOk sig koerper
  let fnsOk := (fns.map fun (sig, koerper) =>
    (sig.name, elabUFunktion consts alias tabOk lockOk globOk kopfOk sig koerper [] whyOk sumOk)).filterMap
    fun (_, r) => match r with
      | .ok v => some v
      | .error _ => none
  let wurzF := (ms.filter fun it => match it with
    | .entryT _ => true
    | _ => false).filterMap fun it =>
    match uWurzeln tabOk fnsOk [it] with
    | .error e => some ({ stufe := "eintritt", art := "entry", name := "", meldung := e } : Befund)
    | .ok _ => none
  globF ++ tabF ++ lockF ++ fnF.flatten ++ wurzF

/-! ## Drivers: one source text to findings and markers -/

/-- Render a lexer error (constructor names from `Parser/Lexer.lean`). -/
def zeigeLexFehler : LexFehler → String
  | .unbekannt s => "unbekannt " ++ s
  | .offeneZeichenkette => "offeneZeichenkette"
  | .offenerKommentar => "offenerKommentar"
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
      | .float _ => true
      | _ => false) toks then "float-lit" :: mitAt else mitAt
  if arrayAnfang toks then "array-lit" :: mitGleit else mitGleit

/-- Render one finding on one line. -/
def zeigeBefund (b : Befund) : String :=
  b.stufe ++ "/" ++ b.art ++ "/" ++ b.name ++ "/" ++ b.meldung

end Gabbro.Grammatik.GabbroV.GvZensus
