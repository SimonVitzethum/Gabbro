module
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil14
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

def lowerSichertLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    UEns → Except String UEnsLies
  | .globB _ | .var _ | .ergB => .error "static without G form in the 104 lowering"
  | .alle .. | .einige .. => .error "quantifier without G form in the 104 lowering"
  | .cmp op a b => lowerVglLies tabs names types res op a b
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowerSichertLies tabs names types res a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertLies tabs names types res b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowerSichertLies tabs names types res a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertLies tabs names types res b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowerSichertLies tabs names types res a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .slotB .. | .tabB .. => .error "bool place without G form in the 104 lowering"
  | .held .. => .error "held predicate without G form in the 104 lowering"
  | .imp .. => .error "implication without G form in the 104 lowering"
  | .reach .. | .member .. | .filtered .. | .arrayElements .. => .error "source relation without G form in the 104 lowering"
  | .istSome .. => .error "option test without G form in the 104 lowering"

def lowerSichertListeLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    List UEns → Except String UEnsLies
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowerSichertLies tabs names types res e with
    | .error err => .error err
    | .ok x =>
      match lowerSichertListeLies tabs names types res rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

/-- A value at an expected range in the `lies` body. -/
def lowerWertLies (tabs : List UTab) (names : List String)
    (types : List Ty) (lo hi : Int) : USide →
    Except String (Expr G104_referenz.gD UCtxLies ULLies (.int lo hi))
  | .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "literal outside"
    else .error "literal outside"
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int a b) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumLies j (Ty.int a b) with
          | .error e => .error e
          | .ok v =>
            if h1 : lo ≤ a then
              if h2 : b ≤ hi then .ok (Expr.widen h1 h2 (Expr.var v))
              else .error "parameter outside"
            else .error "parameter outside"
      | _, _ => .error "parameter without G form"
  | s =>
    match lowerSeiteLies tabs names types s with
    | .error e => .error e
    | .ok t =>
      if h1 : lo ≤ t.range.1 then
        if h2 : t.range.2 ≤ hi then .ok (Expr.widen h1 h2 t.term)
        else .error "value outside"
      else .error "value outside"

/-- The body of `lies`: empty with a trailing value return
    (a read-only function; statements have no lowered proofs
    here -- an explicit error). A same-range slot read returns
    bare (the no-op arm of the exporter's `fit`); every other
    value widens. -/
def lowerSaetzeLies (tabs : List UTab) (names : List String)
    (types : List Ty) : List UStmt → URet → Except String UKoerpLies
  | [], .val (.slot b f ix) =>
    if !(strEq b "k" && strEq f "stand") then
      .error "return without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok (Endblock.ret
            (ErgExpr.val (Expr.thru (Expr.var Var.here)
              G104_referenz.GTab.Konto rfl
              G104_referenz.GKontoFeld.stand i
              G104_referenz.gDarf_lies_Konto))
            (List.Perm.refl _))
  | [], .val (.tab b f ix) =>
    if !(strEq b "Konto" && strEq f "stand") then
      .error "return without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok (Endblock.ret
            (ErgExpr.val (Expr.slot G104_referenz.GTab.Konto
              G104_referenz.GKontoFeld.stand i
              G104_referenz.gDarf_lies_Konto))
            (List.Perm.refl _))
  | [], .val s =>
    match lowerWertLies tabs names types 0 100 s with
    | .error e => .error e
    | .ok v => .ok (Endblock.ret (ErgExpr.val v) (List.Perm.refl _))
  | _, _ => .error "lies body without G form"

/-! ## Program assembly -/

/-- Assemble the lowered pieces to a program (same shape as
    `gP`: no contract content in `requires`, per-function
    `ensures` and bodies). -/
def uProgBaue (e1 : UEnsEin) (e2 : UEnsLies) (b1 : UKoerpEin)
    (b2 : UKoerpLies) : Programm G104_referenz.gD where
  invariante := fun i => (nomatch i)
  requires := fun _ => Expr.tru
  ensures
    | G104_referenz.GFn.einzahlen => e1
    | G104_referenz.GFn.lies => e2
  rumpf
    | G104_referenz.GFn.einzahlen => b1
    | G104_referenz.GFn.lies => b2

/-- The lowered program: the two functions assembled to the
    exporter's `gP`/`gFs` (signatures stay in `gD`; the
    elaborated signature data is checked against `gD` entry by
    entry, so a divergent `UFn` is an explicit error). -/
def lowerProg : UProg →
    Except String
      (Programm G104_referenz.gD × List G104_referenz.GFn)
  | { tabs := [tab], locks := [lock], fns := [fe, fl], roots := [], hands := [], globs := [], axs := [], annahmen := [], gestartet := [], whys := [], sums := [], regs := [], invs := [], zustaende := [], regiert := [], ptrs := [], ptrKeys := [], exportGate := _, checks := [] } =>
    if !(strEq tab.name "Konto" && strEq lock.name "M" &&
        strEq fe.name "einzahlen" && strEq fl.name "lies") then
      .error "program shape without G form"
    else if !(decide (fe.params.map (·.2) =
        G104_referenz.gD.params G104_referenz.g_einzahlen)) then
      .error "signature of einzahlen foreign"
    else if !(decide (fl.params.map (·.2) =
        G104_referenz.gD.params G104_referenz.g_lies)) then
      .error "signature of lies foreign"
    else if !(decide (fe.res = none)) then
      .error "result of einzahlen foreign"
    else if !(decide (fl.res = some (0, 100))) then
      .error "result of lies foreign"
    else if !(fe.held == ["M"] && fl.held == ["M"]) then
      .error "held set foreign"
    else if !(fe.puts == ["Konto"] && fl.puts == []) then
      .error "write set foreign"
    else
      let pnamenEin := fe.params.map (·.1)
      let ptypenEin := fe.params.map (·.2)
      match lowerSichertListeEin [tab] pnamenEin ptypenEin fe.gives with
      | .error e => .error e
      | .ok e1 =>
        let pnamenLies := fl.params.map (·.1)
        let ptypenLies := fl.params.map (·.2)
        match lowerSichertListeLies [tab] pnamenLies ptypenLies
            fl.res fl.gives with
        | .error e => .error e
        | .ok e2 =>
          match lowerSaetzeEin [tab] pnamenEin ptypenEin
              fe.body fe.ret with
          | .error e => .error e
          | .ok b1 =>
            match lowerSaetzeLies [tab] pnamenLies ptypenLies
                fl.body fl.ret with
            | .error e => .error e
            | .ok b2 =>
              .ok (uProgBaue e1 e2 b1 b2,
                [G104_referenz.GFn.einzahlen, G104_referenz.GFn.lies])
  | _ => .error "program shape without G form"

/-! ## The 104 instance: tokens -/

/-- The token list of `beispiele/0104-referenz.gab` (comment-free;
    `u104lex` checks it against the lexer). -/
def tt104 : List Token :=
  [.wort "module", .ident "beispiel", .zeichen "::", .ident "referenz",
   .zeichen "{",
   .wort "const", .ident "NKONTO", .zeichen ":", .wort "u32",
   .zeichen "=", .num 2, .zeichen ";",
   .wort "type", .ident "Betrag", .zeichen "=",
   .wort "u32", .wort "in", .num 0, .zeichen "..", .num 10,
   .zeichen ";",
   .wort "type", .ident "Stand", .zeichen "=",
   .wort "u32", .wort "in", .num 0, .zeichen "..", .num 100,
   .zeichen ";",
   .wort "table", .ident "Konto", .wort "count", .ident "NKONTO",
   .zeichen "{", .wort "slot", .zeichen "{", .ident "stand",
   .zeichen ":", .ident "Stand", .zeichen ",", .zeichen "}",
   .zeichen "}",
   .wort "lock", .ident "M", .wort "protects", .zeichen "{",
   .ident "stand", .zeichen "}", .wort "rank", .num 0,
   .wort "held", .zeichen "<=", .num 50, .wort "ops", .zeichen ";",
   .wort "impl", .wort "fn", .ident "einzahlen", .zeichen "(",
   .ident "k", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "rw", .zeichen ">",
   .ident "Konto", .zeichen ",",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Konto", .zeichen ",",
   .ident "b", .zeichen ":", .ident "Betrag", .zeichen ")",
   .wort "requires", .ident "Held", .zeichen "(", .ident "M",
   .zeichen ")",
   .wort "ensures", .wort "old", .zeichen "(", .ident "k",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "stand", .zeichen ")",
   .zeichen "<=", .ident "k", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "stand",
   .wort "effects", .zeichen "{", .wort "reads", .ident "k",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "writes",
   .ident "k", .zeichen ".", .wort "slots", .zeichen ",",
   .wort "locks", .ident "M", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 16, .wort "ops",
   .zeichen "{", .ident "k", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "stand", .zeichen "=", .num 100, .zeichen ";",
   .ident "lies", .zeichen "(", .ident "k", .zeichen ",",
   .ident "i", .zeichen ")", .zeichen ";", .zeichen "}",
   .wort "impl", .wort "fn", .ident "lies", .zeichen "(",
   .ident "k", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "r", .zeichen ">",
   .ident "Konto", .zeichen ",",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Konto", .zeichen ")", .zeichen "->", .ident "Stand",
   .wort "requires", .ident "Held", .zeichen "(", .ident "M",
   .zeichen ")",
   .wort "ensures", .wort "result", .zeichen "==", .ident "k",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "stand",
   .wort "effects", .zeichen "{", .wort "reads", .ident "k",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "locks",
   .ident "M", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops",
   .zeichen "{", .wort "return", .ident "k", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "stand", .zeichen ";", .zeichen "}",
   .zeichen "}", .ende]

/-- The comment-free 104 source text, pinned as CHARACTERS in short
    pieces. One 669-byte `String` literal costs the kernel 8,96 GB and
    55 s here (measured 2026-09-15); the pieces cost a fraction of it, and
    `lex_ofList` carries the pin to the `String` without running Lean 4.33's
    UTF-8 decoder at all. See O13 and `Parser/Lexer.lean`. -/
def srcZeilen104K : List (List Char) :=
  ["module beispiel::referenz { const NKONTO ".toList,
   ": u32 = 2; type Betrag = u32 in 0 .. 10; ".toList,
   "type Stand = u32 in 0 .. 100; table ".toList,
   "Konto count NKONTO { slot { stand : ".toList,
   "Stand, } } lock M protects { stand } ".toList,
   "rank 0 held <= 50 ops; impl fn ".toList,
   "einzahlen(k : ptr<normal, rw> Konto, i : ".toList,
   "index into Konto, b : Betrag) requires ".toList,
   "Held(M) ensures old(k.slots[i].stand) <= ".toList,
   "k.slots[i].stand effects { reads ".toList,
   "k.slots, writes k.slots, locks M } costs ".toList,
   "<= 16 ops { k.slots[i].stand = 100; ".toList,
   "lies(k, i); } impl fn lies(k : ".toList,
   "ptr<normal, r> Konto, i : index into ".toList,
   "Konto) -> Stand requires Held(M) ensures ".toList,
   "result == k.slots[i].stand effects { ".toList,
   "reads k.slots, locks M } costs <= 8 ops ".toList,
   "{ return k.slots[i].stand; } }".toList]

/-- The same text as characters. -/
def srcQuelle104K : List Char := srcZeilen104K.flatten

set_option maxHeartbeats 3200000 in
/-- The comment-free 104 text lexes to `tt104`, over the characters. -/
theorem u104lexL : lexL srcQuelle104K = .ok tt104 := by
  decide

/-- The same, about the `String` -- a rewrite, not a reduction (O13). -/
theorem u104lex : lex (String.ofList srcQuelle104K) = .ok tt104 := by
  rw [lex_ofList]
  exact u104lexL

/-! ## The 104 instance: parse tree -/

/-- The slot read `k.slots[i].stand` shared by every 104
    contract and body (see `sonde04`/`sonde05`). -/
def uStand104 : SExpr :=
  .field (.index (.field (.variable "k") "slots") (.variable "i")) "stand"

/-- The parsed surface tree of `beispiele/0104-referenz.gab`
    (`u104parse` checks it against the reader). -/
def items104 : List SItemTief :=
  [.modT "beispiel::referenz" [
    .constT "NKONTO" (.atom "u32") (.one (.lit 2)),
    .typeT [] "Betrag" [] []
      (.some (.range (.atom "u32") (.lit 0) (.lit 10) false)),
    .typeT [] "Stand" [] []
      (.some (.range (.atom "u32") (.lit 0) (.lit 100) false)),
    .tableT "Konto" .none (.some (.variable "NKONTO")) .none .none false
      [.tSlot [{ fname := "stand", ftyp := .atom "Stand", pos := .none, bezug := .none, wo := .none, reserviert := false, byOps := false }]],
    .lockT "M" [.variable "stand"] (.lit 0)
      (.some (.lit 50)) .none .none .none,
    .fnT
      { art := "impl", name := "einzahlen", params := [("k", .ptr "normal" "rw" (.atom "Konto")), ("i", .index false "Konto"), ("b", .atom "Betrag")], res := .none, fehler := .none, klauseln := [.needs (.call "Held" [.variable "M"]), .gives (.bin "<=" (.old uStand104) uStand104), .effs [.reads (.field (.variable "k") "slots"), .writes (.field (.variable "k") "slots"), .locks false (.variable "M")], .cost (.lit 16)] }
      (.block [.set uStand104 "=" (.lit 100),
        .call "lies" [.variable "k", .variable "i"]] .none),
    .fnT
      { art := "impl", name := "lies", params := [("k", .ptr "normal" "r" (.atom "Konto")), ("i", .index false "Konto")], res := .some (.atom "Stand"), fehler := .none, klauseln := [.needs (.call "Held" [.variable "M"]), .gives (.bin "==" .res uStand104), .effs [.reads (.field (.variable "k") "slots"), .locks false (.variable "M")], .cost (.lit 8)] }
      (.block [] (.some (.ret (.some uStand104))))]]

theorem u104parse : beqTopTief (parseTopTief tt104) (.ok items104) = true := by
  decide

/-! ## The 104 instance: elaboration -/

/-- The elaborated 104 program (`u104elab` checks it against
    the elaborator). -/
def uExp104 : UProg :=
{ tabs := [{ name := "Konto", count := 2, cols := [("stand", (0, 100))], breiten := [("stand", 32)] }], locks := [{ name := "M", rank := 0, guard := ["Konto"] }], fns := [ { name := "einzahlen", params := [("k", .ptr (.table 0 (true, true))), ("i", .index 2), ("b", .int 0 10)], kinds := [.ptr (.table 0 (true, true)), .index 0, .int], res := .none, held := ["M"], puts := ["Konto"], gives := [.cmp "<=" (.old "k" "stand" (.param "i")) (.slot "k" "stand" (.param "i"))], body := [.assign "k" "stand" (.param "i") (.lit 100), .call "lies" [.freshPtr "Konto" (.table 0 (true, false)), .val (.param "i")]], ret := .empty, boden := some 1 }, { name := "lies", params := [("k", .ptr (.table 0 (true, false))), ("i", .index 2)], kinds := [.ptr (.table 0 (true, false)), .index 0], res := .some (0, 100), held := ["M"], puts := [], gives := [.cmp "==" .erg (.slot "k" "stand" (.param "i"))], body := [], ret := .val (.slot "k" "stand" (.param "i")), boden := some 1 }], exportGate := ExportMetadata.check (uMembers items104) }

/-! ## Shape equality on U (Bool pins, like `beqTopTief`) -/

def beqIntPair : Int × Int → Int × Int → Bool
  | (a, b), (c, d) => a == c && b == d

def beqOptIntPair : Option (Int × Int) → Option (Int × Int) → Bool
  | none, none => true
  | some a, some b => beqIntPair a b
  | _, _ => false

def beqPayloads : List (Option Ty) →
    List (Option Ty) → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && beqPayloads xs ys
  | _, _ => false

/-- Complete shape equality, including recursively typed payloads and arrays. -/
def beqTy (a b : Ty) : Bool := decide (a = b)
