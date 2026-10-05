/-
  File:      Grammatik/Parser/AnweisungProben.lean
  Subject:   T3 PART 2: the `decide` probes for the statement/item
              readers.

  Like `Parser/AusdruckProben.lean`: one kernel evaluation per
  theorem keeps every worker small. Each probe is split in two: a
  lex pin (`sNN_lex`/`eNN_lex`: the source line lexes to this token
  list) and a tree pin (`sNN`/`eNN`: the reader maps the list to
  this shape). A mistranscribed list fails its lex pin loudly. Tree
  shapes were compared against `ast.rs`/`parse.rs` by reading (no
  cargo in this lane); all differences are booked in the CUTS
  blocks of `Parser/Anweisung.lean` and `Parser/Element.lean`.
  Corpus sites stand at each probe; probes with no corpus line say
  so (`{ }` bodies stand for the corpus block at the cited site).
-/
import Grammatik.Parser.Element

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

def st01 : List Token :=
  [.wort "r", .zeichen ".", .wort "slots", .zeichen "[",
   .ident "i", .zeichen "]", .zeichen ".", .ident "belegt",
   .zeichen "=", .wort "true", .zeichen ";", .ende]
theorem s01_lex :
    lex "r.slots[i].belegt = true;" = .ok st01 := by
  decide
theorem s01 : beqTopStmt (parseTopStmt st01)
    (.ok (.zuweis
      (.feld (.index (.feld (.variable "r") "slots")
        (.variable "i")) "belegt")
      "=" .wahr)) = true := by
  decide
-- beispiele/15 (the body of `uebernehmen`). Rust: `Zuweisung`
-- with a slot target -- same shape.
def st02 : List Token :=
  [.ident "c", .zeichen ".", .wort "slots", .zeichen "[",
   .ident "s", .zeichen "]", .zeichen ".", .ident "marke",
   .zeichen "+=", .zahl 1, .zeichen ";", .ende]
theorem s02_lex :
    lex "c.slots[s].marke += 1;" = .ok st02 := by
  decide
theorem s02 : beqTopStmt (parseTopStmt st02)
    (.ok (.zuweis
      (.feld (.index (.feld (.variable "c") "slots")
        (.variable "s")) "marke")
      "+=" (.lit 1))) = true := by
  decide
-- beispiele/01-tabelle.gab:156. Rust: `Zuweisung` with `Plus` --
-- same shape.
def st03 : List Token :=
  [.ident "wurzel_setzen", .zeichen "(", .ident "v",
   .zeichen ")", .zeichen ";", .ende]
theorem s03_lex :
    lex "wurzel_setzen(v);" = .ok st03 := by
  decide
theorem s03 : beqTopStmt (parseTopStmt st03)
    (.ok (.ruf "wurzel_setzen" [.variable "v"])) = true := by
  decide
-- beispiele/02-geraet.gab (the `uebersetzung_an` call shape).
-- Rust: `Ruf` on a one-segment path -- same shape.
def st04 : List Token :=
  [.wort "let", .wort "x", .zeichen ":", .wort "u64",
   .zeichen "=", .ident "SQUARES", .zeichen "[",
   .ident "a", .zeichen "]", .zeichen ";", .ende]
theorem s04_lex :
    lex "let x : u64 = SQUARES[a];" = .ok st04 := by
  decide
theorem s04 : beqTopStmt (parseTopStmt st04)
    (.ok (.lass false "x"
      (.index (.variable "SQUARES") (.variable "a")))) = true := by
  decide
-- beispiele/92-const-squares.gab (the type ascription is skipped,
-- the value rides). Rust: `Let` -- same shape.
def st05 : List Token :=
  [.wort "let", .wort "mut", .ident "n", .zeichen ":",
   .wort "u32", .zeichen "=", .zahl 0, .zeichen ";", .ende]
theorem s05_lex :
    lex "let mut n : u32 = 0;" = .ok st05 := by
  decide
theorem s05 : beqTopStmt (parseTopStmt st05)
    (.ok (.lass true "n" (.lit 0))) = true := by
  decide
-- beispiele/46-verneinung.gab:45. Rust: `Let` with `veraenderlich`
-- -- same shape.
def st06 : List Token :=
  [.wort "let", .ident "g", .zeichen "=",
   .ident "groesse_gemessen", .zeichen "(", .zeichen ")",
   .wort "else", .zeichen "(", .ident "e1", .zeichen ")",
   .zeichen "{", .wort "return", .wort "false", .zeichen ";",
   .zeichen "}", .ende]
theorem s06_lex :
    lex "let g = groesse_gemessen() else (e1) { return false; }" =
      .ok st06 := by
  decide
theorem s06 : beqTopStmt (parseTopStmt st06)
    (.ok (.lassElse "g" "groesse_gemessen()" "e1"
      (.block [] (.some (.ret (.some .falsch)))))) = true := by
  decide
-- beispiele/06-annahmen.gab:136. Rust: `LetSonst` with a call
-- source -- same shape (the `else` takes no trailing `;`, as in
-- `parse.rs`).
def st07 : List Token :=
  [.wort "let", .ident "fertig", .zeichen "=",
   .ident "FARBE_FERTIG", .wort "awaits", .zeichen "{",
   .ident "farbbericht", .zeichen "}", .zeichen ";", .ende]
theorem s07_lex :
    lex "let fertig = FARBE_FERTIG awaits { farbbericht };" =
      .ok st07 := by
  decide
theorem s07 : beqTopStmt (parseTopStmt st07)
    (.ok (.erwartet "fertig" (.variable "FARBE_FERTIG")
      "farbbericht ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:60. Rust: `AwaitLoad` -- same
-- shape (the payload rides raw; `parse.rs` keeps the place list).
def st08 : List Token :=
  [.wort "let", .ident "alt", .zeichen "=",
   .ident "ZAEHLER", .wort "exchange", .wort "update",
   .zeichen "(", .ident "v", .zeichen ")", .wort "bounded",
   .zahl 4, .wort "ops", .wort "on_exceeded", .ident "streit",
   .zeichen "{", .zeichen "}", .wort "publishes",
   .wort "nothing", .zeichen ";", .ende]
theorem s08_lex :
    lex "let alt = ZAEHLER exchange update(v) bounded 4 ops on_exceeded streit { } publishes nothing;" =
      .ok st08 := by
  decide
theorem s08 : beqTopStmt (parseTopStmt st08)
    (.ok (.tauscht "alt" (.variable "ZAEHLER")
      "update ( v ) bounded 4 ops on_exceeded streit { } publishes nothing ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:104 (block emptied). Rust:
-- `Exchange` with the `Update` form -- same head shape (the
-- bound, the exit and the body ride raw).
def st09 : List Token :=
  [.wort "let", .ident "genommen", .zeichen "=",
   .ident "BESITZER", .wort "exchange", .ident "f",
   .wort "when", .wort "old", .zeichen "(",
   .ident "BESITZER", .zeichen ")", .zeichen "==", .zahl 0,
   .wort "returns", .ident "erfolg", .wort "publishes",
   .wort "nothing", .zeichen ";", .ende]
theorem s09_lex :
    lex "let genommen = BESITZER exchange f when old(BESITZER) == 0 returns erfolg publishes nothing;" =
      .ok st09 := by
  decide
theorem s09 : beqTopStmt (parseTopStmt st09)
    (.ok (.tauscht "genommen" (.variable "BESITZER")
      "f when old ( BESITZER ) == 0 returns erfolg publishes nothing ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:131. Rust: `Exchange` with
-- the compare form -- same head shape.
def st10 : List Token :=
  [.wort "let", .ident "s", .zeichen "=", .zeichen "@",
   .ident "summe", .zeichen "#", .ident "sum", .zeichen "(",
   .zeichen ")", .zeichen "{", .zahl 10, .zahl 20, .zahl 30,
   .zahl 40, .zeichen "}", .zeichen ";", .ende]
theorem s10_lex :
    lex "let s = @summe#sum() { 10 20 30 40 };" = .ok st10 := by
  decide
theorem s10 : beqTopStmt (parseTopStmt st10)
    (.ok (.lassLib false "s" "summe" "sum")) = true := by
  decide
-- beispiele/107-summe-zwei-rufe.gab:36. Rust: `Let` over a
-- `LibraryCall` -- same shape (the region is captured balanced,
-- never interpreted).
def st11 : List Token :=
  [.wort "if", .ident "fertig", .zeichen "{", .wort "return",
   .ident "farbbericht", .zeichen ";", .zeichen "}", .ende]
theorem s11_lex :
    lex "if fertig { return farbbericht; }" = .ok st11 := by
  decide
theorem s11 : beqTopStmt (parseTopStmt st11)
    (.ok (.wenn (.variable "fertig")
      (.block [] (.some (.ret (.some (.variable "farbbericht")))))
      [] .none)) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab (the branch of
-- `bericht_lesen`). Rust: `Wenn` with no `else` -- same shape.
def st12 : List Token :=
  [.wort "if", .ident "a", .zeichen "{", .zeichen "}",
   .wort "else", .wort "if", .ident "b", .zeichen "{",
   .zeichen "}", .wort "else", .zeichen "{", .zeichen "}",
   .ende]
theorem s12_lex :
    lex "if a { } else if b { } else { }" = .ok st12 := by
  decide
theorem s12 : beqTopStmt (parseTopStmt st12)
    (.ok (.wenn (.variable "a") (.block [] .none)
      [(.sonstWenn (.variable "b") (.block [] .none))]
      (.some (.block [] .none)))) = true := by
  decide
-- No corpus occurrence of `else if` (measured 2026-09-13): the
-- shape probe for the SYNTAX.md `ifstmt` production. Rust: `Wenn`
-- with one `else if` and one `else` -- same shape.
def st13 : List Token :=
  [.wort "match", .ident "c", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "s", .zeichen "]", .zeichen ".",
   .ident "vorheriges", .zeichen "{", .wort "Some",
   .zeichen "(", .ident "p", .zeichen ")", .zeichen "=>",
   .zeichen "{", .zeichen "}", .wort "None", .zeichen "=>",
   .zeichen "{", .zeichen "}", .zeichen "}", .ende]
theorem s13_lex :
    lex "match c.slots[s].vorheriges { Some(p) => { } None => { } }" =
      .ok st13 := by
  decide
theorem s13 : beqTopStmt (parseTopStmt st13)
    (.ok (.matchS
      (.feld (.index (.feld (.variable "c") "slots")
        (.variable "s")) "vorheriges")
      [(.arm "Some" (.some "p") (.block [] .none)),
       (.arm "None" .none (.block [] .none))])) = true := by
  decide
-- beispiele/01-tabelle.gab:98 (bodies emptied). Rust: `Match`
-- with one binder arm and one bare arm -- same shape.
def st14 : List Token :=
  [.wort "traverse", .ident "e", .wort "over", .wort "slots",
   .wort "of", .ident "q", .wort "by", .wort "unvisited",
   .zeichen "{", .zeichen "}", .ende]
theorem s14_lex :
    lex "traverse e over slots of q by unvisited { }" =
      .ok st14 := by
  decide
theorem s14 : beqTopStmt (parseTopStmt st14)
    (.ok (.traverseS "e over slots of q by unvisited "
      (.block [] .none))) = true := by
  decide
-- beispiele/04-schleifen.gab (the `dienstschleife` header, body
-- emptied). Rust: `Schleife::Traverse` -- same head shape (the
-- domain and the mode ride raw).
def st15 : List Token :=
  [.wort "retry", .ident "warten", .wort "until",
   .ident "ok", .wort "bounded", .zahl 8, .wort "ops",
   .wort "on_exceeded", .ident "haengt", .zeichen "{",
   .zeichen "}", .ende]
theorem s15_lex :
    lex "retry warten until ok bounded 8 ops on_exceeded haengt { }" =
      .ok st15 := by
  decide
theorem s15 : beqTopStmt (parseTopStmt st15)
    (.ok (.retryS "warten until ok bounded 8 ops on_exceeded haengt "
      (.block [] .none))) = true := by
  decide
-- beispiele/02-geraet.gab:65 (shortened). Rust:
-- `Schleife::Retry` -- same head shape (the `until` predicate
-- needs the `pred` reader and rides raw).
def st16 : List Token :=
  [.wort "forever", .ident "dienst", .wort "per_pass",
   .wort "bounded", .zahl 4096, .wort "ops",
   .wort "on_exceeded", .wort "w", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .wort "progress",
   .ident "tick", .zeichen "{", .zeichen "}", .ende]
theorem s16_lex :
    lex "forever dienst per_pass bounded 4096 ops on_exceeded w effects { pure } progress tick { }" =
      .ok st16 := by
  decide
theorem s16 : beqTopStmt (parseTopStmt st16)
    (.ok (.foreverS
      "dienst per_pass bounded 4096 ops on_exceeded w effects { pure } progress tick "
      (.block [] .none))) = true := by
  decide
-- beispiele/04-schleifen.gab:76 (shortened). Rust:
-- `Schleife::Forever` -- same head shape (the `effects` braces
-- are stepped over balanced).
def st17 : List Token :=
  [.wort "breaking", .ident "antwortpflicht_paarig",
   .zeichen "{", .zeichen "}", .ende]
theorem s17_lex :
    lex "breaking antwortpflicht_paarig { }" = .ok st17 := by
  decide
theorem s17 : beqTopStmt (parseTopStmt st17)
    (.ok (.bricht ["antwortpflicht_paarig"]
      (.block [] .none))) = true := by
  decide
-- beispiele/53-zwei-orte.gab:64 (body emptied). Rust: `Bricht`
-- -- same shape.
def st18 : List Token :=
  [.wort "narrow", .ident "roh", .wort "to", .zahl 0,
   .zeichen "..", .ident "GRENZE", .wort "else",
   .zeichen "{", .wort "return", .zahl 0, .zeichen ";",
   .zeichen "}", .ende]
theorem s18_lex :
    lex "narrow roh to 0 .. GRENZE else { return 0; }" =
      .ok st18 := by
  decide
theorem s18 : beqTopStmt (parseTopStmt st18)
    (.ok (.narrowS (.variable "roh") "0 .. GRENZE "
      (.block [] (.some (.ret (.some (.lit 0))))))) = true := by
  decide
-- beispiele/08-bereiche.gab:127. Rust: `Narrow` over a range --
-- same shape (the range rides raw).
def st19 : List Token :=
  [.wort "narrow", .wort "x", .wort "to", .wort "finite",
   .wort "else", .zeichen "{", .wort "return",
   .ident "HALB", .zeichen ";", .zeichen "}", .ende]
theorem s19_lex :
    lex "narrow x to finite else { return HALB; }" =
      .ok st19 := by
  decide
theorem s19 : beqTopStmt (parseTopStmt st19)
    (.ok (.narrowS (.variable "x") "finite"
      (.block [] (.some (.ret (.some (.variable "HALB"))))))) = true := by
  decide
-- beispiele/26-gleitkomma.gab:73. Rust: `Narrow` to `finite` --
-- same shape.
def st20 : List Token :=
  [.wort "locks", .ident "P", .zeichen "{", .zeichen "}",
   .ende]
theorem s20_lex :
    lex "locks P { }" = .ok st20 := by
  decide
theorem s20 : beqTopStmt (parseTopStmt st20)
    (.ok (.sperrt false (.variable "P")
      (.block [] .none))) = true := by
  decide
-- beispiele/71-frist-und-zaehlung.gab (body emptied). Rust:
-- `Sperrt` -- same shape.
def st21 : List Token :=
  [.wort "locks", .wort "shared", .ident "PLANER",
   .zeichen "{", .zeichen "}", .ende]
theorem s21_lex :
    lex "locks shared PLANER { }" = .ok st21 := by
  decide
theorem s21 : beqTopStmt (parseTopStmt st21)
    (.ok (.sperrt true (.variable "PLANER")
      (.block [] .none))) = true := by
  decide
-- beispiele/04-schleifen.gab (the `locks PLANER` shape with the
-- shared witness). Rust: `Sperrt` with `geteilt` -- same shape.
def st22 : List Token :=
  [.wort "observes", .ident "BACCT", .zeichen "{",
   .zeichen "}", .ende]
theorem s22_lex :
    lex "observes BACCT { }" = .ok st22 := by
  decide
theorem s22 : beqTopStmt (parseTopStmt st22)
    (.ok (.beobachtet "BACCT" (.block [] .none))) = true := by
  decide
-- beispiele/31-rcu.gab:39 (body emptied). Rust: `Observiert` --
-- same shape.
def st23 : List Token :=
  [.wort "leave", .ident "dienst", .zeichen ";", .ende]
theorem s23_lex :
    lex "leave dienst;" = .ok st23 := by
  decide
theorem s23 : beqTopStmt (parseTopStmt st23)
    (.ok (.verlasse "dienst")) = true := by
  decide
-- beispiele/04-schleifen.gab. Rust: `Leave` -- same shape.
def st24 : List Token :=
  [.wort "next", .ident "dienst", .zeichen ";", .ende]
theorem s24_lex :
    lex "next dienst;" = .ok st24 := by
  decide
theorem s24 : beqTopStmt (parseTopStmt st24)
    (.ok (.weiter "dienst")) = true := by
  decide
-- SYNTAX.md `nextstmt` (no corpus occurrence beside `leave`
-- sites; measured 2026-09-13). Rust: `Next` -- same shape.
def st25 : List Token :=
  [.ident "FARBE_FERTIG", .zeichen "=", .wort "true",
   .wort "publishes", .zeichen "{", .ident "farbbericht",
   .zeichen "}", .zeichen ";", .ende]
theorem s25_lex :
    lex "FARBE_FERTIG = true publishes { farbbericht };" =
      .ok st25 := by
  decide
theorem s25 : beqTopStmt (parseTopStmt st25)
    (.ok (.publiziert (.variable "FARBE_FERTIG") .wahr
      "farbbericht ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:52. Rust: `Publish` with a
-- braced payload -- same shape (the payload rides raw).
def st26 : List Token :=
  [.ident "TIEFE_MAX", .zeichen "=", .ident "t",
   .wort "publishes", .wort "nothing", .zeichen ";", .ende]
theorem s26_lex :
    lex "TIEFE_MAX = t publishes nothing;" = .ok st26 := by
  decide
theorem s26 : beqTopStmt (parseTopStmt st26)
    (.ok (.publiziert (.variable "TIEFE_MAX") (.variable "t")
      "nothing")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:72. Rust: `Publish` with
-- `nothing` -- same shape.
def st27 : List Token :=
  [.wort "return", .wort "r", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "belegt", .zeichen ";", .ende]
theorem s27_lex :
    lex "return r.slots[i].belegt;" = .ok st27 := by
  decide
theorem s27 : beqTopStmt (parseTopStmt st27)
    (.ok (.rueck (.some
      (.feld (.index (.feld (.variable "r") "slots")
        (.variable "i")) "belegt")))) = true := by
  decide
-- beispiele/15 (the `uebernehmen` exit). Rust: `Return` over a
-- place -- same shape.
def st28 : List Token :=
  [.wort "return", .zeichen ";", .ende]
theorem s28_lex :
    lex "return;" = .ok st28 := by
  decide
theorem s28 : beqTopStmt (parseTopStmt st28)
    (.ok (.rueck .none)) = true := by
  decide
-- beispiele/06-annahmen.gab:101. Rust: `Return` with no value --
-- same shape.
def st29 : List Token :=
  [.wort "return", .ident "Fehler", .zeichen "::",
   .ident "Buchfuehrung", .zeichen ";", .ende]
theorem s29_lex :
    lex "return Fehler::Buchfuehrung;" = .ok st29 := by
  decide
theorem s29 : beqTopStmt (parseTopStmt st29)
    (.ok (.rueck (.some (.grund "Fehler" "Buchfuehrung")))) = true := by
  decide
-- beispiele/48-grund-mit-erzeuger.gab (the error-return shape).
-- Rust: `Return` over a `Grund` -- same shape.
def st30 : List Token :=
  [.wort "transition", .ident "T", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "s", .zeichen ":", .ident "Idle",
   .zeichen "->", .ident "Busy", .zeichen ";", .ende]
theorem s30_lex :
    lex "transition T.slots[i].s : Idle -> Busy;" = .ok st30 := by
  decide
theorem s30 : beqTopStmt (parseTopStmt st30)
    (.ok (.uebergang
      (.feld (.index (.feld (.variable "T") "slots")
        (.variable "i")) "s")
      "Idle" "Busy")) = true := by
  decide
-- No corpus occurrence of a `state` field transition (measured
-- 2026-09-13; devices carry `transition` at the item level
-- instead): the shape probe for the SYNTAX.md `stateassign`
-- production. Rust has no statement-level counterpart; the
-- device-level `transset` is skipped by the item reader.
def st31 : List Token :=
  [.wort "advances", .ident "setup", .zeichen "->",
   .ident "live", .zeichen ";", .ende]
theorem s31_lex :
    lex "advances setup -> live;" = .ok st31 := by
  decide
theorem s31 : beqTopStmt (parseTopStmt st31)
    (.ok (.schreitet "setup" "live")) = true := by
  decide
-- beispiele/02-geraet.gab:129. The phase step as a statement --
-- `parse.rs` has no statement-level counterpart either (it rides
-- in the checker); the shape is the SYNTAX.md `advstmt`
-- production.
def st32 : List Token :=
  [.wort "let", .ident "a", .zeichen "=", .wort "alloc",
   .ident "Log", .zeichen "(", .zahl 10, .zeichen ")",
   .zeichen ";", .ende]
theorem s32_lex :
    lex "let a = alloc Log (10);" = .ok st32 := by
  decide
theorem s32 : beqTopStmt (parseTopStmt st32)
    (.ok (.allocS false "a" "Log" (.lit 10) .none)) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:11. Rust: `Alloc` with no
-- `else` -- same shape.
def st33 : List Token :=
  [.wort "let", .ident "c", .zeichen "=", .wort "alloc",
   .ident "Log", .zeichen "(", .ident "a", .zeichen "+",
   .ident "b", .zeichen ")", .wort "else", .zeichen "{",
   .wort "return", .zahl 0, .zeichen ";", .zeichen "}",
   .zeichen ";", .ende]
theorem s33_lex :
    lex "let c = alloc Log (a + b) else { return 0; };" =
      .ok st33 := by
  decide
theorem s33 : beqTopStmt (parseTopStmt st33)
    (.ok (.allocS false "c" "Log"
      (.bin "+" (.variable "a") (.variable "b"))
      (.some (.block [] (.some (.ret (.some (.lit 0)))))))) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:13 (shortened). Rust: `Alloc`
-- with the full-arena continuation -- same shape (the `else`
-- takes a plain block here, unlike `let … else`).
def st34 : List Token :=
  [.wort "reset", .ident "Log", .zeichen ";", .ende]
theorem s34_lex :
    lex "reset Log;" = .ok st34 := by
  decide
theorem s34 : beqTopStmt (parseTopStmt st34)
    (.ok (.resetS "Log")) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:16. Rust: `ResetArena` --
-- same shape.
def st35 : List Token :=
  [.zeichen "@", .ident "spirv", .zeichen "#", .wort "kernel",
   .zeichen "(", .ident "n", .zeichen ")", .zeichen "{",
   .wort "dispatch", .zahl 0, .zeichen "}", .zeichen ";",
   .ende]
theorem s35_lex :
    lex "@spirv#kernel(n) { dispatch 0 };" = .ok st35 := by
  decide
theorem s35 : beqTopStmt (parseTopStmt st35)
    (.ok (.libruf "spirv" "kernel" 1)) = true := by
  decide
-- SYNTAX.md §7 (the library-call example). Rust: `LibraryCall`
-- in statement position -- same shape (one argument, region
-- skipped balanced).
def et01 : List Token :=
  [.wort "module", .ident "beispiel", .zeichen "::",
   .ident "eigen", .zeichen "{", .zeichen "}", .ende]
theorem e01_lex :
    lex "module beispiel::eigen { }" = .ok et01 := by
  decide
theorem e01 : beqTopItems (parseTopItems et01)
    (.ok [(.modul "beispiel :: eigen " [])]) = true := by
  decide
-- beispiele/15 (the module head, body emptied). Rust: `Modul`
-- with the path and the member list -- same shape (the path
-- rides raw).
def et02 : List Token :=
  [.wort "use", .ident "gpu", .zeichen "::", .ident "spirv",
   .zeichen ";", .ende]
theorem e02_lex :
    lex "use gpu::spirv;" = .ok et02 := by
  decide
theorem e02 : beqTopItems (parseTopItems et02)
    (.ok [(.useS "gpu :: spirv ")]) = true := by
  decide
-- beispiele/100-hardwareprofil.gab (the `use` shape). Rust:
-- `Use` -- same shape (the path rides raw).
def et03 : List Token :=
  [.wort "type", .ident "Fuellstand", .zeichen "=",
   .wort "u32", .wort "in", .zahl 0, .zeichen "..",
   .ident "VOLL", .zeichen ";", .ende]
theorem e03_lex :
    lex "type Fuellstand = u32 in 0 .. VOLL;" = .ok et03 := by
  decide
theorem e03 : beqTopItems (parseTopItems et03)
    (.ok [(.typS "Fuellstand")]) = true := by
  decide
-- beispiele/52-baugatter.gab (the `Fuellstand` shape). Rust:
-- `Typ` -- same shape (the right-hand side is skipped, not
-- validated).
def et04 : List Token :=
  [.wort "const", .ident "NSLOTS", .zeichen ":",
   .wort "u32", .zeichen "=", .zahl 16, .zeichen ";", .ende]
theorem e04_lex :
    lex "const NSLOTS : u32 = 16;" = .ok et04 := by
  decide
theorem e04 : beqTopItems (parseTopItems et04)
    (.ok [(.konstS "NSLOTS")]) = true := by
  decide
-- beispiele/71-frist-und-zaehlung.gab. Rust: `Konst` -- same
-- shape.
def et05 : List Token :=
  [.wort "static", .wort "mut", .ident "hoechstmarke",
   .zeichen ":", .ident "Fuellstand", .zeichen "=",
   .zahl 0, .zeichen ";", .ende]
theorem e05_lex :
    lex "static mut hoechstmarke : Fuellstand = 0;" =
      .ok et05 := by
  decide
theorem e05 : beqTopItems (parseTopItems et05)
    (.ok [(.statikS "hoechstmarke")]) = true := by
  decide
-- beispiele/52-baugatter.gab. Rust: `Statisch` -- same shape.
def et06 : List Token :=
  [.wort "extern", .wort "fn", .ident "geraet_haengt",
   .zeichen "(", .zeichen ")", .zeichen "->", .wort "never",
   .wort "effects", .zeichen "{", .wort "diverges",
   .zeichen "}", .zeichen ";", .ende]
theorem e06_lex :
    lex "extern fn geraet_haengt() -> never effects { diverges };" =
      .ok et06 := by
  decide
theorem e06 : beqTopItems (parseTopItems et06)
    (.ok [(.protoS "geraet_haengt")]) = true := by
  decide
-- beispiele/02-geraet.gab:74. Rust: `Funktion` with no body --
-- same shape (a bodiless declaration rides `protoS`).
def et07 : List Token :=
  [.wort "spec", .wort "fn", .ident "ist_blatt",
   .zeichen "(", .ident "c", .zeichen ":", .wort "u32",
   .zeichen ")", .zeichen "->", .wort "bool", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .zeichen "=",
   .ident "c", .zeichen "==", .ident "c", .zeichen ";", .ende]
theorem e07_lex :
    lex "spec fn ist_blatt(c : u32) -> bool effects { pure } = c == c;" =
      .ok et07 := by
  decide
theorem e07 : beqTopItems (parseTopItems et07)
    (.ok [(.protoS "ist_blatt")]) = true := by
  decide
-- beispiele/01-tabelle.gab:81 (signature shortened). Rust:
-- `Funktion` with a `= pred` body -- same shape (the predicate
-- is skipped, not validated).
def et08 : List Token :=
  [.wort "format", .ident "Manifest", .zeichen "@",
   .ident "version", .zahl 1, .wort "endian", .wort "little",
   .zeichen "{", .zeichen "}", .ende]
theorem e08_lex :
    lex "format Manifest @version 1 endian little { }" =
      .ok et08 := by
  decide
theorem e08 : beqTopItems (parseTopItems et08)
    (.ok [(.formatS "Manifest")]) = true := by
  decide
-- beispiele/04-schleifen.gab (the `Manifest` head, body
-- emptied). Rust: `Format` -- same shape.
def et09 : List Token :=
  [.wort "table", .ident "Region", .wort "count", .zahl 8,
   .zeichen "{", .wort "slot", .zeichen "{",
   .ident "belegt", .zeichen ":", .wort "bool", .zeichen ",",
   .zeichen "}", .zeichen "}", .ende]
theorem e09_lex :
    lex "table Region count 8 { slot { belegt : bool, } }" =
      .ok et09 := by
  decide
theorem e09 : beqTopItems (parseTopItems et09)
    (.ok [(.tabelle "Region")]) = true := by
  decide
-- beispiele/15 (the `Region` table). Rust: `Tabelle` -- same
-- shape (slots, invariants and ops are skipped balanced).
def et10 : List Token :=
  [.wort "arena", .ident "Log", .wort "capacity", .zahl 2,
   .zeichen "..", .zahl 8, .wort "of", .wort "u32",
   .zeichen ";", .ende]
theorem e10_lex :
    lex "arena Log capacity 2 .. 8 of u32;" = .ok et10 := by
  decide
theorem e10 : beqTopItems (parseTopItems et10)
    (.ok [(.arenaS "Log")]) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:8. Rust: `Arena` -- same
-- shape.
def et11 : List Token :=
  [.wort "reason", .ident "KappenFehler", .zeichen "{",
   .zeichen "}", .ende]
theorem e11_lex :
    lex "reason KappenFehler { }" = .ok et11 := by
  decide
theorem e11 : beqTopItems (parseTopItems et11)
    (.ok [(.grundS "KappenFehler")]) = true := by
  decide
-- beispiele/01-tabelle.gab:24 (body emptied). Rust: `Reason` --
-- same shape.
def et12 : List Token :=
  [.wort "state", .ident "S", .zeichen "{", .zeichen "}",
   .ende]
theorem e12_lex :
    lex "state S { }" = .ok et12 := by
  decide
theorem e12 : beqTopItems (parseTopItems et12)
    (.ok [(.zustandS "S")]) = true := by
  decide
-- No corpus occurrence of a `state` item (measured 2026-09-13):
-- the shape probe for the SYNTAX.md `state` production. Rust:
-- `StateDecl` -- same head shape.
def et13 : List Token :=
  [.wort "device", .ident "Vtd", .zeichen "(",
   .ident "basis", .zeichen ":", .ident "Pa", .zeichen ")",
   .wort "at", .wort "mmio", .zeichen "{", .zeichen "}",
   .ende]
theorem e13_lex :
    lex "device Vtd(basis : Pa) at mmio { }" = .ok et13 := by
  decide
theorem e13 : beqTopItems (parseTopItems et13)
    (.ok [(.geraetS "Vtd")]) = true := by
  decide
-- beispiele/02-geraet.gab:14 (body emptied). Rust: `Device` --
-- same shape (registers, banks and transitions are skipped
-- balanced).
def et14 : List Token :=
  [.wort "assume", .ident "vtd_te_wirksam",
   .text "GCMD.TE schaltet die Uebersetzung scharf.",
   .wort "falsifier", .ident "sonde_vtd_te", .zeichen ";",
   .ende]
theorem e14_lex :
    lex "assume vtd_te_wirksam \"GCMD.TE schaltet die Uebersetzung scharf.\" falsifier sonde_vtd_te;" =
      .ok et14 := by
  decide
theorem e14 : beqTopItems (parseTopItems et14)
    (.ok [(.annahmeS "vtd_te_wirksam")]) = true := by
  decide
-- beispiele/02-geraet.gab:47 (string shortened). Rust: `Assume`
-- -- same shape (the string is one token).
def et15 : List Token :=
  [.wort "axiom", .ident "rdtsc", .zeichen "(", .zeichen ")",
   .wort "effects", .zeichen "{", .wort "reads",
   .ident "zeitzaehler", .zeichen "}", .wort "falsifier",
   .ident "sonde_tsc", .zeichen ";", .ende]
theorem e15_lex :
    lex "axiom rdtsc() effects { reads zeitzaehler } falsifier sonde_tsc;" =
      .ok et15 := by
  decide
theorem e15 : beqTopItems (parseTopItems et15)
    (.ok [(.axiomaS "rdtsc")]) = true := by
  decide
-- beispiele/06-annahmen.gab:82. Rust: `Axiom` -- same shape.
def et16 : List Token :=
  [.wort "check", .ident "stapel_wasserstand", .zeichen "{",
   .zeichen "}", .ende]
theorem e16_lex :
    lex "check stapel_wasserstand { }" = .ok et16 := by
  decide
theorem e16 : beqTopItems (parseTopItems et16)
    (.ok [(.pruefungS "stapel_wasserstand")]) = true := by
  decide
-- beispiele/06-annahmen.gab:127 (body emptied). Rust: `Check`
-- -- same shape.
def et17 : List Token :=
  [.wort "atomic", .ident "FARBE_FERTIG", .zeichen ":",
   .wort "bool", .wort "publishes", .zeichen "{",
   .ident "farbbericht", .zeichen "}", .wort "release",
   .zeichen ";", .ende]
theorem e17_lex :
    lex "atomic FARBE_FERTIG : bool publishes { farbbericht } release;" =
      .ok et17 := by
  decide
theorem e17 : beqTopItems (parseTopItems et17)
    (.ok [(.atomarS "FARBE_FERTIG")]) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab (the `FARBE_FERTIG` shape).
-- Rust: `AtomicDecl` -- same shape.
def et18 : List Token :=
  [.wort "lock", .ident "P", .wort "protects", .zeichen "{",
   .ident "Plaetze", .zeichen "}", .wort "rank", .zahl 1,
   .zeichen ";", .ende]
theorem e18_lex :
    lex "lock P protects { Plaetze } rank 1;" = .ok et18 := by
  decide
theorem e18 : beqTopItems (parseTopItems et18)
    (.ok [(.sperreS "P")]) = true := by
  decide
-- beispiele/71-frist-und-zaehlung.gab. Rust: `LockDecl` --
-- same shape.
def et19 : List Token :=
  [.wort "rcu", .ident "BACCT", .wort "protects",
   .zeichen "{", .ident "Konten", .zeichen "}",
   .wort "reclaims", .ident "frei", .zeichen ";", .ende]
theorem e19_lex :
    lex "rcu BACCT protects { Konten } reclaims frei;" =
      .ok et19 := by
  decide
theorem e19 : beqTopItems (parseTopItems et19)
    (.ok [(.rcuS "BACCT")]) = true := by
  decide
-- beispiele/31-rcu.gab:24. Rust: `RcuDecl` -- same shape.
def et20 : List Token :=
  [.wort "group", .ident "Zustellung", .wort "over",
   .zeichen "{", .ident "Endpunkte", .zeichen ",",
   .ident "Faeden", .zeichen "}", .zeichen "{",
   .zeichen "}", .ende]
theorem e20_lex :
    lex "group Zustellung over { Endpunkte, Faeden } { }" =
      .ok et20 := by
  decide
theorem e20 : beqTopItems (parseTopItems et20)
    (.ok [(.gruppeS "Zustellung")]) = true := by
  decide
-- beispiele/17-gruppe-ueber-zwei-sperren.gab:42 (invariant
-- block emptied). Rust: `GruppeDecl` -- same shape.
def et21 : List Token :=
  [.wort "concurrent", .zeichen "{", .ident "read_a",
   .zeichen ",", .ident "read_c", .zeichen "}",
   .zeichen ";", .ende]
theorem e21_lex :
    lex "concurrent { read_a, read_c };" = .ok et21 := by
  decide
theorem e21 : beqTopItems (parseTopItems et21)
    (.ok [(.nebenS "{ read_a , read_c } ")]) = true := by
  decide
-- beispiele/108-disjoint-start-locks.gab:39. Rust:
-- `ConcurrentDecl` -- same shape (the member list rides raw).
def et22 : List Token :=
  [.wort "accumulates", .ident "hoechststand", .zeichen ":",
   .wort "u64", .wort "merge", .wort "max", .wort "per",
   .wort "cpu", .ident "NKERNE", .zeichen ";", .ende]
theorem e22_lex :
    lex "accumulates hoechststand : u64 merge max per cpu NKERNE;" =
      .ok et22 := by
  decide
theorem e22 : beqTopItems (parseTopItems et22)
    (.ok [(.akkumS "hoechststand")]) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:40. Rust: `AccDecl` --
-- same shape.
def et23 : List Token :=
  [.wort "walk", .ident "Seitentabelle", .wort "levels",
   .zahl 4, .zeichen "{", .zeichen "}", .ende]
theorem e23_lex :
    lex "walk Seitentabelle levels 4 { }" = .ok et23 := by
  decide
theorem e23 : beqTopItems (parseTopItems et23)
    (.ok [(.wegS "Seitentabelle")]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:26 (body emptied). Rust:
-- `WalkDecl` -- same shape.
def et24 : List Token :=
  [.wort "entry", .ident "nmi", .wort "vector", .zahl 2,
   .wort "via", .ident "idt", .wort "arch", .ident "x86_64",
   .zeichen "{", .zeichen "}", .ende]
theorem e24_lex :
    lex "entry nmi vector 2 via idt arch x86_64 { }" =
      .ok et24 := by
  decide
theorem e24 : beqTopItems (parseTopItems et24)
    (.ok [(.eingangS "nmi")]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:72 (body emptied). Rust:
-- `EntryDecl` -- same shape.
def et25 : List Token :=
  [.wort "entrust", .ident "jitpuffer", .wort "at",
   .ident "Gastbild", .wort "arch", .ident "x86_64",
   .zeichen "{", .zeichen "}", .ende]
theorem e25_lex :
    lex "entrust jitpuffer at Gastbild arch x86_64 { }" =
      .ok et25 := by
  decide
theorem e25 : beqTopItems (parseTopItems et25)
    (.ok [(.anvertrautS "jitpuffer")]) = true := by
  decide
-- beispiele/25-entrust.gab:32 (body emptied). Rust:
-- `EntrustDecl` -- same shape.
def et26 : List Token :=
  [.wort "boot", .ident "multiboot1", .wort "arch",
   .ident "x86_64", .zeichen "{", .zeichen "}", .ende]
theorem e26_lex :
    lex "boot multiboot1 arch x86_64 { }" = .ok et26 := by
  decide
theorem e26 : beqTopItems (parseTopItems et26)
    (.ok [(.startS "multiboot1")]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:86 (body emptied). Rust:
-- `BootDecl` -- same shape.
def et27 : List Token :=
  [.wort "syscall", .ident "write", .zeichen "(",
   .ident "fd", .zeichen ":", .wort "u64", .zeichen ")",
   .zeichen "->", .wort "u64", .wort "or", .ident "IoError",
   .wort "abi", .ident "linux", .wort "arch", .ident "x86_64",
   .wort "number", .zahl 1, .wort "regs", .wort "in",
   .zeichen "{", .ident "rdi", .zeichen "=", .ident "fd",
   .zeichen "}", .wort "regs", .wort "out", .zeichen "{",
   .ident "rax", .zeichen "}", .wort "clobbers",
   .zeichen "{", .ident "rcx", .zeichen "}", .wort "errors",
   .zeichen "{", .ident "EBADF", .zeichen "=>",
   .ident "BadFd", .zeichen "}", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .wort "assume",
   .ident "linux_write_contract", .wort "falsifier",
   .ident "sonde_write", .zeichen ";", .ende]
theorem e27_lex :
    lex "syscall write(fd : u64) -> u64 or IoError abi linux arch x86_64 number 1 regs in { rdi = fd } regs out { rax } clobbers { rcx } errors { EBADF => BadFd } effects { pure } assume linux_write_contract falsifier sonde_write;" =
      .ok et27 := by
  decide
theorem e27 : beqTopItems (parseTopItems et27)
    (.ok [(.sysrufS "write")]) = true := by
  decide
-- beispiele/74-syscall-schreiben.gab:27 (register maps and
-- clauses shortened). Rust: `SyscallDecl` -- same shape (maps
-- and clauses are skipped balanced).
def et28 : List Token :=
  [.wort "translator", .ident "build", .wort "for",
   .wort "kernel", .zeichen "(", .ident "region",
   .zeichen ":", .ident "KernelTab", .zeichen ")",
   .zeichen "->", .ident "KernelTab", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .wort "costs",
   .zeichen "<=", .zahl 8, .wort "ops", .wort "decreases",
   .ident "region", .zeichen ".", .ident "words",
   .zeichen "{", .wort "return", .ident "region",
   .zeichen ";", .zeichen "}", .ende]
theorem e28_lex :
    lex "translator build for kernel(region : KernelTab) -> KernelTab effects { pure } costs <= 8 ops decreases region.words { return region; }" =
      .ok et28 := by
  decide
theorem e28 : beqTopItems (parseTopItems et28)
    (.ok [(.uebersetzerS "build"
      (.block [] (.some (.ret (.some (.variable "region"))))))]) = true := by
  decide
-- beispiele/100-hardwareprofil.gab:40. A translator with a real
-- body -- the name and the block ride; the linkage clauses are
-- skipped like a function header.
def et29 : List Token :=
  [.wort "profile", .zeichen "{", .wort "arch",
   .ident "x86_64", .zeichen ";", .zeichen "}",
   .zeichen ";", .ende]
theorem e29_lex :
    lex "profile { arch x86_64; };" = .ok et29 := by
  decide
theorem e29 : beqTopItems (parseTopItems et29)
    (.ok [(.profilS false)]) = true := by
  decide
-- beispiele/100-hardwareprofil.gab:50 (entries shortened).
-- Rust: `ProfilBlock` -- same shape (entries ride unchecked).
def et30 : List Token :=
  [.wort "requires", .wort "profile", .zeichen "{",
   .wort "arch", .ident "x86_64", .zeichen ";",
   .zeichen "}", .zeichen ";", .ende]
theorem e30_lex :
    lex "requires profile { arch x86_64; };" = .ok et30 := by
  decide
theorem e30 : beqTopItems (parseTopItems et30)
    (.ok [(.profilS true)]) = true := by
  decide
-- beispiele/100-hardwareprofil.gab:26 (entries shortened).
-- Rust: `ProfilBedarf` -- same shape.
def et31 : List Token :=
  [.wort "when", .ident "TESTBUILD", .wort "static",
   .wort "mut", .ident "hoechstmarke", .zeichen ":",
   .ident "Fuellstand", .zeichen "=", .zahl 0,
   .zeichen ";", .ende]
theorem e31_lex :
    lex "when TESTBUILD static mut hoechstmarke : Fuellstand = 0;" =
      .ok et31 := by
  decide
theorem e31 : beqTopItems (parseTopItems et31)
    (.ok [(.torS (.statikS "hoechstmarke"))]) = true := by
  decide
-- beispiele/52-baugatter.gab (the gated `static`). Rust: the
-- `when` gate over an item -- same shape (`TESTBUILD` lexes as
-- an identifier, not a keyword).
def ft01 : List Token :=
  [.wort "impl", .wort "fn", .ident "uebernehmen",
   .zeichen "(", .wort "r", .zeichen ":", .wort "ptr",
   .zeichen "<", .wort "normal", .zeichen ",", .wort "own",
   .zeichen ">", .ident "Region", .zeichen ",", .ident "i",
   .zeichen ":", .wort "index", .wort "into",
   .ident "Region", .zeichen ")", .zeichen "->", .wort "bool",
   .wort "effects", .zeichen "{", .wort "reads", .wort "r",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "writes",
   .wort "r", .zeichen ".", .wort "slots", .zeichen "}",
   .wort "costs", .zeichen "<=", .zahl 4, .wort "ops",
   .zeichen "{", .wort "r", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "belegt", .zeichen "=", .wort "true", .zeichen ";",
   .wort "return", .wort "r", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "belegt", .zeichen ";", .zeichen "}", .ende]
theorem f01_lex :
    lex "impl fn uebernehmen(r : ptr<normal, own> Region, i : index into Region) -> bool effects { reads r.slots, writes r.slots } costs <= 4 ops { r.slots[i].belegt = true; return r.slots[i].belegt; }" =
      .ok ft01 := by
  decide
theorem f01 : beqTopItems (parseTopItems ft01)
    (.ok [(.funktion "uebernehmen"
      (.block
        [(.zuweis
          (.feld (.index (.feld (.variable "r") "slots")
            (.variable "i")) "belegt")
          "=" .wahr)]
        (.some (.ret (.some
          (.feld (.index (.feld (.variable "r") "slots")
            (.variable "i")) "belegt"))))))]) = true := by
  decide
-- beispiele/15-own-traegt-beide-rechte.gab: the smallest
-- corpus function with a two-statement body (66 tokens): the
-- `impl` prefix is skipped, the header clauses (`ptr<…>`
-- signature, `effects`, `costs`) are stepped over, the body
-- parses end to end -- an assignment plus the `return` ender.
-- Newlines are whitespace to the lexer, so the single-line form
-- above carries exactly the corpus tokens.

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * The tree shapes above are checked by kernel `Bool` evaluation
    (`beqTopStmt`/`beqTopItems … = true`), not by a soundness
    theorem for `beqSAnw` -- the same cut as item 11 of the CUTS
    block in `Parser/Ausdruck.lean`.
  * Every shape difference against `crates/gabbro-syntax` found by
    these probes is booked in the CUTS blocks of
    `Parser/Anweisung.lean` and `Parser/Element.lean`; the probe
    comments name the Rust counterpart (`ast.rs`) of each form.
  * `{ }` bodies stand for the corpus block at the cited site: the
    probe pins the head dispatch and the empty-body shape, not the
    full corpus block. The one full block is `f01`.
  * Synthetic probes (no corpus occurrence, measured 2026-09-13):
    `s12` (`else if`), `s24` (`next`), `s30` (`stateassign`),
    `e12` (`state` item). The `s31` (`advances`) shape has no
    statement-level counterpart in `parse.rs` either (it rides in
    the checker); the probe pins the SYNTAX.md production.
-/

#print axioms Gabbro.Grammatik.Parser.s01
#print axioms Gabbro.Grammatik.Parser.e01
#print axioms Gabbro.Grammatik.Parser.f01
