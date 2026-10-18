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
import Grammatik.Parser.Stmt.Anweisung

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
    (.ok (.set
      (.field (.index (.field (.variable "r") "slots")
        (.variable "i")) "belegt")
      "=" .tru)) = true := by
  decide
-- beispiele/15 (the body of `uebernehmen`). Rust: `Zuweisung`
-- with a slot target -- same shape.
def st02 : List Token :=
  [.ident "c", .zeichen ".", .wort "slots", .zeichen "[",
   .ident "s", .zeichen "]", .zeichen ".", .ident "marke",
   .zeichen "+=", .num 1, .zeichen ";", .ende]
theorem s02_lex :
    lex "c.slots[s].marke += 1;" = .ok st02 := by
  decide
theorem s02 : beqTopStmt (parseTopStmt st02)
    (.ok (.set
      (.field (.index (.field (.variable "c") "slots")
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
    (.ok (.call "wurzel_setzen" [.variable "v"])) = true := by
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
    (.ok (.bind false "x" (.some (.atom "u64"))
      (.index (.variable "SQUARES") (.variable "a")))) = true := by
  decide
-- beispiele/92-const-squares.gab (the type ascription is read,
-- the value rides). Rust: `Let` -- same shape.
def st05 : List Token :=
  [.wort "let", .wort "mut", .ident "n", .zeichen ":",
   .wort "u32", .zeichen "=", .num 0, .zeichen ";", .ende]
theorem s05_lex :
    lex "let mut n : u32 = 0;" = .ok st05 := by
  decide
theorem s05 : beqTopStmt (parseTopStmt st05)
    (.ok (.bind true "n" (.some (.atom "u32")) (.lit 0))) = true := by
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
    (.ok (.bindElse "g" .none (.call "groesse_gemessen" []) "e1"
      (.block [] (.some (.ret (.some .fls)))))) = true := by
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
    (.ok (.await "fertig" (.variable "FARBE_FERTIG")
      "farbbericht ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:60. Rust: `AwaitLoad` -- same
-- shape (the payload rides raw; `parse.rs` keeps the place list).
def st08 : List Token :=
  [.wort "let", .ident "alt", .zeichen "=",
   .ident "ZAEHLER", .wort "exchange", .wort "update",
   .zeichen "(", .ident "v", .zeichen ")", .wort "bounded",
   .num 4, .wort "ops", .wort "on_exceeded", .ident "streit",
   .zeichen "{", .zeichen "}", .wort "publishes",
   .wort "nothing", .zeichen ";", .ende]
theorem s08_lex :
    lex "let alt = ZAEHLER exchange update(v) bounded 4 ops on_exceeded streit { } publishes nothing;" =
      .ok st08 := by
  decide
theorem s08 : beqTopStmt (parseTopStmt st08)
    (.ok (.swap "alt" (.variable "ZAEHLER")
      "update ( v ) bounded 4 ops on_exceeded streit { } publishes nothing ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:104 (block emptied). Rust:
-- `Exchange` with the `Update` form -- same head shape (the
-- bound, the exit and the body ride raw).
def st09 : List Token :=
  [.wort "let", .ident "genommen", .zeichen "=",
   .ident "BESITZER", .wort "exchange", .ident "f",
   .wort "when", .wort "old", .zeichen "(",
   .ident "BESITZER", .zeichen ")", .zeichen "==", .num 0,
   .wort "returns", .ident "erfolg", .wort "publishes",
   .wort "nothing", .zeichen ";", .ende]
theorem s09_lex :
    lex "let genommen = BESITZER exchange f when old(BESITZER) == 0 returns erfolg publishes nothing;" =
      .ok st09 := by
  decide
theorem s09 : beqTopStmt (parseTopStmt st09)
    (.ok (.swap "genommen" (.variable "BESITZER")
      "f when old ( BESITZER ) == 0 returns erfolg publishes nothing ")) = true := by
  decide
-- beispiele/05-nebenlaeufigkeit.gab:131. Rust: `Exchange` with
-- the compare form -- same head shape.
def st10 : List Token :=
  [.wort "let", .ident "s", .zeichen "=", .zeichen "@",
   .ident "summe", .zeichen "#", .ident "sum", .zeichen "(",
   .zeichen ")", .zeichen "{", .num 10, .num 20, .num 30,
   .num 40, .zeichen "}", .zeichen ";", .ende]
theorem s10_lex :
    lex "let s = @summe#sum() { 10 20 30 40 };" = .ok st10 := by
  decide
theorem s10 : beqTopStmt (parseTopStmt st10)
    (.ok (.bindLib false "s" .none "summe" "sum")) = true := by
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
    (.ok (.cond (.variable "fertig")
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
    (.ok (.cond (.variable "a") (.block [] .none)
      [(.elsif (.variable "b") (.block [] .none))]
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
    (.ok (.cases
      (.field (.index (.field (.variable "c") "slots")
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
    (.ok (.each "e" none "slots" (.variable "q") "unvisited" "" none
      (.block [] .none))) = true := by
  decide
-- beispiele/04-schleifen.gab (the `dienstschleife` header, body
-- emptied). Rust: `Schleife::Traverse` -- same head shape (the
-- domain and the mode ride raw).
def st15 : List Token :=
  [.wort "retry", .ident "warten", .wort "until",
   .ident "ok", .wort "bounded", .num 8, .wort "ops",
   .wort "on_exceeded", .ident "haengt", .zeichen "{",
   .zeichen "}", .ende]
theorem s15_lex :
    lex "retry warten until ok bounded 8 ops on_exceeded haengt { }" =
      .ok st15 := by
  decide
theorem s15 : beqTopStmt (parseTopStmt st15)
    (.ok (.retry "warten until ok bounded 8 ops on_exceeded haengt "
      (.block [] .none))) = true := by
  decide
-- beispiele/02-geraet.gab:65 (shortened). Rust:
-- `Schleife::Retry` -- same head shape (the `until` predicate
-- needs the `pred` reader and rides raw).
def st16 : List Token :=
  [.wort "forever", .ident "dienst", .wort "per_pass",
   .wort "bounded", .num 4096, .wort "ops",
   .wort "on_exceeded", .wort "w", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .wort "progress",
   .ident "tick", .zeichen "{", .zeichen "}", .ende]
theorem s16_lex :
    lex "forever dienst per_pass bounded 4096 ops on_exceeded w effects { pure } progress tick { }" =
      .ok st16 := by
  decide
theorem s16 : beqTopStmt (parseTopStmt st16)
    (.ok (.loop
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
    (.ok (.waive ["antwortpflicht_paarig"]
      (.block [] .none))) = true := by
  decide
-- beispiele/53-zwei-orte.gab:64 (body emptied). Rust: `Bricht`
-- -- same shape.
def st18 : List Token :=
  [.wort "narrow", .ident "roh", .wort "to", .num 0,
   .zeichen "..", .ident "GRENZE", .wort "else",
   .zeichen "{", .wort "return", .num 0, .zeichen ";",
   .zeichen "}", .ende]
theorem s18_lex :
    lex "narrow roh to 0 .. GRENZE else { return 0; }" =
      .ok st18 := by
  decide
theorem s18 : beqTopStmt (parseTopStmt st18)
    (.ok (.trim (.variable "roh") "0 .. GRENZE "
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
    (.ok (.trim (.variable "x") "finite"
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
    (.ok (.locks false (.variable "P")
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
    (.ok (.locks true (.variable "PLANER")
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
    (.ok (.watch "BACCT" (.block [] .none))) = true := by
  decide
-- beispiele/31-rcu.gab:39 (body emptied). Rust: `Observiert` --
-- same shape.
def st23 : List Token :=
  [.wort "leave", .ident "dienst", .zeichen ";", .ende]
theorem s23_lex :
    lex "leave dienst;" = .ok st23 := by
  decide
theorem s23 : beqTopStmt (parseTopStmt st23)
    (.ok (.leave "dienst")) = true := by
  decide
-- beispiele/04-schleifen.gab. Rust: `Leave` -- same shape.
def st24 : List Token :=
  [.wort "next", .ident "dienst", .zeichen ";", .ende]
theorem s24_lex :
    lex "next dienst;" = .ok st24 := by
  decide
theorem s24 : beqTopStmt (parseTopStmt st24)
    (.ok (.next "dienst")) = true := by
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
    (.ok (.emit (.variable "FARBE_FERTIG") .tru
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
    (.ok (.emit (.variable "TIEFE_MAX") (.variable "t")
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
    (.ok (.ret (.some
      (.field (.index (.field (.variable "r") "slots")
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
    (.ok (.ret .none)) = true := by
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
    (.ok (.ret (.some (.why "Fehler" "Buchfuehrung")))) = true := by
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
    (.ok (.shift
      (.field (.index (.field (.variable "T") "slots")
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
    (.ok (.step "setup" "live")) = true := by
  decide
-- beispiele/02-geraet.gab:129. The phase step as a statement --
-- `parse.rs` has no statement-level counterpart either (it rides
-- in the checker); the shape is the SYNTAX.md `advstmt`
-- production.
def st32 : List Token :=
  [.wort "let", .ident "a", .zeichen "=", .wort "alloc",
   .ident "Log", .zeichen "(", .num 10, .zeichen ")",
   .zeichen ";", .ende]
theorem s32_lex :
    lex "let a = alloc Log (10);" = .ok st32 := by
  decide
theorem s32 : beqTopStmt (parseTopStmt st32)
    (.ok (.alloc false "a" .none "Log" (.lit 10) .none)) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:11. Rust: `Alloc` with no
-- `else` -- same shape.
def st33 : List Token :=
  [.wort "let", .ident "c", .zeichen "=", .wort "alloc",
   .ident "Log", .zeichen "(", .ident "a", .zeichen "+",
   .ident "b", .zeichen ")", .wort "else", .zeichen "{",
   .wort "return", .num 0, .zeichen ";", .zeichen "}",
   .zeichen ";", .ende]
theorem s33_lex :
    lex "let c = alloc Log (a + b) else { return 0; };" =
      .ok st33 := by
  decide
theorem s33 : beqTopStmt (parseTopStmt st33)
    (.ok (.alloc false "c" .none "Log"
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
    (.ok (.reset "Log" .none)) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:16. Rust: `ResetArena` --
-- same shape.
def st35 : List Token :=
  [.zeichen "@", .ident "spirv", .zeichen "#", .wort "kernel",
   .zeichen "(", .ident "n", .zeichen ")", .zeichen "{",
   .wort "dispatch", .num 0, .zeichen "}", .zeichen ";",
   .ende]
theorem s35_lex :
    lex "@spirv#kernel(n) { dispatch 0 };" = .ok st35 := by
  decide
theorem s35 : beqTopStmt (parseTopStmt st35)
    (.ok (.lcall "spirv" "kernel" 1)) = true := by
  decide
-- SYNTAX.md §7 (the library-call example). Rust: `LibraryCall`
-- in statement position -- same shape (one argument, region
-- skipped balanced).

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
    (the item probes live in `ElementTiefProben`). The `s31` (`advances`) shape has no
    statement-level counterpart in `parse.rs` either (it rides in
    the checker); the probe pins the SYNTAX.md production.
-/

#print axioms Gabbro.Grammatik.Parser.s01
