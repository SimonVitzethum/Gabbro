/-
  File:      Grammatik/Parser/ElementTiefProben.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers.

  Like `Parser/AnweisungProben.lean`: one kernel evaluation per
  theorem keeps every worker small. Each probe is split in two: a
  lex pin (`tNN_lex`: the source line lexes to this token list)
  and a tree pin (`tNN`: the reader maps the list to this
  shape). A mistranscribed list fails its lex pin loudly. Tree
  shapes were compared against `ast.rs`/`parse.rs` by reading (no
  cargo in this lane); all differences are booked in the CUTS
  block of `Parser/ElementTief.lean`.
  Corpus sites stand at each probe; probes with no corpus line say
  so. The end-to-end probe is `tEnd` (beispiele/112, the smallest
  whole file with a table, a lock and contracted functions).
-/
import Grammatik.Parser.ElementTief

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

def tt01 : List Token :=
  [.wort "table", .ident "Zustand", .wort "count", .zahl 4,
   .zeichen "{", .wort "slot", .zeichen "{", .ident "bereit",
   .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}",
   .zeichen "}", .ende]
theorem t01_lex :
    lex "table Zustand count 4 { slot { bereit : u32, } }" =
      .ok tt01 := by
  decide
theorem t01 : beqTopTief (parseTopTief tt01)
    (.ok [.tabelleT "Zustand" (.some (.lit 4)) .none .none false
      [.tPlatz [{ fname := "bereit", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/112-register-traeger-bewacht.gab (the `Zustand`
-- table). Rust: `Tabelle` with one slot field -- same shape.
def tt02 : List Token :=
  [.wort "lock", .ident "Sperre", .wort "protects", .zeichen "{",
   .ident "Zustand", .zeichen "}", .wort "rank", .zahl 0,
   .zeichen ";", .ende]
theorem t02_lex :
    lex "lock Sperre protects { Zustand } rank 0;" = .ok tt02 := by
  decide
theorem t02 : beqTopTief (parseTopTief tt02)
    (.ok [.sperreT "Sperre" [.variable "Zustand"] (.lit 0)
      .none .none .none]) = true := by
  decide
-- beispiele/112 (the `Sperre` lock). Rust: `Lock` with one
-- carrier and a bare rank -- same shape.
def tt03 : List Token :=
  [.wort "device", .ident "Geraet", .zeichen "(", .ident "basis",
   .zeichen ":", .wort "u64", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "reg", .ident "ST",
   .zeichen ":", .wort "u32", .zeichen "@", .zahl 0,
   .wort "class", .wort "r", .wort "depends", .zeichen "{",
   .ident "Zustand", .zeichen "}", .zeichen "}", .ende]
theorem t03_lex :
    lex "device Geraet(basis : u64) at mmio { reg ST : u32 @0x00 class r depends { Zustand } }" =
      .ok tt03 := by
  decide
theorem t03 : beqTopTief (parseTopTief tt03)
    (.ok [.geraetT "Geraet" [("basis", .atom "u64")] "mmio"
      [.regTief { rname := "ST", rtyp := .atom "u32",
                   adresse := .lit 0, klasse := "r", phasen := [],
                   felder := [], voraus := .none,
                   vorausSonst := .none,
                   abhaengt := [["Zustand"]] }]]) = true := by
  decide
-- beispiele/112 (the `Geraet` device). Rust: `Device` with one
-- parameter and one `depends` register -- same shape.
def tt04 : List Token :=
  [.wort "impl", .wort "fn", .ident "lesen", .zeichen "(",
   .ident "d", .zeichen ":", .ident "Geraet", .zeichen ")",
   .zeichen "->", .wort "u32", .wort "requires", .ident "Held",
   .zeichen "(", .ident "Sperre", .zeichen ")", .wort "effects",
   .zeichen "{", .wort "reads", .ident "d", .zeichen "}",
   .wort "costs", .zeichen "<=", .zahl 8, .wort "ops",
   .zeichen "{", .wort "let", .ident "stand", .zeichen "=",
   .ident "d", .zeichen ".", .ident "ST", .zeichen ";",
   .wort "return", .ident "stand", .zeichen ";", .zeichen "}",
   .ende]
theorem t04_lex :
    lex "impl fn lesen(d : Geraet) -> u32 requires Held(Sperre) effects { reads d } costs <= 8 ops { let stand = d.ST; return stand; }" =
      .ok tt04 := by
  decide
theorem t04 : beqTopTief (parseTopTief tt04)
    (.ok [.funktionT
      { art := "impl", name := "lesen", params := [("d", .atom "Geraet")],
        ergebnis := .some (.atom "u32"), fehler := .none,
        klauseln := [.voraus (.ruf "Held" [.variable "Sperre"]),
          .wirkung [.liest (.variable "d")], .kosten (.lit 8)] }
      (.block [.lass false "stand" (.feld (.variable "d") "ST")]
        (.some (.ret (.some (.variable "stand")))))]) = true := by
  decide
-- beispiele/112 (the `lesen` reader). Rust: `Funktion` with one
-- `requires`, an `effects` and a `costs` clause -- same shape.
def tt05 : List Token :=
  [.wort "impl", .wort "fn", .ident "schreiben", .zeichen "(",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Zustand", .zeichen ",", .wort "w", .zeichen ":",
   .wort "u32", .zeichen ")", .zeichen "->", .wort "u32",
   .wort "requires", .ident "Held", .zeichen "(", .ident "Sperre",
   .zeichen ")", .wort "effects", .zeichen "{", .wort "writes",
   .ident "Zustand", .zeichen "}", .wort "costs", .zeichen "<=",
   .zahl 8, .wort "ops", .zeichen "{", .ident "Zustand",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "bereit", .zeichen "=",
   .wort "w", .zeichen ";", .wort "return", .zahl 0,
   .zeichen ";", .zeichen "}", .ende]
theorem t05_lex :
    lex "impl fn schreiben(i : index into Zustand, w : u32) -> u32 requires Held(Sperre) effects { writes Zustand } costs <= 8 ops { Zustand.slots[i].bereit = w; return 0; }" =
      .ok tt05 := by
  decide
theorem t05 : beqTopTief (parseTopTief tt05)
    (.ok [.funktionT
      { art := "impl", name := "schreiben",
        params := [("i", .index false "Zustand"), ("w", .atom "u32")],
        ergebnis := .some (.atom "u32"), fehler := .none,
        klauseln := [.voraus (.ruf "Held" [.variable "Sperre"]),
          .wirkung [.schreibt (.variable "Zustand")], .kosten (.lit 8)] }
      (.block [.zuweis
        (.feld (.index (.feld (.variable "Zustand") "slots")
          (.variable "i")) "bereit")
        "=" (.variable "w")]
        (.some (.ret (.some (.lit 0)))))]) = true := by
  decide
-- beispiele/112 (the `schreiben` writer). Rust: `Funktion` over
-- an `index into` parameter -- same shape.

end Gabbro.Grammatik.Parser
