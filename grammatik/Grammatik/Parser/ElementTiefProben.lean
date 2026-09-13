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

end Gabbro.Grammatik.Parser
