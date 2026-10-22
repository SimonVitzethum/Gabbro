/-
  File:      Grammatik/Parser/Item/ElementTiefProben5.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers, part 5 of 7 (the tree pin of ttEnd).

  The probes are split over seven modules only so that each one
  builds under the 4 GiB memory ceiling; part 6 carries the CUTS
  block for all seven.

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
import Grammatik.Parser.Item.ElementTief

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

def ttEnd : List Token :=
  [.wort "module", .ident "beispiel112", .zeichen "{",
  .wort "table", .ident "Zustand", .wort "count", .num 4,
   .zeichen "{", .wort "slot", .zeichen "{", .ident "bereit",
   .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}",
   .zeichen "}",
  .wort "lock", .ident "Sperre", .wort "protects", .zeichen "{",
   .ident "Zustand", .zeichen "}", .wort "rank", .num 0,
   .zeichen ";",
  .wort "device", .ident "Geraet", .zeichen "(", .ident "basis",
   .zeichen ":", .wort "u64", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "reg", .ident "ST",
   .zeichen ":", .wort "u32", .zeichen "@", .num 0,
   .wort "class", .wort "r", .wort "depends", .zeichen "{",
   .ident "Zustand", .zeichen "}", .zeichen "}",
  .wort "impl", .wort "fn", .ident "lesen", .zeichen "(",
   .ident "d", .zeichen ":", .ident "Geraet", .zeichen ")",
   .zeichen "->", .wort "u32", .wort "requires", .ident "Held",
   .zeichen "(", .ident "Sperre", .zeichen ")", .wort "effects",
   .zeichen "{", .wort "reads", .ident "d", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops",
   .zeichen "{", .wort "let", .ident "stand", .zeichen "=",
   .ident "d", .zeichen ".", .ident "ST", .zeichen ";",
   .wort "return", .ident "stand", .zeichen ";", .zeichen "}",
  .wort "impl", .wort "fn", .ident "schreiben", .zeichen "(",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Zustand", .zeichen ",", .wort "w", .zeichen ":",
   .wort "u32", .zeichen ")", .zeichen "->", .wort "u32",
   .wort "requires", .ident "Held", .zeichen "(", .ident "Sperre",
   .zeichen ")", .wort "effects", .zeichen "{", .wort "writes",
   .ident "Zustand", .zeichen "}", .wort "costs", .zeichen "<=",
   .num 8, .wort "ops", .zeichen "{", .ident "Zustand",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "bereit", .zeichen "=",
   .wort "w", .zeichen ";", .wort "return", .num 0,
   .zeichen ";", .zeichen "}",
  .zeichen "}", .ende]
theorem tEnd : beqTopTief (parseTopTief ttEnd)
    (.ok [.modT "beispiel112" [
.tableT "Zustand" (.some (.lit 4)) .none .none false
      [.tSlot [{ fname := "bereit", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
.lockT "Sperre" [.variable "Zustand"] (.lit 0)
      .none .none .none .none,
.devT "Geraet" [("basis", .atom "u64")] "mmio"
      [.reg { name := "ST", rtyp := .atom "u32",
                   addr := .lit 0, klasse := "r", stage := [],
                   felder := [], voraus := .none,
                   elseF := .none,
                   abhaengt := [["Zustand"]] }],
.fnT
      { art := "impl", name := "lesen", params := [("d", .atom "Geraet")],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "Sperre"]),
          .effs [.reads (.variable "d")], .cost (.lit 8)] }
      (.block [.bind false "stand" .none (.field (.variable "d") "ST")]
        (.some (.ret (.some (.variable "stand"))))),
.fnT
      { art := "impl", name := "schreiben",
        params := [("i", .index false "Zustand"), ("w", .atom "u32")],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.needs (.call "Held" [.variable "Sperre"]),
          .effs [.writes (.variable "Zustand")], .cost (.lit 8)] }
      (.block [.set
        (.field (.index (.field (.variable "Zustand") "slots")
          (.variable "i")) "bereit")
        "=" (.variable "w")]
        (.some (.ret (.some (.lit 0)))))]]) = true := by
  decide
-- beispiele/112-register-traeger-bewacht.gab, whole file (38 lines): the smallest whole corpus file with a table, a lock and contracted functions. Module, table, lock, device and both function bodies parse end to end with nothing skipped.
end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.tEnd
