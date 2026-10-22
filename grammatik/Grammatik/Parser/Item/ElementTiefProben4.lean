/-
  File:      Grammatik/Parser/Item/ElementTiefProben4.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers, part 4 of 7 (tt51..tt55, ttVar).

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

def tt51 : List Token :=
  [.wort "impl", .wort "fn", .ident "freigeben", .zeichen "(",
   .ident "p", .zeichen ":", .wort "index", .wort "into",
   .ident "Buch", .zeichen ")", .wort "refines", .ident "ist_frei",
   .wort "requires", .ident "Held", .zeichen "(", .ident "BUCH",
   .zeichen ")", .zeichen ",", .ident "Buch", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "p", .zeichen "]",
   .zeichen ".", .ident "belegt", .wort "effects", .zeichen "{",
   .wort "reads", .ident "Buch", .zeichen ".", .wort "slots",
   .zeichen ",", .wort "writes", .ident "Buch", .zeichen ".",
   .wort "slots", .zeichen ",", .wort "locks", .ident "BUCH",
   .zeichen "}", .wort "costs", .zeichen "<=", .num 8,
   .wort "ops", .zeichen "{", .ident "Buch", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "p", .zeichen "]",
   .zeichen ".", .ident "belegt", .zeichen "=", .wort "false",
   .zeichen ";", .ident "Buch", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "p", .zeichen "]", .zeichen ".",
   .ident "wert", .zeichen "=", .num 0, .zeichen ";",
   .zeichen "}", .ende]
theorem t51_lex :
    lex "impl fn freigeben(p : index into Buch) refines ist_frei requires Held(BUCH), Buch.slots[p].belegt effects { reads Buch.slots, writes Buch.slots, locks BUCH } costs <= 8 ops { Buch.slots[p].belegt = false; Buch.slots[p].wert = 0; }" =
      .ok tt51 := by
  decide
theorem t51 : beqTopTief (parseTopTief tt51)
    (.ok [.fnT { art := "impl", name := "freigeben", params := [("p", .index false "Buch")], res := .none, fehler := .none, klauseln := [.refs ["ist_frei"], .needs (.call "Held" [.variable "BUCH"]), .needs (.field (.index (.field (.variable "Buch") "slots") (.variable "p")) "belegt"), .effs [.reads (.field (.variable "Buch") "slots"), .writes (.field (.variable "Buch") "slots"), .locks false (.variable "BUCH")], .cost (.lit 8)] } (.block [.set (.field (.index (.field (.variable "Buch") "slots") (.variable "p")) "belegt") "=" .fls, .set (.field (.index (.field (.variable "Buch") "slots") (.variable "p")) "wert") "=" (.lit 0)] .none)]) = true := by
  decide
-- beispiele/50-verfeinerung.gab (the `freigeben` refinement).
-- Rust: `Funktion` with `refines`, two `requires` and three
-- effects -- same shape.
def tt52 : List Token :=
  [.wort "extern", .wort "fn", .ident "groesse_gemessen",
   .zeichen "(", .zeichen ")", .zeichen "->", .ident "Stapelgroesse",
   .wort "or", .ident "MessFehler", .wort "ensures",
   .wort "result", .zeichen ">=", .num 1, .wort "effects",
   .zeichen "{", .wort "reads", .ident "stapel", .zeichen "}",
   .zeichen ";", .ende]
theorem t52_lex :
    lex "extern fn groesse_gemessen() -> Stapelgroesse or MessFehler ensures result >= 1 effects { reads stapel };" =
      .ok tt52 := by
  decide
theorem t52 : beqTopTief (parseTopTief tt52)
    (.ok [.protoT { art := "extern", name := "groesse_gemessen", params := [], res := (.some (.atom "Stapelgroesse")), fehler := (.some "MessFehler"), klauseln := [(.gives ((.bin ">=" .res (.lit 1)))), (.effs [(.reads (.variable "stapel"))])] }]) = true := by
  decide
-- beispiele/06-annahmen.gab:163-165. Rust: `Funktion` with the
-- `or` error channel -- same shape.
def tt53 : List Token :=
  [.wort "prim", .wort "fn", .ident "wechseln", .zeichen "(",
   .ident "von", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "rw", .zeichen ">",
   .ident "Kontext", .zeichen ",", .ident "nach", .zeichen ":",
   .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",",
   .wort "r", .zeichen ">", .ident "Kontext", .zeichen ")",
   .zeichen "->", .wort "never", .wort "effects", .zeichen "{",
   .wort "writes", .ident "maschinenzustand", .zeichen ",",
   .wort "writes", .ident "stapel", .zeichen ",", .wort "diverges",
   .zeichen "}", .zeichen ";", .ende]
theorem t53_lex :
    lex "prim fn wechseln(von : ptr<normal, rw> Kontext, nach : ptr<normal, r> Kontext) -> never effects { writes maschinenzustand, writes stapel, diverges };" =
      .ok tt53 := by
  decide
theorem t53 : beqTopTief (parseTopTief tt53)
    (.ok [.protoT { art := "prim", name := "wechseln", params := [(("von", (.ptr "normal" "rw" (.atom "Kontext")))), (("nach", (.ptr "normal" "r" (.atom "Kontext"))))], res := (.some (.atom "never")), fehler := .none, klauseln := [(.effs [(.writes (.variable "maschinenzustand")), (.writes (.variable "stapel")), .loops])] }]) = true := by
  decide
-- beispiele/07-eintritt-und-boot.gab:148-149. Rust: `Funktion`
-- over `never` with a diverging effect -- same shape.
def tt54 : List Token :=
  [.wort "impl", .wort "fn", .ident "f", .zeichen "(",
   .zeichen ")", .wort "maintains", .ident "invA", .zeichen ",",
   .ident "invB", .wort "by", .wort "induction", .wort "over",
   .wort "descendants", .wort "of", .ident "s",
   .wort "section", .text ".text", .wort "arch", .ident "x86_64",
   .wort "advances", .ident "roh", .zeichen "->", .ident "mmu",
   .wort "retires", .ident "t", .wort "from", .wort "boot",
   .wort "falsifier", .ident "p", .zeichen ";", .ende]
theorem t54_lex :
    lex "impl fn f() maintains invA, invB by induction over descendants of s section \".text\" arch x86_64 advances roh -> mmu retires t from boot falsifier p;" =
      .ok tt54 := by
  decide
theorem t54 : beqTopTief (parseTopTief tt54)
    (.ok [.protoT { art := "impl", name := "f", params := [], res := .none, fehler := .none, klauseln := [(.keeps ["invA", "invB"]), (.induc "induction over descendants of s "), (.part ".text"), (.arch "x86_64"), (.moves "roh" "mmu"), (.quits "t from boot falsifier p")] }]) = true := by
  decide
-- Synthetic carrier for the remaining clause forms; each cites
-- its corpus shape: `maintains` (beispiele/01-tabelle.gab:94),
-- `by induction over` (beispiele/01-tabelle.gab:77),
-- `section`/`arch` (beispiele/36-asm.gab:27),
-- `advances a -> b` (beispiele/02-geraet.gab:129),
-- `retires` (beispiele/07-eintritt-und-boot.gab:137).
def tt55 : List Token :=
  [.wort "table", .ident "Halde", .wort "count", .num 1048576,
   .wort "backed", .ident "hinterlegt", .zeichen "{",
   .wort "slot", .zeichen "{", .ident "b", .zeichen ":",
   .wort "bool", .zeichen ",", .zeichen "}", .zeichen "}",
   .ende]
theorem t55_lex :
    lex "table Halde count 1048576 backed hinterlegt { slot { b : bool, } }" =
      .ok tt55 := by
  decide
theorem t55 : beqTopTief (parseTopTief tt55)
    (.ok [.tableT "Halde" (.some (.lit 1048576)) (.some "hinterlegt") .none false [.tSlot [{ fname := "b", ftyp := (.atom "bool"), pos := .none, bezug := .none, wo := .none, reserviert := false, byOps := false }]]]) = true := by
  decide
-- beispiele/28-reserve-und-hinterlegung.gab:19 (the header;
-- memory kinds are values, not checked here). Rust: `Tabelle`
-- with a `backed` bound -- same shape.

-- The variadic marker `...` (C-free lane, C2, 2026-09-30): lexed `..` `.`, skipped by the
-- parameter list -- every declared parameter stays, in order. Rust: `params_variadisch`.
def ttVar : List Token :=
  [.wort "extern", .wort "fn", .ident "druck", .zeichen "(",
   .ident "fmt", .zeichen ":", .ident "Text", .zeichen ",",
   .zeichen "..", .zeichen ".", .zeichen ",",
   .ident "a", .zeichen ":", .wort "u64", .zeichen ")",
   .wort "costs", .zeichen "<=", .num 8, .wort "ops", .zeichen ";", .ende]
theorem tVar_lex :
    lex "extern fn druck(fmt : Text, ..., a : u64) costs <= 8 ops;" = .ok ttVar := by
  decide
theorem tVar : beqTopTief (parseTopTief ttVar)
    (.ok [.protoT
      { art := "extern", name := "druck",
        params := [("fmt", .atom "Text"), ("a", .atom "u64")], res := .none,
        fehler := .none, klauseln := [.cost (.lit 8)] }]) = true := by
  decide
end Gabbro.Grammatik.Parser
