module
public import Grammatik.Parser.Lex.Lexer.Teil2a

import all Init.Data.Repr
public import Grammatik.Parser.Lex.Lexer.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000
/-- The block closer step: `*/` at depth `d + 1` leaves depth `d`. -/
theorem ueberBlock_schliesst (d : Nat) (cs : List Char) :
    ueberBlock (d + 1) ('*' :: '/' :: cs) = ueberBlock d cs := by rfl

/-- The block opener step: `/*` at depth `d + 1` goes to depth `d + 2`. -/
theorem ueberBlock_oeffnet (d : Nat) (cs : List Char) :
    ueberBlock (d + 1) ('/' :: '*' :: cs) = ueberBlock (d + 2) cs := by rfl

/-- Depth zero consumes nothing: the comment is over. -/
theorem ueberBlock_null (cs : List Char) : ueberBlock 0 cs = some cs := by
  cases cs <;> rfl

/-- WITNESS of the nesting rule on a nested comment: `ueberBlock` reaches the
    text after the OUTER closer. -/
theorem ueberBlock_verschachtelt :
    ueberBlock 1 " a /* b */ c */ d".toList = some " d".toList := by
  decide

/-- PLANTED DEFECT: the flat variant (no depth counter) stops at the inner
    closer, so it differs from `ueberBlock` on the same text -- the nesting
    witness above is not vacuous. -/
theorem ueberBlock_verschachtelt_flach :
    ueberBlockFlach " a /* b */ c */ d".toList = some " c */ d".toList ∧
    ueberBlockFlach " a /* b */ c */ d".toList ≠
      ueberBlock 1 " a /* b */ c */ d".toList := by
  decide

/-- A string literal carries its content without the quotes. -/
theorem lex_text_beispiel :
    lex "\"hi\"" = .ok [Token.text "hi", Token.ende] := by
  decide

/-- An unterminated string is the first error. -/
theorem lex_text_offen :
    lex "\"offen" = .error .offeneZeichenkette := by
  decide

-- Lexer half of the agreement probes with `crates/gabbro-syntax`
-- (`parse.rs`): each `sondeNN_lex` pins the token list of one
-- `beispiele/` source line (cited at the parse half in
-- `Parser/Ausdruck.lean`, which checks the tree shape on these
-- token lists). Token lists live here because they are lexer
-- output; the parser file never re-lexes them.
def tok01 : List Token :=
  [.ident "e_phoff", .zeichen "+", .ident "e_phentsize",
   .zeichen "*", .ident "e_phnum", .zeichen "<=", .wort "lenof",
   .zeichen "(", .wort "Self", .zeichen ")", .ende]
theorem sonde01_lex :
    lex "e_phoff + e_phentsize * e_phnum <= lenof(Self)" =
      .ok tok01 := by
  decide
def tok02 : List Token :=
  [.ident "m", .zeichen ".", .ident "va", .zeichen "<",
   .num 18446603336221196288, .zeichen "||", .zeichen "!",
   .ident "m", .zeichen ".", .ident "nutzer", .ende]
theorem sonde02_lex :
    lex "m.va < 0xFFFF_8000_0000_0000 || !m.nutzer" = .ok tok02 := by
  decide
def tok03 : List Token :=
  [.ident "c", .zeichen ".", .wort "slots", .zeichen "[",
   .ident "s", .zeichen "]", .zeichen ".", .ident "benutzt",
   .zeichen "&&", .ident "c", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "s", .zeichen "]", .zeichen ".",
   .ident "erstes_kind", .zeichen "==", .wort "None", .ende]
theorem sonde03_lex :
    lex "c.slots[s].benutzt && c.slots[s].erstes_kind == None" =
      .ok tok03 := by
  decide
def tok04 : List Token :=
  [.wort "old", .zeichen "(", .ident "k", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "stand", .zeichen ")", .zeichen "<=",
   .ident "k", .zeichen ".", .wort "slots", .zeichen "[",
   .ident "i", .zeichen "]", .zeichen ".", .ident "stand", .ende]
theorem sonde04_lex :
    lex "old(k.slots[i].stand) <= k.slots[i].stand" = .ok tok04 := by
  decide
def tok05 : List Token :=
  [.wort "result", .zeichen "==", .ident "k", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "stand", .ende]
theorem sonde05_lex :
    lex "result == k.slots[i].stand" = .ok tok05 := by
  decide
def tok06 : List Token :=
  [.wort "u64", .zeichen "::", .wort "max", .ende]
theorem sonde06_lex : lex "u64::max" = .ok tok06 := by decide
def tok07 : List Token :=
  [.ident "Geraetelug", .zeichen "::", .ident "ZuTief", .ende]
theorem sonde07_lex :
    lex "Geraetelug::ZuTief" = .ok tok07 := by
  decide
def tok08 : List Token :=
  [.ident "Verzeichnis", .zeichen "::", .wort "insert",
   .zeichen "(", .ident "v", .zeichen ",", .ident "i",
   .zeichen ")", .ende]
theorem sonde08_lex :
    lex "Verzeichnis::insert(v, i)" = .ok tok08 := by
  decide
def tok09 : List Token :=
  [.ident "lies", .zeichen "(", .ident "k", .zeichen ",",
   .ident "i", .zeichen ")", .ende]
theorem sonde09_lex : lex "lies(k, i)" = .ok tok09 := by decide
def tok10 : List Token :=
  [.wort "Some", .zeichen "(", .ident "i", .zeichen ")", .ende]
theorem sonde10_lex : lex "Some(i)" = .ok tok10 := by decide
def tok11 : List Token :=
  [.wort "Self", .zeichen ".", .wort "slots", .zeichen "[",
   .ident "s", .zeichen "]", .zeichen ".", .ident "elter",
   .zeichen "==", .wort "None", .ende]
theorem sonde11_lex :
    lex "Self.slots[s].elter == None" = .ok tok11 := by
  decide
def tok12 : List Token :=
  [.wort "x", .zeichen ">=", .float "0.0", .zeichen "&&",
   .wort "x", .zeichen "<=", .float "1.0", .ende]
theorem sonde12_lex :
    lex "x >= 0.0 && x <= 1.0" = .ok tok12 := by
  decide
def tok13 : List Token :=
  [.ident "d", .zeichen ".", .ident "TIEFE", .ende]
theorem sonde13_lex : lex "d.TIEFE" = .ok tok13 := by decide
def tok14 : List Token :=
  [.ident "TIEFE", .zeichen "<=", .num 8, .ende]
theorem sonde14_lex : lex "TIEFE <= 8" = .ok tok14 := by decide
def tok15 : List Token :=
  [.ident "m", .zeichen ".", .ident "rahmen", .zeichen ">=",
   .ident "BOOT_RAHMEN_UNTEN", .zeichen "&&", .ident "m",
   .zeichen ".", .ident "rahmen", .zeichen "<",
   .ident "BOOT_RAHMEN_OBEN", .ende]
theorem sonde15_lex :
    lex "m.rahmen >= BOOT_RAHMEN_UNTEN && m.rahmen < BOOT_RAHMEN_OBEN" =
      .ok tok15 := by
  decide
def tok16 : List Token :=
  [.ident "it", .zeichen ".", .ident "praesent", .zeichen "&&",
   .ident "it", .zeichen ".", .ident "gross", .ende]
theorem sonde16_lex :
    lex "it.praesent && it.gross" = .ok tok16 := by
  decide
def tok17 : List Token :=
  [.zeichen "!", .zeichen "(", .ident "m", .zeichen ".",
   .ident "schreibbar", .zeichen "&&", .zeichen "!", .ident "m",
   .zeichen ".", .ident "nx", .zeichen ")", .ende]
theorem sonde17_lex :
    lex "!(m.schreibbar && !m.nx)" = .ok tok17 := by
  decide
def tok18 : List Token :=
  [.ident "c", .zeichen ".", .ident "wert", .zeichen "+",
   .num 1, .ende]
theorem sonde18_lex : lex "c.wert + 1" = .ok tok18 := by decide
def tok19 : List Token :=
  [.ident "v", .zeichen "+", .num 1, .ende]
theorem sonde19_lex : lex "v + 1" = .ok tok19 := by decide
def tok20 : List Token :=
  [.ident "z", .zeichen "+", .num 1, .ende]
theorem sonde20_lex : lex "z + 1" = .ok tok20 := by decide
def tok21 : List Token :=
  [.ident "a", .zeichen "+%", .ident "b", .zeichen "*%",
   .ident "c", .ende]
theorem sonde21_lex : lex "a +% b *% c" = .ok tok21 := by decide
def tok22 : List Token :=
  [.wort "x", .zeichen "+|", .ident "y", .ende]
theorem sonde22_lex : lex "x +| y" = .ok tok22 := by decide

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * `lex` returns the FIRST error where `lex.rs` accumulates refusals
    and still emits a partial stream. A certificate starts from source
    that lexes cleanly, so the partial stream has no reader; the
    refusal CODES (`L001`-`L008`) are not modelled either.
  * Integer values are unbounded `Nat`: the `u128` overflow refusal
    (`L005`) has no counterpart -- a certificate value past `2^128`
    would need its own refusal at the typing layer.
  * `lex` does not record spans: every Rust token carries one, every
    Lean token none. Diagnostics cannot point into the source from
    here; positions must be re-attached by the outer layer.
  * The float token carries the canonical text, not the `f64` bits or
    the dyadic flag `lex.rs` computes -- whether the literal is exact
    in its target type is an M1 question, not a lexing one.
  * The keyword/identifier split is positional in the grammar
    (`WORTSTELLUNG.md`): at an `ident` position every table word is a
    name. `lex` emits `wort` unconditionally; the parser decides.
  * `lexL` is not a second lexer and proves nothing new: it is `scan`
    with the fuel `lex` would have passed, and `lex_ofList` is the
    only bridge to it. A source text pinned as characters therefore
    means exactly what a `String` literal meant -- the saving is in
    WHO converts, not in WHAT is claimed (O13, and the measured table
    in `messung/muse/OPUS-BERICHT-O13.md`).
  * `schluesselTafelC` stores the table as character lists in
    first-character buckets, and `strEq` compares through
    character lists: kernel evaluation of `String ==` runs through
    byte arrays and dominates `decide` time, while `Char ==` runs
    on numbers. `lex_keywords` re-checks the bucketing word by
    word, so the optimisation cannot silently misfile a word.
-/

#print axioms Gabbro.Grammatik.Parser.lex_total
#print axioms Gabbro.Grammatik.Parser.lex_ofList
#print axioms Gabbro.Grammatik.Parser.lex_keywords
#print axioms Gabbro.Grammatik.Parser.lex_keywords_zeuge
#print axioms Gabbro.Grammatik.Parser.sonde01_lex
