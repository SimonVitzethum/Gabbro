/-
  File:      Grammatik/Parser/AusdruckProben.lean
  Subject:   T3 PART 1: the `decide` probes for the expression parser.

  Split from `Parser/Ausdruck.lean` (which keeps the definitions):
  one kernel evaluation per theorem keeps every worker small -- a
  single file with all probes is killed before it finishes (exit
  137 with no error line). `sondeNN` checks the tree shape of one
  `beispiele/` line on its token list (`tokNN`, defined in
  `Parser/Ausdruck.lean`, pinned by `sondeNN_lex` in
  `Parser/Lexer.lean`). The decided round trip `print_parse` lives
  in `Parser/Ausdruck.lean`.
-/
import Grammatik.Parser.Ausdruck

namespace Gabbro.Grammatik.Parser


theorem sonde01 : beqTop
    (parseTop tok01)
    (.ok (.bin "<="
      (.bin "+" (.variable "e_phoff")
        (.bin "*" (.variable "e_phentsize") (.variable "e_phnum")))
      (.eingebaut "lenof" [.variable "Self"]))) = true := by
  decide
-- 03-format.gab:19. Rust: `Binaer(KleinerGleich, Binaer(Plus, …,
-- Binaer(Mal, …)), Eingebaut(Lenof(Ort(Self))))` -- same shape.
theorem sonde02 : beqTop
    (parseTop tok02)
    (.ok (.bin "||"
      (.bin "<" (.feld (.variable "m") "va")
        (.lit 18446603336221196288))
      (.un "!" (.feld (.variable "m") "nutzer")))) = true := by
  decide
-- 07-eintritt-und-boot.gab:35. Rust: `Binaer(Oder, Binaer(Kleiner,
-- Ort, Zahl), Unaer(Nicht, Ort))` -- same shape.
theorem sonde03 : beqTop
    (parseTop tok03)
    (.ok (.bin "&&"
      (.feld (.index (.feld (.variable "c") "slots") (.variable "s"))
        "benutzt")
      (.bin "=="
        (.feld (.index (.feld (.variable "c") "slots")
          (.variable "s")) "erstes_kind")
        (.ruf "None" [])))) = true := by
  decide
-- 01-tabelle.gab:83. Rust: `Binaer(Und, Ort, Binaer(Gleich, Ort,
-- Ruf(None)))` -- same shape (`None` is a call on both sides).
theorem sonde04 : beqTop
    (parseTop tok04)
    (.ok (.bin "<="
      (.alt (.feld (.index (.feld (.variable "k") "slots")
        (.variable "i")) "stand"))
      (.feld (.index (.feld (.variable "k") "slots")
        (.variable "i")) "stand"))) = true := by
  decide
-- 104-referenz.gab:35. Rust: `Binaer(KleinerGleich, Alt(Ort),
-- Ort)` -- same shape.
theorem sonde05 : beqTop
    (parseTop tok05)
    (.ok (.bin "==" (.ergebnis)
      (.feld (.index (.feld (.variable "k") "slots")
        (.variable "i")) "stand"))) = true := by
  decide
-- 104-referenz.gab:47. Rust: `Binaer(Gleich, Ergebnis, Ort)` --
-- same shape.
theorem sonde06 : beqTop
    (parseTop tok06)
    (.ok (.feld (.variable "u64") "max")) = true := by
  decide
-- 11-grammatikbefunde.gab:24. Rust: `Ort` with a `Feld` suffix
-- (the `ist_intty` arm, never `Grund`) -- same shape.
theorem sonde07 : beqTop
    (parseTop tok07)
    (.ok (.grund "Geraetelug" "ZuTief")) = true := by
  decide
-- 44-register-einmal-lesen.gab:103. Rust: `Grund{grund, fall}` --
-- same shape.
theorem sonde08 : beqTop
    (parseTop tok08)
    (.ok (.ruf "Verzeichnis::insert"
      [.variable "v", .variable "i"])) = true := by
  decide
-- 47-ops-wortmenge.gab:105. Rust: `Ruf` on a two-segment path --
-- same shape (spans and empty `marken` dropped).
theorem sonde09 : beqTop
    (parseTop tok09)
    (.ok (.ruf "lies" [.variable "k", .variable "i"])) = true := by
  decide
-- 104-referenz.gab:40. Rust: `Ruf` on a one-segment path -- same.
theorem sonde10 : beqTop
    (parseTop tok10)
    (.ok (.ruf "Some" [.variable "i"])) = true := by
  decide
-- 27-freiliste.gab:49. Rust: `Ruf` on path `Some` («B35»: a
-- constructor IS a call) -- same shape.
theorem sonde11 : beqTop
    (parseTop tok11)
    (.ok (.bin "=="
      (.feld (.index (.feld (.variable "Self") "slots")
        (.variable "s")) "elter")
      (.ruf "None" []))) = true := by
  decide
-- 01-tabelle.gab:70. Rust: `Binaer(Gleich, Ort(Self…), Ruf(None))`.
theorem sonde12 : beqTop
    (parseTop tok12)
    (.ok (.bin "&&"
      (.bin ">=" (.variable "x") (.gleit "0.0"))
      (.bin "<=" (.variable "x") (.gleit "1.0")))) = true := by
  decide
-- 26-gleitkomma.gab:57. Rust: `Gleitkomma{bits, dyadisch,
-- gerundet=false}` per literal; the Lean tree keeps the canonical
-- text -- the value comparison is booked in CUTS.
theorem sonde13 : beqTop
    (parseTop tok13)
    (.ok (.feld (.variable "d") "TIEFE")) = true := by
  decide
-- 44-register-einmal-lesen.gab:103. Rust: `Ort` -- same shape.
theorem sonde14 : beqTop
    (parseTop tok14)
    (.ok (.bin "<=" (.variable "TIEFE") (.lit 8))) = true := by
  decide
-- 44-register-einmal-lesen.gab:89. Same shape.
theorem sonde15 : beqTop
    (parseTop tok15)
    (.ok (.bin "&&"
      (.bin ">=" (.feld (.variable "m") "rahmen")
        (.variable "BOOT_RAHMEN_UNTEN"))
      (.bin "<" (.feld (.variable "m") "rahmen")
        (.variable "BOOT_RAHMEN_OBEN")))) = true := by
  decide
-- 07-eintritt-und-boot.gab:136. Same shape.
theorem sonde16 : beqTop
    (parseTop tok16)
    (.ok (.bin "&&" (.feld (.variable "it") "praesent")
      (.feld (.variable "it") "gross"))) = true := by
  decide
-- 07-eintritt-und-boot.gab:29. Same shape.
theorem sonde17 : beqTop
    (parseTop tok17)
    (.ok (.un "!" (.bin "&&"
      (.feld (.variable "m") "schreibbar")
      (.un "!" (.feld (.variable "m") "nx"))))) = true := by
  decide
-- 07-eintritt-und-boot.gab:32 (the inner expression of the
-- quantifier). Same shape.
theorem sonde18 : beqTop
    (parseTop tok18)
    (.ok (.bin "+" (.feld (.variable "c") "wert") (.lit 1))) = true := by
  decide
-- 05-nebenlaeufigkeit.gab:145 (right-hand side). Same shape.
theorem sonde19 : beqTop
    (parseTop tok19)
    (.ok (.bin "+" (.variable "v") (.lit 1))) = true := by
  decide
-- 05-nebenlaeufigkeit.gab:111. Same shape.
theorem sonde20 : beqTop
    (parseTop tok20)
    (.ok (.bin "+" (.variable "z") (.lit 1))) = true := by
  decide
-- 08-bereiche.gab:50. Same shape.
theorem sonde21 : beqTop
    (parseTop tok21)
    (.ok (.bin "+%" (.variable "a")
      (.bin "*%" (.variable "b") (.variable "c")))) = true := by
  decide
-- SYNTAX.md section 4, PLAN-BITS section 4: `*%` rides at `mulexpr`,
-- `+%` at `addexpr`. Rust: `Binaer(PlusWrap, a, Binaer(MalWrap, b,
-- c))` -- same shape.
theorem sonde22 : beqTop
    (parseTop tok22)
    (.ok (.bin "+|" (.variable "x") (.variable "y"))) = true := by
  decide
-- SYNTAX.md section 4: `+|` saturates at `addexpr`. Rust:
-- `Binaer(PlusSat, x, y)` -- same shape.

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * The tree shapes below are checked by kernel `Bool` evaluation
    (`beqTop ... = true`), not by a soundness theorem for `beqSExpr`
    -- see item 11 of the CUTS block in `Parser/Ausdruck.lean`, which
    also books every shape difference against `crates/gabbro-syntax`.
  * The decided round trip `print_parse` lives in
    `Parser/Ausdruck.lean` (CUTS item 13 there).
-/

#print axioms Gabbro.Grammatik.Parser.sonde01
#print axioms Gabbro.Grammatik.Parser.sonde22
