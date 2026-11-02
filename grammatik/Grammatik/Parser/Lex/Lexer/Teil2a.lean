module

import all Init.Data.Repr
public import Grammatik.Parser.Lex.Lexer.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Decidable equality on lexing outcomes (core Lean 4.33 has none for
    `Except`): both sides agree constructor-wise and inside. -/
instance : DecidableEq (Except LexFehler (List Token)) :=
  fun
  | .ok x, .ok y =>
    match decEq x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun h' => absurd (by cases h'; rfl) h)
  | .error e1, .error e2 =>
    match decEq e1 e2 with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun h' => absurd (by cases h'; rfl) h)
  | .ok _, .error _ => isFalse (fun h => nomatch h)
  | .error _, .ok _ => isFalse (fun h => nomatch h)

/-- `lex` is a function: every source text has a lexing outcome
    (a token list or the first error). Trivially, by exhibiting it. -/
theorem lex_total (s : String) : ∃ r, lex s = r :=
  ⟨lex s, rfl⟩

set_option maxRecDepth 100000

/-- Every word of the closed vocabulary table lexes as its keyword
    token, checked by `decide` over the whole 248-word list. The
    raised recursion depth above is the price of the whole-table
    check (the default depth fails). -/
theorem lex_keywords :
    ∀ w ∈ wortschatz, lex w = .ok [Token.wort w, Token.ende] := by
  decide

/-- Joint witness for `lex_keywords`: the same shape over five
    concrete words -- an ordinary word, a clause word with `_`, a
    reserved expression head, a one-letter right, and a profile key. -/
theorem lex_keywords_zeuge :
    ∀ w ∈ ["module", "on_exceeded", "None", "r", "fp_contract"],
      lex w = .ok [Token.wort w, Token.ende] := by
  decide

/-- A non-table word lexes as an identifier, not a keyword. -/
theorem lex_ident_beispiel :
    lex "konto" = .ok [Token.ident "konto", Token.ende] := by
  decide

/-- Hex and binary literals with `_` separators take their value. -/
theorem lex_zahl_hex :
    lex "0xFFFF_FFFF" = .ok [Token.num 4294967295, Token.ende] := by
  decide

/-- Binary literal. -/
theorem lex_zahl_bin :
    lex "0b101" = .ok [Token.num 5, Token.ende] := by
  decide

/-- A float literal with an exponent. -/
theorem lex_gleit_beispiel :
    lex "1.5e-3" = .ok [Token.float "1.5e-3", Token.ende] := by
  decide

/-- Maximal munch: `1..5` is a range, never a float. -/
theorem lex_bereich :
    lex "1..5" = .ok [Token.num 1, Token.zeichen "..", Token.num 5,
      Token.ende] := by
  decide

/-- The new PLAN-BITS operators lex as single marks. -/
theorem lex_operatoren :
    lex "+% -% *% <<% +|" = .ok
      [Token.zeichen "+%", Token.zeichen "-%", Token.zeichen "*%",
       Token.zeichen "<<%", Token.zeichen "+|", Token.ende] := by
  decide

/-- `@` and `#` (the library-call separator of lane E1) are marks. -/
theorem lex_at_hash :
    lex "@ #" = .ok [Token.zeichen "@", Token.zeichen "#",
      Token.ende] := by
  decide

/-- A `//` comment runs to the end of the line and vanishes. -/
theorem lex_kommentar :
    lex "a // rest\nb" = .ok [Token.ident "a", Token.ident "b",
      Token.ende] := by
  decide

/-- The old `--` is no comment any more: it lexes as two minus marks. -/
theorem lex_alter_strich_kein_kommentar :
    lex "a -- b" = .ok [Token.ident "a", Token.zeichen "-",
      Token.zeichen "-", Token.ident "b", Token.ende] := by
  decide

/-- A block comment vanishes and may span lines. -/
theorem lex_block :
    lex "a /* x\ny */ b" = .ok [Token.ident "a", Token.ident "b",
      Token.ende] := by
  decide

/-- Block comments NEST: the first `*/` closes only the inner one. -/
theorem lex_block_verschachtelt :
    lex "a /* x /* y */ still comment */ b" = .ok [Token.ident "a",
      Token.ident "b", Token.ende] := by
  decide

/-- Witness of the depth counter at depth three: three openers need three
    closers, and what follows the last one is code again. -/
theorem lex_block_tief :
    lex "/* /* /* */ */ */ c" = .ok [Token.ident "c", Token.ende] := by
  decide

/-- `/**/` is an empty ordinary block comment. -/
theorem lex_block_leer :
    lex "a /**/ b" = .ok [Token.ident "a", Token.ident "b", Token.ende] := by
  decide

/-- An unterminated block comment is a lexical error ... -/
theorem lex_block_offen :
    lex "a /* never closed" = .error .offenerKommentar := by
  decide

/-- ... and so is one whose nesting is not closed all the way. -/
theorem lex_block_offen_verschachtelt :
    lex "a /* x /* y */ z" = .error .offenerKommentar := by
  decide

/-- A stray `*/` is no comment end: it lexes as `*` and `/`. -/
theorem lex_block_streuende_ende :
    lex "a */ b" = .ok [Token.ident "a", Token.zeichen "*",
      Token.zeichen "/", Token.ident "b", Token.ende] := by
  decide

/-- Comment markers inside a string literal are text, not comments. -/
theorem lex_marker_im_text :
    lex "\"a // b /* c\" y" = .ok [Token.text "a // b /* c",
      Token.ident "y", Token.ende] := by
  decide

/-- A string opener inside a comment is nothing either. -/
theorem lex_text_im_kommentar :
    lex "/* \" */ a // \"\nb" = .ok [Token.ident "a", Token.ident "b",
      Token.ende] := by
  decide

/-- `///` is a doc comment: `lex` drops it, `lexDoku` keeps it as trivia
    with its text after the three slashes. -/
theorem lex_doku :
    lex "/// the item\nfn" = .ok [Token.wort "fn", Token.ende] := by
  decide

theorem lexDoku_doku :
    lexDoku "/// the item\nfn" = .ok [Token.doku " the item",
      Token.wort "fn", Token.ende] := by
  decide

/-- `////` and more slashes are an ordinary comment, as in Rust. -/
theorem lexDoku_vier_striche :
    lexDoku "//// not doc\n///// nor this\nfn" =
      .ok [Token.wort "fn", Token.ende] := by
  decide

/-- Plain `//` is no doc comment. -/
theorem lexDoku_zwei_striche :
    lexDoku "// plain\nfn" = .ok [Token.wort "fn", Token.ende] := by
  decide

/-- A `///` inside a block comment is block text. -/
theorem lexDoku_doku_im_block :
    lexDoku "/* /// x */ fn" = .ok [Token.wort "fn", Token.ende] := by
  decide

/-- A doc comment as the last line, without a newline. -/
theorem lexDoku_doku_am_ende :
    lexDoku "fn ///" = .ok [Token.wort "fn", Token.doku "", Token.ende] := by
  decide

/-- Doc comments change no program: on these sources `lex` is `lexDoku`
    without its `doku` tokens. -/
theorem lex_ohne_doku_beispiel :
    lexDoku "/// a\nfn f /* /// b */ () /// c" =
      .ok [Token.doku " a", Token.wort "fn", Token.ident "f",
        Token.zeichen "(", Token.zeichen ")", Token.doku " c", Token.ende] ∧
    lex "/// a\nfn f /* /// b */ () /// c" =
      .ok [Token.wort "fn", Token.ident "f", Token.zeichen "(",
        Token.zeichen ")", Token.ende] := by
  decide


end Gabbro.Grammatik.Parser
