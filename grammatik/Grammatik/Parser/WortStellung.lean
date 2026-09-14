/-
  File:      Grammatik/Parser/WortStellung.lean
  Subject:   PLAN-EINFACHHEIT.md lever 5 (lane 188): the contextual/reserved
             split of the closed vocabulary, on the Lean side.

  The Rust reader decides positionally: a word of the table is a keyword
  only where the grammar expects one (`parse.rs` `erwarte_ident` takes
  every word except the seventeen below; `erwarte_feldname` takes all of
  them). The Lean lexer already emits `wort` unconditionally and lets the
  parser decide (`Lexer.lean` CUTS), but until this file nothing pinned
  WHICH words stay reserved -- the refusals were scattered (`keinPlatzTafel`
  holds twelve, the five expression heads live in `parsePrimary` arms, the
  seven emitted-C words nowhere). This file is that pin: the seventeen in
  `kw.rs` `res` column order, with the theorems that tie each existing
  refusal to it.
-/
import Grammatik.Parser.Ausdruck

namespace Gabbro.Grammatik.Parser

/-- The seventeen reserved words: the `res` column of `kw.rs`, in
    `tests/wortschatz.rs` order (expression heads, then emitted-C words).
    Character lists, as in `keinPlatzTafel`: kernel-cheap, unlike
    `String ==` through byte arrays. -/
def reserviertTafel : List (List Char) :=
  [['s','i','z','e','o','f'], ['l','e','n','o','f'], ['a','l','i','g','n','e','d'],
   ['f','o','r','a','l','l'], ['e','x','i','s','t','s'],
   ['t','r','u','e'], ['f','a','l','s','e'],
   ['S','e','l','f'], ['S','o','m','e'], ['N','o','n','e'],
   ['c','o','n','s','t'], ['s','t','a','t','i','c'], ['e','x','t','e','r','n'],
   ['i','f'], ['e','l','s','e'], ['r','e','t','u','r','n'], ['b','o','o','l']]

/-- Is this spelling a reserved word (bucket-free: seventeen short
    comparisons, as in `istSchluessel`)? -/
def istReserviert (s : String) : Bool :=
  reserviertTafel.contains s.toList

/-- The same seventeen as plain words, for the vocabulary link below
    (`wortschatz` is a `List String`). -/
def reserviertWoerter : List String :=
  ["sizeof", "lenof", "aligned", "forall", "exists",
   "true", "false", "Self", "Some", "None",
   "const", "static", "extern", "if", "else", "return", "bool"]

/-- The table holds seventeen entries. -/
theorem reserviert_siebzehn : reserviertTafel.length = 17 := by decide

/-- Spelling and table agree word by word. -/
theorem reserviertWortlaut : reserviertWoerter.map String.toList = reserviertTafel := by
  decide

/-- The twelve place-refusals of `Ausdruck.keinPlatzTafel` are all
    reserved words: the existing refusal is tied to this table, so a
    word leaving the table breaks the build here instead of silently
    widening a name position. -/
theorem keinPlatz_in_reserviert :
    ∀ w ∈ keinPlatzTafel, reserviertTafel.contains w = true := by
  decide

/-- The five expression heads that never reach `keinPlatzTafel`
    (`true` `false` `Self` `Some` `None`: `parsePrimary` takes them
    before the name path in `Ausdruck.lean`) are reserved too. -/
theorem ausdruckskoepfe_in_reserviert :
    ∀ w ∈ [['t','r','u','e'], ['f','a','l','s','e'],
            ['S','e','l','f'], ['S','o','m','e'], ['N','o','n','e']],
      reserviertTafel.contains w = true := by
  decide

/-- The seven emitted-C words (`uint32_t <w> = 1; return <w>;` through
    `cc -std=c11 -Wall -Wextra -Werror`, measured 2026-09-05,
    `messung/WORTSTELLUNG.md`) are reserved too. -/
theorem cNamen_in_reserviert :
    ∀ w ∈ [['c','o','n','s','t'], ['s','t','a','t','i','c'], ['e','x','t','e','r','n'],
            ['i','f'], ['e','l','s','e'], ['r','e','t','u','r','n'], ['b','o','o','l']],
      reserviertTafel.contains w = true := by
  decide

set_option maxRecDepth 100000

/-- The closed vocabulary counts 243 words
    (`instrumente/zaehle-wortschatz.py`; the lane brief says 242,
    measured 243 -- the brief predates `depends`, lane 157). -/
theorem wortschatz_dreihundertdreiundvierzig : wortschatz.length = 243 := by
  decide

/-- Every reserved word stands in the closed vocabulary: the split
    stays inside the table, so no reservation can drift onto a word
    the lexer never emits. Seventeen membership checks -- the raised
    recursion depth above is the price of the whole-table `contains`. -/
theorem reserviert_in_wortschatz :
    ∀ w ∈ reserviertWoerter, wortschatz.contains w = true := by
  decide

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * The theorems pin the SET, not the refusal: `parse.rs`
    `erwarte_ident` refuses the seventeen at every `ident` position,
    while Lean `nimmName`/`nameText` still take any `wort` token as a
    name. A `let true = 1;` parses here and is refused there. The
    direction is the safe one for certificates (Lean accepts a
    superset with the same meaning on the intersection -- keyword
    arms stand above the name path on both sides), but the positional
    refusal itself has no Lean counterpart yet.
  * Field names need none: `erwarte_feldname` takes all 243 words,
    and Lean path segments do the same through `nameText` -- the two
    agree where both are permissive.
  * `istReserviert` decides by spelling only. Whether a reserved
    spelling at some position still parses as its keyword form is a
    parser question (`istKopfForm`, `keinPlatzTafel`, the
    `parsePrimary` arms), answered where it is asked, not here.
-/

#print axioms Gabbro.Grammatik.Parser.reserviert_siebzehn
#print axioms Gabbro.Grammatik.Parser.keinPlatz_in_reserviert
#print axioms Gabbro.Grammatik.Parser.reserviert_in_wortschatz
