/-
  File:      Grammatik/Parser/LexerVertrauen.lean
  Subject:   Lane 182 (source trust: homoglyphs and bidi) on the Lean side.

  Gabbro's promise is that a HUMAN reads a body ("written by hand and read by a
  person"); a program that reads differently to a human than to the parser breaks
  exactly that premise (Trojan Source, CVE-2021-42574). `Lexer.lean` is untouched:
  this file is the gate in front of it -- `lexVertrauen` refuses first (`P060`
  to `P063`, the codes `lex.rs::quelltext_pruefe` issues) and lexes second.

  The checks mirror the Rust gate class for class: bidi control characters
  anywhere including comments and strings (`P060`), identifier characters outside
  the allowed set (`P061`), two scripts in one identifier (`P062`), invisible
  characters (`P063`, with the BOM-at-offset-0 exception). What cannot be seen
  is refused, never interpreted -- on both sides.
-/

module
public import Grammatik.Parser.Lex.Lexer
@[expose] public section


namespace Gabbro.Grammatik.Parser

/-- The gate's own refusals: the four source-trust classes, plus whatever the
    lexer itself refuses behind the gate. -/
inductive VertrauenFehler
  | bidi : VertrauenFehler
  | fremd : VertrauenFehler
  | gemischt : VertrauenFehler
  | unsichtbar : VertrauenFehler
  | lex : LexFehler → VertrauenFehler
  deriving DecidableEq, Repr

/-- The diagnostic code of a gate refusal (the Rust codes `P060`-`P063`;
    a lexer refusal behind the gate keeps its own channel). -/
def vertrauenCode : VertrauenFehler → String
  | .bidi => "P060"
  | .fremd => "P061"
  | .gemischt => "P062"
  | .unsichtbar => "P063"
  | .lex _ => "lex"

/-- A bidi control/format character (`lex.rs::ist_bidi`): it reorders the line
    for a human while the parser reads bytes in order. -/
def istBidi (c : Char) : Bool :=
  let n := c.toNat
  (0x202A ≤ n && n ≤ 0x202E) || (0x2066 ≤ n && n ≤ 0x2069) ||
  n == 0x200E || n == 0x200F || n == 0x061C

/-- An invisible character (`lex.rs::ist_unsichtbar`): zero-width space and
    joiners, and the byte-order mark. The BOM rule lives in `ohneBom`,
    not here: a mark anywhere past offset 0 is a hiding place. -/
def istUnsichtbar (c : Char) : Bool :=
  let n := c.toNat
  (0x200B ≤ n && n ≤ 0x200D) || n == 0xFEFF

/-- Drop a leading BOM: an editor's signature, not source text. Only offset 0;
    every later mark still falls under `istUnsichtbar`. -/
def ohneBom : List Char → List Char
  | c :: cs => if c.toNat == 0xFEFF then cs else c :: cs
  | [] => []

/-- The script family of a code point (`lex.rs::schrift`): an approximation of
    UTS#39, not the table. `0` is neutral (digits, `_`, ASCII punctuation);
    every other value is one family. Only the COUNT matters downstream:
    one family is a foreign letter, two are a homoglyph. -/
def schrift (n : Nat) : Nat :=
  if (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) then 1
  else if (0xC0 ≤ n && n ≤ 0xFF) || (0x100 ≤ n && n ≤ 0x24F) ||
      (0x1E00 ≤ n && n ≤ 0x1EFF) then 1
  else if (0x370 ≤ n && n ≤ 0x3FF) || (0x1F00 ≤ n && n ≤ 0x1FFF) then 2
  else if (0x400 ≤ n && n ≤ 0x4FF) || (0x500 ≤ n && n ≤ 0x52F) ||
      (0x2DE0 ≤ n && n ≤ 0x2DFF) || (0xA640 ≤ n && n ≤ 0xA69F) then 3
  else if 0x530 ≤ n && n ≤ 0x58F then 4
  else if 0x590 ≤ n && n ≤ 0x5FF then 5
  else if (0x600 ≤ n && n ≤ 0x6FF) || (0x750 ≤ n && n ≤ 0x77F) then 6
  else if 0x900 ≤ n && n ≤ 0x97F then 7
  else if 0xE00 ≤ n && n ≤ 0xE7F then 8
  else if 0x10A0 ≤ n && n ≤ 0x10FF then 9
  else if (0x1100 ≤ n && n ≤ 0x11FF) || (0xAC00 ≤ n && n ≤ 0xD7AF) then 10
  else if (0x3040 ≤ n && n ≤ 0x309F) || (0x30A0 ≤ n && n ≤ 0x30FF) then 11
  else if (0x3400 ≤ n && n ≤ 0x4DBF) || (0x4E00 ≤ n && n ≤ 0x9FFF) then 12
  else if n < 128 then 0
  else 13

/-- A word character past the ASCII table: one of the twelve script families
    (`lex.rs` starts and continues runs on `is_alphabetic`/`is_alphanumeric`;
    the families are that predicate's shape here -- the umlauts fall in Latin).
    Punctuation, format characters and exotic numbers split runs on both
    sides; exotic LETTERS past the twelve families are the one documented
    corner where they do not (see CUTS). -/
def istWortZeichen (c : Char) : Bool :=
  let s := schrift c.toNat
  1 ≤ s && s ≤ 12

/-- A run starts at `_` or a word character -- the run rule of
    `lex.rs::quelltext_pruefe`, except in the two named corners below:
    exotic letters past the twelve families start a run there and not here
    (corner (a)), family-range non-ASCII digits start one here and not there
    (corner (b)). Both sides refuse in both corners regardless
    (`L006`/`.unbekannt` catch every foreign character in code position). -/
def istLaufStart (c : Char) : Bool :=
  c == '_' || istWortZeichen c

/-- Continuation adds the ASCII digits -- character for character the rule of
    `lex.rs::ist_laufzeichen`, over the same `schrift` table. An exotic number
    (`²`) or punctuation (`·`) breaks a run on both sides; whatever they cut
    around still falls under `L006`/`.unbekannt`. -/
def istLaufWeiter (c : Char) : Bool :=
  c == '_' || istZiffer c || istWortZeichen c

/-- Take a run tail (the head is already consumed). -/
def nimmLauf : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if istLaufWeiter c then let (h, t) := nimmLauf cs; (c :: h, t)
    else ([], c :: cs)

/-- Phase 1: bidi and invisible characters over the RAW characters --
    comments and strings included, because the reordering happens
    in the editor, not in the token. -/
def pruefeZeichen : List Char → Except VertrauenFehler Unit
  | [] => .ok ()
  | c :: cs =>
    if istBidi c then .error .bidi
    else if istUnsichtbar c then .error .unsichtbar
    else pruefeZeichen cs

/-- Skip a string body starting after the opening quote (mirrors `nimmText`:
    to the closing quote; a newline or the end stops the skip). -/
def ueberText : List Char → List Char
  | [] => []
  | '\n' :: cs => '\n' :: cs
  | '"' :: cs => cs
  | _ :: cs => ueberText cs

/-- The code characters: each string becomes one blank (so no run spans one),
    each line comment is dropped up to its newline and each block comment
    (nested, by the depth counter) up to its end; an unterminated block
    comment drops the rest (the lexer refuses it) -- exactly as `lex.rs` skips them,
    except that the blank also breaks digit adjacency the way a skipped string
    does there (a run starts behind code, never behind a quote).
    Fuel like `scan`: every step shortens the list, so `length + 1` always
    suffices; the exhausted-fuel arm returns the rest unscanned (fail-safe:
    an unscanned tail is checked as code, which can only refuse, never miss). -/
def codeZeichen : List Char → Nat → List Char
  | [], _ => []
  | '"' :: cs, n + 1 => ' ' :: codeZeichen (ueberText cs) n
  | '/' :: '/' :: cs, n + 1 => codeZeichen (nimmZeile cs).2 n
  | '/' :: '*' :: cs, n + 1 =>
    match ueberBlock 1 cs with
    | some rest => codeZeichen rest n
    | none => []
  | c :: cs, n + 1 => c :: codeZeichen cs n
  | cs, 0 => cs

/-- The distinct non-neutral scripts of a run (`schrift` without the `0`s). -/
def laufArten : List Char → List Nat
  | [] => []
  | c :: cs =>
    let rest := laufArten cs
    let s := schrift c.toNat
    if s == 0 || rest.contains s then rest else s :: rest

/-- Phase 2: identifier-like runs over code only. The allowed set is exactly
    `istFolge` (ASCII letters, digits, `_`, plus the umlauts of the `letter`
    rule) -- so a clean run needs no script table at all. A run starting right
    behind a digit belongs to the number neighbourhood (`L003`/`L006` own it)
    and is skipped, as in `lex.rs`.
    Fuel like `scan`: every step consumes a character, so `length + 1` always
    suffices; the exhausted-fuel arm refuses through the lex channel, as
    `scan` does (`out of fuel` is dead from `pruefeQuelle`, and dead code
    refuses). -/
def pruefeLaeufe : List Char → Bool → Nat → Except VertrauenFehler Unit
  | [], _, _ => .ok ()
  | c :: cs, nachZiffer, n + 1 =>
    if istLaufStart c then
      let (h, rest) := nimmLauf cs
      let lauf := c :: h
      if lauf.all istFolge then pruefeLaeufe rest false n
      else if nachZiffer then pruefeLaeufe rest false n
      else
        let arten := laufArten lauf
        if 2 ≤ arten.length then .error .gemischt
        else .error .fremd
    else if istZiffer c then pruefeLaeufe cs true n
    else pruefeLaeufe cs false n
  | _ :: _, _, 0 => .error (.lex (.unbekannt "out of fuel"))


end Gabbro.Grammatik.Parser
