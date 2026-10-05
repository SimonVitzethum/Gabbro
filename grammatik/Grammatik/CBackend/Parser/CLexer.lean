/-
  File:      Grammatik/CParser/CLexer.lean
  Subject:   A2, PART 1: the LEXER of the emitted C subset, as a total Lean
             function (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`
             §6.4, assumption A2).

  Today the chain says "the emitted TEXT means `kProg zert`" -- a HAND
  transcription, named as assumption A2. This file is the first half of
  its replacement: the emitted C text becomes a token list, in Lean,
  kernel-reducible over the real emitted bytes.

  Shape and cost follow `Parser/Lexer.lean` (the Gabbro lexer, T3):
  * the scanner works on `List Char`, never on `String` -- `String ==`
    goes through byte arrays and is expensive in the kernel, while
    `Char ==` is a comparison of numbers;
  * every branch consumes at least one character, so fuel `length + 1`
    always suffices and the fuel refusal is unreachable from `lexC`;
  * identifiers keep their characters (`CTok.id`), so no token carries a
    `String` at all.

  AND THE TEXT ITSELF IS A `List Char` (`lexC`), not a `String`. That is
  measured, not taste: in Lean 4.33 `String.toList` goes through the
  array representation, and forcing the first character of ONE 1419-byte
  literal costs the kernel 33,7 GB. The same text as a `List Char` built
  from 45 short `"…".toList` pieces costs 3,3 GB for lexing AND counting.
  See `lexC` below and the report.

  PREPROCESSOR. The emitted C carries `#include` and `#define` lines, and
  a directive ends at the newline -- the only place where the emitted C is
  line-sensitive. The lexer therefore cuts a directive's line off and
  lexes it separately into `CTok.direkt ts`; everywhere else newlines are
  whitespace. `scanFlach` (the directive's scanner) refuses a `#`, so a
  directive cannot nest.

  WHAT IS REFUSED, by construction: every character that is not
  whitespace, a letter, `_`, a digit, `"` or one of the punctuation marks
  of `CPunct` -- `lexC` returns `none`. A lexer that guesses is worse than
  one that stops.
-/

namespace Gabbro.Grammatik.CParser

/-- The punctuation the emitted subset uses. `/` is deliberately absent:
    the only `/` the emitter writes at this level opens a comment, and a
    division would have to come with its C computation type, which this
    parser does not infer (it refuses instead). -/
inductive CPunct where
  | lpar | rpar | lbrace | rbrace | lbrack | rbrack
  | semi | comma | dot | arrow
  | star | assign | eq | ne | le | ge | lt | gt
  | plus | minus | amp | pipe | caret | bang | tilde | shl | shr
  | quest | colon
  deriving DecidableEq, Repr

/-- A token of the emitted C. `direkt` is one preprocessor line, already
    lexed (`#define NKONTO 2u` is `direkt [id "define", id "NKONTO",
    num 2]`). -/
inductive CTok where
  | id (s : List Char)
  | num (v : Nat)
  | str (s : List Char)
  | pn (p : CPunct)
  | direkt (ts : List CTok)
  deriving Repr

/-! ## 1. Characters -/

/-- Whitespace of the emitted C (space, tab, CR, LF). -/
def istLeerC : Char → Bool
  | ' ' => true
  | '\t' => true
  | '\r' => true
  | '\n' => true
  | _ => false

/-- A name start: ASCII letter or `_` (the emitter writes no other). -/
def istAnfangC (c : Char) : Bool :=
  if c = '_' then true
  else let n := c.toNat; (97 ≤ n && n ≤ 122) || (65 ≤ n && n ≤ 90)

/-- A decimal digit. -/
def istZifferC (c : Char) : Bool :=
  let n := c.toNat; 48 ≤ n && n ≤ 57

/-- A name continuation. -/
def istFolgeC (c : Char) : Bool := istAnfangC c || istZifferC c

/-- The value of a hexadecimal digit. -/
def hexWertC (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

/-- Character-list equality (kernel-cheap, see the header). -/
def lcEq : List Char → List Char → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && lcEq as bs
  | _, _ => false

theorem lcEq_refl (s : List Char) : lcEq s s = true := by
  induction s with
  | nil => rfl
  | cons c t ih => simp [lcEq, ih]

theorem lcEq_eq : ∀ {a b : List Char}, lcEq a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [lcEq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, lcEq_eq h.2]
  | [], _ :: _, h => by simp [lcEq] at h
  | _ :: _, [], h => by simp [lcEq] at h

/-- Lookup in an association list keyed by character lists. -/
def lcFind {α : Type} : List (List Char × α) → List Char → Option α
  | [], _ => none
  | (k, v) :: rest, s => if lcEq k s then some v else lcFind rest s

/-! ## 2. Taking pieces -/

/-- Take a name tail (the head is already consumed). -/
def nimmFolgeC : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if istFolgeC c then let (h, t) := nimmFolgeC cs; (c :: h, t)
    else ([], c :: cs)

/-- Take decimal digits, accumulating the value. -/
def nimmZehnC : List Char → Nat → Nat × List Char
  | [], acc => (acc, [])
  | c :: cs, acc =>
    if istZifferC c then nimmZehnC cs (acc * 10 + (c.toNat - 48))
    else (acc, c :: cs)

/-- Take hexadecimal digits, accumulating the value. Reports whether a
    digit was seen, so `0x` without digits is refused. -/
def nimmHexC : List Char → Nat → Bool → Nat × Bool × List Char
  | [], acc, g => (acc, g, [])
  | c :: cs, acc, g =>
    match hexWertC c with
    | some d => nimmHexC cs (acc * 16 + d) true
    | none => (acc, g, c :: cs)

/-- Drop an integer suffix (`u`, `U`, `l`, `L`, up to three of them:
    `2u`, `1ul`, `0xFFFFFFFFu`, `1ull`). A LETTER after the suffix is
    refused by the caller's `istFolgeC` check, so `2ux` never lexes as
    `2u` followed by `x`. -/
def nimmSuffixC : List Char → Nat → List Char
  | c :: cs, n + 1 =>
    if c = 'u' || c = 'U' || c = 'l' || c = 'L' then nimmSuffixC cs n
    else c :: cs
  | cs, _ => cs

/-- A number literal: `0x…` hexadecimal or decimal, then the suffix.
    A letter or digit still standing after the suffix is a refusal
    (`0b101` and `2ux` are not numbers of this subset). -/
def zahlC : List Char → Option (Nat × List Char)
  | '0' :: 'x' :: cs =>
    let (v, g, r) := nimmHexC cs 0 false
    if g then
      let r' := nimmSuffixC r 3
      match r' with
      | c :: _ => if istFolgeC c then none else some (v, r')
      | [] => some (v, r')
    else none
  | cs =>
    let (v, r) := nimmZehnC cs 0
    let r' := nimmSuffixC r 3
    match r' with
    | c :: _ => if istFolgeC c then none else some (v, r')
    | [] => some (v, r')

/-- Skip a `/* … */` comment; an unterminated one is a refusal. -/
def ueberBlockC : List Char → Option (List Char)
  | [] => none
  | '*' :: '/' :: cs => some cs
  | _ :: cs => ueberBlockC cs

/-- The rest of the line, newline included (a `//` comment). -/
def zeilenRestC : List Char → List Char
  | [] => []
  | '\n' :: cs => '\n' :: cs
  | _ :: cs => zeilenRestC cs

/-- Cut a line at the newline: the line's characters, and the rest
    starting AT the newline. -/
def bisZeileC : List Char → List Char × List Char
  | [] => ([], [])
  | '\n' :: cs => ([], '\n' :: cs)
  | c :: cs => let (h, t) := bisZeileC cs; (c :: h, t)

/-- Take a string literal's body (the opening quote is consumed). There
    are no escapes in the emitted C -- the only string literals are the
    `_Static_assert` messages -- so a backslash is an ordinary
    character, and a newline inside a literal is a refusal. -/
def nimmTextC : List Char → Option (List Char × List Char)
  | [] => none
  | '\n' :: _ => none
  | '"' :: cs => some ([], cs)
  | c :: cs => match nimmTextC cs with
    | some (h, t) => some (c :: h, t)
    | none => none

/-- Cut one punctuation mark, longest match first. -/
def zeichenC : List Char → Option (CPunct × List Char)
  | '-' :: '>' :: cs => some (.arrow, cs)
  | '=' :: '=' :: cs => some (.eq, cs)
  | '!' :: '=' :: cs => some (.ne, cs)
  | '<' :: '=' :: cs => some (.le, cs)
  | '>' :: '=' :: cs => some (.ge, cs)
  | '<' :: '<' :: cs => some (.shl, cs)
  | '>' :: '>' :: cs => some (.shr, cs)
  | '(' :: cs => some (.lpar, cs)
  | ')' :: cs => some (.rpar, cs)
  | '{' :: cs => some (.lbrace, cs)
  | '}' :: cs => some (.rbrace, cs)
  | '[' :: cs => some (.lbrack, cs)
  | ']' :: cs => some (.rbrack, cs)
  | ';' :: cs => some (.semi, cs)
  | ',' :: cs => some (.comma, cs)
  | '.' :: cs => some (.dot, cs)
  | '*' :: cs => some (.star, cs)
  | '=' :: cs => some (.assign, cs)
  | '<' :: cs => some (.lt, cs)
  | '>' :: cs => some (.gt, cs)
  | '+' :: cs => some (.plus, cs)
  | '-' :: cs => some (.minus, cs)
  | '&' :: cs => some (.amp, cs)
  | '|' :: cs => some (.pipe, cs)
  | '^' :: cs => some (.caret, cs)
  | '!' :: cs => some (.bang, cs)
  | '~' :: cs => some (.tilde, cs)
  | '?' :: cs => some (.quest, cs)
  | ':' :: cs => some (.colon, cs)
  | _ => none

/-! ## 3. The scanner -/

/-- ONE step: the next token, or whitespace/comment skipped
    (`some (none, rest)`). `none` is a refusal. `#` is NOT handled here;
    the two loops below do it, because a directive ends at a newline.
    Every `some` answer consumes at least one character. -/
def einTokC : List Char → Option (Option CTok × List Char)
  | [] => some (none, [])
  | '/' :: '*' :: cs => (ueberBlockC cs).map fun r => (none, r)
  | '/' :: '/' :: cs => some (none, zeilenRestC cs)
  | '"' :: cs => (nimmTextC cs).map fun p => (some (.str p.1), p.2)
  | c :: cs =>
    if istLeerC c then some (none, cs)
    else if istZifferC c then (zahlC (c :: cs)).map fun p => (some (.num p.1), p.2)
    else if istAnfangC c then
      let (h, t) := nimmFolgeC cs
      some (some (.id (c :: h)), t)
    else match zeichenC (c :: cs) with
      | some (p, r) => some (some (.pn p), r)
      | none => none

/-- The scanner of ONE preprocessor line: no `#` inside a directive. -/
def scanFlachC : List Char → Nat → Option (List CTok)
  | [], _ => some []
  | _ :: _, 0 => none
  | c :: cs, n + 1 =>
    if c = '#' then none
    else match einTokC (c :: cs) with
      | some (some t, r) => (scanFlachC r n).map (t :: ·)
      | some (none, r) => scanFlachC r n
      | none => none

/-- The scanner. A `#` cuts its line off and lexes it into one
    `CTok.direkt`; everywhere else a newline is whitespace. -/
def scanC : List Char → Nat → Option (List CTok)
  | [], _ => some []
  | _ :: _, 0 => none
  | '#' :: cs, n + 1 =>
    let (zeile, rest) := bisZeileC cs
    match scanFlachC zeile (zeile.length + 1) with
    | some ts => (scanC rest n).map (CTok.direkt ts :: ·)
    | none => none
  | c :: cs, n + 1 =>
    match einTokC (c :: cs) with
    | some (some t, r) => (scanC r n).map (t :: ·)
    | some (none, r) => scanC r n
    | none => none

/-- **THE C LEXER**: the emitted text -- its CHARACTERS -- as a token
    list, or `none`.

    THE TEXT IS A `List Char`, AND THAT IS A COST DECISION, measured.
    In Lean 4.33 a `String` is an array underneath (`String.toList s =
    (String.Internal.toArray s).toList`), and converting ONE long string
    literal to its characters is what costs the kernel its memory:
    forcing the FIRST cons cell of a 1419-character literal measured
    **33,7 GB / 217 s** on `ki-pc-fisch-101` (2026-09-15), and splitting
    the literal into 45 short literals joined by `++` did not help
    (`String.append` goes through the array too). The SAME text as a
    `List Char`, built from 45 short `"…".toList` pieces, lexes and gets
    counted in **3,3 GB / 20 s** -- a factor of 13 in memory. The whole
    measurement is in `messung/muse/OPUS-BERICHT-CPARSER.md`; it is the
    same wall `dokumente/OFFEN.md` O13 ran into. -/
def lexC (cs : List Char) : Option (List CTok) :=
  scanC cs (cs.length + 1)

/-- The same on a `String`, for short texts (the probes below). On a long
    literal this is the expensive path -- see `lexC`. -/
def lexS (s : String) : Option (List CTok) := lexC s.toList

/-- The lexer is a function: every text has an outcome. Trivially, by
    exhibiting it -- the content is that `lexC` is TOTAL (no `partial`,
    no `sorry`), which the definition above carries. -/
theorem lexC_total (cs : List Char) : ∃ r, lexC cs = r := ⟨lexC cs, rfl⟩

/-! ## 4. Probes: one per lexer decision -/

/-- An identifier keeps its characters. -/
theorem lexC_ident : lexS "stand" = some [.id ['s','t','a','n','d']] := rfl

/-- `__attribute__` is an ordinary identifier (leading underscores). -/
theorem lexC_attr_ident :
    lexS "__attribute__" = some [.id "__attribute__".toList] := rfl

/-- A decimal literal with the `u` suffix takes its value. -/
theorem lexC_zahl_u : lexS "100u" = some [.num 100] := rfl

/-- A hexadecimal literal with a suffix. -/
theorem lexC_zahl_hex : lexS "0xFFFFFFFFu" = some [.num 4294967295] := rfl

/-- A letter after the suffix is a refusal, never a second token. -/
theorem lexC_zahl_buchstabe : lexS "2ux" = none := rfl

/-- `0b101` is no literal of this subset (the emitter writes none). -/
theorem lexC_zahl_binaer : lexS "0b101" = none := rfl

/-- The arrow and the dot are one mark each, longest match first. -/
theorem lexC_pfeil :
    lexS "k->slots[i].stand" =
      some [.id ['k'], .pn .arrow, .id "slots".toList, .pn .lbrack, .id ['i'],
            .pn .rbrack, .pn .dot, .id "stand".toList] := rfl

/-- A block comment vanishes. -/
theorem lexC_kommentar : lexS "a /* weg */ b" = some [.id ['a'], .id ['b']] := rfl

/-- An unterminated block comment is a refusal. -/
theorem lexC_kommentar_offen : lexS "/* offen" = none := rfl

/-- A directive is ONE token carrying its own token list. -/
theorem lexC_define :
    lexS "#define NKONTO 2u\n" =
      some [.direkt [.id "define".toList, .id "NKONTO".toList, .num 2]] := rfl

/-- An `#include` line, and the newline that ends it. -/
theorem lexC_include :
    lexS "#include <stdint.h>\nx" =
      some [.direkt [.id "include".toList, .pn .lt, .id "stdint".toList, .pn .dot,
              .id ['h'], .pn .gt], .id ['x']] := rfl

/-- A directive cannot nest. -/
theorem lexC_direktive_verschachtelt : lexS "#define # x\n" = none := rfl

/-- The `_Static_assert` prelude line, with its string literal. -/
theorem lexC_pin :
    lexS "_Static_assert((-1 >> 1) == -1, \"arithmetic right shift\");" =
      some [.id "_Static_assert".toList, .pn .lpar, .pn .lpar, .pn .minus, .num 1,
            .pn .shr, .num 1, .pn .rpar, .pn .eq, .pn .minus, .num 1, .pn .comma,
            .str "arithmetic right shift".toList, .pn .rpar, .pn .semi] := rfl

/-- A character the subset has no use for is a refusal, not a token. -/
theorem lexC_unbekannt : lexS "a $ b" = none := rfl

/-- A `\\` is no escape here -- and no character of the subset either. -/
theorem lexC_backslash : lexS "a \\ b" = none := rfl

-- **THE WITNESS OBLIGATION of `lexC_total`** (rule 13): its premise is a ∀ over
-- syntax -- every character list -- and the probes above are the non-degenerate
-- witnesses, in both directions: NINE texts that lex to a named token list, and
-- SIX that are REFUSED. A totality theorem without them would be a decoration.
#print axioms Gabbro.Grammatik.CParser.lcEq_refl
#print axioms Gabbro.Grammatik.CParser.lcEq_eq
#print axioms Gabbro.Grammatik.CParser.lexC_total
#print axioms Gabbro.Grammatik.CParser.lexC_ident
#print axioms Gabbro.Grammatik.CParser.lexC_attr_ident
#print axioms Gabbro.Grammatik.CParser.lexC_zahl_u
#print axioms Gabbro.Grammatik.CParser.lexC_zahl_hex
#print axioms Gabbro.Grammatik.CParser.lexC_zahl_buchstabe
#print axioms Gabbro.Grammatik.CParser.lexC_zahl_binaer
#print axioms Gabbro.Grammatik.CParser.lexC_pfeil
#print axioms Gabbro.Grammatik.CParser.lexC_kommentar
#print axioms Gabbro.Grammatik.CParser.lexC_kommentar_offen
#print axioms Gabbro.Grammatik.CParser.lexC_define
#print axioms Gabbro.Grammatik.CParser.lexC_include
#print axioms Gabbro.Grammatik.CParser.lexC_direktive_verschachtelt
#print axioms Gabbro.Grammatik.CParser.lexC_pin
#print axioms Gabbro.Grammatik.CParser.lexC_unbekannt
#print axioms Gabbro.Grammatik.CParser.lexC_backslash

end Gabbro.Grammatik.CParser
