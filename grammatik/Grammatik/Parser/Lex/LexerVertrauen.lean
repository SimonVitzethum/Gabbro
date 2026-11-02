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
public import Grammatik.Parser.Lex.LexerVertrauena
public import Grammatik.Parser.Lex.Lexer
@[expose] public section


namespace Gabbro.Grammatik.Parser
/-- The gate: phase 1 over the raw source (BOM stripped), then phase 2
    over code. The first refusal wins, as in `lex`. -/
def pruefeQuelle (s : String) : Except VertrauenFehler Unit :=
  let roh := ohneBom s.toList
  let code := codeZeichen s.toList (s.length + 1)
  match pruefeZeichen roh with
  | .error e => .error e
  | .ok _ => pruefeLaeufe code false (code.length + 1)

/-- The lexer with the gate in front: refuse first, lex second. -/
def lexVertrauen (s : String) : Except VertrauenFehler (List Token) :=
  match pruefeQuelle s with
  | .error e => .error e
  | .ok _ =>
    match lex s with
    | .error e => .error (.lex e)
    | .ok t => .ok t

/-- Decidable equality on gate outcomes over `Unit` (the probe half needs it
    for `decide`; the shape is the one `Lexer.lean` proves for `lex`). -/
instance : DecidableEq (Except VertrauenFehler Unit) :=
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

/-- Decidable equality on lexer outcomes behind the gate (same shape). -/
instance : DecidableEq (Except VertrauenFehler (List Token)) :=
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

/-- `lexVertrauen` is a function: every source text has a gated lexing outcome. -/
theorem lexVertrauen_total (s : String) : ∃ r, lexVertrauen s = r :=
  ⟨lexVertrauen s, rfl⟩

/-- The four codes are the booked ones (`P060`-`P063`). -/
theorem vertrauen_codes :
    vertrauenCode .bidi = "P060" ∧ vertrauenCode .fremd = "P061" ∧
    vertrauenCode .gemischt = "P062" ∧ vertrauenCode .unsichtbar = "P063" := by
  decide

/-- A bidi override is refused, even in a comment. -/
theorem quelle_bidi :
    pruefeQuelle (String.ofList ['/', '/', ' ', Char.ofNat 0x202E]) =
      .error .bidi := by
  decide

/-- A zero-width space is refused. -/
theorem quelle_unsichtbar :
    pruefeQuelle (String.ofList ['a', Char.ofNat 0x200B]) =
      .error .unsichtbar := by
  decide

/-- One foreign script is outside the allowed set. -/
theorem quelle_fremd :
    pruefeQuelle (String.ofList [' ', Char.ofNat 0x430, ' ']) =
      .error .fremd := by
  decide

/-- Two scripts in one run are the homoglyph. -/
theorem quelle_gemischt :
    pruefeQuelle (String.ofList ['p', Char.ofNat 0x430, 's']) =
      .error .gemischt := by
  decide

/-- The documented set (ASCII plus umlauts) still lexes. -/
theorem quelle_umlaut_sauber :
    pruefeQuelle "const Größe : u32 = 1;" = .ok () := by
  decide

/-- Foreign letters in a comment are prose, not names. -/
theorem quelle_kommentar_sauber :
    pruefeQuelle "// Größe σ →\nconst A : u32 = 1;" = .ok () := by
  decide

/-- Foreign letters in a block comment, nested or not, and in a doc comment. -/
theorem quelle_blockkommentar_sauber :
    pruefeQuelle "/* Größe /* σ */ → */ /// ж\nconst A : u32 = 1;" = .ok () := by
  decide

/-- A foreign letter glued to a number belongs to `L003`/`L006`, not here. -/
theorem quelle_zahlumgebung_sauber :
    pruefeQuelle ("const A : u32 = 0" ++ String.ofList [Char.ofNat 0x4000] ++ ";") =
      .ok () := by
  decide

/-- A BOM at offset 0 is an editor's signature, not a hiding place. -/
theorem quelle_bom_sauber :
    pruefeQuelle (String.ofList [Char.ofNat 0xFEFF, 'a']) = .ok () := by
  decide

/-- The same BOM one character later hides. -/
theorem quelle_bom_spaet :
    pruefeQuelle (String.ofList ['a', Char.ofNat 0xFEFF]) =
      .error .unsichtbar := by
  decide

/-- Behind a clean gate the lexer reads as before. -/
theorem lexVertrauen_weiter :
    lexVertrauen "const A : u32 = 1;" = .ok
      [Token.wort "const", Token.ident "A", Token.zeichen ":",
       Token.wort "u32", Token.zeichen "=", Token.num 1,
       Token.zeichen ";", Token.ende] := by
  decide

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * Run agreement, measured by fuzzing both sides. Both implementations cut
    runs with the same predicate (`lex.rs::ist_laufzeichen` here character for
    character: `_`, ASCII digits, and the twelve families over the same
    `schrift` table), so both cut the same runs -- except where the START rule
    differs, in two named corners:
    (a) exotic LETTERS past the twelve families (e.g. Runic): `lex.rs` starts
    a run on them (`is_alphabetic`), this gate does not;
    (b) non-ASCII DIGITS inside a family range (e.g. Arabic-Indic `٠`, family
    6): this gate starts a run on them, `lex.rs` does not (its start rule is
    letters only).
    Fuzzed over 40000 adversarial inputs mixing ASCII, umlauts, Greek,
    Cyrillic, Han, bidi, invisible, punctuation, exotic numbers and exotic
    letters: the two gates return the same first code everywhere outside (a)
    and (b) -- inside them only the sibling code differs (`P061` vs `P062`,
    or gate vs `L006`/`.unbekannt`) -- and NO input is accepted on one side
    and refused on the other (1768 gate-level divergences, all in (a)/(b),
    zero acceptance holes: every such input still refuses on both sides, at
    worst under `L006`/`.unbekannt`, which fire on every foreign character in
    code position). *Refuse, never interpret, on both sides.*
  * The script table is an approximation of UTS#39 (twelve families plus one
    rest), exactly as in `lex.rs` -- two exotic scripts sharing one family
    would pass as one, there and here.
  * Like `lex`, the gate returns the FIRST refusal where `lex.rs` accumulates;
    like `lex`, it records no spans.
  * `Lexer.lean` is untouched by construction: the gate is a new module, and
    `Grammatik.lean` gains one import line. Callers that must pass the gate
    use `lexVertrauen`; `lex` itself stays as the agreement half proved
    against `lex.rs` token for token.
-/

#print axioms Gabbro.Grammatik.Parser.lexVertrauen_total
#print axioms Gabbro.Grammatik.Parser.quelle_gemischt
