/-
  File:      Grammatik/Parser/Lexer.lean
  Subject:   T3 PART 1 (PLAN-UEBERSETZUNGSVALIDIERUNG.md section 1): the
             Gabbro lexer as a total Lean function, step 1.

  Skeleton: token type, error type, the closed vocabulary table, and a
  stub `lex`. The full scanner lands in the next step.
-/

namespace Gabbro.Grammatik.Parser

/-- A surface token. Keywords carry their spelling (`wort "module"`);
    punctuation carries its spelling (`zeichen "<<%"`). -/
inductive Token
  | ident : String → Token
  | wort : String → Token
  | zahl : Nat → Token
  | gleit : String → Token
  | text : String → Token
  | zeichen : String → Token
  | ende : Token
  deriving DecidableEq, Repr

/-- The one error channel of the lexer: the first bad site. -/
inductive LexFehler
  | unbekannt : String → LexFehler
  | offeneZeichenkette : LexFehler
  | zahlOhneZiffern : LexFehler
  deriving DecidableEq, Repr

/-- The closed vocabulary: SYNTAX.md vocabulary table plus `kw.rs`
    (`Kw::text` over `ALLE`). 242 words; SYNTAX.md prints 239 because
    five words stand in two rows each (`fields`, `protects`, `rank`,
    `chain`, `via`) -- the Lean list counts each once. -/
def wortschatz : List String :=
  ["module", "pub", "use", "type", "opaque", "linear", "ghost", "tagged",
   "const", "static", "fn", "spec", "impl", "raw", "divergent", "prim",
   "extern", "section", "arch", "when", "requires", "ensures", "maintains",
   "refines", "breaking", "effects", "costs", "deadline", "decreases",
   "where", "in", "exhaustive", "old", "narrow", "to", "induction",
   "reads", "writes", "locks", "masks", "allocs", "consumes", "publishes",
   "diverges", "pure", "if", "else", "match", "traverse", "over", "by",
   "touches", "retry", "forever", "until", "bounded", "progress",
   "on_exceeded", "per_pass", "return", "let", "mut", "unvisited",
   "consuming", "leave", "leaves", "next", "ops", "insert", "remove",
   "relabel", "result", "exchange", "update", "returns", "ptr", "normal",
   "mmio", "dma", "code", "boot", "r", "w", "rw", "x", "own", "library",
   "payload", "profile", "rounding", "fp_contract", "memory_model",
   "interrupt_routing", "arena", "capacity", "alloc", "reset",
   "translator", "for", "format", "table", "slot", "invariant", "reason",
   "state", "transition", "device", "reg", "class", "w1c", "rc", "fields",
   "bank", "at", "stride", "count", "owner", "backed", "mirrors", "from",
   "assume", "falsifier", "unfalsifiable", "axiom", "lock", "rcu",
   "observes", "reclaims", "group", "concurrent", "protects", "rank",
   "order", "advances", "retires", "check", "claim", "measures", "gates",
   "can_fail", "floor", "counterprobe", "expects", "endian", "little",
   "big", "reserved", "cost", "runs", "online", "offline", "offset_into",
   "index", "into", "option", "chain", "wrapping", "atomic", "acquire",
   "release", "seq", "relaxed", "nothing", "accumulates", "merge", "max",
   "min", "add", "or", "and", "held", "shared", "embeds", "scale", "walk",
   "levels", "node", "down", "leaf", "mappings", "entry", "syscall",
   "abi", "number", "errors", "kernel", "entrust", "vector", "regs",
   "out", "preserves", "clobbers", "asm", "stack", "dispatch", "per",
   "cpu", "ist", "nested", "masked", "awaits", "port", "step", "via",
   "slots", "of", "descendants", "ancestors", "observed", "tree",
   "parent", "child", "sibling", "occupied", "queue", "elems", "threads",
   "reaches", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64",
   "f32", "f64", "rounded", "finite", "bool", "never", "sizeof",
   "lenof", "aligned", "forall", "exists", "true", "false", "Self",
   "Some", "None"]

/-- Whitespace of the source (`lex.rs`: space, tab, CR, LF). -/
def istLeer : Char → Bool
  | ' ' => true
  | '\t' => true
  | '\r' => true
  | '\n' => true
  | _ => false

/-- A name start: ASCII letter, `_`, or one of the umlauts of the
    SYNTAX.md `letter` rule. -/
def istAnfang (c : Char) : Bool :=
  match c with
  | 'ä' => true
  | 'ö' => true
  | 'ü' => true
  | 'Ä' => true
  | 'Ö' => true
  | 'Ü' => true
  | 'ß' => true
  | '_' => true
  | _ => let n := c.toNat; (97 ≤ n && n ≤ 122) || (65 ≤ n && n ≤ 90)

/-- A decimal digit. -/
def istZiffer (c : Char) : Bool :=
  let n := c.toNat; 48 ≤ n && n ≤ 57

/-- A name continuation: start or digit. -/
def istFolge (c : Char) : Bool :=
  istAnfang c || istZiffer c

/-- The value of a digit in the given base, or `none`. -/
def hexWert (c : Char) (basis : Nat) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then
    let d := n - 48
    if d < basis then some d else none
  else if basis == 16 then
    if 97 ≤ n && n ≤ 102 then some (n - 87)
    else if 65 ≤ n && n ≤ 70 then some (n - 55)
    else none
  else none

/-- A single-character punctuation mark. -/
def istEinfach : Char → Bool
  | ':' => true
  | ';' => true
  | ',' => true
  | '.' => true
  | '=' => true
  | '<' => true
  | '>' => true
  | '+' => true
  | '-' => true
  | '*' => true
  | '/' => true
  | '%' => true
  | '&' => true
  | '|' => true
  | '^' => true
  | '!' => true
  | '~' => true
  | '@' => true
  | '#' => true
  | '(' => true
  | ')' => true
  | '[' => true
  | ']' => true
  | '{' => true
  | '}' => true
  | _ => false

/-- Take a name tail (the head is already consumed). -/
def nimmFolge : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if istFolge c then let (h, t) := nimmFolge cs; (c :: h, t)
    else ([], c :: cs)

/-- Take digits of the given base, skipping `_` separators
    (`lex.rs`: separators never reach the value). Reports whether any
    digit was seen, for the `0x`-without-digits refusal. -/
def nimmZiffern (cs : List Char) (basis : Nat) : Nat × Bool × List Char :=
  go cs 0 false
where
  go : List Char → Nat → Bool → Nat × Bool × List Char
    | [], acc, g => (acc, g, [])
    | c :: cs, acc, g =>
      if c == '_' then go cs acc g
      else match hexWert c basis with
        | some d => go cs (acc * basis + d) true
        | none => (acc, g, c :: cs)

/-- Take decimal digits, skipping `_` (integer and fraction parts). -/
def nimmDez : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c == '_' then nimmDez cs
    else if istZiffer c then let (h, t) := nimmDez cs; (c :: h, t)
    else ([], c :: cs)

/-- Take decimal digits strictly (no `_`): the exponent of a float
    literal (`lex.rs` reads the exponent with `is_ascii_digit` only,
    so `1.5e1_0` is the float `1.5e1` followed by the name `_0`). -/
def nimmDezStreng : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if istZiffer c then let (h, t) := nimmDezStreng cs; (c :: h, t)
    else ([], c :: cs)

/-- Take an exponent `[e [+-] digits]`; only lowercase `e` (`lex.rs`
    `L004` rationale: one spelling). With no digits after the `e`,
    nothing is consumed (`1.5e` is the float `1.5` plus the name `e`). -/
def nimmExponent : List Char → String × List Char
  | 'e' :: '+' :: cs =>
    let (d, r) := nimmDezStreng cs
    match d with
    | [] => ("", 'e' :: '+' :: cs)
    | _ :: _ => ("e+" ++ String.ofList d, r)
  | 'e' :: '-' :: cs =>
    let (d, r) := nimmDezStreng cs
    match d with
    | [] => ("", 'e' :: '-' :: cs)
    | _ :: _ => ("e-" ++ String.ofList d, r)
  | 'e' :: cs =>
    let (d, r) := nimmDezStreng cs
    match d with
    | [] => ("", 'e' :: cs)
    | _ :: _ => ("e" ++ String.ofList d, r)
  | cs => ("", cs)

/-- Take a string body: every character except the closing quote and
    the newline (`char = any character except quote and newline` --
    there are no escapes, so there is nothing to interpret). -/
def nimmText : List Char → Option (List Char × List Char)
  | [] => none
  | '\n' :: _ => none
  | '"' :: cs => some ([], cs)
  | c :: cs => match nimmText cs with
    | some (h, t) => some (c :: h, t)
    | none => none

/-- Skip a `--` comment up to (not including) the newline. -/
def ueberKommentar : List Char → List Char
  | [] => []
  | '\n' :: cs => '\n' :: cs
  | _ :: cs => ueberKommentar cs

/-- Cut one punctuation mark, longest match first (`..<` before `..`
    before `.`; `<<%` before `<<`; `+|`, `+%`, `+=` before `+`). -/
def nimmZeichen : List Char → Option (String × List Char)
  | '<' :: '<' :: '%' :: cs => some ("<<%", cs)
  | '.' :: '.' :: '<' :: cs => some ("..<", cs)
  | ':' :: ':' :: cs => some ("::", cs)
  | '.' :: '.' :: cs => some ("..", cs)
  | '-' :: '>' :: cs => some ("->", cs)
  | '=' :: '>' :: cs => some ("=>", cs)
  | '=' :: '=' :: cs => some ("==", cs)
  | '!' :: '=' :: cs => some ("!=", cs)
  | '<' :: '=' :: cs => some ("<=", cs)
  | '>' :: '=' :: cs => some (">=", cs)
  | '<' :: '<' :: cs => some ("<<", cs)
  | '>' :: '>' :: cs => some (">>", cs)
  | '+' :: '=' :: cs => some ("+=", cs)
  | '+' :: '%' :: cs => some ("+%", cs)
  | '+' :: '|' :: cs => some ("+|", cs)
  | '-' :: '=' :: cs => some ("-=", cs)
  | '-' :: '%' :: cs => some ("-%", cs)
  | '*' :: '%' :: cs => some ("*%", cs)
  | '&' :: '&' :: cs => some ("&&", cs)
  | '&' :: '=' :: cs => some ("&=", cs)
  | '|' :: '|' :: cs => some ("||", cs)
  | '|' :: '=' :: cs => some ("|=", cs)
  | c :: cs => if istEinfach c then some (String.ofList [c], cs) else none
  | [] => none

/-- After a number value: the trailing-letter refusal (`lex.rs`
    `L003`: `0b12` is never `0b1` followed by `2`). Pure: returns the
    token and the rest, so `scan` keeps the only recursion. -/
def zahlWeiter : Nat → List Char → Except LexFehler (Token × List Char)
  | v, [] => .ok (Token.zahl v, [])
  | v, c :: cs =>
    if istAnfang c || istZiffer c then
      .error (.unbekannt "letter in number")
    else .ok (Token.zahl v, c :: cs)

/-- A number body of the given base: value, then the maximal-munch
    float branch (`1..5` stays a range, `1.5` a float, `1.` refuses
    the fraction), then `zahlWeiter`. -/
def zahlBasis (basis : Nat) (cs : List Char) :
    Except LexFehler (Token × List Char) :=
  let (v, gesehen, rest) := nimmZiffern cs basis
  if !gesehen then .error .zahlOhneZiffern
  else if basis == 10 then match rest with
    | '.' :: d :: ds =>
      if istZiffer d then
        let (nach, rest') := nimmDez (d :: ds)
        let (exp, rest'') := nimmExponent rest'
        .ok (Token.gleit (toString v ++ "." ++ String.ofList nach ++ exp),
          rest'')
      else zahlWeiter v rest
    | _ => zahlWeiter v rest
  else zahlWeiter v rest

/-- A number head: the `0x`/`0b` prefix, or none. A capital prefix is
    refused (`lex.rs` `L004`: one spelling, `0x` and `0b` only). -/
def scanZahlKopf : List Char → Except LexFehler (Token × List Char)
  | '0' :: 'x' :: rest => zahlBasis 16 rest
  | '0' :: 'b' :: rest => zahlBasis 2 rest
  | '0' :: 'X' :: _ => .error (.unbekannt "0X")
  | '0' :: 'B' :: _ => .error (.unbekannt "0B")
  | cs => zahlBasis 10 cs

/-- The scanner over a character list with fuel. Every branch either
    reports the first error or consumes at least one character, so
    fuel `length + 1` always suffices; the fuel error is unreachable
    from `lex`. -/
def scan : List Char → Nat → Except LexFehler (List Token)
  | [], _ => .ok [Token.ende]
  | '-' :: '-' :: rest, n + 1 => scan (ueberKommentar rest) n
  | '"' :: rest, n + 1 =>
    match nimmText rest with
    | some (inhalt, rest') =>
      Except.map (Token.text (String.ofList inhalt) :: ·) (scan rest' n)
    | none => .error .offeneZeichenkette
  | c :: cs, n + 1 =>
    if istLeer c then scan cs n
    else if istZiffer c then match scanZahlKopf (c :: cs) with
      | .ok (t, rest) => Except.map (t :: ·) (scan rest n)
      | .error e => .error e
    else if istAnfang c then
      let (h, t) := nimmFolge cs
      let s := String.ofList (c :: h)
      let tok := if wortschatz.contains s then Token.wort s else Token.ident s
      Except.map (tok :: ·) (scan t n)
    else match nimmZeichen (c :: cs) with
      | some (s, rest) =>
        Except.map (Token.zeichen s :: ·) (scan rest n)
      | none => .error (.unbekannt (String.ofList [c]))
  | _ :: _, 0 => .error (.unbekannt "out of fuel")

/-- The lexer: `lex.rs` `zerlege` as a total Lean function. The one
    difference in shape: Rust accumulates refusals and still emits a
    (partial) token stream, while `lex` returns the FIRST error --
    a certificate starts from source text that lexes cleanly, so the
    partial stream has no reader here. -/
def lex (s : String) : Except LexFehler (List Token) :=
  scan s.toList (s.length + 1)

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
    token, checked by `decide` over the whole 242-word list. The
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
    lex "0xFFFF_FFFF" = .ok [Token.zahl 4294967295, Token.ende] := by
  decide

/-- Binary literal. -/
theorem lex_zahl_bin :
    lex "0b101" = .ok [Token.zahl 5, Token.ende] := by
  decide

/-- A float literal with an exponent. -/
theorem lex_gleit_beispiel :
    lex "1.5e-3" = .ok [Token.gleit "1.5e-3", Token.ende] := by
  decide

/-- Maximal munch: `1..5` is a range, never a float. -/
theorem lex_bereich :
    lex "1..5" = .ok [Token.zahl 1, Token.zeichen "..", Token.zahl 5,
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

/-- Comments run to the end of the line and vanish. -/
theorem lex_kommentar :
    lex "a -- rest\nb" = .ok [Token.ident "a", Token.ident "b",
      Token.ende] := by
  decide

/-- A string literal carries its content without the quotes. -/
theorem lex_text_beispiel :
    lex "\"hi\"" = .ok [Token.text "hi", Token.ende] := by
  decide

/-- An unterminated string is the first error. -/
theorem lex_text_offen :
    lex "\"offen" = .error .offeneZeichenkette := by
  decide

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * `lex` returns the FIRST error where `lex.rs` accumulates refusals
    and still emits a partial stream. A certificate starts from source
    that lexes cleanly, so the partial stream has no reader; the
    refusal CODES (`L001`-`L007`) are not modelled either.
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
-/

#print axioms Gabbro.Grammatik.Parser.lex_total
#print axioms Gabbro.Grammatik.Parser.lex_keywords
#print axioms Gabbro.Grammatik.Parser.lex_keywords_zeuge
