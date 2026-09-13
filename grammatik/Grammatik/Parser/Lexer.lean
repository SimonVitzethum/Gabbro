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

/-- Keyword lookup by first character: buckets of character
    lists, so both the scan (at most 28 candidates) and the
    comparison (`Char ==` on numbers) stay kernel-cheap, unlike
    `String ==` through byte arrays. `lex_keywords` checks the
    table against this bucketing word by word, so a misfiled word
    fails the build instead of lexing as an identifier. -/
def schluesselTafelC : Char → List (List Char)
  | 'N' => [['N','o','n','e']]
  | 'S' => [['S','e','l','f'], ['S','o','m','e']]
  | 'a' => [['a','r','c','h'], ['a','l','l','o','c','s'], ['a','r','e','n','a'], ['a','l','l','o','c'], ['a','t'], ['a','s','s','u','m','e'], ['a','x','i','o','m'], ['a','d','v','a','n','c','e','s'], ['a','t','o','m','i','c'], ['a','c','q','u','i','r','e'], ['a','c','c','u','m','u','l','a','t','e','s'], ['a','d','d'], ['a','n','d'], ['a','b','i'], ['a','s','m'], ['a','w','a','i','t','s'], ['a','n','c','e','s','t','o','r','s'], ['a','l','i','g','n','e','d']]
  | 'b' => [['b','r','e','a','k','i','n','g'], ['b','y'], ['b','o','u','n','d','e','d'], ['b','o','o','t'], ['b','a','n','k'], ['b','a','c','k','e','d'], ['b','i','g'], ['b','o','o','l']]
  | 'c' => [['c','o','n','s','t'], ['c','o','s','t','s'], ['c','o','n','s','u','m','e','s'], ['c','o','n','s','u','m','i','n','g'], ['c','o','d','e'], ['c','a','p','a','c','i','t','y'], ['c','l','a','s','s'], ['c','o','u','n','t'], ['c','o','n','c','u','r','r','e','n','t'], ['c','h','e','c','k'], ['c','l','a','i','m'], ['c','a','n','_','f','a','i','l'], ['c','o','u','n','t','e','r','p','r','o','b','e'], ['c','o','s','t'], ['c','h','a','i','n'], ['c','l','o','b','b','e','r','s'], ['c','p','u'], ['c','h','i','l','d']]
  | 'd' => [['d','i','v','e','r','g','e','n','t'], ['d','e','a','d','l','i','n','e'], ['d','e','c','r','e','a','s','e','s'], ['d','i','v','e','r','g','e','s'], ['d','m','a'], ['d','e','v','i','c','e'], ['d','o','w','n'], ['d','i','s','p','a','t','c','h'], ['d','e','s','c','e','n','d','a','n','t','s']]
  | 'e' => [['e','x','t','e','r','n'], ['e','n','s','u','r','e','s'], ['e','f','f','e','c','t','s'], ['e','x','h','a','u','s','t','i','v','e'], ['e','l','s','e'], ['e','x','c','h','a','n','g','e'], ['e','x','p','e','c','t','s'], ['e','n','d','i','a','n'], ['e','m','b','e','d','s'], ['e','n','t','r','y'], ['e','r','r','o','r','s'], ['e','n','t','r','u','s','t'], ['e','l','e','m','s'], ['e','x','i','s','t','s']]
  | 'f' => [['f','n'], ['f','o','r','e','v','e','r'], ['f','p','_','c','o','n','t','r','a','c','t'], ['f','o','r'], ['f','o','r','m','a','t'], ['f','i','e','l','d','s'], ['f','r','o','m'], ['f','a','l','s','i','f','i','e','r'], ['f','l','o','o','r'], ['f','3','2'], ['f','6','4'], ['f','i','n','i','t','e'], ['f','o','r','a','l','l'], ['f','a','l','s','e']]
  | 'g' => [['g','h','o','s','t'], ['g','r','o','u','p'], ['g','a','t','e','s']]
  | 'h' => [['h','e','l','d']]
  | 'i' => [['i','m','p','l'], ['i','n'], ['i','n','d','u','c','t','i','o','n'], ['i','f'], ['i','n','s','e','r','t'], ['i','n','t','e','r','r','u','p','t','_','r','o','u','t','i','n','g'], ['i','n','v','a','r','i','a','n','t'], ['i','n','d','e','x'], ['i','n','t','o'], ['i','s','t'], ['i','8'], ['i','1','6'], ['i','3','2'], ['i','6','4']]
  | 'k' => [['k','e','r','n','e','l']]
  | 'l' => [['l','i','n','e','a','r'], ['l','o','c','k','s'], ['l','e','t'], ['l','e','a','v','e'], ['l','e','a','v','e','s'], ['l','i','b','r','a','r','y'], ['l','o','c','k'], ['l','i','t','t','l','e'], ['l','e','v','e','l','s'], ['l','e','a','f'], ['l','e','n','o','f']]
  | 'm' => [['m','o','d','u','l','e'], ['m','a','i','n','t','a','i','n','s'], ['m','a','s','k','s'], ['m','a','t','c','h'], ['m','u','t'], ['m','m','i','o'], ['m','e','m','o','r','y','_','m','o','d','e','l'], ['m','i','r','r','o','r','s'], ['m','e','a','s','u','r','e','s'], ['m','e','r','g','e'], ['m','a','x'], ['m','i','n'], ['m','a','p','p','i','n','g','s'], ['m','a','s','k','e','d']]
  | 'n' => [['n','a','r','r','o','w'], ['n','e','x','t'], ['n','o','r','m','a','l'], ['n','o','t','h','i','n','g'], ['n','o','d','e'], ['n','u','m','b','e','r'], ['n','e','s','t','e','d'], ['n','e','v','e','r']]
  | 'o' => [['o','p','a','q','u','e'], ['o','l','d'], ['o','v','e','r'], ['o','n','_','e','x','c','e','e','d','e','d'], ['o','p','s'], ['o','w','n'], ['o','w','n','e','r'], ['o','b','s','e','r','v','e','s'], ['o','r','d','e','r'], ['o','n','l','i','n','e'], ['o','f','f','l','i','n','e'], ['o','f','f','s','e','t','_','i','n','t','o'], ['o','p','t','i','o','n'], ['o','r'], ['o','u','t'], ['o','f'], ['o','b','s','e','r','v','e','d'], ['o','c','c','u','p','i','e','d']]
  | 'p' => [['p','u','b'], ['p','r','i','m'], ['p','u','b','l','i','s','h','e','s'], ['p','u','r','e'], ['p','r','o','g','r','e','s','s'], ['p','e','r','_','p','a','s','s'], ['p','t','r'], ['p','a','y','l','o','a','d'], ['p','r','o','f','i','l','e'], ['p','r','o','t','e','c','t','s'], ['p','r','e','s','e','r','v','e','s'], ['p','e','r'], ['p','o','r','t'], ['p','a','r','e','n','t']]
  | 'q' => [['q','u','e','u','e']]
  | 'r' => [['r','a','w'], ['r','e','q','u','i','r','e','s'], ['r','e','f','i','n','e','s'], ['r','e','a','d','s'], ['r','e','t','r','y'], ['r','e','t','u','r','n'], ['r','e','m','o','v','e'], ['r','e','l','a','b','e','l'], ['r','e','s','u','l','t'], ['r','e','t','u','r','n','s'], ['r'], ['r','w'], ['r','o','u','n','d','i','n','g'], ['r','e','s','e','t'], ['r','e','a','s','o','n'], ['r','e','g'], ['r','c'], ['r','c','u'], ['r','e','c','l','a','i','m','s'], ['r','a','n','k'], ['r','e','t','i','r','e','s'], ['r','e','s','e','r','v','e','d'], ['r','u','n','s'], ['r','e','l','e','a','s','e'], ['r','e','l','a','x','e','d'], ['r','e','g','s'], ['r','e','a','c','h','e','s'], ['r','o','u','n','d','e','d']]
  | 's' => [['s','t','a','t','i','c'], ['s','p','e','c'], ['s','e','c','t','i','o','n'], ['s','l','o','t'], ['s','t','a','t','e'], ['s','t','r','i','d','e'], ['s','e','q'], ['s','h','a','r','e','d'], ['s','c','a','l','e'], ['s','y','s','c','a','l','l'], ['s','t','a','c','k'], ['s','t','e','p'], ['s','l','o','t','s'], ['s','i','b','l','i','n','g'], ['s','i','z','e','o','f']]
  | 't' => [['t','y','p','e'], ['t','a','g','g','e','d'], ['t','o'], ['t','r','a','v','e','r','s','e'], ['t','o','u','c','h','e','s'], ['t','r','a','n','s','l','a','t','o','r'], ['t','a','b','l','e'], ['t','r','a','n','s','i','t','i','o','n'], ['t','r','e','e'], ['t','h','r','e','a','d','s'], ['t','r','u','e']]
  | 'u' => [['u','s','e'], ['u','n','t','i','l'], ['u','n','v','i','s','i','t','e','d'], ['u','p','d','a','t','e'], ['u','n','f','a','l','s','i','f','i','a','b','l','e'], ['u','8'], ['u','1','6'], ['u','3','2'], ['u','6','4']]
  | 'v' => [['v','e','c','t','o','r'], ['v','i','a']]
  | 'w' => [['w','h','e','n'], ['w','h','e','r','e'], ['w','r','i','t','e','s'], ['w'], ['w','1','c'], ['w','r','a','p','p','i','n','g'], ['w','a','l','k']]
  | 'x' => [['x']]
  | _ => []

/-- Is this name a keyword (bucket lookup, see above)? -/
def istSchluessel (s : String) : Bool :=
  match s.toList with
  | c :: t => (schluesselTafelC c).contains (c :: t)
  | [] => false

/-- String equality through character lists: kernel-cheap, unlike
    `String ==` (see above). -/
def strEq (a b : String) : Bool :=
  a.toList == b.toList

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
      let tok := if istSchluessel s then Token.wort s else Token.ident s
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
   .zahl 18446603336221196288, .zeichen "||", .zeichen "!",
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
  [.wort "x", .zeichen ">=", .gleit "0.0", .zeichen "&&",
   .wort "x", .zeichen "<=", .gleit "1.0", .ende]
theorem sonde12_lex :
    lex "x >= 0.0 && x <= 1.0" = .ok tok12 := by
  decide
def tok13 : List Token :=
  [.ident "d", .zeichen ".", .ident "TIEFE", .ende]
theorem sonde13_lex : lex "d.TIEFE" = .ok tok13 := by decide
def tok14 : List Token :=
  [.ident "TIEFE", .zeichen "<=", .zahl 8, .ende]
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
   .zahl 1, .ende]
theorem sonde18_lex : lex "c.wert + 1" = .ok tok18 := by decide
def tok19 : List Token :=
  [.ident "v", .zeichen "+", .zahl 1, .ende]
theorem sonde19_lex : lex "v + 1" = .ok tok19 := by decide
def tok20 : List Token :=
  [.ident "z", .zeichen "+", .zahl 1, .ende]
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
  * `schluesselTafelC` stores the table as character lists in
    first-character buckets, and `strEq` compares through
    character lists: kernel evaluation of `String ==` runs through
    byte arrays and dominates `decide` time, while `Char ==` runs
    on numbers. `lex_keywords` re-checks the bucketing word by
    word, so the optimisation cannot silently misfile a word.
-/

#print axioms Gabbro.Grammatik.Parser.lex_total
#print axioms Gabbro.Grammatik.Parser.lex_keywords
#print axioms Gabbro.Grammatik.Parser.lex_keywords_zeuge
#print axioms Gabbro.Grammatik.Parser.sonde01_lex
