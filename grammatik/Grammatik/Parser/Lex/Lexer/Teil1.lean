module

import all Init.Data.Repr

@[expose] public section


namespace Gabbro.Grammatik.Parser

/-- A surface token. Keywords carry their spelling (`wort "module"`);
    punctuation carries its spelling (`zeichen "<<%"`). `doku` is the
    trivia kind of a `///` doc comment (its text after the three slashes,
    to the end of the line): only `lexDoku` produces it, `lex` drops it, so
    a doc comment can never change what a program means. -/
inductive Token
  | ident : String → Token
  | wort : String → Token
  | num : Nat → Token
  | float : String → Token
  | text : String → Token
  | zeichen : String → Token
  | doku : String → Token
  | ende : Token
  deriving DecidableEq, Repr

/-- The one error channel of the lexer: the first bad site. -/
inductive LexFehler
  | unbekannt : String → LexFehler
  | offeneZeichenkette : LexFehler
  | offenerKommentar : LexFehler
  | zahlOhneZiffern : LexFehler
  deriving DecidableEq, Repr

/-- The canonical Lean keyword vocabulary. `space` introduces the nominal
    table-space binder independently of the linear `owner` binder. -/
def wortschatz : List String :=
  ["module", "pub", "use", "type", "opaque", "linear", "ghost", "tagged",
   "const", "static", "fn", "spec", "impl", "raw", "divergent", "prim",
   "extern", "section", "arch", "when", "requires", "ensures", "maintains",
   "refines", "breaking", "effects", "costs", "deadline", "decreases",
   "where", "in", "exhaustive", "old", "narrow", "to", "induction",
    "reads", "writes", "locks", "masks", "allocs", "consumes", "borrows", "moves", "mints", "publishes",
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
   "bank", "at", "stride", "count", "owner", "space", "backed", "mirrors", "from",
   "depends",
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
   "Some", "None", "grow", "pb", "blw", "free", "target", "dyn"]

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
  | 'b' => [['b','r','e','a','k','i','n','g'], ['b','y'], ['b','o','u','n','d','e','d'], ['b','o','o','t'], ['b','a','n','k'], ['b','a','c','k','e','d'], ['b','i','g'], ['b','o','o','l'], ['b','l','w'], ['b','o','r','r','o','w','s']]
  | 'c' => [['c','o','n','s','t'], ['c','o','s','t','s'], ['c','o','n','s','u','m','e','s'], ['c','o','n','s','u','m','i','n','g'], ['c','o','d','e'], ['c','a','p','a','c','i','t','y'], ['c','l','a','s','s'], ['c','o','u','n','t'], ['c','o','n','c','u','r','r','e','n','t'], ['c','h','e','c','k'], ['c','l','a','i','m'], ['c','a','n','_','f','a','i','l'], ['c','o','u','n','t','e','r','p','r','o','b','e'], ['c','o','s','t'], ['c','h','a','i','n'], ['c','l','o','b','b','e','r','s'], ['c','p','u'], ['c','h','i','l','d']]
  | 'd' => [['d','y','n'], ['d','i','v','e','r','g','e','n','t'], ['d','e','a','d','l','i','n','e'], ['d','e','c','r','e','a','s','e','s'], ['d','i','v','e','r','g','e','s'], ['d','m','a'], ['d','e','v','i','c','e'], ['d','o','w','n'], ['d','i','s','p','a','t','c','h'], ['d','e','s','c','e','n','d','a','n','t','s'], ['d','e','p','e','n','d','s']]
  | 'e' => [['e','x','t','e','r','n'], ['e','n','s','u','r','e','s'], ['e','f','f','e','c','t','s'], ['e','x','h','a','u','s','t','i','v','e'], ['e','l','s','e'], ['e','x','c','h','a','n','g','e'], ['e','x','p','e','c','t','s'], ['e','n','d','i','a','n'], ['e','m','b','e','d','s'], ['e','n','t','r','y'], ['e','r','r','o','r','s'], ['e','n','t','r','u','s','t'], ['e','l','e','m','s'], ['e','x','i','s','t','s']]
  | 'f' => [['f','n'], ['f','o','r','e','v','e','r'], ['f','p','_','c','o','n','t','r','a','c','t'], ['f','o','r'], ['f','o','r','m','a','t'], ['f','i','e','l','d','s'], ['f','r','o','m'], ['f','a','l','s','i','f','i','e','r'], ['f','l','o','o','r'], ['f','3','2'], ['f','6','4'], ['f','i','n','i','t','e'], ['f','o','r','a','l','l'], ['f','a','l','s','e'], ['f','r','e','e']]
  | 'g' => [['g','h','o','s','t'], ['g','r','o','u','p'], ['g','a','t','e','s'], ['g','r','o','w']]
  | 'h' => [['h','e','l','d']]
  | 'i' => [['i','m','p','l'], ['i','n'], ['i','n','d','u','c','t','i','o','n'], ['i','f'], ['i','n','s','e','r','t'], ['i','n','t','e','r','r','u','p','t','_','r','o','u','t','i','n','g'], ['i','n','v','a','r','i','a','n','t'], ['i','n','d','e','x'], ['i','n','t','o'], ['i','s','t'], ['i','8'], ['i','1','6'], ['i','3','2'], ['i','6','4']]
  | 'k' => [['k','e','r','n','e','l']]
  | 'l' => [['l','i','n','e','a','r'], ['l','o','c','k','s'], ['l','e','t'], ['l','e','a','v','e'], ['l','e','a','v','e','s'], ['l','i','b','r','a','r','y'], ['l','o','c','k'], ['l','i','t','t','l','e'], ['l','e','v','e','l','s'], ['l','e','a','f'], ['l','e','n','o','f']]
  | 'm' => [['m','o','d','u','l','e'], ['m','a','i','n','t','a','i','n','s'], ['m','a','s','k','s'], ['m','a','t','c','h'], ['m','u','t'], ['m','m','i','o'], ['m','e','m','o','r','y','_','m','o','d','e','l'], ['m','i','r','r','o','r','s'], ['m','e','a','s','u','r','e','s'], ['m','e','r','g','e'], ['m','a','x'], ['m','i','n'], ['m','a','p','p','i','n','g','s'], ['m','a','s','k','e','d'], ['m','o','v','e','s'], ['m','i','n','t','s']]
  | 'n' => [['n','a','r','r','o','w'], ['n','e','x','t'], ['n','o','r','m','a','l'], ['n','o','t','h','i','n','g'], ['n','o','d','e'], ['n','u','m','b','e','r'], ['n','e','s','t','e','d'], ['n','e','v','e','r']]
  | 'o' => [['o','p','a','q','u','e'], ['o','l','d'], ['o','v','e','r'], ['o','n','_','e','x','c','e','e','d','e','d'], ['o','p','s'], ['o','w','n'], ['o','w','n','e','r'], ['o','b','s','e','r','v','e','s'], ['o','r','d','e','r'], ['o','n','l','i','n','e'], ['o','f','f','l','i','n','e'], ['o','f','f','s','e','t','_','i','n','t','o'], ['o','p','t','i','o','n'], ['o','r'], ['o','u','t'], ['o','f'], ['o','b','s','e','r','v','e','d'], ['o','c','c','u','p','i','e','d']]
  | 'p' => [['p','u','b'], ['p','r','i','m'], ['p','u','b','l','i','s','h','e','s'], ['p','u','r','e'], ['p','r','o','g','r','e','s','s'], ['p','e','r','_','p','a','s','s'], ['p','t','r'], ['p','a','y','l','o','a','d'], ['p','r','o','f','i','l','e'], ['p','r','o','t','e','c','t','s'], ['p','r','e','s','e','r','v','e','s'], ['p','e','r'], ['p','o','r','t'], ['p','a','r','e','n','t'], ['p','b']]
  | 'q' => [['q','u','e','u','e']]
  | 'r' => [['r','a','w'], ['r','e','q','u','i','r','e','s'], ['r','e','f','i','n','e','s'], ['r','e','a','d','s'], ['r','e','t','r','y'], ['r','e','t','u','r','n'], ['r','e','m','o','v','e'], ['r','e','l','a','b','e','l'], ['r','e','s','u','l','t'], ['r','e','t','u','r','n','s'], ['r'], ['r','w'], ['r','o','u','n','d','i','n','g'], ['r','e','s','e','t'], ['r','e','a','s','o','n'], ['r','e','g'], ['r','c'], ['r','c','u'], ['r','e','c','l','a','i','m','s'], ['r','a','n','k'], ['r','e','t','i','r','e','s'], ['r','e','s','e','r','v','e','d'], ['r','u','n','s'], ['r','e','l','e','a','s','e'], ['r','e','l','a','x','e','d'], ['r','e','g','s'], ['r','e','a','c','h','e','s'], ['r','o','u','n','d','e','d']]
  | 's' => [['s','t','a','t','i','c'], ['s','p','e','c'], ['s','p','a','c','e'], ['s','e','c','t','i','o','n'], ['s','l','o','t'], ['s','t','a','t','e'], ['s','t','r','i','d','e'], ['s','e','q'], ['s','h','a','r','e','d'], ['s','c','a','l','e'], ['s','y','s','c','a','l','l'], ['s','t','a','c','k'], ['s','t','e','p'], ['s','l','o','t','s'], ['s','i','b','l','i','n','g'], ['s','i','z','e','o','f']]
  | 't' => [['t','y','p','e'], ['t','a','g','g','e','d'], ['t','o'], ['t','r','a','v','e','r','s','e'], ['t','o','u','c','h','e','s'], ['t','r','a','n','s','l','a','t','o','r'], ['t','a','b','l','e'], ['t','r','a','n','s','i','t','i','o','n'], ['t','r','e','e'], ['t','h','r','e','a','d','s'], ['t','r','u','e'], ['t','a','r','g','e','t']]
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

/-- `strEq` through the native comparison, for compiled code. -/
def strEqSchnell (a b : String) : Bool := decide (a = b)

/-- **The native comparison answers as the character lists do.** The kernel keeps `strEq`. -/
@[csimp] theorem strEq_eq_schnell : @strEq = @strEqSchnell := by
  funext a b
  unfold strEq strEqSchnell
  by_cases h : a = b
  · subst h
    simp only [BEq.rfl, decide_true]
  · have differ : a.toList ≠ b.toList := fun e => h (String.toList_inj.1 e)
    rw [beq_eq_false_iff_ne.2 differ]
    simp only [h, decide_false]

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
  | '?' => true
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

/-- Read one ASCII byte after an opening apostrophe, including its closer.
    Character literals are numeric sugar; no character token is introduced. -/
def takeCharacter : List Char → Option (Nat × List Char)
  | '\\' :: c :: '\'' :: rest =>
    let value := match c with
      | 'n' => some 10
      | 't' => some 9
      | 'r' => some 13
      | '0' => some 0
      | '\\' => some 92
      | '\'' => some 39
      | _ => none
    value.map (fun n => (n, rest))
  | c :: '\'' :: rest =>
    if 32 ≤ c.toNat && c.toNat ≤ 126 && c != '\'' && c != '\\' then
      some (c.toNat, rest)
    else none
  | _ => none

/-- Cut a line comment body: the text up to (not including) the newline,
    and the rest starting at the newline (or empty). -/
def nimmZeile : List Char → List Char × List Char
  | [] => ([], [])
  | '\n' :: cs => ([], '\n' :: cs)
  | c :: cs => let (h, t) := nimmZeile cs; (c :: h, t)

/-- Skip a block comment body after its opening `/*`. The first argument is
    the nesting depth still open (the depth counter): `/*` opens one more,
    `*/` closes one, and the comment ends when the depth reaches 0. `none`
    means the text ended inside the comment. Every step consumes a
    character, so the recursion is structural. -/
def ueberBlock : Nat → List Char → Option (List Char)
  | 0, rest => some rest
  | _ + 1, [] => none
  | d + 1, '/' :: '*' :: cs => ueberBlock (d + 2) cs
  | d + 1, '*' :: '/' :: cs => ueberBlock d cs
  | d + 1, _ :: cs => ueberBlock (d + 1) cs

/-- The non-nesting variant, kept ONLY as the planted defect of
    `ueberBlock_verschachtelt_flach`: it ends at the first `*/`. -/
def ueberBlockFlach : List Char → Option (List Char)
  | [] => none
  | '*' :: '/' :: cs => some cs
  | _ :: cs => ueberBlockFlach cs

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
  | v, [] => .ok (Token.num v, [])
  | v, c :: cs =>
    if istAnfang c || istZiffer c then
      .error (.unbekannt "letter in number")
    else .ok (Token.num v, c :: cs)

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
        .ok (Token.float (toString v ++ "." ++ String.ofList nach ++ exp),
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
def scan (mitDoku : Bool) : List Char → Nat → Except LexFehler (List Token)
  | [], _ => .ok [Token.ende]
  | '/' :: '/' :: '/' :: '/' :: rest, n + 1 => scan mitDoku (nimmZeile rest).2 n
  | '/' :: '/' :: '/' :: rest, n + 1 =>
    let (text, rest') := nimmZeile rest
    if mitDoku then
      Except.map (Token.doku (String.ofList text) :: ·) (scan mitDoku rest' n)
    else scan mitDoku rest' n
  | '/' :: '/' :: rest, n + 1 => scan mitDoku (nimmZeile rest).2 n
  | '/' :: '*' :: rest, n + 1 =>
    match ueberBlock 1 rest with
    | some rest' => scan mitDoku rest' n
    | none => .error .offenerKommentar
  | '"' :: rest, n + 1 =>
    match nimmText rest with
    | some (inhalt, rest') =>
      Except.map (Token.text (String.ofList inhalt) :: ·) (scan mitDoku rest' n)
    | none => .error .offeneZeichenkette
  | c :: cs, n + 1 =>
    if istLeer c then scan mitDoku cs n
    else if istZiffer c then match scanZahlKopf (c :: cs) with
      | .ok (t, rest) => Except.map (t :: ·) (scan mitDoku rest n)
      | .error e => .error e
    else if istAnfang c then
      let (h, t) := nimmFolge cs
      let s := String.ofList (c :: h)
      let tok := if istSchluessel s then Token.wort s else Token.ident s
      Except.map (tok :: ·) (scan mitDoku t n)
    else match nimmZeichen (c :: cs) with
      | some (s, rest) =>
        Except.map (Token.zeichen s :: ·) (scan mitDoku rest n)
      | none =>
        if c == '\'' then match takeCharacter cs with
          | some (value, rest) => Except.map (Token.num value :: ·) (scan mitDoku rest n)
          | none => .error (.unbekannt "invalid character literal")
        else .error (.unbekannt (String.ofList [c]))
  | _ :: _, 0 => .error (.unbekannt "out of fuel")

/-- The lexer: `lex.rs` `zerlege` as a total Lean function. The one
    difference in shape: Rust accumulates refusals and still emits a
    (partial) token stream, while `lex` returns the FIRST error --
    a certificate starts from source text that lexes cleanly, so the
    partial stream has no reader here. -/
def lex (s : String) : Except LexFehler (List Token) :=
  scan false s.toList (s.length + 1)

/-- The same scan with the doc comments kept as `Token.doku` trivia, in
    source position. Tools (documentation, the formatter) read this; the
    parser reads `lex`, which is this stream without the `doku` tokens. -/
def lexDoku (s : String) : Except LexFehler (List Token) :=
  scan true s.toList (s.length + 1)

/-- **The same lexer, over the CHARACTERS**: `scan` is what `lex` runs;
    the only difference is who converts. It exists for the kernel, not
    for the reader -- see `lex_ofList` and the cost note in the CUTS. -/
def lexL (cs : List Char) : Except LexFehler (List Token) :=
  scan false cs (cs.length + 1)

/-- **`lex` OF A SOURCE PINNED AS CHARACTERS IS `lexL` OF THEM** -- the
    one step that keeps the chain files inside ordinary memory (O13).

    In Lean 4.33 a `String` is a UTF-8 byte array, `String.toList` is
    `(s.toByteArray.utf8Decode?.get _).toList`, and `String.length` is
    a second pass over the same bytes. `.get` forces the WHOLE decode,
    so asking the kernel for the FIRST character of a long literal
    costs what the whole text costs: measured 2026-09-15 on
    `ki-pc-fisch-101`, Lean 4.33.1, a 1419-byte ASCII literal needs
    **17,8 GB and 95 s** for `(s.toList).isEmpty = false` alone, and
    the growth is about `n^1.9` -- the 2064-byte chain source is past
    30 GB before the lexer has seen a token.

    The same text as a `List Char` of short `"…".toList` pieces costs
    **1,5 GB and 8,5 s** FULLY forced. So a chain pins its source as
    pieces and defines the `String` as `String.ofList` of them; this
    theorem carries the pin across, and it is a REWRITE, not a kernel
    reduction: `String.toList_ofList` and `String.length_ofList` are
    core lemmas, so the decoder is never run at all. Nothing is
    weakened -- `src` still IS the text, character for character, and
    a guardian (`zaehle-kette.py`) still compares the pieces against
    the file byte for byte. -/
theorem lex_ofList (l : List Char) : lex (String.ofList l) = lexL l := by
  unfold lex lexL
  rw [String.toList_ofList, String.length_ofList]

end Gabbro.Grammatik.Parser
