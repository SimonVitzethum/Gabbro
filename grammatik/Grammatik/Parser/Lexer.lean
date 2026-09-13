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

/-- The lexer (stub in this step: the scanner lands next). -/
def lex (_ : String) : Except LexFehler (List Token) :=
  .ok [Token.ende]

end Gabbro.Grammatik.Parser
