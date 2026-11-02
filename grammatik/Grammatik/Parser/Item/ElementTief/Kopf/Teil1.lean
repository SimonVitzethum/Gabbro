module

public import Grammatik.Parser.Stmt.Anweisung

@[expose] public section



namespace Gabbro.Grammatik.Parser

/-- The pure prefix words before an item head (`parse.rs` `item`:
    `pub` plus the `fn`/`type` modifiers; `const` is NOT among them
    -- `const fn` splits on the next word, as in `parse.rs`). -/
def istMod (s : String) : Bool :=
  ["library", "spec", "impl", "raw", "divergent", "prim", "extern",
   "opaque", "linear", "ghost", "tagged"].any (strEq · s)

set_option maxRecDepth 100000

/- A surface effect: one arm of SYNTAX.md section 6 `eff`
    (`efflist`), the place arms as `SExpr` (`parse.rs` reads them
    as places; this reader has no `pred` reader, so contracts ride
    `SExpr` too -- see CUTS). `locks` carries the `shared` flag. -/
inductive SEffekt
  | reads : SExpr → SEffekt
  | writes : SExpr → SEffekt
  | locks : Bool → SExpr → SEffekt
  | masks : String → SEffekt
  | allocs : String → SEffekt
  | takes : SExpr → SEffekt
  | posts : SExpr → SEffekt
  | loops : SEffekt
  | pure : SEffekt
  | param : String → SEffekt
  | instanceEffects : String → List STyp → SEffekt
  deriving Repr

mutual
def beqSEffekt : SEffekt → SEffekt → Bool
  | .reads a, .reads b => beqSExpr a b
  | .writes a, .writes b => beqSExpr a b
  | .locks x a, .locks y b => (x == y) && beqSExpr a b
  | .masks a, .masks b => strEq a b
  | .allocs a, .allocs b => strEq a b
  | .takes a, .takes b => beqSExpr a b
  | .posts a, .posts b => beqSExpr a b
  | .loops, .loops => true
  | .pure, .pure => true
  | .param a, .param b => strEq a b
  | .instanceEffects a ts, .instanceEffects b us => strEq a b && beqSTypList ts us
  | _, _ => false
def beqSEffektList : List SEffekt → List SEffekt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSEffekt x y && beqSEffektList xs ys
  | _, _ => false
end

/- One contract clause of SYNTAX.md section 6 `fndecl`: `voraus`
    and `gives` ride one `SExpr` each (a `pred` is an `expr`
    shape here -- no `pred` reader, see CUTS); `erhaelt` and
    `refs` ride name lists; `kosten` the `<= e ops`
    expression; `faellt` the `decreases` measure; `induktion` the
    raw `by` tail; `nutzlast` the `payload` path; `part` the
    `section` text; `arch` the `arch` name; `moves`
    the `advances a -> b` pair; `quits` the raw `retires`
    tail; `frist` the raw `deadline` tail (both raw tails are
    delimited, not interpreted -- see CUTS). -/
inductive SKlausel
  | needs : SExpr → SKlausel
  | gives : SExpr → SKlausel
  | keeps : List String → SKlausel
  | refs : List String → SKlausel
  | cost : SExpr → SKlausel
  | drops : SExpr → SKlausel
  | induc : String → SKlausel
  | load : List String → SKlausel
  | part : String → SKlausel
  | arch : String → SKlausel
  | moves : String → String → SKlausel
  | quits : String → SKlausel
  | limit : String → SKlausel
  | effs : List SEffekt → SKlausel
  deriving Repr

mutual
def beqSKlausel : SKlausel → SKlausel → Bool
  | .needs a, .needs b => beqSExpr a b
  | .gives a, .gives b => beqSExpr a b
  | .keeps a, .keeps b => beqWorte a b
  | .refs a, .refs b => beqWorte a b
  | .cost a, .cost b => beqSExpr a b
  | .drops a, .drops b => beqSExpr a b
  | .induc a, .induc b => strEq a b
  | .load a, .load b => beqWorte a b
  | .part a, .part b => strEq a b
  | .arch a, .arch b => strEq a b
  | .moves a b, .moves c d => strEq a c && strEq b d
  | .quits a, .quits b => strEq a b
  | .limit a, .limit b => strEq a b
  | .effs a, .effs b => beqSEffektList a b
  | _, _ => false
def beqSKlauselList : List SKlausel → List SKlausel → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSKlausel x y && beqSKlauselList xs ys
  | _, _ => false
end

/- A function head: SYNTAX.md section 6 `fndecl` up to the body.
    `art` is the modifier word (`impl`, `spec`, `library`,
    `const`, `raw`, `divergent`, `prim`, `extern`, else `""` for a
    plain `fn`); `fehler` the `or R` channel; `klauseln` every
    contract clause in source order. The body rides outside
    (`fnT`/`protoT`/`specT`/`asmT` below). -/
structure FnSig where
  art : String
  name : String
  params : List (String × STyp)
  res : Option STyp
  fehler : Option String
  klauseln : List SKlausel
  deriving Repr

def beqParam : (String × STyp) → (String × STyp) → Bool
  | (a, x), (b, y) => strEq a b && beqSTyp x y

def beqParamList : List (String × STyp) → List (String × STyp) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqParam x y && beqParamList xs ys
  | _, _ => false

def beqFnSig : FnSig → FnSig → Bool
  | s, t => strEq s.art t.art && strEq s.name t.name &&
    beqParamList s.params t.params && beqSTypOpt s.res t.res &&
    beqOptWort s.fehler t.fehler && beqSKlauselList s.klauseln t.klauseln

/-- Structural equality of a spec's function signatures. -/
def beqFnSigs : List FnSig → List FnSig → Bool
  | [], [] => true
  | s :: ss, t :: ts => beqFnSig s t && beqFnSigs ss ts
  | _, _ => false

end Gabbro.Grammatik.Parser
