module

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- The forms of `ext` (below): predicates and the expression forms outside the printable core.
    Layout of `ext k names subs`:
    * `all`/`any`/`count`: `names = [x, domain kind] ++ domain names`, `subs = domain operands ++ [body]`
      (`forall x in D : p`, `exists x in D : p`, `count x in D : p`);
    * `mem`: `names = [domain kind] ++ domain names`, `subs = [e] ++ domain operands` (`e in D`);
    * `reach`: `names = [field]`, `subs = [a, b]` (`a reaches b via field`);
    * `imp`: `subs = [a, b]` (`a => b`);
    * `text`: `names = [s]` (a string literal);
    * `call`: `subs = callee :: args` (a call through a place, `v->f(x)`). -/
inductive XKind
  | all | any | count | mem | reach | imp | text | call
  /-- One labelled call argument: `names = [label]`, `subs = [value]`. -/
  | label
  /-- Producer: names = [spec], subs = [payload]. -/
  | dyn
  /-- Explicit instantiation: `names = callee :: argument spellings`, `subs = call arguments`.
      Argument spellings are balanced token groups, interpreted by the declared parameter kind. -/
  | instantiate
  /-- Folds: binder/domain names; domain operands, filter, value, optional empty value. -/
  | foldAdd | foldMin | foldMax | foldAnd | foldOr
  /-- Ordered array literal elements; names are empty. -/
  | array
  deriving DecidableEq, Repr

def beqWorte : List String → List String → Bool
  | [], [] => true
  | x :: xs, y :: ys => strEq x y && beqWorte xs ys
  | _, _ => false

/-- A surface expression: SYNTAX.md section 4 `expr` without types,
    spans or sugar resolution. Operators ride as their spelling
    (`bin "+%"`), so the precedence table stays one function.
    Against `ast.rs` `ExprArt`: `Zahl/Wahr/Falsch/Ort/Ruf/Grund`
    carry over (spans dropped); `Some(x)`/`None` stay calls
    (`ruf "Some" [x]`, `ruf "None" []`, as `parse.rs` builds them);
    `FnWert` is `fnref` with the path text; `Eingebaut` is
    `built` with the head word and the argument expressions;
    `Klammer` vanishes (the printer re-parenthesises); counting uses `ext count`,
    array literals use `ext array [] elements`; library calls are statement forms. -/
inductive SExpr
  | lit : Nat → SExpr
  | float : String → SExpr
  | tru : SExpr
  | fls : SExpr
  | «variable» : String → SExpr
  | field : SExpr → String → SExpr
  | index : SExpr → SExpr → SExpr
  | arrow : SExpr → String → SExpr
  | un : String → SExpr → SExpr
  | bin : String → SExpr → SExpr → SExpr
  | call : String → List SExpr → SExpr
  | fnref : String → SExpr
  | built : String → List SExpr → SExpr
  | old : SExpr → SExpr
  | res : SExpr
  | why : String → String → SExpr
  /-- Extended forms, including ordered arrays (layout at `XKind`). The token printer
      spells them separately from the printable scalar core (`gut`). -/
  | ext : XKind → List String → List SExpr → SExpr
  deriving Repr

-- Structural equality on surface trees, as a `Bool`: core Lean
-- derives no `DecidableEq` through the `List SExpr` field, and the
-- agreement probes compare shapes by kernel evaluation.
mutual
def beqSExpr : SExpr → SExpr → Bool
  | .lit m, .lit n => m == n
  | .float a, .float b => strEq a b
  | .tru, .tru => true
  | .fls, .fls => true
  | .variable a, .variable b => strEq a b
  | .field x f, .field y g => beqSExpr x y && strEq f g
  | .index x i, .index y j => beqSExpr x y && beqSExpr i j
  | .arrow x f, .arrow y g => beqSExpr x y && strEq f g
  | .un o x, .un p y => strEq o p && beqSExpr x y
  | .bin o x1 x2, .bin p y1 y2 =>
    strEq o p && beqSExpr x1 y1 && beqSExpr x2 y2
  | .call f a, .call g b => strEq f g && beqSExprList a b
  | .fnref f, .fnref g => strEq f g
  | .built f a, .built g b => strEq f g && beqSExprList a b
  | .old x, .old y => beqSExpr x y
  | .res, .res => true
  | .why g1 f1, .why g2 f2 => strEq g1 g2 && strEq f1 f2
  | .ext k a x, .ext l b y => decide (k = l) && beqWorte a b && beqSExprList x y
  | _, _ => false
def beqSExprList : List SExpr → List SExpr → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSExpr x y && beqSExprList xs ys
  | _, _ => false
end

/-- One token as raw text (for unsplit headers). -/
def zeigeTok : Token → String
  | .ident s => s
  | .wort s => s
  | .num n => toString n
  | .float s => s
  | .text s => String.ofList ('"' :: (druckTextZeichen s.toList ++ ['"']))
  | .zeichen s => s
  | .doku s => "///" ++ s
  | .ende => "<ende>"

/-- A name token (identifier or contextual keyword) with its text.
    `parse.rs` `erwarte_ident` takes the same two token shapes. -/
def nameText : Token → Option String
  | .ident s => some s
  | .wort s => some s
  | _ => none

/-- Words that never start a place: the reserved words without a
    dedicated primary arm and without `Self` (`parse.rs` reads
    `Self.slots[s]` as a place, and `old` stays a bare name outside
    `old(`). `true`/`false`/`Some`/`None`/`sizeof`/`lenof`/
    `aligned`/`result` never reach here except malformed, and are
    refused rather than misread as names. -/
def keinPlatzTafel : List (List Char) :=
  [['f','o','r','a','l','l'], ['e','x','i','s','t','s'], ['c','o','n','s','t'], ['s','t','a','t','i','c'], ['e','x','t','e','r','n'], ['i','f'], ['e','l','s','e'], ['r','e','t','u','r','n'], ['b','o','o','l'], ['s','i','z','e','o','f'], ['l','e','n','o','f'], ['a','l','i','g','n','e','d']]

def istKeinPlatz (s : String) : Bool :=
  keinPlatzTafel.contains s.toList

/-- Words that name a type, never a place: refused as `sizeof` /
    `lenof` arguments (`parse.rs` `typ_oder_ort` reads a type there,
    and this parser has no `typeexpr` reader). -/
def typWortTafel : List (List Char) :=
  [['u','8'], ['u','1','6'], ['u','3','2'], ['u','6','4'], ['i','8'], ['i','1','6'], ['i','3','2'], ['i','6','4'], ['b','o','o','l'], ['n','e','v','e','r'], ['p','t','r'], ['f','n']]

def istTypWort (s : String) : Bool :=
  typWortTafel.contains s.toList

/-- The eight standard integer words: `parse.rs` reads `u64::max`
    as a place and `u64(x)` as a conversion, never as a `Grund`. -/
def intWortTafel : List (List Char) :=
  [['u','8'], ['u','1','6'], ['u','3','2'], ['u','6','4'], ['i','8'], ['i','1','6'], ['i','3','2'], ['i','6','4']]

def istIntWort (s : String) : Bool :=
  intWortTafel.contains s.toList

/-- A sugared width (`u13`, `i37`): identifier head, `u`/`i` plus
    digits for `1 .. 64` (PLAN-BITS section 1; `u0(a)` stays a call
    to the name `u0`, as in `parse.rs` `zuckerbreite`). -/
def istZuckerBreite (s : String) : Bool :=
  match s.toList with
  | 'u' :: d :: ds => zuckerZahl (d :: ds)
  | 'i' :: d :: ds => zuckerZahl (d :: ds)
  | _ => false
where
  zuckerZahl : List Char → Bool
    | [] => false
    | ds =>
      -- The number is read off the DIGITS: `String.ofList ds |>.toNat?` would make the kernel
      -- decode a `String` (O13, measured 2026-09-30: `u13::max` in a probe took > 4 GB).
      ds.all istZiffer &&
      (let n := ds.foldl (fun a c => 10 * a + (c.toNat - 48)) 0
       1 ≤ n && n ≤ 64)

/-- One spelled operator of the `||` level. -/
def opOder : List Token → Option (List Token)
  | .zeichen "||" :: rest => some rest
  | _ => none

/-- One spelled operator of the `&&` level. -/
def opUnd : List Token → Option (List Token)
  | .zeichen "&&" :: rest => some rest
  | _ => none

/-- The single comparison (`cmpexpr` takes at most one). -/
def opVgl : List Token → Option (String × List Token)
  | .zeichen "==" :: rest => some ("==", rest)
  | .zeichen "!=" :: rest => some ("!=", rest)
  | .zeichen "<=" :: rest => some ("<=", rest)
  | .zeichen ">=" :: rest => some (">=", rest)
  | .zeichen "<" :: rest => some ("<", rest)
  | .zeichen ">" :: rest => some (">", rest)
  | _ => none

/-- One spelled operator of the `bitexpr` level (`<<%` rides with
    the shifts, PLAN-BITS section 4). -/
def opBit : List Token → Option (String × List Token)
  | .zeichen "&" :: rest => some ("&", rest)
  | .zeichen "|" :: rest => some ("|", rest)
  | .zeichen "^" :: rest => some ("^", rest)
  | .zeichen "<<" :: rest => some ("<<", rest)
  | .zeichen ">>" :: rest => some (">>", rest)
  | .zeichen "<<%" :: rest => some ("<<%", rest)
  | _ => none

/-- One spelled operator of the `addexpr` level (`+%`, `-%` and
    `+|` ride with `+`/`-`). -/
def opAdd : List Token → Option (String × List Token)
  | .zeichen "+" :: rest => some ("+", rest)
  | .zeichen "-" :: rest => some ("-", rest)
  | .zeichen "+%" :: rest => some ("+%", rest)
  | .zeichen "-%" :: rest => some ("-%", rest)
  | .zeichen "+|" :: rest => some ("+|", rest)
  | _ => none

/-- One spelled operator of the `mulexpr` level (`*%` rides
    with `*`). -/
def opMul : List Token → Option (String × List Token)
  | .zeichen "*" :: rest => some ("*", rest)
  | .zeichen "/" :: rest => some ("/", rest)
  | .zeichen "%" :: rest => some ("%", rest)
  | .zeichen "*%" :: rest => some ("*%", rest)
  | _ => none

/-- One `::` segment run after a head name (pure: no fuel needed).
    Stops before the first non-`::` token, leaving it. -/
def sammleSegmente : List Token → List String → List String × List Token
  | .zeichen "::" :: t :: rest, acc => match nameText t with
    | some s => sammleSegmente rest (acc ++ [s])
    | none => (acc, .zeichen "::" :: t :: rest)
  | toks, acc => (acc, toks)

/-- Dispatch a generic call, an ordinary call, or the unchanged name tail.
    Constructor-only patterns keep delimiter tests available to rewriting. -/
def rufKopf {α : Type} (toks : List Token)
    (generic call : List Token → α) (other : Unit → α) : α :=
  match toks with
  | .zeichen s :: rest =>
    if strEq s "::" then
      match rest with
      | .zeichen t :: tail => if strEq t "[" then generic tail else other ()
      | _ => other ()
    else if strEq s "(" then call rest else other ()
  | _ => other ()

theorem strEq_paren_doppelpunkt : strEq "(" "::" = false := by decide
theorem strEq_paren_paren : strEq "(" "(" = true := by decide
theorem strEq_paren_gleich : strEq "(" "=" = false := by decide
theorem strEq_paren_plusgleich : strEq "(" "+=" = false := by decide
theorem strEq_paren_minusgleich : strEq "(" "-=" = false := by decide
theorem strEq_paren_undgleich : strEq "(" "&=" = false := by decide
theorem strEq_paren_odergleich : strEq "(" "|=" = false := by decide
theorem strEq_doppelpunkt_gleich : strEq "::" "=" = false := by decide
theorem strEq_doppelpunkt_plusgleich : strEq "::" "+=" = false := by decide
theorem strEq_doppelpunkt_minusgleich : strEq "::" "-=" = false := by decide
theorem strEq_doppelpunkt_undgleich : strEq "::" "&=" = false := by decide
theorem strEq_doppelpunkt_odergleich : strEq "::" "|=" = false := by decide


-- The expression levels of SYNTAX.md section 4 (`expr` down to
-- `primary`), each with fuel: every call passes strictly less fuel,
-- so the block terminates by `f`. Against `parse.rs`: the level
-- order, the single comparison, the flat bit level and the riding
-- overflow operators match one by one.
/-- A numeral: `-<numeral>` is a negative literal, `-(<numeral>)` the negation of a literal (`.un "-()"`). -/
def istLit : SExpr → Bool
  | .lit _ => true
  | _ => false

end Gabbro.Grammatik.Parser
