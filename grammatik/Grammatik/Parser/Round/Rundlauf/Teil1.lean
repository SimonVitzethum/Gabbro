module

public import Grammatik.Parser.Round.Rundlauf.Teil1a
public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs

@[expose] public section



namespace Gabbro.Grammatik.Parser

/-- Fuel for the round trip: twelve per node, one spare per
    node, eight over the top. Each parser level strips one fuel
    per descent (seven levels from `parseOr` to `parsePrimary`,
    one more for the loop or the argument reader); each AST depth
    level costs at most twelve, and every subexpression is
    smaller -- so `omega` closes every fuel side-goal from the
    size equations. (Measured 2026-09-14, lane 172: the bare
    `12 * (groesse e + 1)` never fits the `RKern` Or-bound --
    thirteen fuel per size unit are needed, twelve given -- so
    the `+ groesse e + 8` rides here and not in the theorem.
    Nothing proved about the old value: `brennstoff` occurred in
    no proof, only in comments.) -/
def brennstoff (e : SExpr) : Nat :=
  12 * (groesse e + 1) + groesse e + 8

/-- A name as the token the lexer reads for it: a table word is a `wort`, every other name an
    `ident`. The readers take both through `nameText`; printing the lexer's token makes every printed
    list the one its rendered text lexes to. -/
def nameTok (s : String) : Token := if istSchluessel s then .wort s else .ident s

@[simp] theorem nameText_nameTok (s : String) : nameText (nameTok s) = some s := by
  unfold nameTok; split <;> rfl

-- The token-level printer: fully parenthesised -- every binary
-- operator rides inside its own parens, so no precedence level can
-- misread the shape, and no associativity question arises. Names
-- print as `nameTok` (the lexer's token for the name): the parser
-- reads a call head, a variable or a `Grund` segment through
-- `nameText`, which takes both. `sizeof`/`lenof`/`aligned`, `old`,
-- `result`, `true`/`false` print as `wort` (their parser arms match
-- `wort` only), so a name spelled like one of the primary words is
-- outside `gut`.
/-- A `::` path as name and separator tokens. -/
def pfadToks : List String → List Token
  | [] => []
  | [a] => [nameTok a]
  | a :: rest => [nameTok a, .zeichen "::"] ++ pfadToks rest

/-- Printed operands, comma separated. -/
def kommaToks : List (List Token) → List Token
  | [] => []
  | [x] => x
  | x :: xs => x ++ [.zeichen ","] ++ kommaToks xs

/-- A `domain` (SYNTAX.md section 5) from its kind word, names and printed places: the inverse of
    `parseDomain`. -/
def domToks (dk : String) (ds : List String) (ops : List (List Token)) : List Token :=
  if strEq dk "threads" then [.wort "threads"]
  else if strEq dk "fields" then [.wort "fields", .wort "of"] ++ pfadToks ds
  else if strEq dk "chain" then
    match ds, ops with
    | [x, y], [p] =>
      [.wort "chain", .zeichen "(", nameTok x, .zeichen ",", nameTok y, .zeichen ")", .wort "in"] ++ p
    | _, _ => [.ende]
  else if strEq dk "queue" then [.wort "queue"] ++ ops.headD []
  else [.wort dk, .wort "of"] ++ ops.headD []

/-- The spelling of the `ext` forms (layout at `XKind`), from the printed sub-expressions: the predicate
    forms ride in parentheses, which `parsePredAtom` reads back through its `( pred )` arm; a string and a
    call through a place print as themselves. Outside the `gut` core, so no round-trip theorem rests on it:
    the witnesses of `Print/ExtProben` decide it per form. -/
def druckExtToks (k : XKind) (ns : List String) (ts : List (List Token)) : List Token :=
  match k with
  | .dyn => match ns, ts with
    | [spec], [payload] => [.wort "dyn"] ++
        (match lex spec with | .ok tokens => tokens.dropLast | .error _ => []) ++
        [.zeichen "("] ++ payload ++ [.zeichen ")"]
    | _, _ => [.ende]
  | .text => match ns with
    | [s] => [.text s]
    | _ => [.ende]
  | .call => match ts with
    | c :: args => c ++ [.zeichen "("] ++ kommaToks args ++ [.zeichen ")"]
    | [] => [.ende]
  | .imp => match ts with
    | [a, b] => [.zeichen "("] ++ a ++ [.zeichen "=>"] ++ b ++ [.zeichen ")"]
    | _ => [.ende]
  | .reach => match ns, ts with
    | [f], [a, b] => [.zeichen "("] ++ a ++ [.wort "reaches"] ++ b ++ [.wort "via", nameTok f, .zeichen ")"]
    | _, _ => [.ende]
  | .mem => match ns, ts with
    | dk :: ds, e :: ops => [.zeichen "("] ++ e ++ [.wort "in"] ++ domToks dk ds ops ++ [.zeichen ")"]
    | _, _ => [.ende]
  | .all => druckQuant "forall" ns ts
  | .any => druckQuant "exists" ns ts
  | .count => druckQuant "count" ns ts
  | .instantiate => match ns with
    | name :: words =>
      let raw := fun s => match lex s with
        | .ok tokens => tokens.filter (fun | .ende => false | _ => true)
        | .error _ => [.ende]
      raw name ++ [.zeichen "::", .zeichen "["] ++ kommaToks (words.map raw) ++
        [.zeichen "]", .zeichen "("] ++ kommaToks ts ++ [.zeichen ")"]
    | [] => [.ende]
  | .foldAdd => druckFold "add" ns ts
  | .foldMin => druckFold "min" ns ts
  | .foldMax => druckFold "max" ns ts
  | .foldAnd => druckFold "and" ns ts
  | .foldOr => druckFold "or" ns ts
  | .array => [.zeichen "["] ++ kommaToks ts ++ [.zeichen "]"]
  | .label => match ns, ts with
    | [name], [value] => nameTok name :: .zeichen ":" :: value
    | _, _ => [.ende]
where
  druckFold (word : String) (names : List String) (operands : List (List Token)) : List Token :=
    match names, operands with
    | [binder, "range"], [lo, hi, filter, value] =>
      [.zeichen "(", .wort word, nameTok binder, .wort "in"] ++ lo ++ [.zeichen "..<"] ++ hi ++
        [.wort "where"] ++ filter ++ [.zeichen ":"] ++ value ++ [.zeichen ")"]
    | [binder, domain], [subject, filter, value] =>
      [.zeichen "(", .wort word, nameTok binder, .wort "in"] ++ domToks domain [] [subject] ++
        [.wort "where"] ++ filter ++ [.zeichen ":"] ++ value ++ [.zeichen ")"]
    | [binder, domain], [subject, filter, value, empty] =>
      [.zeichen "(", .wort word, nameTok binder, .wort "in"] ++ domToks domain [] [subject] ++
        [.wort "where"] ++ filter ++ [.zeichen ":"] ++ value ++ [.wort "else"] ++ empty ++ [.zeichen ")"]
    | _, _ => [.ende]
  druckQuant (w : String) (ns : List String) (ts : List (List Token)) : List Token :=
    match ns, ts.reverse with
    | x :: dk :: ds, body :: opsRev =>
      [.zeichen "(", .wort w, nameTok x, .wort "in"] ++ domToks dk ds opsRev.reverse ++
        [.zeichen ":"] ++ body ++ [.zeichen ")"]
    | _, _ => [.ende]

theorem druckFold_ne_nil (word : String) (names : List String) (operands : List (List Token)) :
    druckExtToks.druckFold word names operands ≠ [] := by
  unfold druckExtToks.druckFold
  split <;> simp

theorem druckQuant_ne_nil (w : String) (ns : List String) (ts : List (List Token)) :
    druckExtToks.druckQuant w ns ts ≠ [] := by
  unfold druckExtToks.druckQuant
  split <;> simp only [List.cons_append, List.nil_append, List.append_assoc, ne_eq, reduceCtorEq, not_false_eq_true, List.cons_ne_self]

theorem druckExtToks_ne_nil (k : XKind) (ns : List String) (ts : List (List Token)) :
    druckExtToks k ns ts ≠ [] := by
  cases k <;> simp only [druckExtToks]
  · exact druckQuant_ne_nil _ _ _
  · exact druckQuant_ne_nil _ _ _
  · exact druckQuant_ne_nil _ _ _
  · split <;> simp only [List.cons_append, List.nil_append, List.append_assoc, ne_eq, reduceCtorEq, not_false_eq_true, List.cons_ne_self]
  · split <;> simp only [List.cons_append, List.nil_append, List.append_assoc, ne_eq, reduceCtorEq, not_false_eq_true, List.cons_ne_self]
  · split <;> simp only [List.cons_append, List.nil_append, List.append_assoc, ne_eq, reduceCtorEq, not_false_eq_true, List.cons_ne_self]
  · split <;> simp only [ne_eq, List.cons_ne_self, List.cons_ne_nil, not_false_eq_true]
  · split <;> simp only [List.append_assoc, List.cons_append, List.nil_append, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.cons_ne_self]
  · split <;> simp only [ne_eq, List.cons_ne_self, List.cons_ne_nil, not_false_eq_true]
  · split <;> simp only [List.cons_append, List.nil_append, ne_eq, reduceCtorEq, not_false_eq_true, List.cons_ne_self]

  · split <;> simp only [List.cons_append, List.nil_append, List.append_assoc, ne_eq,
      List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.cons_ne_self]
  · exact druckFold_ne_nil _ _ _
  · exact druckFold_ne_nil _ _ _
  · exact druckFold_ne_nil _ _ _
  · exact druckFold_ne_nil _ _ _
  · exact druckFold_ne_nil _ _ _
  · simp only [List.cons_append, List.nil_append, ne_eq, reduceCtorEq, not_false_eq_true]

mutual
def druckToks : SExpr → List Token
  | .lit n => [.num n]
  | .float s => [.float s]
  | .tru => [.wort "true"]
  | .fls => [.wort "false"]
  | .variable s => [nameTok s]
  | .field x f => druckToks x ++ [.zeichen ".", nameTok f]
  | .index x i =>
    druckToks x ++ [.zeichen "["] ++ druckToks i ++ [.zeichen "]"]
  | .arrow x f => druckToks x ++ [.zeichen "->", nameTok f]
  | .un o x =>
    if strEq o "-()" then [.zeichen "-", .zeichen "("] ++ druckToks x ++ [.zeichen ")"] else
    [.zeichen o] ++
      if istAtom x then druckToks x
      else [.zeichen "("] ++ druckToks x ++ [.zeichen ")"]
  | .bin o l r =>
    [.zeichen "("] ++ druckToks l ++ [.zeichen o] ++ druckToks r ++
      [.zeichen ")"]
  | .call f xs =>
    [nameTok f, .zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]
  | .fnref p => [.zeichen "&", nameTok p]
  | .built f xs =>
    (if strEq f "#tuple" then [] else [.wort f]) ++
      [.zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]
  | .old x =>
    [.wort "old", .zeichen "("] ++ druckToks x ++ [.zeichen ")"]
  | .res => [.wort "result"]
  | .why g f => [nameTok g, .zeichen "::", nameTok f]
  | .ext k ns xs => druckExtToks k ns (druckToksViele xs)
def druckToksViele : List SExpr → List (List Token)
  | [] => []
  | x :: xs => druckToks x :: druckToksViele xs
def druckToksListe : List SExpr → List Token
  | [] => []
  | [x] => druckToks x
  | x :: xs => druckToks x ++ [.zeichen ","] ++ druckToksListe xs
end

-- The operator groups by level, named once and shared by the
-- printability predicate (`gutOpCmp` etc. below) and the benign
-- follow (`istSchleifenOp`): one spelling list, two uses.
def istCmpOp (s : String) : Bool :=
  strEq s "==" || strEq s "!=" || strEq s "<=" ||
    strEq s ">=" || strEq s "<" || strEq s ">"
def istBitOp (s : String) : Bool :=
  strEq s "&" || strEq s "|" || strEq s "^" ||
    strEq s "<<" || strEq s ">>" || strEq s "<<%"
def istAddOp (s : String) : Bool :=
  strEq s "+" || strEq s "-" || strEq s "+%" ||
    strEq s "-%" || strEq s "+|"
def istMulOp (s : String) : Bool :=
  strEq s "*" || strEq s "/" || strEq s "%" || strEq s "*%"
@[simp] theorem strEq_bang_klammer : strEq "!" "-()" = false := by decide
@[simp] theorem strEq_minus_klammer : strEq "-" "-()" = false := by decide
@[simp] theorem strEq_tilde_klammer : strEq "~" "-()" = false := by decide

def gutOpUn (o : String) : Bool :=
  strEq o "!" || strEq o "-" || strEq o "~"
def gutOpOr (o : String) : Bool :=
  strEq o "||"
def gutOpAnd (o : String) : Bool :=
  strEq o "&&"
-- The four multi-spelling levels share the group predicates above
-- (one spelling list, two uses: printability here, benign follow
-- in `istSchleifenOp`).
def gutOpCmp := istCmpOp
def gutOpBit := istBitOp
def gutOpAdd := istAddOp
def gutOpMul := istMulOp
def gutOpBin (o : String) : Bool :=
  gutOpOr o || gutOpAnd o || gutOpCmp o ||
    gutOpBit o || gutOpAdd o || gutOpMul o

-- A bare type-word variable (`sizeof(u32)` is refused: there is
-- no `typeexpr` reader, so `parseEingebaut` rejects it where any
-- other place passes). Only bare variables are checked.
def istTypWortVar : SExpr → Bool
  | .variable s => istTypWort s
  | _ => false
/-- The words the primary reader takes by their own arm before it reads a name (`parsePrimary`):
    a name spelled like one prints as that `wort` (`nameTok`) and would read as the arm's form;
    `alloc`, which opens the allocation form after `let x =`; and `transition`, which the statement
    reader opens before any place. -/
def primWortTafel : List (List Char) :=
  [['t','r','u','e'], ['f','a','l','s','e'], ['S','o','m','e'], ['N','o','n','e'],
   ['r','e','s','u','l','t'], ['o','l','d'], ['c','o','u','n','t'], ['a','l','l','o','c'],
   ['t','r','a','n','s','i','t','i','o','n'], ['d','y','n'],
   ['a','d','d'], ['m','i','n'], ['m','a','x'], ['a','n','d'], ['o','r'],
   ['r','o','u','n','d','e','d']]

/-- A word that cannot head a printed name: refused as a place (`istKeinPlatz`) or taken by a
    primary arm (`primWortTafel`). -/
def istKopfWort (s : String) : Bool :=
  istKeinPlatz s || primWortTafel.contains s.toList

-- heads under `istKopfWort` are refused; unknown operator
-- spellings match no level; `sizeof`/`lenof` take a place through
-- `parseOrt`, `old` takes a place, `aligned` takes two whole
-- expressions and nothing else is an `built`; a `Grund` with
-- an integer, sugared-width or `Self` head reads as a field or
-- fails; suffixes attach only to place bases, so `feld`/`index`/
-- `arrow` need a `gutPlatz` base (a path of three or more segments
-- is one place head outside the printable core).
/-- A bare variable. -/
def istVar : SExpr → Bool
  | .variable _ => true
  | _ => false

end Gabbro.Grammatik.Parser
