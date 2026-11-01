module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs

@[expose] public section



namespace Gabbro.Grammatik.Parser

/-- String equality through character lists is sound: equal lists
    mean equal strings (`String.ofList_toList` round-trips). -/
theorem strKlingt : ∀ (a b : String), strEq a b = true → a = b := by
  intro a b h
  unfold strEq at h
  have h2 : a.toList = b.toList := beq_iff_eq.mp h
  have h3 := congrArg String.ofList h2
  rwa [String.ofList_toList, String.ofList_toList] at h3

/-- `strEq` as an iff, for rewriting inside `beqSExpr` hypotheses. -/
theorem strEq_eq (a b : String) : strEq a b = true ↔ a = b :=
  ⟨strKlingt a b, by intro h; subst h; exact beq_self_eq_true _⟩

/-- Word-list equality is sound. -/
theorem beqWorte_klingt : ∀ (a b : List String), beqWorte a b = true → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b <;> simp only [beqWorte, Bool.false_eq_true] at h ⊢
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp only [beqWorte, Bool.false_eq_true] at h
    | cons y ys =>
      simp only [beqWorte, Bool.and_eq_true, strEq_eq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, ih _ h2]

-- Soundness of the structural equality on surface trees, with its
-- list helper: a `true` comparison means Leibniz equality. Proved
-- mutually, following the recursion of `beqSExpr` itself. Each arm
-- cases on the second tree: mismatched pairs (hypothesis reduced to
-- `false = true`) die by contradiction, matching pairs substitute
-- the lawful comparisons (`beq_iff_eq`, `strEq_eq`) and rewrite the
-- recursive subterms by the induction hypotheses on strict
-- subterms. (`simp only` cannot apply those hypotheses itself: a
-- bare implication `beqSExpr a b = true -> a = b` is no rewrite
-- rule -- measured 2026-09-13 -- so every recursive step is an
-- explicit term.)
mutual
theorem beqSExpr_klingt : ∀ (a b : SExpr),
    beqSExpr a b = true → a = b := by
  intro a b h
  cases a with
  | lit m =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [beq_iff_eq] at h; exact congrArg SExpr.lit h)
  | float s =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [strEq_eq] at h; exact congrArg SExpr.float h)
  | tru =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | fls =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | «variable» s =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [strEq_eq] at h; exact congrArg SExpr.variable h)
  | field x f =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := beqSExpr_klingt _ _ h1
    rw [e1, h2]
  | index x i =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := beqSExpr_klingt _ _ h1
    have e2 := beqSExpr_klingt _ _ h2
    rw [e1, e2]
  | arrow x f =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := beqSExpr_klingt _ _ h1
    rw [e1, h2]
  | un o x =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have e2 := beqSExpr_klingt _ _ h2
    rw [h1, e2]
  | bin o x1 x2 =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq, and_assoc] at h
    obtain ⟨ho, h1, h2⟩ := h
    have e1 := beqSExpr_klingt _ _ h1
    have e2 := beqSExpr_klingt _ _ h2
    rw [ho, e1, e2]
  | call f xs =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨hs, hl⟩ := h
    have el := beqSExprList_klingt _ _ hl
    rw [hs, el]
  | fnref f =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [strEq_eq] at h; exact congrArg SExpr.fnref h)
  | built f xs =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨hs, hl⟩ := h
    have el := beqSExprList_klingt _ _ hl
    rw [hs, el]
  | old x =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (rw [beqSExpr_klingt x _ h])
  | res =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | why g f =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
  | ext k ns xs =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, beqWorte_klingt _ _ h2, beqSExprList_klingt _ _ h3]
theorem beqSExprList_klingt : ∀ (xs ys : List SExpr),
    beqSExprList xs ys = true → xs = ys := by
  intro xs ys h
  cases xs with
  | nil =>
    cases ys <;> simp only [beqSExprList] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | cons x xs =>
    cases ys <;> simp only [beqSExprList] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := beqSExpr_klingt _ _ h1
    have e2 := beqSExprList_klingt _ _ h2
    rw [e1, e2]
end

/-- Soundness on whole-expression outcomes: equal shapes mean equal
    trees (errors are compared by name, as in `beqTop`). -/
theorem beqTop_klingt : ∀ (a b : SExpr),
    beqTop (.ok a) (.ok b) = true → a = b := by
  intro a b h
  unfold beqTop at h
  exact beqSExpr_klingt a b h

-- The tree size: leaves count 1, every node adds its children.
-- The fuel bound `brennstoff` scales with it (see `parse_druck`).
mutual
def groesse : SExpr → Nat
  | .lit _ => 1
  | .float _ => 1
  | .tru => 1
  | .fls => 1
  | .variable _ => 1
  | .field x _ => groesse x + 1
  | .index x i => groesse x + groesse i + 1
  | .arrow x _ => groesse x + 1
  | .un _ x => groesse x + 1
  | .bin _ l r => groesse l + groesse r + 1
  | .call _ xs => groesseListe xs + 1
  | .fnref _ => 1
  | .built _ xs => groesseListe xs + 1
  | .old x => groesse x + 1
  | .res => 1
  | .why _ _ => 1
  | .ext _ _ xs => groesseListe xs + 1
def groesseListe : List SExpr → Nat
  | [] => 0
  | x :: xs => groesse x + groesseListe xs
end

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
where
  druckQuant (w : String) (ns : List String) (ts : List (List Token)) : List Token :=
    match ns, ts.reverse with
    | x :: dk :: ds, body :: opsRev =>
      [.zeichen "(", .wort w, nameTok x, .wort "in"] ++ domToks dk ds opsRev.reverse ++
        [.zeichen ":"] ++ body ++ [.zeichen ")"]
    | _, _ => [.ende]

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
  · split <;> simp only [ne_eq, List.cons_ne_self, not_false_eq_true]
  · split <;> simp only [List.append_assoc, List.cons_append, List.nil_append, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.cons_ne_self]

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
    [.wort f, .zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]
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
   ['t','r','a','n','s','i','t','i','o','n']]

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
