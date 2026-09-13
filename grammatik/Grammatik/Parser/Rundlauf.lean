/-
  File:      Grammatik/Parser/Rundlauf.lean
  Subject:   T3 (lane 161): printer and general round trip by induction,
              expressions first (MUSE-REPORT-135 findings 2 and 3).

  (1) soundness of the structural equality `beqSExpr`
  (`beqSExpr a b = true -> a = b`); (2) a token-level printer
  `druckToks : SExpr -> List Token`, fully parenthesised (every
  binary operator rides inside its own parens, so no level of the
  precedence chain can misread the shape); (3) `parse_druck`: every
  printable (`gut`) expression parses back from its printed tokens
  with fuel `brennstoff e = 12 * (groesse e + 1)`, by induction
  over `e`; (4) the analogous statement for statements.

  The round trip needs a printability premise (`gut`): the parser
  is fixed, and several `SExpr` shapes have no token spelling that
  parses back (reserved head words, unknown operator spellings,
  `sizeof` over a non-place, `old` over a non-place, `Some` with
  /= 1 argument, `u64::max`-style `Grund` with an integer head,
  suffixes on non-place bases). Each is booked in CUTS.
-/
import Grammatik.Parser.Ausdruck
import Grammatik.Parser.Anweisung

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
  | gleit s =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [strEq_eq] at h; exact congrArg SExpr.gleit h)
  | wahr =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | falsch =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | «variable» s =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [strEq_eq] at h; exact congrArg SExpr.variable h)
  | feld x f =>
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
  | pfeil x f =>
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
  | ruf f xs =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨hs, hl⟩ := h
    have el := beqSExprList_klingt _ _ hl
    rw [hs, el]
  | fnwert f =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (simp only [strEq_eq] at h; exact congrArg SExpr.fnwert h)
  | eingebaut f xs =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨hs, hl⟩ := h
    have el := beqSExprList_klingt _ _ hl
    rw [hs, el]
  | alt x =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | (rw [beqSExpr_klingt x _ h])
  | ergebnis =>
    cases b <;> simp only [beqSExpr] at h <;>
      first
        | exact absurd h Bool.false_ne_true
        | exact rfl
  | grund g f =>
    cases b <;> simp only [beqSExpr] at h <;> try exact absurd h Bool.false_ne_true
    simp only [Bool.and_eq_true, strEq_eq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
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
  | .gleit _ => 1
  | .wahr => 1
  | .falsch => 1
  | .variable _ => 1
  | .feld x _ => groesse x + 1
  | .index x i => groesse x + groesse i + 1
  | .pfeil x _ => groesse x + 1
  | .un _ x => groesse x + 1
  | .bin _ l r => groesse l + groesse r + 1
  | .ruf _ xs => groesseListe xs + 1
  | .fnwert _ => 1
  | .eingebaut _ xs => groesseListe xs + 1
  | .alt x => groesse x + 1
  | .ergebnis => 1
  | .grund _ _ => 1
def groesseListe : List SExpr → Nat
  | [] => 0
  | x :: xs => groesse x + groesseListe xs
end

/-- Fuel for the round trip: twelve per node plus one row. Each
    parser level strips one fuel per descent (seven levels from
    `parseOr` to `parsePrimary`, one more for the loop or the
    argument reader, two spare); each AST depth level costs at most
    twelve, and every subexpression is smaller -- so `omega` closes
    every fuel side-goal from the size equations. -/
def brennstoff (e : SExpr) : Nat :=
  12 * (groesse e + 1)

-- The token-level printer: fully parenthesised -- every binary
-- operator rides inside its own parens, so no precedence level can
-- misread the shape, and no associativity question arises. Names
-- print as `ident` tokens (never `wort`): the parser reads a call
-- head, a variable or a `Grund` segment through `nameText`, which
-- takes both -- so even `Some`, `None`, `old` or `result` as a
-- call head parse back as a call, where the string printer's
-- `None` would lex to a keyword and need its special case.
-- `sizeof`/`lenof`/`aligned`, `old`, `result`, `true`/`false`
-- print as `wort` (their parser arms match `wort` only).
mutual
def druckToks : SExpr → List Token
  | .lit n => [.zahl n]
  | .gleit s => [.gleit s]
  | .wahr => [.wort "true"]
  | .falsch => [.wort "false"]
  | .variable s => [.ident s]
  | .feld x f => druckToks x ++ [.zeichen ".", .ident f]
  | .index x i =>
    druckToks x ++ [.zeichen "["] ++ druckToks i ++ [.zeichen "]"]
  | .pfeil x f => druckToks x ++ [.zeichen "->", .ident f]
  | .un o x =>
    [.zeichen o] ++
      if istAtom x then druckToks x
      else [.zeichen "("] ++ druckToks x ++ [.zeichen ")"]
  | .bin o l r =>
    [.zeichen "("] ++ druckToks l ++ [.zeichen o] ++ druckToks r ++
      [.zeichen ")"]
  | .ruf f xs =>
    [.ident f, .zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]
  | .fnwert p => [.zeichen "&", .ident p]
  | .eingebaut f xs =>
    [.wort f, .zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]
  | .alt x =>
    [.wort "old", .zeichen "("] ++ druckToks x ++ [.zeichen ")"]
  | .ergebnis => [.wort "result"]
  | .grund g f => [.ident g, .zeichen "::", .ident f]
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

-- Printability: the parser is fixed, and several `SExpr` shapes
-- have no token spelling that parses back (each booked in CUTS):
-- heads under `istKeinPlatz` are refused; unknown operator
-- spellings match no level; `sizeof`/`lenof` take a place through
-- `parseOrt`, `old` takes a place, `aligned` takes two whole
-- expressions and nothing else is an `eingebaut`; a `Grund` with
-- an integer, sugared-width or `Self` head reads as a field or
-- fails; suffixes attach only to place bases, so `feld`/`index`/
-- `pfeil` need a `gutPlatz` base (`grundKette` multi-segment
-- paths print as field chains and parse back through suffixes).
mutual
def gut : SExpr → Bool
  | .lit _ => true
  | .gleit _ => true
  | .wahr => true
  | .falsch => true
  | .variable s => !istKeinPlatz s
  | .feld x _ => gutPlatz x
  | .index x i => gutPlatz x && gut i
  | .pfeil x _ => gutPlatz x
  | .un o x => gutOpUn o && gut x
  | .bin o l r => gutOpBin o && gut l && gut r
  | .ruf f xs => !istKeinPlatz f && gutListe xs
  | .fnwert _ => true
  | .eingebaut "sizeof" [x] => gutPlatz x
  | .eingebaut "lenof" [x] => gutPlatz x
  | .eingebaut "aligned" [a, b] => gut a && gut b
  | .eingebaut _ _ => false
  | .alt x => gutPlatz x
  | .ergebnis => true
  | .grund g _ =>
    !istKeinPlatz g && !istIntWort g && !istZuckerBreite g &&
      !strEq g "Self"
def gutPlatz : SExpr → Bool
  | .variable s => !istKeinPlatz s
  | .feld x _ => gutPlatz x
  | .index x i => gutPlatz x && gut i
  | .pfeil x _ => gutPlatz x
  | _ => false
def gutListe : List SExpr → Bool
  | [] => true
  | x :: xs => gut x && gutListe xs
end

-- A benign parser follow: the token list starts with no loop
-- operator of any level, so every level loop (`parseOrL` etc.)
-- stops. Internal follows are `(`, `)`, `[`, `]`, `,`, `.ende`
-- and the enclosing operator (handled by its own level, never by
-- the loops below it); only the outer caller context is unknown,
-- and `ruhig` is its contract.
def istSchleifenOp (s : String) : Bool :=
  strEq s "||" || strEq s "&&" ||
    istCmpOp s || istBitOp s || istAddOp s || istMulOp s
def ruhig : List Token → Bool
  | [] => true
  | .zeichen s :: _ => !istSchleifenOp s
  | _ :: _ => true

-- A benign suffix follow: `.`, `->`, `[` and `::` continue a
-- suffix or segment chain, everything else (including every loop
-- operator) stops `parseSuffixe` and `sammleSegmente`.
def ruhigSuff : List Token → Bool
  | [] => true
  | .zeichen s :: _ =>
    !(strEq s "." || strEq s "->" || strEq s "[" || strEq s "::")
  | _ :: _ => true

-- From a false character-list comparison to the inequality (for
-- discharging the operator-table matches below).
theorem strNe_of (s w : String) (h : strEq s w = false) : s ≠ w := by
  intro e
  subst e
  simp [strEq] at h

-- A negated `true` is `false` (for unfolding `ruhig`).
theorem nichtWahr_falsch : ∀ (b : Bool), (!b) = true → b = false := by
  intro b h
  cases hfs : b <;> simp_all

-- Every operator table misses a benign follow. Each proof cases
-- on the token list: `[]` and non-`zeichen` heads miss by
-- constructor clash (`rfl`); a `zeichen s` head carries
-- `istSchleifenOp s = false`, which splits (through
-- `Bool.or_eq_false_iff`, re-associated right) into one false
-- comparison per spelling -- the needed ones become inequalities
-- (by `strNe_of`), and the table reduces by `simp`.
theorem stopOder : ∀ (t : List Token),
    ruhig t = true → opOder t = none := by
  intro t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨hOr, -, -, -, -, -⟩ := hf
      have ne := strNe_of s "||" hOr
      simp [opOder, ne]
    | ende => rfl
theorem stopUnd : ∀ (t : List Token),
    ruhig t = true → opUnd t = none := by
  intro t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, hAnd, -, -, -, -⟩ := hf
      have ne := strNe_of s "&&" hAnd
      simp [opUnd, ne]
    | ende => rfl
theorem stopVgl : ∀ (t : List Token),
    ruhig t = true → opVgl t = none := by
  intro t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, hCmp, -, -, -⟩ := hf
      simp only [istCmpOp, Bool.or_eq_false_iff, and_assoc] at hCmp
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hCmp
      have ne1 := strNe_of s "==" c1
      have ne2 := strNe_of s "!=" c2
      have ne3 := strNe_of s "<=" c3
      have ne4 := strNe_of s ">=" c4
      have ne5 := strNe_of s "<" c5
      have ne6 := strNe_of s ">" c6
      unfold opVgl
      split
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne1
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne2
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne3
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne4
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne5
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne6
      · rfl
    | ende => rfl
theorem stopBit : ∀ (t : List Token),
    ruhig t = true → opBit t = none := by
  intro t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, -, hBit, -, -⟩ := hf
      simp only [istBitOp, Bool.or_eq_false_iff, and_assoc] at hBit
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hBit
      have ne1 := strNe_of s "&" c1
      have ne2 := strNe_of s "|" c2
      have ne3 := strNe_of s "^" c3
      have ne4 := strNe_of s "<<" c4
      have ne5 := strNe_of s ">>" c5
      have ne6 := strNe_of s "<<%" c6
      unfold opBit
      split
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne1
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne2
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne3
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne4
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne5
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne6
      · rfl
    | ende => rfl
theorem stopAdd : ∀ (t : List Token),
    ruhig t = true → opAdd t = none := by
  intro t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, -, -, hAdd, -⟩ := hf
      simp only [istAddOp, Bool.or_eq_false_iff, and_assoc] at hAdd
      obtain ⟨c1, c2, c3, c4, c5⟩ := hAdd
      have ne1 := strNe_of s "+" c1
      have ne2 := strNe_of s "-" c2
      have ne3 := strNe_of s "+%" c3
      have ne4 := strNe_of s "-%" c4
      have ne5 := strNe_of s "+|" c5
      unfold opAdd
      split
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne1
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne2
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne3
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne4
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne5
      · rfl
    | ende => rfl
theorem stopMul : ∀ (t : List Token),
    ruhig t = true → opMul t = none := by
  intro t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, -, -, -, hMul⟩ := hf
      simp only [istMulOp, Bool.or_eq_false_iff, and_assoc] at hMul
      obtain ⟨c1, c2, c3, c4⟩ := hMul
      have ne1 := strNe_of s "*" c1
      have ne2 := strNe_of s "/" c2
      have ne3 := strNe_of s "%" c3
      have ne4 := strNe_of s "*%" c4
      unfold opMul
      split
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne1
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne2
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne3
      · rename_i heq
        injection heq with h1 h2
        injection h1 with h3
        exact absurd h3 ne4
      · rfl
    | ende => rfl

-- `parseSuffixe` stops on a benign suffix follow (stated with
-- successor fuel, so the fuel match reduces and only the token
-- match remains).
theorem stopSuffix : ∀ (F : Nat) (e : SExpr) (t : List Token),
    ruhigSuff t = true → parseSuffixe (F + 1) e t = .ok (e, t) := by
  intro F e t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhigSuff] at h
      have hf := nichtWahr_falsch _ h
      simp only [Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨c1, c2, c3, -⟩ := hf
      have ne1 := strNe_of s "." c1
      have ne2 := strNe_of s "->" c2
      have ne3 := strNe_of s "[" c3
      simp [parseSuffixe, ne1, ne2, ne3]
    | ende => rfl

-- A prefix operator tree is not a primary tree (the round trip
-- handles `un` at the unary level, never at the primary level).
def unFrei : SExpr → Bool
  | .un _ _ => false
  | _ => true

-- Every tree has size at least one (empties the zero case of every
-- size induction below).
theorem groesse_pos : ∀ (e : SExpr), 1 ≤ groesse e := by
  intro e
  cases e <;> simp only [groesse] at ⊢ <;> omega

-- Every printed tree is a non-empty token list (the argument-label
-- strip of `parseArg` fires only on a `name :` prefix, and the
-- empty-print case below would leave it facing the separator).
theorem toksLang : ∀ (n : Nat) (e : SExpr),
    groesse e ≤ n → 1 ≤ (druckToks e).length := by
  intro n
  induction n with
  | zero =>
    intro e hs
    have hp := groesse_pos e
    omega
  | succ n ih =>
    intro e hs
    cases e with
    | lit m => exact Nat.le_refl _
    | gleit s => exact Nat.le_refl _
    | wahr => exact Nat.le_refl _
    | falsch => exact Nat.le_refl _
    | «variable» s => exact Nat.le_refl _
    | feld x f =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | index x i =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | pfeil x f =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | un o x =>
      simp only [druckToks] at ⊢
      split
      · simp only [List.length_append, List.length] at ⊢
        have hx : groesse x ≤ n := by
          simp only [groesse] at hs
          omega
        have hlen := ih x hx
        omega
      · simp only [List.length_append, List.length] at ⊢
        omega
    | bin o l r =>
      have hl : groesse l ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih l hl
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | ruf f xs =>
      simp only [druckToks, List.length_append,
        List.length] at ⊢
      omega
    | fnwert p =>
      simp only [druckToks, List.length] at ⊢
      omega
    | eingebaut f xs =>
      simp only [druckToks, List.length_append,
        List.length] at ⊢
      omega
    | alt x =>
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have hlen := ih x hx
      simp only [druckToks, List.length_append, List.length] at ⊢
      omega
    | ergebnis => exact Nat.le_refl _
    | grund g f =>
      simp only [druckToks, List.length] at ⊢
      omega

-- An element is no bigger than its list.
theorem groesse_mem_le : ∀ (xs : List SExpr) (x : SExpr),
    x ∈ xs → groesse x ≤ groesseListe xs := by
  intro xs
  induction xs with
  | nil =>
    intro x hm
    simp at hm
  | cons y ys ih =>
    intro x hm
    simp only [List.mem_cons] at hm
    obtain hxy | hm2 := hm
    · subst hxy
      simp only [groesseListe]
      omega
    · simp only [groesseListe]
      have := ih x hm2
      omega

-- A `gut` element stays `gut` in its list.
theorem gutListe_mem : ∀ (xs : List SExpr) (x : SExpr),
    x ∈ xs → gutListe xs = true → gut x = true := by
  intro xs
  induction xs with
  | nil =>
    intro x hm _
    simp at hm
  | cons y ys ih =>
    intro x hm hxs
    simp only [List.mem_cons] at hm
    simp only [gutListe, Bool.and_eq_true] at hxs
    obtain hxy | hm2 := hm
    · subst hxy
      exact hxs.1
    · exact ih x hm2 hxs.2

-- A `gutPlatz` tree is `gut` (every place shape checks the same
-- names; places only exclude more).
theorem gut_of_gutPlatz : ∀ (x : SExpr),
    gutPlatz x = true → gut x = true := by
  intro x h
  cases x with
  | lit m => simp [gutPlatz] at h
  | gleit s => simp [gutPlatz] at h
  | wahr => simp [gutPlatz] at h
  | falsch => simp [gutPlatz] at h
  | «variable» s =>
    simp only [gutPlatz] at h
    simp only [gut] at ⊢
    exact h
  | feld x f =>
    simp only [gutPlatz] at h
    simp only [gut] at ⊢
    exact h
  | index x i =>
    simp only [gutPlatz, Bool.and_eq_true] at h
    simp only [gut, Bool.and_eq_true] at ⊢
    exact h
  | pfeil x f =>
    simp only [gutPlatz] at h
    simp only [gut] at ⊢
    exact h
  | un o x => simp [gutPlatz] at h
  | bin o l r => simp [gutPlatz] at h
  | ruf f xs => simp [gutPlatz] at h
  | fnwert f => simp [gutPlatz] at h
  | eingebaut f xs => simp [gutPlatz] at h
  | alt x => simp [gutPlatz] at h
  | ergebnis => simp [gutPlatz] at h
  | grund g f => simp [gutPlatz] at h

-- Head and tail of a `gut` list stay `gut`.
theorem gutListe_Kopf : ∀ (x : SExpr) (xs : List SExpr),
    gutListe (x :: xs) = true → gut x = true := by
  intro x xs h
  simp only [gutListe, Bool.and_eq_true] at h
  exact h.1
theorem gutListe_Schwanz : ∀ (x : SExpr) (xs : List SExpr),
    gutListe (x :: xs) = true → gutListe xs = true := by
  intro x xs h
  simp only [gutListe, Bool.and_eq_true] at h
  exact h.2

-- Unfolding equations for printed argument lists, as plain
-- rewrite rules (kernel-checked, no equation-lemma matching).
theorem args_einzeln : ∀ (x : SExpr),
    druckToksListe [x] = druckToks x := by
  intro x
  rfl
theorem args_cons : ∀ (x y : SExpr) (ys : List SExpr),
    druckToksListe (x :: y :: ys) =
      druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) := by
  intro x y ys
  rfl

-- No `:` in printed argument lists, from no-`:` in printed
-- elements (plain list induction; the tree fact arrives as a
-- premise, so nothing here recurses into trees).
theorem keinDP_list : ∀ (n : Nat)
    (eP : ∀ (e : SExpr), groesse e ≤ n → gut e = true →
      ∀ (t : Token), t ∈ druckToks e → t ≠ .zeichen ":")
    (xs : List SExpr), groesseListe xs ≤ n → gutListe xs = true →
    ∀ (t : Token), t ∈ druckToksListe xs → t ≠ .zeichen ":" := by
  intro n eP xs
  induction xs with
  | nil =>
    intro hs hg t hm
    simp [druckToksListe] at hm
  | cons x zs ihzs =>
    intro hs hg t hm
    cases zs with
    | nil =>
      rw [args_einzeln] at hm
      have hx : groesse x ≤ n := by
        simp only [groesseListe] at hs
        omega
      exact eP x hx (gutListe_Kopf x [] hg) t hm
    | cons y ys =>
      rw [args_cons] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_append] at hmL
        obtain hm1 | hm2 := hmL
        · have hx : groesse x ≤ n := by
            simp only [groesseListe] at hs
            omega
          exact eP x hx (gutListe_Kopf x (y :: ys) hg) t hm1
        · rw [List.mem_singleton] at hm2
          subst hm2
          intro h
          simp at h
      · have hzs : groesseListe (y :: ys) ≤ n := by
          simp only [groesseListe] at hs ⊢
          omega
        exact ihzs hzs (gutListe_Schwanz x (y :: ys) hg) t hmR

-- Shape equations for `eingebaut` printability, as plain rewrite
-- rules (kernel-checked; the `gut` match has literal and shape
-- arms that `simp` equations do not select).
theorem gut_sizeof_one : ∀ (x : SExpr),
    gut (.eingebaut "sizeof" [x]) = gutPlatz x := by
  intro x
  rfl
theorem gut_sizeof_multi : ∀ (x y : SExpr) (ys : List SExpr),
    gut (.eingebaut "sizeof" (x :: y :: ys)) = false := by
  intro x y ys
  rfl
theorem gut_lenof_one : ∀ (x : SExpr),
    gut (.eingebaut "lenof" [x]) = gutPlatz x := by
  intro x
  rfl
theorem gut_lenof_multi : ∀ (x y : SExpr) (ys : List SExpr),
    gut (.eingebaut "lenof" (x :: y :: ys)) = false := by
  intro x y ys
  rfl
theorem gut_aligned_one : ∀ (a : SExpr),
    gut (.eingebaut "aligned" [a]) = false := by
  intro a
  rfl
theorem gut_aligned_two : ∀ (a b : SExpr),
    gut (.eingebaut "aligned" [a, b]) = (gut a && gut b) := by
  intro a b
  rfl
theorem gut_aligned_multi : ∀ (a b c : SExpr) (xs : List SExpr),
    gut (.eingebaut "aligned" (a :: b :: c :: xs)) = false := by
  intro a b c xs
  rfl

-- No `:` in a printed `gut` tree (the printer emits none, so the
-- argument-label strip of `parseArg` never fires on printed
-- output). By size induction. The `ruf` arm descends into its
-- argument list through `keinDP_list`; the `eingebaut` arm splits
-- the `gut` match (the head word and argument shape substitute in
-- every arm). Operator heads need `gut` (a `:` operator would
-- print); every other head discriminates by constructor.
-- Membership chases run tail-first: `++` associates left, so each
-- `rw [List.mem_append]` peels the rightmost piece.
theorem keinDP_tree : ∀ (n : Nat) (e : SExpr),
    groesse e ≤ n → gut e = true →
    ∀ (t : Token), t ∈ druckToks e → t ≠ .zeichen ":" := by
  intro n
  induction n with
  | zero =>
    intro e hs _ _ _
    have hp := groesse_pos e
    omega
  | succ n ih =>
    intro e hs hg t hm
    cases e with
    | lit m =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp at h
    | gleit s =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp at h
    | wahr =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp at h
    | falsch =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp at h
    | «variable» s =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp at h
    | feld x f =>
      simp only [gut] at hg
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · have hx : groesse x ≤ n := by
          simp only [groesse] at hs
          omega
        exact ih x hx (gut_of_gutPlatz x hg) t hmL
      · rw [List.mem_cons, List.mem_singleton] at hmR
        obtain rfl | rfl := hmR
        · intro h
          simp at h
        · intro h
          simp at h
    | index x i =>
      simp only [gut, Bool.and_eq_true] at hg
      obtain ⟨hpx, hi⟩ := hg
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_append] at hmL
        obtain hmL | hmR := hmL
        · rw [List.mem_append] at hmL
          obtain hmL | hmR := hmL
          · have hx : groesse x ≤ n := by
              simp only [groesse] at hs
              omega
            exact ih x hx (gut_of_gutPlatz x hpx) t hmL
          · rw [List.mem_singleton] at hmR
            subst hmR
            intro h
            simp at h
        · have hii : groesse i ≤ n := by
            simp only [groesse] at hs
            omega
          exact ih i hii hi t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp at h
    | pfeil x f =>
      simp only [gut] at hg
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · have hx : groesse x ≤ n := by
          simp only [groesse] at hs
          omega
        exact ih x hx (gut_of_gutPlatz x hg) t hmL
      · rw [List.mem_cons, List.mem_singleton] at hmR
        obtain rfl | rfl := hmR
        · intro h
          simp at h
        · intro h
          simp at h
    | un o x =>
      simp only [gut, Bool.and_eq_true] at hg
      obtain ⟨hop, hx⟩ := hg
      have hne : o ≠ ":" := by
        intro he
        subst he
        exact absurd hop (by decide)
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_singleton] at hmL
        subst hmL
        intro h
        injection h with ho
        exact hne ho
      · split at hmR
        · have hxx : groesse x ≤ n := by
            simp only [groesse] at hs
            omega
          exact ih x hxx hx t hmR
        · rw [List.mem_append] at hmR
          obtain hmL | hmR := hmR
          · rw [List.mem_append] at hmL
            obtain hmL | hmR := hmL
            · rw [List.mem_singleton] at hmL
              subst hmL
              intro h
              simp at h
            · have hxx : groesse x ≤ n := by
                simp only [groesse] at hs
                omega
              exact ih x hxx hx t hmR
          · rw [List.mem_singleton] at hmR
            subst hmR
            intro h
            simp at h
    | bin o l r =>
      simp only [gut, Bool.and_eq_true, and_assoc] at hg
      obtain ⟨hop, hl, hr⟩ := hg
      have hne : o ≠ ":" := by
        intro he
        subst he
        exact absurd hop (by decide)
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_append] at hmL
        obtain hmL | hmR := hmL
        · rw [List.mem_append] at hmL
          obtain hmL | hmR := hmL
          · rw [List.mem_append] at hmL
            obtain hmL | hmR := hmL
            · rw [List.mem_singleton] at hmL
              subst hmL
              intro h
              simp at h
            · have hll : groesse l ≤ n := by
                simp only [groesse] at hs
                omega
              exact ih l hll hl t hmR
          · rw [List.mem_singleton] at hmR
            subst hmR
            intro h
            injection h with ho
            exact hne ho
        · have hrr : groesse r ≤ n := by
            simp only [groesse] at hs
            omega
          exact ih r hrr hr t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp at h
    | ruf f xs =>
      simp only [gut, Bool.and_eq_true] at hg
      obtain ⟨hf, hxs⟩ := hg
      have hgl : groesseListe xs ≤ n := by
        simp only [groesse] at hs
        omega
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_append] at hmL
        obtain hmL | hmR := hmL
        · rw [List.mem_cons, List.mem_singleton] at hmL
          obtain rfl | rfl := hmL
          · intro h
            simp at h
          · intro h
            simp at h
        · exact keinDP_list n ih xs hgl hxs t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp at h
    | fnwert p =>
      simp only [druckToks] at hm
      rw [List.mem_cons, List.mem_singleton] at hm
      obtain rfl | rfl := hm
      · intro h
        simp at h
      · intro h
        simp at h
    | eingebaut f xs =>
      cases he1 : decEq f "sizeof" with
      | isTrue e1 =>
        subst e1
        cases xs with
        | nil => exact absurd hg (by decide)
        | cons x xs =>
          cases xs with
          | nil =>
            rw [gut_sizeof_one] at hg
            have hxg := gut_of_gutPlatz x hg
            have hxx : groesse x ≤ n := by
              simp only [groesse, groesseListe] at hs
              omega
            simp only [druckToks] at hm
            rw [List.mem_append] at hm
            obtain hmL | hmR := hm
            · rw [List.mem_append] at hmL
              obtain hmL | hmR := hmL
              · rw [List.mem_cons, List.mem_singleton] at hmL
                obtain rfl | rfl := hmL
                · intro h
                  simp at h
                · intro h
                  simp at h
              · rw [args_einzeln] at hmR
                exact ih x hxx hxg t hmR
            · rw [List.mem_singleton] at hmR
              subst hmR
              intro h
              simp at h
          | cons y ys =>
            rw [gut_sizeof_multi] at hg
            exact absurd hg Bool.false_ne_true
      | isFalse ne1 =>
        cases he2 : decEq f "lenof" with
        | isTrue e2 =>
          subst e2
          cases xs with
          | nil => exact absurd hg (by decide)
          | cons x xs =>
            cases xs with
            | nil =>
              rw [gut_lenof_one] at hg
              have hxg := gut_of_gutPlatz x hg
              have hxx : groesse x ≤ n := by
                simp only [groesse, groesseListe] at hs
                omega
              simp only [druckToks] at hm
              rw [List.mem_append] at hm
              obtain hmL | hmR := hm
              · rw [List.mem_append] at hmL
                obtain hmL | hmR := hmL
                · rw [List.mem_cons, List.mem_singleton] at hmL
                  obtain rfl | rfl := hmL
                  · intro h
                    simp at h
                  · intro h
                    simp at h
                · rw [args_einzeln] at hmR
                  exact ih x hxx hxg t hmR
              · rw [List.mem_singleton] at hmR
                subst hmR
                intro h
                simp at h
            | cons y ys =>
              rw [gut_lenof_multi] at hg
              exact absurd hg Bool.false_ne_true
        | isFalse ne2 =>
          cases he3 : decEq f "aligned" with
          | isTrue e3 =>
            subst e3
            cases xs with
            | nil => exact absurd hg (by decide)
            | cons a xs =>
              cases xs with
              | nil =>
                rw [gut_aligned_one] at hg
                exact absurd hg Bool.false_ne_true
              | cons b xs =>
                cases xs with
                | nil =>
                  rw [gut_aligned_two] at hg
                  simp only [Bool.and_eq_true] at hg
                  obtain ⟨ha, hb⟩ := hg
                  have hag : groesse a ≤ n := by
                    simp only [groesse, groesseListe] at hs
                    omega
                  have hbg : groesse b ≤ n := by
                    simp only [groesse, groesseListe] at hs
                    omega
                  simp only [druckToks] at hm
                  rw [List.mem_append] at hm
                  obtain hmL | hmR := hm
                  · rw [List.mem_append] at hmL
                    obtain hmL | hmR := hmL
                    · rw [List.mem_cons, List.mem_singleton] at hmL
                      obtain rfl | rfl := hmL
                      · intro h
                        simp at h
                      · intro h
                        simp at h
                    · rw [args_cons] at hmR
                      rw [List.mem_append] at hmR
                      obtain hmL | hmR := hmR
                      · rw [List.mem_append] at hmL
                        obtain hmL | hmR := hmL
                        · exact ih a hag ha t hmL
                        · rw [List.mem_singleton] at hmR
                          subst hmR
                          intro h
                          simp at h
                      · rw [args_einzeln] at hmR
                        exact ih b hbg hb t hmR
                  · rw [List.mem_singleton] at hmR
                    subst hmR
                    intro h
                    simp at h
                | cons c xs =>
                  rw [gut_aligned_multi] at hg
                  exact absurd hg Bool.false_ne_true
          | isFalse ne3 => simp [gut, ne1, ne2, ne3] at hg
    | alt x =>
      simp only [gut] at hg
      have hxg := gut_of_gutPlatz x hg
      have hxx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      simp only [druckToks] at hm
      rw [List.mem_append] at hm
      obtain hmL | hmR := hm
      · rw [List.mem_append] at hmL
        obtain hmL | hmR := hmL
        · rw [List.mem_cons, List.mem_singleton] at hmL
          obtain rfl | rfl := hmL
          · intro h
            simp at h
          · intro h
            simp at h
        · exact ih x hxx hxg t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp at h
    | ergebnis =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp at h
    | grund g f =>
      simp only [druckToks] at hm
      rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hm
      obtain rfl | rfl | rfl := hm
      · intro h
        simp at h
      · intro h
        simp at h
      · intro h
        simp at h

-- A printed `gut` tree never starts with `)` (heads are literals,
-- names or openers; suffix chains delver into the base, operators
-- are lawful). `parseArgs` needs it to choose its recursive arm.
-- The head equation (`hT`) splits by constructor injectivity; only
-- operator heads need `gut`.
theorem toksKopf : ∀ (n : Nat) (e : SExpr), groesse e ≤ n →
    gut e = true →
    ∀ (a : Token) (R : List Token), druckToks e = a :: R →
    a ≠ .zeichen ")" := by
  intro n
  induction n with
  | zero =>
    intro e hs _ _ _ _
    have hp := groesse_pos e
    omega
  | succ n ih =>
    intro e hs hg a R hT
    cases e with
    | lit m =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | gleit s =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | wahr =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | falsch =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | «variable» s =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | feld x f =>
      simp only [gut] at hg
      have hne : druckToks x ≠ [] := by
        intro he
        have hlen := toksLang (groesse x) x (Nat.le_refl _)
        rw [he] at hlen
        simp at hlen
      obtain ⟨b, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
      simp only [druckToks] at hT
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have ihb := ih x hx (gut_of_gutPlatz x hg) b R2 hxb
      rw [hxb] at hT
      simp only [List.cons_append] at hT
      injection hT with ha _
      subst ha
      exact ihb
    | index x i =>
      simp only [gut, Bool.and_eq_true] at hg
      obtain ⟨hpx, -⟩ := hg
      have hne : druckToks x ≠ [] := by
        intro he
        have hlen := toksLang (groesse x) x (Nat.le_refl _)
        rw [he] at hlen
        simp at hlen
      obtain ⟨b, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
      simp only [druckToks] at hT
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have ihb := ih x hx (gut_of_gutPlatz x hpx) b R2 hxb
      rw [hxb] at hT
      simp only [List.cons_append] at hT
      injection hT with ha _
      subst ha
      exact ihb
    | pfeil x f =>
      simp only [gut] at hg
      have hne : druckToks x ≠ [] := by
        intro he
        have hlen := toksLang (groesse x) x (Nat.le_refl _)
        rw [he] at hlen
        simp at hlen
      obtain ⟨b, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
      simp only [druckToks] at hT
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      have ihb := ih x hx (gut_of_gutPlatz x hg) b R2 hxb
      rw [hxb] at hT
      simp only [List.cons_append] at hT
      injection hT with ha _
      subst ha
      exact ihb
    | un o x =>
      simp only [gut, Bool.and_eq_true] at hg
      obtain ⟨hop, -⟩ := hg
      have hne : o ≠ ")" := by
        intro he
        subst he
        exact absurd hop (by decide)
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      injection h with ho
      exact hne ho
    | bin o l r =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | ruf f xs =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | fnwert p =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | eingebaut f xs =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | alt x =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | ergebnis =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h
    | grund g f =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp at h

-- The round-trip invariant at size bound `n`: every level parses
-- every `gut` tree from its printed tokens with fuel linear in
-- the tree size, plus one spare per node (the `+ groesse e`
-- covers descent strips and short chains wherever a bound is
-- reused at reduced fuel). Levels take a benign follow (`ruhig`
-- for the loops, `ruhigSuff` for the suffixes); `parsePrimary`
-- takes only the suffix follow (it has no loops) plus `unFrei`
-- (prefix trees live at the unary level), with descent slack
-- (`+7`) for application below a descent.
def R (n : Nat) : Prop :=
  (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseOr F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseAnd F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseCmp F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseBit F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseAdd F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseMul F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F →
    parseUnary F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → unFrei e = true → ruhigSuff rest = true →
    12 * (groesse e + 1) + groesse e ≤ F + 7 →
    parsePrimary F (druckToks e ++ rest) = .ok (e, rest))

-- The binary-inner parse: a parenthesised operator's inside
-- (`l op r` between the parens), by operator level. No follow
-- premise: the tail after `)` is never inspected.
def B (n : Nat) : Prop :=
  ∀ (o : String) (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutOpBin o = true →
    gut l = true → gut r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) ≤ F →
    parseOr F (druckToks l ++ [.zeichen o] ++ druckToks r ++
      [.zeichen ")"] ++ W) =
      .ok (.bin o l r, [.zeichen ")"] ++ W)

-- `sammleSegmente` stops on a benign suffix follow (pure: no fuel
-- needed). The `::` arm is the only continuer; anything else
-- returns the accumulator untouched.
theorem sammleSeg_stop : ∀ (segs : List String) (t : List Token),
    ruhigSuff t = true → sammleSegmente t segs = (segs, t) := by
  intro segs t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | zahl n => rfl
    | gleit s => rfl
    | text s => rfl
    | zeichen s =>
      simp only [ruhigSuff] at h
      have hf := nichtWahr_falsch _ h
      simp only [Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, -, hDc⟩ := hf
      have ne := strNe_of s "::" hDc
      simp [sammleSegmente, ne]
    | ende => rfl

-- One argument through `parseArg`: the label strip misses (the
-- second token is never `:`), then the expression parses. The
-- strip-fire case dies by positional injection (`keinDP_tree` for
-- the tail token, the separator spelling for the empty tail).
theorem arg_einzeln : ∀ (n : Nat) (Rn : R n)
    (x : SExpr) (sep : Token) (S : List Token) (F : Nat),
    groesse x ≤ n → gut x = true →
    (sep = .zeichen "," ∨ sep = .zeichen ")") →
    12 * (groesse x + 1) + groesse x + 1 ≤ F →
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  intro n Rn x sep S F hx hxg hsep hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp at hlen
    obtain ⟨a, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
    rw [hxb] at hcon
    simp only [List.cons_append] at hcon
    injection hcon with _ ht
    cases hR : R2 with
    | nil =>
      rw [hR] at ht
      simp only [List.nil_append, List.cons_append] at ht
      injection ht with hsep2 _
      cases hsep with
      | inl h =>
        subst h
        simp at hsep2
      | inr h =>
        subst h
        simp at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp [hxb, hR]
      have hne2 := keinDP_tree n x hx hxg b hbmem
      exact hne2 hb
  simp only [parseArg] at ⊢
  have hr1 : ruhig ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr2 : ruhigSuff ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hFr : 12 * (groesse x + 1) + groesse x ≤ F' := by omega
  obtain ⟨hOr, -⟩ := Rn
  simpa only [List.append_assoc] using hOr x ([sep] ++ S) F' hx hxg hr1 hr2 hFr

-- Whole argument lists through `parseArgs`: head by `toksKopf`
-- (never `)`, so the recursive arm is taken), element by
-- `arg_einzeln`, tail by list induction. Ends at `)`, which is
-- consumed (like every `parseArgs` arm).
theorem args_rund : ∀ (n : Nat) (Rn : R n)
    (xs : List SExpr) (rest : List Token) (F : Nat),
    groesseListe xs ≤ n → gutListe xs = true →
    12 * (groesseListe xs + 1) + groesseListe xs + 2 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) =
      .ok (xs, rest) := by
  intro n Rn xs
  induction xs with
  | nil =>
    intro rest F hs hg hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append,
      List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hg hF
    cases zs with
    | nil =>
      -- Singleton: `T(x)` then `)`. One `parseArg`, then close.
      have hx : groesse x ≤ n := by
        simp only [groesseListe] at hs
        omega
      have hxg : gut x = true := gutListe_Kopf x [] hg
      have hkop : ∀ (a : Token) (R : List Token),
          druckToks x = a :: R → a ≠ .zeichen ")" :=
        toksKopf n x hx hxg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_einzeln] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_einzeln n Rn x (.zeichen ")") rest F' hx hxg
        (Or.inr rfl) (by simp only [groesseListe] at hF ⊢; omega)
      simp only [harg, List.cons_append] at ⊢
      rfl
    | cons y ys =>
      -- Cons: `T(x)` then `,`. Parse the head, step, recurse.
      have hx : groesse x ≤ n := by
        simp only [groesseListe] at hs
        omega
      have hxg : gut x = true := gutListe_Kopf x (y :: ys) hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_cons] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hkop : ∀ (a : Token) (R : List Token),
            druckToks x = a :: R → a ≠ .zeichen ")" :=
          toksKopf n x hx hxg
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_einzeln n Rn x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hx hxg (Or.inl rfl) (by simp only [groesseListe] at hF ⊢; omega)
      -- ⊢ : match parseArgs F' (rest-args) ... — the `,` arm was taken;
      -- recurse on the tail.
      have hzs : groesseListe (y :: ys) ≤ n := by
        simp only [groesseListe] at hs ⊢
        omega
      have hxp := groesse_pos x
      have htail := ihzs rest F'
        hzs (gutListe_Schwanz x (y :: ys) hg)
        (by simp only [groesseListe] at hF ⊢; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append] at ⊢

-- Suffix fragments: one `.f`, `->f` or `[i]` step of a place
-- chain. Every `gutPlatz` tree is a head variable plus fragments
-- (`zerlege` below); the printer lays them end to end.
inductive SuffFrag
  | dot : String → SuffFrag
  | arrow : String → SuffFrag
  | idx : SExpr → SuffFrag
def suffToks : List SuffFrag → List Token
  | [] => []
  | .dot f :: s => .zeichen "." :: .ident f :: suffToks s
  | .arrow f :: s => .zeichen "->" :: .ident f :: suffToks s
  | .idx i :: s =>
    .zeichen "[" :: druckToks i ++ [.zeichen "]"] ++ suffToks s
def applySuff : SExpr → List SuffFrag → SExpr
  | e, [] => e
  | e, .dot f :: s => applySuff (.feld e f) s
  | e, .arrow f :: s => applySuff (.pfeil e f) s
  | e, .idx i :: s => applySuff (.index e i) s
def suffGroesse : List SuffFrag → Nat
  | [] => 0
  | .dot _ :: s => suffGroesse s + 1
  | .arrow _ :: s => suffGroesse s + 1
  | .idx i :: s => groesse i + suffGroesse s + 1

-- Which suffix fragments are printable (index payloads are).
def suffGut : List SuffFrag → Bool
  | [] => true
  | .dot _ :: s => suffGut s
  | .arrow _ :: s => suffGut s
  | .idx i :: s => gut i && suffGut s

-- Sizes commute with fragment application (for `omega`).
theorem groesse_applySuff : ∀ (base : SExpr) (suff : List SuffFrag),
    groesse (applySuff base suff) =
      groesse base + suffGroesse suff := by
  intro base suff
  induction suff generalizing base with
  | nil => simp [applySuff, suffGroesse]
  | cons f s ih =>
    cases f with
    | dot g => simp [applySuff, suffGroesse, groesse, ih]; omega
    | arrow g => simp [applySuff, suffGroesse, groesse, ih]; omega
    | idx i => simp [applySuff, suffGroesse, groesse, ih]; omega
theorem applySuff_append : ∀ (base : SExpr) (s1 s2 : List SuffFrag),
    applySuff base (s1 ++ s2) =
      applySuff (applySuff base s1) s2 := by
  intro base s1
  induction s1 generalizing base with
  | nil => simp [applySuff]
  | cons f s ih =>
    cases f with
    | dot g => simp [applySuff, ih]
    | arrow g => simp [applySuff, ih]
    | idx i => simp [applySuff, ih]
theorem suffGroesse_append : ∀ (s1 s2 : List SuffFrag),
    suffGroesse (s1 ++ s2) = suffGroesse s1 + suffGroesse s2 := by
  intro s1
  induction s1 with
  | nil => simp [suffGroesse]
  | cons f s ih =>
    cases f with
    | dot g => simp [suffGroesse, ih]; omega
    | arrow g => simp [suffGroesse, ih]; omega
    | idx i => simp [suffGroesse, ih]; omega

-- `suffGut` splits over appends.
theorem suffGut_append : ∀ (s1 s2 : List SuffFrag),
    suffGut (s1 ++ s2) = (suffGut s1 && suffGut s2) := by
  intro s1
  induction s1 with
  | nil => simp [suffGut]
  | cons f s ih =>
    cases f with
    | dot g => simp [suffGut, ih]
    | arrow g => simp [suffGut, ih]
    | idx i => simp [suffGut, ih, Bool.and_assoc]

-- Every `gutPlatz` tree is a head variable plus fragments, with a
-- lawful head and lawful index payloads. By size induction.
theorem zerlege : ∀ (n : Nat) (p : SExpr), groesse p ≤ n →
    gutPlatz p = true →
    ∃ (a : String) (suff : List SuffFrag),
      p = applySuff (.variable a) suff ∧
      (!istKeinPlatz a) = true ∧
      suffGut suff = true ∧
      suffGroesse suff + 1 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro p hs _
    have hp := groesse_pos p
    omega
  | succ n ih =>
    intro p hs hg
    cases p with
    | lit m => simp [gutPlatz] at hg
    | gleit s => simp [gutPlatz] at hg
    | wahr => simp [gutPlatz] at hg
    | falsch => simp [gutPlatz] at hg
    | «variable» a =>
      simp only [gutPlatz] at hg
      exact ⟨a, [], rfl, hg, rfl, by simp only [suffGroesse]; omega⟩
    | feld x f =>
      simp only [gutPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.dot f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGut (suff ++ [.dot f]) = suffGut suff := by
          simp [suffGut_append, suffGut]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | index x i =>
      simp only [gutPlatz, Bool.and_eq_true] at hg
      obtain ⟨hpx, hi⟩ := hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hpx
      refine ⟨a, suff ++ [.idx i], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hgi : gut i = true := hi
        have hsg : suffGut (suff ++ [.idx i]) = (suffGut suff && gut i) := by
          simp [suffGut_append, suffGut, Bool.and_assoc]
        rw [hsg]
        simp [hgs, hgi]
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        simp only [groesse, groesse_applySuff] at hs
        omega
    | pfeil x f =>
      simp only [gutPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.arrow f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGut (suff ++ [.arrow f]) = suffGut suff := by
          simp [suffGut_append, suffGut]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | un o x => simp [gutPlatz] at hg
    | bin o l r => simp [gutPlatz] at hg
    | ruf f xs => simp [gutPlatz] at hg
    | fnwert f => simp [gutPlatz] at hg
    | eingebaut f xs => simp [gutPlatz] at hg
    | alt x => simp [gutPlatz] at hg
    | ergebnis => simp [gutPlatz] at hg
    | grund g f => simp [gutPlatz] at hg

-- Suffix chains through `parseSuffixe`, by list induction. Index
-- payloads parse via `R n` (smaller); fuel carries one spare per
-- fragment (`suff.length`) over the linear bound, so every strip
-- and every child is covered.
theorem suff_rund : ∀ (n : Nat) (Rn : R n)
    (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    suffGroesse suff + groesse base ≤ n →
    suffGut suff = true →
    ruhigSuff rest = true →
    12 * (suffGroesse suff + groesse base + 1) + suffGroesse suff ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) =
      .ok (applySuff base suff, rest) := by
  intro n Rn suff
  induction suff with
  | nil =>
    intro base rest F hs hg hr hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append] at ⊢
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro base rest F hs hg hr hF
      simp only [suffGut] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe] at ⊢
      -- ⊢ : parseSuffixe F' (feld base f) (suffToks suff ++ rest) = ...
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.feld base f) ≤ n := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.feld base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.feld base f) rest F' hs2 hg hr hF2
    | arrow f =>
      intro base rest F hs hg hr hF
      simp only [suffGut] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.pfeil base f) ≤ n := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.pfeil base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.pfeil base f) rest F' hs2 hg hr hF2
    | idx i =>
      intro base rest F hs hg hr hF
      simp only [suffGut, Bool.and_eq_true] at hg
      obtain ⟨hi, hgs⟩ := hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe] at ⊢
      -- ⊢ : parseOr F' (T(i) ++ ...) then `]` then recurse.
      have hii : groesse i ≤ n := by
        simp only [suffGroesse] at hs
        omega
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hFi : 12 * (groesse i + 1) + groesse i ≤ F' := by
        simp only [suffGroesse] at hs hF ⊢
        omega
      obtain ⟨hOr, -⟩ := Rn
      have hOi := hOr i ([.zeichen "]"] ++ suffToks suff ++ rest) F'
        hii hi hr1 hr2 hFi
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.index base i) ≤ n := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.index base i) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.index base i) rest F' hs2 hgs hr hF2

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here (filled in as the file grows).
-/

#print axioms Gabbro.Grammatik.Parser.strKlingt
