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

-- A benign suffix follow: `.`, `->` and `[` continue a suffix
-- chain, everything else (including every loop operator) stops
-- `parseSuffixe`.
def ruhigSuff : List Token → Bool
  | [] => true
  | .zeichen s :: _ =>
    !(strEq s "." || strEq s "->" || strEq s "[")
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
      obtain ⟨c1, c2, c3⟩ := hf
      have ne1 := strNe_of s "." c1
      have ne2 := strNe_of s "->" c2
      have ne3 := strNe_of s "[" c3
      simp [parseSuffixe, ne1, ne2, ne3]
    | ende => rfl

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here (filled in as the file grows).
-/

#print axioms Gabbro.Grammatik.Parser.strKlingt
