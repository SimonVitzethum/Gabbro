module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser

mutual
def gut : SExpr → Bool
  | .lit _ => true
  | .float _ => true
  | .tru => true
  | .fls => true
  | .variable s => !istKopfWort s
  | .field x _ => gutPlatz x
  | .index x i => gutPlatz x && gut i
  | .arrow x _ => gutPlatz x
  | .un o x => (gutOpUn o && gut x) || (strEq o "-()" && istLit x)
  | .bin o l r => gutOpBin o && gut l && gut r
  | .call f xs => !istKopfWort f && gutListe xs
  | .fnref _ => true
  | .built "sizeof" [x] => gutPlatz x && (!istTypWortVar x)
  | .built "lenof" [x] => gutPlatz x && (!istTypWortVar x)
  | .built "aligned" [a, b] => gut a && gut b
  | .built _ _ => false
  | .old x => gutPlatz x
  | .res => true
  | .why g _ =>
    !istKopfWort g && !istIntWort g && !istZuckerBreite g &&
      !strEq g "Self"
  | .ext .call [] xs => gutOrtRuf xs
  | .ext _ _ _ => false
def gutPlatz : SExpr → Bool
  | .variable s => !istKopfWort s
  | .field x _ => gutPlatz x
  | .index x i => gutPlatz x && gut i
  | .arrow x _ => gutPlatz x
  | _ => false
def gutListe : List SExpr → Bool
  | [] => true
  | x :: xs => gut x && gutListe xs
-- A call through a place (`o.is_some()`, `p->f(x)`): the callee is a suffixed place, never a bare
-- name (a bare name before `(` reads as the direct call `.call`).
def gutOrtRuf : List SExpr → Bool
  | [] => false
  | c :: xs => gutPlatz c && !istVar c && gutListe xs
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

-- A benign suffix follow: `.`, `->`, `[`, `::` and `(` continue
-- a suffix, segment or call chain; everything else (including
-- every loop operator) stops `parseSuffixe`, `sammleSegmente` and
-- the `parseKopf` call arm.
def ruhigSuff : List Token → Bool
  | [] => true
  | .zeichen s :: _ =>
    !(strEq s "." || strEq s "->" || strEq s "[" || strEq s "::" ||
      strEq s "(")
  | _ :: _ => true

-- A benign float follow: `wort "rounded"` after a float literal is
-- absorbed (`gleit "1.0 rounded"`); anything else leaves it alone.
-- Loop operators, suffix marks and `ende` are all benign.
def ruhigGleit : List Token → Bool
  | [] => true
  | .wort s :: _ => !strEq s "rounded"
  | _ :: _ => true

-- From a false character-list comparison to the inequality (for
-- discharging the operator-table matches below).
theorem strNe_of (s w : String) (h : strEq s w = false) : s ≠ w := by
  intro e
  subst e
  simp only [strEq, BEq.rfl, Bool.true_eq_false] at h

-- A negated `true` is `false` (for unfolding `ruhig`).
theorem nichtWahr_falsch : ∀ (b : Bool), (!b) = true → b = false := by
  intro b h
  cases hfs : b <;> simp_all

/-- A head word gate: not a refused place word. -/
theorem kopf_kp {s : String} (h : istKopfWort s = false) : istKeinPlatz s = false := by
  simp only [istKopfWort, Bool.or_eq_false_iff] at h; exact h.1

/-- A head word gate: none of the words with a primary arm. -/
theorem kopf_ne {s : String} (h : istKopfWort s = false) :
    s ≠ "count" ∧ s ≠ "true" ∧ s ≠ "false" ∧ s ≠ "Some" ∧ s ≠ "None" ∧ s ≠ "result" ∧
      s ≠ "old" ∧ s ≠ "sizeof" ∧ s ≠ "lenof" ∧ s ≠ "aligned" := by
  simp only [istKopfWort, Bool.or_eq_false_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; subst e) <;>
    first | (revert h1; decide) | (revert h2; decide)

/-- The name token is no mark, no literal and no end: the readers that look for those pass it by. -/
@[simp] theorem nameTok_ne_zeichen (s z : String) : nameTok s ≠ .zeichen z := by
  unfold nameTok; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
@[simp] theorem nameTok_ne_ende (s : String) : nameTok s ≠ .ende := by
  unfold nameTok; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
@[simp] theorem nameTok_ne_num (s : String) (n : Nat) : nameTok s ≠ .num n := by
  unfold nameTok; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
@[simp] theorem nameTok_ne_float (s z : String) : nameTok s ≠ .float z := by
  unfold nameTok; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
@[simp] theorem nameTok_ne_text (s z : String) : nameTok s ≠ .text z := by
  unfold nameTok; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
@[simp] theorem nameTok_ne_doku (s z : String) : nameTok s ≠ .doku z := by
  unfold nameTok; split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A printed name at a primary: read through `parseKopf`. -/
theorem parsePrimary_nameTok (f : Nat) (s : String) (r : List Token) (h : istKopfWort s = false) :
    parsePrimary (f + 1) (nameTok s :: r) = parseKopf f (nameTok s :: r) := by
  have hdyn : s ≠ "dyn" := by
    intro he
    subst s
    revert h
    decide
  have hheads : s ≠ "exists" ∧ s ≠ "add" ∧ s ≠ "min" ∧ s ≠ "max" := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro he; subst s; revert h; decide)
  obtain ⟨hexists, hadd, hmin, hmax⟩ := hheads
  have hk := kopf_kp h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := kopf_ne h
  unfold nameTok
  split
  · simp [parsePrimary, nameText, hk, hdyn, hexists, hadd, hmin, hmax,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · simp only [parsePrimary, nameText, hk, Bool.false_eq_true, ↓reduceIte]

/-- A printed name at a unary: no prefix mark, so the primary reader. -/
theorem parseUnary_nameTok (f : Nat) (s : String) (r : List Token) :
    parseUnary (f + 1) (nameTok s :: r) = parsePrimary f (nameTok s :: r) := by
  unfold nameTok; split <;> simp only [parseUnary]

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
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨hOr, -, -, -, -, -⟩ := hf
      have ne := strNe_of s "||" hOr
      simp only [opOder, List.cons.injEq, Token.zeichen.injEq, ne, false_and, imp_self, implies_true]
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
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
    | zeichen s =>
      simp only [ruhig] at h
      have hf := nichtWahr_falsch _ h
      simp only [istSchleifenOp, Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, hAnd, -, -, -, -⟩ := hf
      have ne := strNe_of s "&&" hAnd
      simp only [opUnd, List.cons.injEq, Token.zeichen.injEq, ne, false_and, imp_self, implies_true]
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
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
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

end Gabbro.Grammatik.Parser
