module

public import Grammatik.Parser.Round.Rundlauf.Teil2a
public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
theorem stopBit : ∀ (t : List Token),
    ruhig t = true → opBit t = none := by
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
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
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
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
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
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
    | zeichen s =>
      simp only [ruhigSuff] at h
      have hf := nichtWahr_falsch _ h
      simp only [Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨c1, c2, c3, -, c5⟩ := hf
      have ne1 := strNe_of s "." c1
      have ne2 := strNe_of s "->" c2
      have ne3 := strNe_of s "[" c3
      have ne5 := strNe_of s "(" c5
      simp only [parseSuffixe, List.cons.injEq, Token.zeichen.injEq, ne1, false_and, imp_self, implies_true, ne2,
  ne3, ne5]
    | ende => rfl

-- Trees handled at the primary level (prefix `un` trees and
-- `fnref` live at the unary level: `parsePrimary` fails on their
-- operator heads, so the round trip never asks it about them).
def primFrei : SExpr → Bool
  | .un _ _ => false
  | .fnref _ => false
  | _ => true

-- Every tree has size at least one (empties the zero case of every
-- size induction below).
theorem groesse_pos : ∀ (e : SExpr), 1 ≤ groesse e := by
  intro e
  cases e <;> simp only [groesse] at ⊢ <;> omega

end Gabbro.Grammatik.Parser
