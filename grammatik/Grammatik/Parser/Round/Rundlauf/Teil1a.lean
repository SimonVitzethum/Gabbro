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

/-- A tail excluding both call openers takes the ordinary name branch. -/
theorem rufKopf_ohne {α : Type} (toks : List Token)
    (generic call : List Token → α) (other : Unit → α)
    (hgeneric : ∀ R, toks ≠ .zeichen "::" :: .zeichen "[" :: R)
    (hmiss : ∀ R, toks ≠ .zeichen "(" :: R) :
    rufKopf toks generic call other = other () := by
  cases toks with
  | nil => rfl
  | cons tok rest =>
    cases tok <;> try rfl
    rename_i s
    simp only [rufKopf]
    split
    · rename_i hs
      have heq := strKlingt _ _ hs
      subst s
      cases rest with
      | nil => rfl
      | cons tok tail =>
        cases tok <;> try rfl
        rename_i s
        split
        · rename_i hs
          have heq := strKlingt _ _ hs
          subst s
          exact (hgeneric tail rfl).elim
        · rfl
    · split
      · rename_i hs
        have heq := strKlingt _ _ hs
        subst s
        exact (hmiss rest rfl).elim
      · rfl

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


end Gabbro.Grammatik.Parser
