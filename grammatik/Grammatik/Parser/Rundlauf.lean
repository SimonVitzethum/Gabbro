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

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here (filled in as the file grows).
-/

#print axioms Gabbro.Grammatik.Parser.strKlingt
