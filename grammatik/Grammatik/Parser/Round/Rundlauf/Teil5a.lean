module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser

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
      simp only [reduceCtorEq] at h
    | float s =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [reduceCtorEq] at h
    | tru =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [reduceCtorEq] at h
    | fls =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [reduceCtorEq] at h
    | «variable» s =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [nameTok_ne_zeichen] at h
    | field x f =>
      simp only [gut] at hg
      have hne : druckToks x ≠ [] := by
        intro he
        have hlen := toksLang (groesse x) x (Nat.le_refl _)
        rw [he] at hlen
        simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
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
        simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
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
    | arrow x f =>
      simp only [gut] at hg
      have hne : druckToks x ≠ [] := by
        intro he
        have hlen := toksLang (groesse x) x (Nat.le_refl _)
        rw [he] at hlen
        simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
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
      by_cases hs0 : strEq o "-()" = true
      · simp only [druckToks, hs0, ite_true, List.cons_append] at hT
        injection hT with ha _
        subst ha
        intro h
        simp only [Token.zeichen.injEq, String.reduceEq] at h
      simp only [gut, hs0, Bool.false_and, Bool.or_false, Bool.and_eq_true] at hg
      obtain ⟨hop, -⟩ := hg
      have hne : o ≠ ")" := by
        intro he
        subst he
        exact absurd hop (by decide)
      simp only [druckToks, hs0, Bool.false_eq_true, ite_false, List.cons_append] at hT
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
      simp only [Token.zeichen.injEq, String.reduceEq] at h
    | call f xs =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [nameTok_ne_zeichen] at h
    | fnref p =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [Token.zeichen.injEq, String.reduceEq] at h
    | built f xs =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [reduceCtorEq] at h
    | old x =>
      simp only [druckToks, List.cons_append] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [reduceCtorEq] at h
    | res =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [reduceCtorEq] at h
    | why g f =>
      simp only [druckToks] at hT
      injection hT with ha _
      subst ha
      intro h
      simp only [nameTok_ne_zeichen] at h
    | ext xk xn xs =>
      obtain ⟨rfl, rfl, c, ys, rfl, hc, -, -⟩ := gut_ruf_faelle xk xn xs hg
      have hcs : groesse c ≤ n := by simp only [groesse, groesseListe] at hs; omega
      have hlen := toksLang (groesse c) c (Nat.le_refl _)
      obtain ⟨a', R', hc'⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hlen)
      rw [druck_ruf, hc', List.cons_append] at hT
      injection hT with ha _
      subst ha
      exact ih c hcs (gut_of_gutPlatz c hc) a' R' hc'


end Gabbro.Grammatik.Parser
