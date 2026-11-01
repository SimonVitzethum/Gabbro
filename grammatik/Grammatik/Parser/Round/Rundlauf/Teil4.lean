module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- No `:` in a printed `gut` tree (the printer emits none, so the
-- argument-label strip of `parseArg` never fires on printed
-- output). By size induction. The `ruf` arm descends into its
-- argument list through `keinDP_list`; the `built` arm splits
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
      simp only [reduceCtorEq] at h
    | float s =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp only [reduceCtorEq] at h
    | tru =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp only [reduceCtorEq] at h
    | fls =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp only [reduceCtorEq] at h
    | «variable» s =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp only [nameTok_ne_zeichen] at h
    | field x f =>
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
          simp only [Token.zeichen.injEq, String.reduceEq] at h
        · intro h
          simp only [nameTok_ne_zeichen] at h
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
            simp only [Token.zeichen.injEq, String.reduceEq] at h
        · have hii : groesse i ≤ n := by
            simp only [groesse] at hs
            omega
          exact ih i hii hi t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp only [Token.zeichen.injEq, String.reduceEq] at h
    | arrow x f =>
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
          simp only [Token.zeichen.injEq, String.reduceEq] at h
        · intro h
          simp only [nameTok_ne_zeichen] at h
    | un o x =>
      by_cases hs0 : strEq o "-()" = true
      · have ho := strKlingt o "-()" hs0
        subst ho
        have hl : istLit x = true := by
          have h0 : gutOpUn "-()" = false := by decide
          simp only [gut, h0, Bool.false_and, Bool.false_or, hs0, Bool.true_and] at hg; exact hg
        cases x with
        | lit k =>
          simp only [druckToks, hs0, ite_true, List.mem_append, List.mem_cons, List.mem_nil_iff,
            or_false] at hm
          rcases hm with ((rfl | rfl) | rfl) | rfl <;> intro h <;> simp only [Token.zeichen.injEq, String.reduceEq, reduceCtorEq] at h
        | _ => simp only [istLit, Bool.false_eq_true] at hl
      simp only [gut, hs0, Bool.false_and, Bool.or_false, Bool.and_eq_true] at hg
      obtain ⟨hop, hx⟩ := hg
      have hne : o ≠ ":" := by
        intro he
        subst he
        exact absurd hop (by decide)
      simp only [druckToks, hs0, Bool.false_eq_true, ite_false] at hm
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
              simp only [Token.zeichen.injEq, String.reduceEq] at h
            · have hxx : groesse x ≤ n := by
                simp only [groesse] at hs
                omega
              exact ih x hxx hx t hmR
          · rw [List.mem_singleton] at hmR
            subst hmR
            intro h
            simp only [Token.zeichen.injEq, String.reduceEq] at h
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
              simp only [Token.zeichen.injEq, String.reduceEq] at h
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
        simp only [Token.zeichen.injEq, String.reduceEq] at h
    | call f xs =>
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
            simp only [nameTok_ne_zeichen] at h
          · intro h
            simp only [Token.zeichen.injEq, String.reduceEq] at h
        · exact keinDP_list n ih xs hgl hxs t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp only [Token.zeichen.injEq, String.reduceEq] at h
    | fnref p =>
      simp only [druckToks] at hm
      rw [List.mem_cons, List.mem_singleton] at hm
      obtain rfl | rfl := hm
      · intro h
        simp only [Token.zeichen.injEq, String.reduceEq] at h
      · intro h
        simp only [nameTok_ne_zeichen] at h
    | built f xs =>
      cases he1 : decEq f "sizeof" with
      | isTrue e1 =>
        subst e1
        cases xs with
        | nil => exact absurd hg (by decide)
        | cons x xs =>
          cases xs with
          | nil =>
            rw [gut_sizeof_one] at hg
            simp only [Bool.and_eq_true] at hg
            obtain ⟨hpx, -⟩ := hg
            have hxg := gut_of_gutPlatz x hpx
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
                  simp only [reduceCtorEq] at h
                · intro h
                  simp only [Token.zeichen.injEq, String.reduceEq] at h
              · rw [args_einzeln] at hmR
                exact ih x hxx hxg t hmR
            · rw [List.mem_singleton] at hmR
              subst hmR
              intro h
              simp only [Token.zeichen.injEq, String.reduceEq] at h
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
              simp only [Bool.and_eq_true] at hg
              obtain ⟨hpx, -⟩ := hg
              have hxg := gut_of_gutPlatz x hpx
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
                    simp only [reduceCtorEq] at h
                  · intro h
                    simp only [Token.zeichen.injEq, String.reduceEq] at h
                · rw [args_einzeln] at hmR
                  exact ih x hxx hxg t hmR
              · rw [List.mem_singleton] at hmR
                subst hmR
                intro h
                simp only [Token.zeichen.injEq, String.reduceEq] at h
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
                  have hpa := groesse_pos a
                  have hpb := groesse_pos b
                  simp only [druckToks] at hm
                  rw [List.mem_append] at hm
                  obtain hmL | hmR := hm
                  · rw [List.mem_append] at hmL
                    obtain hmL | hmR := hmL
                    · rw [List.mem_cons, List.mem_singleton] at hmL
                      obtain rfl | rfl := hmL
                      · intro h
                        simp only [reduceCtorEq] at h
                      · intro h
                        simp only [Token.zeichen.injEq, String.reduceEq] at h
                    · rw [args_cons] at hmR
                      rw [List.mem_append] at hmR
                      obtain hmL | hmR := hmR
                      · rw [List.mem_append] at hmL
                        obtain hmL | hmR := hmL
                        · exact ih a hag ha t hmL
                        · rw [List.mem_singleton] at hmR
                          subst hmR
                          intro h
                          simp only [Token.zeichen.injEq, String.reduceEq] at h
                      · rw [args_einzeln] at hmR
                        exact ih b hbg hb t hmR
                  · rw [List.mem_singleton] at hmR
                    subst hmR
                    intro h
                    simp only [Token.zeichen.injEq, String.reduceEq] at h
                | cons c xs =>
                  rw [gut_aligned_multi] at hg
                  exact absurd hg Bool.false_ne_true
          | isFalse ne3 => simp only [ne1, imp_false, false_implies, implies_true, ne2, ne3, gut, Bool.false_eq_true] at hg
    | old x =>
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
            simp only [reduceCtorEq] at h
          · intro h
            simp only [Token.zeichen.injEq, String.reduceEq] at h
        · exact ih x hxx hxg t hmR
      · rw [List.mem_singleton] at hmR
        subst hmR
        intro h
        simp only [Token.zeichen.injEq, String.reduceEq] at h
    | res =>
      simp only [druckToks] at hm
      rw [List.mem_singleton] at hm
      subst hm
      intro h
      simp only [reduceCtorEq] at h
    | why g f =>
      simp only [druckToks] at hm
      rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hm
      obtain rfl | rfl | rfl := hm
      · intro h
        simp only [nameTok_ne_zeichen] at h
      · intro h
        simp only [Token.zeichen.injEq, String.reduceEq] at h
      · intro h
        simp only [nameTok_ne_zeichen] at h
    | ext xk xn xs =>
      obtain ⟨rfl, rfl, c, ys, rfl, hc, -, hys⟩ := gut_ruf_faelle xk xn xs hg
      have hpc := groesse_pos c
      have hcs : groesse c ≤ n := by simp only [groesse, groesseListe] at hs; omega
      have hcall : groesse (.call "x" ys) ≤ n := by simp only [groesse, groesseListe] at hs ⊢; omega
      have hgc : gut (.call "x" ys) = true := by simp only [gut, hys, Bool.and_true]; decide
      rw [druck_ruf, List.mem_append] at hm
      rcases hm with hm | hm
      · exact ih c hcs (gut_of_gutPlatz c hc) t hm
      · apply ih (.call "x" ys) hcall hgc t
        simp only [druckToks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        rcases hm with (h | h) | h <;> simp only [h, or_true, true_or, Token.zeichen.injEq, String.reduceEq, or_false]

end Gabbro.Grammatik.Parser
