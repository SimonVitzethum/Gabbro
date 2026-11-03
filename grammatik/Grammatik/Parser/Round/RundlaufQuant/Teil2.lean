module

public import Grammatik.Parser.Round.RundlaufQuant.Verknuepfung

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem bein_und (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin "&&" l r) :=
  bein_bool "&&" (Or.inl rfl) l r hl hr

theorem bein_oder (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin "||" l r) :=
  bein_bool "||" (Or.inr rfl) l r hl hr

/-- An extra parenthesis around a predicate preserves either expression outcome. -/
theorem bein_prim_klammer (e : SExpr) (h : PredBein e) (R : List Token) (G : Nat)
    (hG : bE e + 9 ≤ G) :
    AusdruckAntwort (parsePrimary G (.zeichen "(" :: (druckToks e ++ .zeichen ")" :: R))) e R := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  apply antwort_klammer
  exact antwort_or (bE e) (druckToks e) (.zeichen ")" :: R) e (hr_paren R)
    (fun F hF => h.expr _ F (atomFolge_zeichen ")" R (Or.inr (Or.inr (Or.inr rfl))))
      (by omega)) g (by omega)

theorem bein_cmp_klammer (e : SExpr) (h : PredBein e) (R : List Token) (hR : CmpStop R)
    (G : Nat) (hG : bE e + 16 ≤ G) :
    AusdruckAntwort (parseCmp G (.zeichen "(" :: (druckToks e ++ .zeichen ")" :: R))) e R := by
  have hU : ∀ F, bE e + 10 + 2 ≤ F →
      AusdruckAntwort (parseUnary F ((.zeichen "(" :: (druckToks e ++ [.zeichen ")"])) ++ R)) e R := by
    intro F hF
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
    rw [unary_klammer]
    exact bein_prim_klammer e h R f (by omega)
  have hC := antwort_cmp (bE e + 10) (.zeichen "(" :: (druckToks e ++ [.zeichen ")"]))
    R e hR hU G hG
  simpa only [List.cons_append, List.append_assoc, List.singleton_append] using hC

theorem bein_nicht (x : SExpr) (hx : PredBein x) : PredBein (.un "!" x) := by
  by_cases hg : gut (.un "!" x) = true
  · exact bein_expr _ hg
  · have hgx : gut x = false := by
      cases h : gut x
      · rfl
      · exact absurd (by simp only [gut, h, Bool.and_true, strEq_bang_klammer, Bool.false_and, Bool.or_false]; decide) hg
    have hdr := druck_nichtKopf _ (nichtKopf_un x)
    have hW : atomWert (.un "!" x) = x := by simp only [atomWert, strEq_self, ↓reduceIte]
    obtain ⟨t, ts, hxd, hxb, hxk⟩ := hx.kopf
    have hlen : (druckToks x).length + 1 ≤ (druckToks (.un "!" x)).length := by
      cases ha : istAtom x <;> simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true,
        ↓reduceIte, ha, List.cons_append, List.nil_append, List.length_cons,
        List.length_append, List.length_nil, Nat.zero_add, Nat.add_le_add_iff_right,
        Nat.le_add_right, Std.le_refl]
    refine ⟨?_, ?_, ⟨_, _, hdr, fun _ => nichtKopf_un x, fun _ => Or.inr rfl⟩⟩
    · intro R G hR hG
      rw [hW]
      cases ha : istAtom x with
      | true =>
        have hnk : nichtKopf x = false := by cases x <;> simp_all [istAtom, nichtKopf]
        obtain ⟨h1, h2⟩ := atom_nicht_nichtKopf x hnk
        have := hx.atom R G hR (by simp only [bP] at hG ⊢; omega)
        rw [h1, h2] at this
        simpa [atomTeil, strEq_self, ha] using this
      | false =>
        simp only [atomTeil, strEq_self, ite_true, ha, Bool.false_eq_true, ite_false,
          List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
        obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
        have hlen' : (druckToks (.un "!" x)).length = (druckToks x).length + 3 := by
          simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true, ite_false, ha,
            List.length_append, List.length_cons, List.length_nil]; omega
        have hC := bein_cmp_klammer x hx R hR.cmp g
          (by simp only [bP, bE, hlen'] at hG ⊢; omega)
        exact atom_klammer_antwort _ _ R _ hR hC (bein_top x hx (.zeichen ")" :: R) g
          ⟨rfl, rfl, rfl, by simp, by simp, by simp⟩
          (by simp only [bP, hlen'] at hG ⊢; omega))
    · intro R G hR hG
      obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by simp only [bE] at hG; omega⟩
      have hP : AusdruckAntwort (parsePrimary g (atomTeil (.un "!" x) ++ R)) x R := by
        cases ha : istAtom x with
        | true =>
          have ht : t = .zeichen "(" := by
            rcases hxk hgx with h | h
            · exact h
            · have := hxb h
              cases x <;> simp_all [istAtom, nichtKopf]
          simp only [atomTeil, strEq_self, ite_true, ha]
          have hU := hx.expr R (g + 1) hR (by simp only [bE] at hG ⊢; omega)
          rw [hxd, ht, List.cons_append, unary_klammer] at hU
          rw [hxd, ht, List.cons_append]
          exact hU
        | false =>
          simp only [atomTeil, strEq_self, ite_true, ha, Bool.false_eq_true, ite_false,
            List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
          have hlen' : (druckToks (.un "!" x)).length = (druckToks x).length + 3 := by
            simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true, ite_false, ha,
              List.length_append, List.length_cons, List.length_nil]; omega
          exact bein_prim_klammer x hx R g (by simp only [bE, hlen'] at hG ⊢; omega)
      rw [hdr, List.cons_append]
      rcases hP with hP | ⟨m, hP⟩
      · exact Or.inl (by simp only [parseUnary, hP])
      · exact Or.inr ⟨m, by simp only [parseUnary, hP]⟩

theorem bein_folgt (a b : SExpr) (ha : PredBein a) (hb : PredBein b) : PredBein (.ext .imp [] [a, b]) := by
  have hdr := folgt_druck a b
  have hF : ∀ R, Fehlt parseUnary (bE (.ext .imp [] [a, b]))
      (druckToks (.ext .imp [] [a, b]) ++ R) := by
    intro R G hG
    simp only [bE, hdr, List.cons_append, List.nil_append, List.append_assoc,
      List.length_cons, List.length_append, List.length_nil] at hG
    rw [hdr]
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
    rw [unary_klammer]
    have hO := antwort_or (bE a) (druckToks a)
      (.zeichen "=>" :: (druckToks b ++ .zeichen ")" :: R)) a rfl
      (fun F hF => ha.expr _ F (atomFolge_zeichen "=>" _ (Or.inr (Or.inr (Or.inl rfl))))
        (by omega)) g (by simp only [bE]; omega)
    rcases hO with hO | ⟨m, hO⟩
    · exact ⟨"( without )", by simp only [parsePrimary, hO, List.cons.injEq,
        Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]⟩
    · exact ⟨m, by simp only [parsePrimary, hO]⟩
  refine ⟨?_, fun R G _ hG => Or.inr (hF R G hG), ⟨_, _, hdr,
    by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
  intro R G hR hG
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
  simp only [atomTeil, atomWert]
  obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) g (by simp only [bP, bE] at hG ⊢; omega)
  simp only [bP] at hG
  rw [hdr] at hm hG ⊢
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hG
  obtain ⟨g4, rfl⟩ : ∃ g4, g = g4 + 4 := ⟨g - 4, by omega⟩
  exact atom_klammer _ _ R _ m hm
    (folgt_innen a b ha hb R g4 (by simp only [bP]; omega) (by simp only [bP]; omega))

/-- **The induction**: every printable predicate has its legs. -/
theorem pred_bein : ∀ (e : SExpr), PredGut e → PredBein e := by
  intro e h
  induction h with
  | expr e hg => exact bein_expr e hg
  | quant k x dk ns ops body hk hd _ ih => exact bein_quant k hk x dk ns ops hd body ih
  | und l r _ _ ihl ihr => exact bein_und l r ihl ihr
  | oder l r _ _ ihl ihr => exact bein_oder l r ihl ihr
  | nicht x _ ih => exact bein_nicht x ih
  | folgt a b _ _ iha ihb => exact bein_folgt a b iha ihb

/-- **Predicates with quantifiers read back** through `parsePred`, before a predicate follow. -/
theorem pred_voll (e : SExpr) (h : PredGut e) (R : List Token) (hR : PredFolge R) (F : Nat)
    (hF : bP e + 4 ≤ F) : parsePred F (druckToks e ++ R) = .ok (e, R) :=
  bein_top e (pred_bein e h) R F hR hF

/-- Existentials with any printable predicate body also read back as expressions. -/
theorem exists_expr_voll (x dk : String) (ns : List String) (ops : List SExpr)
    (hd : DomGut dk ns ops) (body : SExpr) (hb : PredGut body) (R : List Token) (G : Nat)
    (hG : bE (.ext .any (x :: dk :: ns) (ops ++ [body])) ≤ G) :
    parseUnary G (druckToks (.ext .any (x :: dk :: ns) (ops ++ [body])) ++ R) =
      .ok (.ext .any (x :: dk :: ns) (ops ++ [body]), R) :=
  exists_unary_rund x dk ns ops hd body (pred_bein body hb) R G hG

/-! ### Witness -/

/-- An expression-level existential may contain a predicate-only universal. -/
def zeugeExistsExpr : SExpr :=
  .ext .any ["x", "threads"] [.ext .all ["y", "threads"] [.tru]]

theorem zeugeExistsExpr_body : PredGut (.ext .all ["y", "threads"] [.tru]) :=
  .quant .all "y" "threads" [] [] .tru (Or.inl rfl) .threads (.expr .tru (by decide))

theorem zeugeExistsExpr_unary :
    parseUnary 300 (druckToks zeugeExistsExpr ++ [.ende]) = .ok (zeugeExistsExpr, [.ende]) :=
  exists_expr_voll "x" "threads" [] [] .threads _ zeugeExistsExpr_body [.ende] 300 (by decide)

theorem zeugeExistsExpr_pred :
    parsePred 300 (druckToks zeugeExistsExpr ++ [.ende]) = .ok (zeugeExistsExpr, [.ende]) :=
  pred_voll zeugeExistsExpr
    (.quant .any "x" "threads" [] [] _ (Or.inr rfl) .threads zeugeExistsExpr_body)
    [.ende] ⟨rfl, rfl, rfl, by simp, by simp, by simp⟩ 300 (by decide)

/-- `(!(exists k in queue Q : true) => ((forall s in descendants of b.kinder : s >= 0) || x))`:
    an implication over a negated `exists`, a `||` over a `forall`, a `queue` and a place domain. -/
def zeugePred : SExpr :=
  .ext .imp [] [.un "!" (.ext .any ["k", "queue"] [.variable "Q", .tru]),
    .bin "||" (.ext .all ["s", "descendants"] [.field (.variable "b") "kinder", .bin ">=" (.variable "s") (.lit 0)])
      (.variable "x")]

theorem zeugePred_gut : PredGut zeugePred :=
  .folgt _ _ (.nicht _ (.quant .any "k" "queue" [] [.variable "Q"] _ (Or.inr rfl) (.queue _ (by decide))
      (.expr _ (by decide))))
    (.oder _ _ (.quant .all "s" "descendants" [] [.field (.variable "b") "kinder"] _ (Or.inl rfl)
      (.ort _ _ (Or.inr (Or.inl rfl)) (by decide)) (.expr _ (by decide))) (.expr _ (by decide)))

/-- The witness reads back through the predicate reader. -/
theorem zeugePred_rund : parsePred 400 (druckToks zeugePred ++ [.ende]) = .ok (zeugePred, [.ende]) :=
  pred_voll zeugePred zeugePred_gut [.ende] ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, List.nil_eq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, List.nil_eq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, List.nil_eq, false_and, not_false_eq_true, implies_true]⟩ 400 (by decide)

/-- Its rendered text lexes back to its tokens (so the reader sees the same list). -/
theorem zeugePred_text : lex (renderText (druckToks zeugePred)) = .ok (druckToks zeugePred ++ [.ende]) :=
  lex_render _ (tokGut_of_all _ (by decide))

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.exists_expr_voll
#print axioms Gabbro.Grammatik.Parser.zeugeExistsExpr_unary
#print axioms Gabbro.Grammatik.Parser.zeugeExistsExpr_pred
#print axioms Gabbro.Grammatik.Parser.pred_voll
#print axioms Gabbro.Grammatik.Parser.zeugePred_rund
#print axioms Gabbro.Grammatik.Parser.zeugePred_text

/-
  CUTS: what the predicate round trip does not cover, and why.

  * `count x in D : p`: the reader takes `count` at the primary level (`parsePrimary`), so it is an
    expression form that nests inside comparisons; it needs its own leg in the expression towers
    (`LegsB`), not a predicate leg.
  * `e in D` and `a reaches b via f` (`ext .mem`, `ext .reach`): the reader takes them behind a
    comparison (`parsePredAtom` after `parseCmp`); a further `PredGut` case each, with the
    comparison leg before `in`/`reaches`.
  * The domains `fields of` a path and `chain (x, y) in` a place: two more `DomGut` cases.
-/
