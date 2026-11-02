module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2a
public import Grammatik.Parser.Round.Statements.RundlaufPred
public import Grammatik.Parser.Round.RundlaufQuant.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem bein_und (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin "&&" l r) := by
  by_cases hg : gut (.bin "&&" l r) = true
  · exact bein_expr _ hg
  · have hgf : gut (.bin "&&" l r) = false := by simpa using hg
    have hdr : druckToks (.bin "&&" l r) =
        .zeichen "(" :: (druckToks l ++ .zeichen "&&" :: (druckToks r ++ [.zeichen ")"])) := by
      simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
    have hF : ∀ R, Fehlt parseUnary (bE (.bin "&&" l r)) (druckToks (.bin "&&" l r) ++ R) := by
      intro R
      rw [hdr]
      simp only [List.cons_append, List.append_assoc, List.singleton_append]
      have hL : (druckToks l).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hl.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      have hR' : (druckToks r).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hr.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      apply fehlt_mono (fehlt_klammer (b := bE (.bin "&&" l r) - 2) _)
      · simp only [bE]; omega
      · cases hgl : gut l with
        | false =>
          exact fehlt_mono (fehlt_or_u (hl.fehlt hgl _)) (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
        | true =>
          have hgr : gut r = false := by
            cases hgr : gut r
            · rfl
            · have : gut (.bin "&&" l r) = true := by simp only [gut, hgl, hgr, Bool.and_true]; decide
              rw [this] at hgf; cases hgf
          exact und_fehlt l hgl _ _ _ (fehlt_cmp_u (hr.fehlt hgr _)) (by simp only [fb, bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
            (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
    refine ⟨?_, fun _ R => hF R, ⟨_, _, hdr, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
    intro R G hR hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
    simp only [atomTeil, atomWert]
    obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP, bE] at hG ⊢; omega)
    simp only [bP] at hG
    rw [hdr] at hm hG ⊢
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hG
    obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 4 := ⟨G' - 4, by omega⟩
    exact atom_klammer _ _ R _ m hm (und_innen l r hl hr R G5 (by simp only [bP]; omega) (by simp only [bP]; omega))

theorem bein_oder (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin "||" l r) := by
  by_cases hg : gut (.bin "||" l r) = true
  · exact bein_expr _ hg
  · have hgf : gut (.bin "||" l r) = false := by simpa using hg
    have hdr : druckToks (.bin "||" l r) =
        .zeichen "(" :: (druckToks l ++ .zeichen "||" :: (druckToks r ++ [.zeichen ")"])) := by
      simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
    have hF : ∀ R, Fehlt parseUnary (bE (.bin "||" l r)) (druckToks (.bin "||" l r) ++ R) := by
      intro R
      rw [hdr]
      simp only [List.cons_append, List.append_assoc, List.singleton_append]
      have hL : (druckToks l).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hl.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      have hR' : (druckToks r).length ≥ 1 := by
        obtain ⟨t, ts, h, -⟩ := hr.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
      apply fehlt_mono (fehlt_klammer (b := bE (.bin "||" l r) - 2) _)
      · simp only [bE]; omega
      · cases hgl : gut l with
        | false =>
          exact fehlt_mono (fehlt_or_u (hl.fehlt hgl _)) (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
        | true =>
          have hgr : gut r = false := by
            cases hgr : gut r
            · rfl
            · have : gut (.bin "||" l r) = true := by simp only [gut, hgl, hgr, Bool.and_true]; decide
              rw [this] at hgf; cases hgf
          exact oder_fehlt l hgl _ _ _ (fehlt_and (fehlt_cmp_u (hr.fehlt hgr _)))
            (by simp only [fb, bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega) (by simp only [bE, hdr]; simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceSubDiff, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)
    refine ⟨?_, fun _ R => hF R, ⟨_, _, hdr, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
    intro R G hR hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
    simp only [atomTeil, atomWert]
    obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP, bE] at hG ⊢; omega)
    simp only [bP] at hG
    rw [hdr] at hm hG ⊢
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hG
    obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 4 := ⟨G' - 4, by omega⟩
    exact atom_klammer _ _ R _ m hm (oder_innen l r hl hr R G5 (by simp only [bP]; omega) (by simp only [bP]; omega))

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
      cases ha : istAtom x <;> simp only [druckToks, strEq_bang_klammer, Bool.false_eq_true, ↓reduceIte, ha, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_le_add_iff_right, Nat.le_add_right, Std.le_refl]
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
        simp only [atomTeil, strEq_self, ite_true, ha, Bool.false_eq_true, ite_false, List.cons_append,
          List.nil_append, List.append_assoc, List.singleton_append]
        obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
        have hF : Fehlt parseCmp (bE x + 12) (.zeichen "(" :: (druckToks x ++ .zeichen ")" :: R)) :=
          fehlt_cmp_u (fehlt_klammer (fehlt_or_u (hx.fehlt hgx (.zeichen ")" :: R))))
        obtain ⟨m, hm⟩ := hF G' (by simp only [bP, bE] at hG ⊢; omega)
        exact atom_klammer _ _ R _ m hm (bein_top x hx (.zeichen ")" :: R) G'
          ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ (by simp only [bP] at hG ⊢; omega))
    · intro _ R
      rw [hdr, List.cons_append]
      apply fehlt_mono (fehlt_nicht (b := bE x + 7) _) (by simp only [bE]; omega)
      cases ha : istAtom x with
      | true =>
        have ht : t = .zeichen "(" := by
          rcases hxk hgx with h | h
          · exact h
          · have := hxb h
            cases x <;> simp_all [istAtom, nichtKopf]
        simp only [atomTeil, strEq_self, ite_true, ha]
        have h0 := hx.fehlt hgx R
        rw [hxd, ht, List.cons_append] at h0
        rw [hxd, ht, List.cons_append]
        exact fehlt_mono (fehlt_prim_aus_unary h0) (by omega)
      | false =>
        simp only [atomTeil, strEq_self, ite_true, ha, Bool.false_eq_true, ite_false, List.cons_append,
          List.nil_append, List.append_assoc, List.singleton_append]
        exact fehlt_mono (fehlt_prim_klammer (fehlt_or_u (hx.fehlt hgx (.zeichen ")" :: R)))) (by omega)

theorem bein_folgt (a b : SExpr) (ha : PredBein a) (hb : PredBein b) : PredBein (.ext .imp [] [a, b]) := by
  have hdr := folgt_druck a b
  have hgf : gut (.ext .imp [] [a, b]) = false := rfl
  have hL : (druckToks a).length ≥ 1 := by
    obtain ⟨t, ts, h, -⟩ := ha.kopf; rw [h]; simp only [List.length_cons, ge_iff_le, Nat.le_add_left]
  have hF : ∀ R, Fehlt parseUnary (bE (.ext .imp [] [a, b])) (druckToks (.ext .imp [] [a, b]) ++ R) := by
    intro R
    rw [hdr]
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    have hX : gut a = true ∨ Fehlt parseOr (bE a + 6) (druckToks a ++ .zeichen "=>" ::
        (druckToks b ++ .zeichen ")" :: R)) := by
      cases hga : gut a with
      | true => exact Or.inl rfl
      | false => exact Or.inr (fehlt_or_u (ha.fehlt hga _))
    apply fehlt_mono (fehlt_unary_aus_prim (folgt_fehlt a _ (bE a + 6) (bE (.ext .imp [] [a, b]) - 1) hX
      (by simp only [fb, bE, hdr]; simp only [List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_one_sub_one, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega) (by simp only [bE, hdr]; simp only [List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_one_sub_one, Nat.add_le_add_iff_right, Nat.reduceLeDiff]; omega)))
    simp only [bE]; omega
  refine ⟨?_, fun _ R => hF R, ⟨_, _, hdr, by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
  intro R G hR hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
  simp only [atomTeil, atomWert]
  obtain ⟨m, hm⟩ := fehlt_cmp_u (hF R) G' (by simp only [bP, bE] at hG ⊢; omega)
  simp only [bP] at hG
  rw [hdr] at hm hG ⊢
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at hm ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hG
  obtain ⟨G5, rfl⟩ : ∃ G5, G' = G5 + 4 := ⟨G' - 4, by omega⟩
  exact atom_klammer _ _ R _ m hm (folgt_innen a b ha hb R G5 (by simp only [bP]; omega) (by simp only [bP]; omega))

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

/-! ### Witness -/

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
