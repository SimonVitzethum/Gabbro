module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2a

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- Both Boolean operators preserve an exact expression result; an operand failure
    propagates to the expression attempt, leaving predicate fallback available. -/
theorem bool_innen_antwort (o : String) (ho : o = "&&" ∨ o = "||")
    (l r : SExpr) (hl : PredBein l) (hr : PredBein r) (R : List Token) (G : Nat)
    (h1 : bE l + 6 ≤ G) (h2 : bE r + 6 ≤ G) :
    AusdruckAntwort (parseOr (G + 4)
      (druckToks l ++ .zeichen o :: (druckToks r ++ .zeichen ")" :: R)))
      (.bin o l r) (.zeichen ")" :: R) := by
  have uAnd : ∀ T : List Token, opUnd (.zeichen "&&" :: T) = some T := fun _ => rfl
  have uOr : ∀ T : List Token, opUnd (.zeichen "||" :: T) = none := fun _ => rfl
  have uEnd : opUnd (.zeichen ")" :: R) = none := rfl
  have oOr : ∀ T : List Token, opOder (.zeichen "||" :: T) = some T := fun _ => rfl
  have oEnd : opOder (.zeichen ")" :: R) = none := rfl
  have hRC := bein_cmp r hr (.zeichen ")" :: R)
    (atomFolge_zeichen ")" R (Or.inr (Or.inr (Or.inr rfl)))) (G + 1) (by omega)
  have hLC := bein_cmp l hl (.zeichen o :: (druckToks r ++ .zeichen ")" :: R))
    (atomFolge_zeichen o _ (by
      rcases ho with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)))
    (G + 2) (by omega)
  rcases ho with rfl | rfl <;>
    rcases hLC with hLC | ⟨m, hLC⟩
  · rcases hRC with hRC | ⟨m, hRC⟩
    · exact Or.inl (by simp only [parseOr, parseAnd, hLC, parseAndL, uAnd, uOr, uEnd, hRC, parseOrL, oOr, oEnd])
    · exact Or.inr ⟨m, by simp only [parseOr, parseAnd, hLC, parseAndL, uAnd, uOr, uEnd, hRC]⟩
  · exact Or.inr ⟨m, by simp only [parseOr, parseAnd, hLC]⟩
  · rcases hRC with hRC | ⟨m, hRC⟩
    · exact Or.inl (by simp only [parseOr, parseAnd, hLC, parseAndL, uAnd, uOr, uEnd, parseOrL, oOr, oEnd, hRC])
    · exact Or.inr ⟨m, by simp only [parseOr, parseAnd, hLC, parseAndL, uAnd, uOr, uEnd, parseOrL, oOr, oEnd, hRC]⟩
  · exact Or.inr ⟨m, by simp only [parseOr, parseAnd, hLC]⟩

/-- A shared induction step for conjunction and disjunction, independent of whether
    either predicate is also an expression. -/
theorem bein_bool (o : String) (ho : o = "&&" ∨ o = "||")
    (l r : SExpr) (hl : PredBein l) (hr : PredBein r) : PredBein (.bin o l r) := by
  have hdr : druckToks (.bin o l r) =
      .zeichen "(" :: (druckToks l ++ .zeichen o :: (druckToks r ++ [.zeichen ")"])) := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hE : ∀ R G, AtomFolge R → bE (.bin o l r) ≤ G →
      AusdruckAntwort (parseUnary G (druckToks (.bin o l r) ++ R)) (.bin o l r) R := by
    intro R G _ hG
    simp only [bE, hdr, List.length_cons, List.length_append, List.length_nil] at hG
    rw [hdr]
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 6 := ⟨G - 6, by omega⟩
    rw [unary_klammer]
    exact antwort_klammer _ _ _ _ (bool_innen_antwort o ho l r hl hr R g
      (by simp only [bE]; omega) (by simp only [bE]; omega))
  refine ⟨?_, hE, ⟨_, _, hdr,
    by simp only [Token.zeichen.injEq, String.reduceEq, false_implies], fun _ => Or.inl rfl⟩⟩
  intro R G hR hG
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by simp only [bP] at hG; omega⟩
  simp only [atomTeil, atomWert]
  have hC := antwort_cmp (bE (.bin o l r)) (druckToks (.bin o l r)) R _ hR.cmp
    (fun F hF => hE R F hR (by omega)) g (by simp only [bP, bE] at hG ⊢; omega)
  simp only [bP, hdr, List.length_cons, List.length_append, List.length_nil] at hG
  rw [hdr] at hC ⊢
  simp only [List.cons_append, List.append_assoc, List.singleton_append] at hC ⊢
  obtain ⟨g4, rfl⟩ : ∃ g4, g = g4 + 4 := ⟨g - 4, by omega⟩
  apply atom_klammer_antwort _ _ R _ hR hC
  rcases ho with rfl | rfl
  · exact und_innen l r hl hr R g4 (by simp only [bP]; omega) (by simp only [bP]; omega)
  · exact oder_innen l r hl hr R g4 (by simp only [bP]; omega) (by simp only [bP]; omega)

end Gabbro.Grammatik.Parser
