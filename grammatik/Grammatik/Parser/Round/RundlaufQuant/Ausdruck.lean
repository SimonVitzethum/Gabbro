module

public import Grammatik.Parser.Round.RundlaufQuant.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- An expression attempt either returns the intended tree and tail, or fails.
    Failure permits the predicate reader's parenthesised fallback. -/
def AusdruckAntwort (result : Except String (SExpr × List Token)) (e : SExpr) (R : List Token) : Prop :=
  result = .ok (e, R) ∨ ∃ message, result = .error message

/-- Carry both possible expression outcomes up to the comparison level. -/
theorem antwort_cmp (b : Nat) (T R : List Token) (e : SExpr) (hR : CmpStop R)
    (hU : ∀ G, b + 2 ≤ G → AusdruckAntwort (parseUnary G (T ++ R)) e R) :
    ∀ G, b + 6 ≤ G → AusdruckAntwort (parseCmp G (T ++ R)) e R := by
  have hM : ∀ G, b + 3 ≤ G → AusdruckAntwort (parseMul G (T ++ R)) e R := by
    intro G hG
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
    rcases hU (g + 1) (by omega) with h | ⟨m, h⟩
    · exact Or.inl (by simp only [parseMul, h, parseMulL, hR.mul])
    · exact Or.inr ⟨m, by simp only [parseMul, h]⟩
  have hA : ∀ G, b + 4 ≤ G → AusdruckAntwort (parseAdd G (T ++ R)) e R := by
    intro G hG
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
    rcases hM (g + 1) (by omega) with h | ⟨m, h⟩
    · exact Or.inl (by simp only [parseAdd, h, parseAddL, hR.add])
    · exact Or.inr ⟨m, by simp only [parseAdd, h]⟩
  have hB : ∀ G, b + 5 ≤ G → AusdruckAntwort (parseBit G (T ++ R)) e R := by
    intro G hG
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
    rcases hA (g + 1) (by omega) with h | ⟨m, h⟩
    · exact Or.inl (by simp only [parseBit, h, parseBitL, hR.bit])
    · exact Or.inr ⟨m, by simp only [parseBit, h]⟩
  intro G hG
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  rcases hB g (by omega) with h | ⟨m, h⟩
  · exact Or.inl (by simp only [parseCmp, h, hR.vgl])
  · exact Or.inr ⟨m, by simp only [parseCmp, h]⟩

theorem antwort_and (b : Nat) (T R : List Token) (e : SExpr) (hR : opUnd R = none)
    (hC : ∀ G, b + 6 ≤ G → AusdruckAntwort (parseCmp G (T ++ R)) e R) :
    ∀ G, b + 7 ≤ G → AusdruckAntwort (parseAnd G (T ++ R)) e R := by
  intro G hG
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
  rcases hC (g + 1) (by omega) with h | ⟨m, h⟩
  · exact Or.inl (by simp only [parseAnd, h, parseAndL, hR])
  · exact Or.inr ⟨m, by simp only [parseAnd, h]⟩

theorem antwort_or (b : Nat) (T R : List Token) (e : SExpr) (hR : ruhig R = true)
    (hU : ∀ G, b + 2 ≤ G → AusdruckAntwort (parseUnary G (T ++ R)) e R) :
    ∀ G, b + 8 ≤ G → AusdruckAntwort (parseOr G (T ++ R)) e R := by
  have hA := antwort_and b T R e (stopUnd R hR)
    (antwort_cmp b T R e (cmpStop_ruhig R hR) hU)
  intro G hG
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
  rcases hA (g + 1) (by omega) with h | ⟨m, h⟩
  · exact Or.inl (by simp only [parseOr, h, parseOrL, stopOder R hR])
  · exact Or.inr ⟨m, by simp only [parseOr, h]⟩

/-- Closing a parenthesis preserves the exact tree, tail, or error. -/
theorem antwort_klammer (G : Nat) (T R : List Token) (e : SExpr)
    (h : AusdruckAntwort (parseOr G T) e (.zeichen ")" :: R)) :
    AusdruckAntwort (parsePrimary (G + 1) (.zeichen "(" :: T)) e R := by
  rcases h with h | ⟨m, h⟩
  · exact Or.inl (paren_arm G T R e h)
  · exact Or.inr ⟨m, by simp only [parsePrimary, h]⟩

/-- `exists` uses the expression arm of `parsePrimary`, with the same `parseQuant`
    and layout as its predicate arm. No alternate tree is introduced. -/
theorem exists_prim_rund (x dk : String) (ns : List String) (ops : List SExpr)
    (body : SExpr) (T R : List Token) (G : Nat)
    (hD : parseDomain G T = .ok ((dk, ns, ops), .zeichen ":" :: (druckToks body ++ R)))
    (hB : parsePred G (druckToks body ++ R) = .ok (body, R)) :
    parsePrimary (G + 2) (.wort "exists" :: nameTok x :: .wort "in" :: T) =
      .ok (.ext .any (x :: dk :: ns) (ops ++ [body]), R) := by
  have hQ : parseQuant (G + 1) .any x T =
      .ok (.ext .any (x :: dk :: ns) (ops ++ [body]), R) := by
    simp only [parseQuant, hD, hB]
  rw [parsePrimary]
  simp only [nameText_nameTok, hQ]

end Gabbro.Grammatik.Parser
