module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



namespace Gabbro.Grammatik.Parser

-- The eight fuel-generalised round-trip legs for one fixed tree:
-- the `RKern` leg shapes with the size bound and the predicate
-- dropped. `parseUnary` takes no `ruhig` premise (it runs no
-- loop); `parsePrimary` takes `primFrei` (prefix trees live at
-- the unary level). Bounds copy `RKern` exactly (`+1` at
-- `parsePrimary` up to `+8` at `parseOr`).
def Legs (e : SExpr) : Prop :=
  (∀ (rest : List Token) (G : Nat), primFrei e = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 1 ≤ G →
    parsePrimary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 2 ≤ G →
    parseUnary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 3 ≤ G →
    parseMul G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 4 ≤ G →
    parseAdd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 5 ≤ G →
    parseBit G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 6 ≤ G →
    parseCmp G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 7 ≤ G →
    parseAnd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ G →
    parseOr G (druckToks e ++ rest) = .ok (e, rest))

-- Every `gutKern` tree has legs: the `Or`-through-`Primary` legs
-- of `kernRB` at `groesse e`, repackaged (the size premise closes
-- by reflexivity).
theorem legsKern : ∀ (e : SExpr), gutKern e = true → Legs e := by
  intro e hg
  have hRB := (kernRB (groesse e)).1
  obtain ⟨rOr, rAnd, rCmp, rBit, rAdd, rMul, rUn, rPr⟩ := hRB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hpf hrs hrg hG
    exact rPr e rest G (Nat.le_refl _) hg hpf hrs hrg hG
  · intro rest G hrs hrg hG
    exact rUn e rest G (Nat.le_refl _) hg hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rMul e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rAdd e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rBit e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rCmp e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rAnd e rest G (Nat.le_refl _) hg hr hrs hrg hG
  · intro rest G hr hrs hrg hG
    exact rOr e rest G (Nat.le_refl _) hg hr hrs hrg hG

-- LEVEL CMP (comparisons `==`, `!=`, `<=`, `>=`, `<`, `>`).
--
-- A lawful comparison spelling names itself: the six cases of
-- `istCmpOp`.
theorem cmp_is : ∀ (o : String), istCmpOp o = true →
    o = "==" ∨ o = "!=" ∨ o = "<=" ∨ o = ">=" ∨ o = "<" ∨ o = ">" := by
  intro o h
  simp only [istCmpOp, Bool.or_eq_true] at h
  obtain h5 | hF := h
  · obtain h4 | hE := h5
    · obtain h3 | hD := h4
      · obtain h2 | hC := h3
        · obtain hA | hB := h2
          · exact Or.inl (strKlingt o "==" hA)
          · exact Or.inr (Or.inl (strKlingt o "!=" hB))
        · exact Or.inr (Or.inr (Or.inl (strKlingt o "<=" hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o ">=" hD))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (strKlingt o "<" hE)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (strKlingt o ">" hF)))))

-- Facts for a comparison-operator follow: every loop below
-- `parseCmp` misses it (`parseCmp` itself consumes it -- the
-- single-shot level has no loop), and the suffix/float tails are
-- benign. One bundle for all six spellings (each case `rfl`).
theorem cmpbar_facts : ∀ (op : String) (T : List Token),
    istCmpOp op = true →
    opMul ([.zeichen op] ++ T) = none ∧
    opAdd ([.zeichen op] ++ T) = none ∧
    opBit ([.zeichen op] ++ T) = none ∧
    ruhigSuff ([.zeichen op] ++ T) = true ∧
    ruhigGleit ([.zeichen op] ++ T) = true := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl | rfl := cmp_is op h
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- The comparison table hits its own spelling (one lemma for all
-- six spellings; each case `rfl`).
theorem opVgl_cmp_hit : ∀ (op : String) (T : List Token),
    istCmpOp op = true →
    opVgl ([.zeichen op] ++ T) = some (op, T) := by
  intro op T h
  obtain rfl | rfl | rfl | rfl | rfl | rfl := cmp_is op h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

-- The `parseBit`-level bar tower for a comparison follow: from
-- the `parseUnary` leg, the three loop levels below `parseCmp`
-- each run their child and stop on the operator. Mirror of
-- `tower_up_orbar` (which stops five levels on `||`); here the
-- tower stops at `parseBit` because `parseCmp` consumes.
theorem tower_up_cmpbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd hBit
  have hM : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  exact ⟨hM, hA, hB⟩


end Gabbro.Grammatik.Parser
