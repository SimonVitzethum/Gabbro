module

public import Grammatik.Parser.Round.Rundlauf2.Teil2a
public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- The `||`-follow upper tower (`parseMul` up to `parseAnd`):
-- mirror of `tower_up`, but every loop stops on the concrete
-- `||` head (miss facts as hypotheses) instead of a benign
-- follow. Needed for the left operand of the `||` inner
-- trace, whose follow is the operator itself.
theorem tower_up_orbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none → opUnd S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd hBit hVgl hUnd
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
  have hC : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  have hN : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAnd, parseAndL, hC', hUnd] at ⊢
  exact ⟨hM, hA, hB, hC, hN⟩

-- The `&&`-follow upper tower (`parseMul` up to `parseCmp`):
-- mirror of `tower_up_orbar` one level down (the single
-- comparison check misses the concrete `&&`).
theorem tower_up_andbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd hBit hVgl
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
  have hC : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  exact ⟨hM, hA, hB, hC⟩

-- A bare atom head is `primFrei` (only prefix trees and
-- `fnref` are not).
theorem primFrei_of_atom : ∀ (x : SExpr), istAtom x = true →
    gutKern x = true → primFrei x = true := by
  intro x hat hgx
  cases x with
  | lit m => rfl
  | float s => rfl
  | tru => rfl
  | fls => rfl
  | «variable» s => rfl
  | field x f => rfl
  | index x i => rfl
  | arrow x f => rfl
  | un o y => simp only [istAtom, Bool.false_eq_true] at hat
  | bin o l r => simp only [istAtom, Bool.false_eq_true] at hat
  | call f xs => simp only [gutKern, Bool.false_eq_true] at hgx
  | fnref f => simp only [istAtom, Bool.false_eq_true] at hat
  | built f xs => simp only [gutKern, Bool.false_eq_true] at hgx
  | old x => simp only [gutKern, Bool.false_eq_true] at hgx
  | res => simp only [gutKern, Bool.false_eq_true] at hgx
  | why g f => simp only [gutKern, Bool.false_eq_true] at hgx
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at hgx

-- Atom towers, one per remaining leaf shape: the `parsePrimary`
-- leg (concrete head) plus the `parseUnary` fall-through (head is
-- no prefix operator), then `tower_up` for the six loop levels.
theorem turm_gleit : ∀ (s : String) (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 1 ≤ G →
      parsePrimary G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 2 ≤ G →
      parseUnary G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 3 ≤ G →
      parseMul G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 4 ≤ G →
      parseAdd G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 5 ≤ G →
      parseBit G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 6 ≤ G →
      parseCmp G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 7 ≤ G →
      parseAnd G (druckToks (.float s) ++ rest) = .ok (.float s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.float s) + 1) + groesse (.float s) + 8 ≤ G →
      parseOr G (druckToks (.float s) ++ rest) = .ok (.float s, rest)) := by
  intro s rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse (.float s) + 1) + groesse (.float s) + 1 ≤ G →
      parsePrimary G (druckToks (.float s) ++ rest) =
        .ok (.float s, rest) := by
    intro G hG
    exact prim_gleit s rest G hrg (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse (.float s) + 1) + groesse (.float s) + 2 ≤ G →
      parseUnary G (druckToks (.float s) ++ rest) =
        .ok (.float s, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up (.float s) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_wahr : ∀ (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 1 ≤ G →
      parsePrimary G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 2 ≤ G →
      parseUnary G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 3 ≤ G →
      parseMul G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 4 ≤ G →
      parseAdd G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 5 ≤ G →
      parseBit G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 6 ≤ G →
      parseCmp G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 7 ≤ G →
      parseAnd G (druckToks .tru ++ rest) = .ok (.tru, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .tru + 1) + groesse .tru + 8 ≤ G →
      parseOr G (druckToks .tru ++ rest) = .ok (.tru, rest)) := by
  intro rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse .tru + 1) + groesse .tru + 1 ≤ G →
      parsePrimary G (druckToks .tru ++ rest) = .ok (.tru, rest) := by
    intro G hG
    exact prim_wahr rest G (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse .tru + 1) + groesse .tru + 2 ≤ G →
      parseUnary G (druckToks .tru ++ rest) = .ok (.tru, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up .tru rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

end Gabbro.Grammatik.Parser
