module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The full eight-level tower for one literal shape. Every
-- leg is generalised over its own fuel (so upper levels reuse
-- lower ones at stripped fuel, and every `RKern` level
-- instantiates at its own staggered bound). Pattern for every
-- atom shape in step A.
theorem turm_lit : ∀ (m : Nat) (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 1 ≤ G →
      parsePrimary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 2 ≤ G →
      parseUnary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 3 ≤ G →
      parseMul G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 4 ≤ G →
      parseAdd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 5 ≤ G →
      parseBit G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 6 ≤ G →
      parseCmp G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 7 ≤ G →
      parseAnd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 8 ≤ G →
      parseOr G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest)) := by
  intro m rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 1 ≤ G →
      parsePrimary G (druckToks (.lit m) ++ rest) =
        .ok (.lit m, rest) := by
    intro G hG
    exact prim_lit m rest G (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 2 ≤ G →
      parseUnary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hM : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 3 ≤ G →
      parseMul G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopMul rest hr
    simp only [parseMul, parseMulL, hU', hstop] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 4 ≤ G →
      parseAdd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopAdd rest hr
    simp only [parseAdd, parseAddL, hM', hstop] at ⊢
  have hB : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 5 ≤ G →
      parseBit G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopBit rest hr
    simp only [parseBit, parseBitL, hA', hstop] at ⊢
  have hC : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 6 ≤ G →
      parseCmp G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hstop := stopVgl rest hr
    simp only [parseCmp, hB', hstop] at ⊢
  have hN : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 7 ≤ G →
      parseAnd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopUnd rest hr
    simp only [parseAnd, parseAndL, hC', hstop] at ⊢
  have hO : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 8 ≤ G →
      parseOr G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hN' := hN G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopOder rest hr
    simp only [parseOr, parseOrL, hN', hstop] at ⊢
  exact ⟨hP, hU, hM, hA, hB, hC, hN, hO⟩

-- The shape-independent upper tower (`parseMul` up to
-- `parseOr`): every level runs its child and stops its loop on
-- the benign follow. Callers supply the `parseUnary` leg (which
-- is the only head-dependent step) generalised over its fuel;
-- every leg is returned generalised, so each `RKern` level
-- instantiates at its own staggered bound.
theorem tower_up : ∀ (e : SExpr) (rest : List Token),
    ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 2 ≤ G →
      parseUnary G (druckToks e ++ rest) = .ok (e, rest)) →
    (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 3 ≤ G →
      parseMul G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 4 ≤ G →
      parseAdd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 5 ≤ G →
      parseBit G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 7 ≤ G →
      parseAnd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 8 ≤ G →
      parseOr G (druckToks e ++ rest) = .ok (e, rest)) := by
  intro e rest hr hU
  have hM : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 3 ≤ G →
      parseMul G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopMul rest hr
    simp only [parseMul, parseMulL, hU', hstop] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 4 ≤ G →
      parseAdd G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopAdd rest hr
    simp only [parseAdd, parseAddL, hM', hstop] at ⊢
  have hB : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 5 ≤ G →
      parseBit G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopBit rest hr
    simp only [parseBit, parseBitL, hA', hstop] at ⊢
  have hC : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hstop := stopVgl rest hr
    simp only [parseCmp, hB', hstop] at ⊢
  have hN : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 7 ≤ G →
      parseAnd G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopUnd rest hr
    simp only [parseAnd, parseAndL, hC', hstop] at ⊢
  have hO : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 8 ≤ G →
      parseOr G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hN' := hN G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopOder rest hr
    simp only [parseOr, parseOrL, hN', hstop] at ⊢
  exact ⟨hM, hA, hB, hC, hN, hO⟩


end Gabbro.Grammatik.Parser
