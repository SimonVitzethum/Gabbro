module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The `bin "||"` tower from a binary-inner leg: word for word
-- the `*` tower with the spelling swapped (no proof step
-- inspects the spelling).
theorem kern_bin_or_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "||" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "||"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "||" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "&&"` tower from a binary-inner leg: word for word
-- the `||` tower with the spelling swapped.
theorem kern_bin_and_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "&&" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "&&"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "&&" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩


end Gabbro.Grammatik.Parser
