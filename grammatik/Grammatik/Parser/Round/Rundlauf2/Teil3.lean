module
public import Grammatik.Parser.Round.Rundlauf2.Teil3a

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The `un` tower for PARENTHESISED (non-atom) children: the
-- `parseOr` leg (`)` follow) through the prefix arm into the
-- `(` arm, then `tower_up`.
theorem kern_un_paren_turm : ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    istAtom x = false → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
      parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
        .ok (x, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro o x rest hop hat hr hOx
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) =
        .ok (.un o x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un o x) = [.zeichen o] ++
        (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
      simp only [druckToks, un_ne_klammer _ hop, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
    have hF2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hO' := hOx G'' (by omega)
    have hPar := paren_arm _ _ _ _ hO'
    have hBang := bang_arm_gen _ _ _ _ _ hop hPar (Or.inr (nonatom_bed x hat))
    simp only [hd, List.append_assoc] at ⊢
    exact hBang
  have hup := tower_up (.un o x) rest hr hU
  exact ⟨hU, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "+"` tower from a binary-inner leg: the
-- `parsePrimary` leg runs the `(` arm over the inner parse, the
-- `parseUnary` leg falls through on `(`, then `tower_up`. Every
-- leg generalised over its own fuel.
theorem kern_bin_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    -- Inner token shape for `paren_arm`: `(` head, `l + r`
    -- body, `)` tail, all left-nested exactly as printed.
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    -- `hPar` and the goal differ by association only:
    -- canonicalise both, then they coincide.
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    -- Canonicalise both sides; the underscores let unification
    -- infer the middle and tail (the lemma holds for any tail).
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "+" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "*"` tower from a binary-inner leg: word for word
-- the `+` tower with the spelling swapped (no proof step
-- inspects the spelling -- the printer, the paren arm and the
-- fall-through are all spelling-blind).
theorem kern_bin_star_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "*" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "*"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "*" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

end Gabbro.Grammatik.Parser
