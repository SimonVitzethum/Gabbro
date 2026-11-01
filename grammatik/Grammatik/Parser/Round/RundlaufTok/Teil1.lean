module

public import Grammatik.Parser.Round.RundlaufVoll

@[expose] public section



namespace Gabbro.Grammatik.Parser

/-- The eight round-trip legs at an abstract fuel bound `m` (`Legs` is the instance at the size
    bound). -/
def LegsB (m : Nat) (e : SExpr) : Prop :=
  (∀ (rest : List Token) (G : Nat), primFrei e = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 1 ≤ G →
    parsePrimary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhigSuff rest = true →
    ruhigGleit rest = true → m + 2 ≤ G →
    parseUnary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 3 ≤ G →
    parseMul G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 4 ≤ G →
    parseAdd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 5 ≤ G →
    parseBit G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 6 ≤ G →
    parseCmp G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 7 ≤ G →
    parseAnd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 8 ≤ G →
    parseOr G (druckToks e ++ rest) = .ok (e, rest))

/-- `Legs` is `LegsB` at the size bound. -/
theorem legsB_of_legs (e : SExpr) (h : Legs e) : LegsB (12 * (groesse e + 1) + groesse e) e := h

/-- A bound may always be raised. -/
theorem LegsB_mono {m m' : Nat} {e : SExpr} (hm : m ≤ m') (h : LegsB m e) : LegsB m' e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G a b c hG; exact h1 rest G a b c (by omega)
  · intro rest G a b hG; exact h2 rest G a b (by omega)
  · intro rest G a b c hG; exact h3 rest G a b c (by omega)
  · intro rest G a b c hG; exact h4 rest G a b c (by omega)
  · intro rest G a b c hG; exact h5 rest G a b c (by omega)
  · intro rest G a b c hG; exact h6 rest G a b c (by omega)
  · intro rest G a b c hG; exact h7 rest G a b c (by omega)
  · intro rest G a b c hG; exact h8 rest G a b c (by omega)

/-! ### Towers and inner traces over an abstract bound (Rundlauf2/3, restated over `m`) -/

theorem tower_upM : ∀ (m : Nat) (e : SExpr) (rest : List Token),
    ruhig rest = true →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks e ++ rest) = .ok (e, rest)) →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 7 ≤ G →
      parseAnd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 8 ≤ G →
      parseOr G (druckToks e ++ rest) = .ok (e, rest)) := by
  intro m e rest hr hU
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
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
      m + 4 ≤ G →
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
      m + 5 ≤ G →
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
      m + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hstop := stopVgl rest hr
    simp only [parseCmp, hB', hstop] at ⊢
  have hN : ∀ (G : Nat),
      m + 7 ≤ G →
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
      m + 8 ≤ G →
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

theorem tower_up_orbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none → opUnd S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd hBit hVgl hUnd
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  have hC : ∀ (G : Nat),
      m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  have hN : ∀ (G : Nat),
      m + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAnd, parseAndL, hC', hUnd] at ⊢
  exact ⟨hM, hA, hB, hC, hN⟩

theorem tower_up_andbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd hBit hVgl
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  have hC : ∀ (G : Nat),
      m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  exact ⟨hM, hA, hB, hC⟩

theorem tower_up_cmpbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd hBit
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  exact ⟨hM, hA, hB⟩

theorem tower_up_bitbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  exact ⟨hM, hA⟩

theorem cmpB_stepM : ∀ (m : Nat) (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opAdd ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opBit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opVgl ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro m op l r W hUl hUr hMul hAdd hBit hop G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand at `parseBit` with the operator follow.
  have hBl : ∀ (G5 : Nat),
      m + 5 ≤ G5 →
      parseBit G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have hbar := tower_up_cmpbarM m l ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) hUl hMul hAdd hBit
    exact hbar.2.2 G5 hG5
  -- Right operand at `parseBit` with the `)` follow.
  have hBr : ∀ (G5x : Nat),
      m + 5 ≤ G5x →
      parseBit G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have hup := tower_upM m r ([.zeichen ")"] ++ W) (hr_paren W) hUr
    exact hup.2.2.1 G5x hG5x
  -- The `parseCmp` core: `l`, consume the operator, `r`. No
  -- loop stop: the single-shot level has no loop.
  have hCmp : ∀ (G2 : Nat),
      m + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBl' := hBl G3 (by omega)
    have hBr' := hBr G3 (by omega)
    simp only [parseCmp, hBl', hop, hBr'] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hAnd : ∀ (G1 : Nat),
      m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      m + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG

end Gabbro.Grammatik.Parser
