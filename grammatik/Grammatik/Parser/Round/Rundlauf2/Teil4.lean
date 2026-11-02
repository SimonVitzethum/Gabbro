module

public import Grammatik.Parser.Round.Rundlauf2.Teil4a

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Concrete op-table and benign-follow facts for the `+`
-- inner trace (probe piece: each must close by kernel
-- evaluation on the concrete head; tails stay variable).
theorem opMul_plus : ∀ (T : List Token),
    opMul ([.zeichen "+"] ++ T) = none := by
  intro T
  rfl
theorem opAdd_plus : ∀ (T : List Token),
    opAdd ([.zeichen "+"] ++ T) = some ("+", T) := by
  intro T
  rfl
theorem opAdd_paren : ∀ (T : List Token),
    opAdd ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opBit_paren : ∀ (T : List Token),
    opBit ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opVgl_paren : ∀ (T : List Token),
    opVgl ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opUnd_paren : ∀ (T : List Token),
    opUnd ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opOder_paren : ∀ (T : List Token),
    opOder ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opMul_paren : ∀ (T : List Token),
    opMul ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
-- Facts for the `*` inner trace: `parseMulL` consumes the
-- concrete `*`, and a `*` follow is benign for the suffix and
-- float tails (loop levels never see it -- it is consumed
-- inside `parseMul`).
theorem opMul_star_some : ∀ (T : List Token),
    opMul ([.zeichen "*"] ++ T) = some ("*", T) := by
  intro T
  rfl
theorem hrs_star : ∀ (T : List Token),
    ruhigSuff ([.zeichen "*"] ++ T) = true := by
  intro T
  rfl
theorem hrg_star : ∀ (T : List Token),
    ruhigGleit ([.zeichen "*"] ++ T) = true := by
  intro T
  rfl
-- Facts for the `||` inner trace: every loop below `Or`
-- misses the concrete `||`, and `parseOrL` consumes it.
theorem opMul_orbar : ∀ (T : List Token),
    opMul ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opAdd_orbar : ∀ (T : List Token),
    opAdd ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opBit_orbar : ∀ (T : List Token),
    opBit ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opVgl_orbar : ∀ (T : List Token),
    opVgl ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opUnd_orbar : ∀ (T : List Token),
    opUnd ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opOder_or_some : ∀ (T : List Token),
    opOder ([.zeichen "||"] ++ T) = some T := by
  intro T
  rfl
theorem hrs_orbar : ∀ (T : List Token),
    ruhigSuff ([.zeichen "||"] ++ T) = true := by
  intro T
  rfl
theorem hrg_orbar : ∀ (T : List Token),
    ruhigGleit ([.zeichen "||"] ++ T) = true := by
  intro T
  rfl
-- Facts for the `&&` inner trace: every loop below `And`
-- misses the concrete `&&`, and `parseAndL` consumes it.
theorem opMul_andbar : ∀ (T : List Token),
    opMul ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opAdd_andbar : ∀ (T : List Token),
    opAdd ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opBit_andbar : ∀ (T : List Token),
    opBit ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opVgl_andbar : ∀ (T : List Token),
    opVgl ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opUnd_and_some : ∀ (T : List Token),
    opUnd ([.zeichen "&&"] ++ T) = some T := by
  intro T
  rfl
theorem hrs_andbar : ∀ (T : List Token),
    ruhigSuff ([.zeichen "&&"] ++ T) = true := by
  intro T
  rfl
theorem hrg_andbar : ∀ (T : List Token),
    ruhigGleit ([.zeichen "&&"] ++ T) = true := by
  intro T
  rfl
theorem hrs_plus : ∀ (T : List Token),
    ruhigSuff ([.zeichen "+"] ++ T) = true := by
  intro T
  rfl
theorem hrg_plus : ∀ (T : List Token),
    ruhigGleit ([.zeichen "+"] ++ T) = true := by
  intro T
  rfl
theorem hr_paren : ∀ (T : List Token),
    ruhig ([.zeichen ")"] ++ T) = true := by
  intro T
  rfl
theorem hrs_paren : ∀ (T : List Token),
    ruhigSuff ([.zeichen ")"] ++ T) = true := by
  intro T
  rfl
theorem hrg_paren : ∀ (T : List Token),
    ruhigGleit ([.zeichen ")"] ++ T) = true := by
  intro T
  rfl

-- The `+` inner trace (`BKern` from `RKern`): `parseOr`
-- descends Or->And->Cmp->Bit->Add, `parseAdd` runs `parseMul`
-- on `l` (the `+` follow needs no `ruhig`: `parseUnary` runs no
-- loop and `parseMulL` stops on the concrete `+`), consumes `+`
-- and `r`, stops at `)`, and every level above stops at `)`.
-- Only the `parseUnary` leg of `RKern` is used (weak premises);
-- no `ruhig` hypothesis appears anywhere. Each leg is
-- generalised over its own fuel, exactly like `tower_up`, and
-- every token list is written right-nested (the canonical form).
theorem kernB_step : ∀ (n : Nat), RKern n → BKern (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, -, -, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  -- Canonicalise the goal once (right-nested); every leg below
  -- is stated in this shape.
  simp only [List.append_assoc] at ⊢
  -- Left operand through `parseMul` with the `+` follow.
  have hMl : ∀ (G5 : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G5 →
      parseMul G5 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "+"] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have h51 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl := hUn l ([.zeichen "+"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G6 hln hgl
      (hrs_plus _) (hrg_plus _) (by omega)
    have h52 : 1 ≤ G6 := by omega
    obtain ⟨G7, rfl⟩ : ∃ G7, G6 = G7 + 1 := ⟨G6 - 1, by omega⟩
    have hstop := opMul_plus (druckToks r ++ ([.zeichen ")"] ++ W))
    simp only [parseMul, parseMulL, hUl, hstop] at ⊢
  -- Right operand through `parseMul` with the `)` follow.
  have hMr : ∀ (G5x : Nat),
      12 * (groesse r + 1) + groesse r + 3 ≤ G5x →
      parseMul G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have h53 : 1 ≤ G5x := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G5x = G6x + 1 := ⟨G5x - 1, by omega⟩
    have hUr := hUn r ([.zeichen ")"] ++ W) G6x hrn hgr
      (hrs_paren W) (hrg_paren W) (by omega)
    have h54 : 1 ≤ G6x := by omega
    obtain ⟨G7x, rfl⟩ : ∃ G7x, G6x = G7x + 1 := ⟨G6x - 1, by omega⟩
    have hstop := opMul_paren W
    simp only [parseMul, parseMulL, hUr, hstop] at ⊢
  -- The `parseAdd` core: `l`, consume `+`, `r`, stop at `)`.
  have hAdd : ∀ (G4 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have hMl' := hMl G5 (by omega)
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G5x, rfl⟩ : ∃ G5x, G5 = G5x + 1 := ⟨G5 - 1, by omega⟩
    have hop := opAdd_plus (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr' := hMr G5x (by omega)
    have hstop := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    -- One more strip for the SECOND `parseAddL` (after the
    -- consume step); fuel-free (`omega` from the bound).
    have h43 : 1 ≤ G5x := by omega
    obtain ⟨G5y, rfl⟩ : ∃ G5y, G5x = G5y + 1 := ⟨G5x - 1, by omega⟩
    simp only [parseAdd, parseAddL, hMl', hop, hMr', hstop] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAdd' := hAdd G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hstop := stopBit ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseBit, parseBitL, hAdd', hstop] at ⊢
  have hCmp : ∀ (G2 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr F hF

end Gabbro.Grammatik.Parser
